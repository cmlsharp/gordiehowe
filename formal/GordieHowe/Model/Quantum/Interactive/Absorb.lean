-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Embed

@[expose] public section

/-!
# Absorbing classical side requests into an adversary

An interactive adversary `A` (`AdaptiveIAlg`) whose requests are answered by a challenger that
relays some of them to a main challenger and answers the others itself, from values that do not
depend on the oracle (a classical *side* challenger: no oracle queries, no reprogramming), is,
at fixed side values, an adversary of the main challenger's interface: the side requests and
answers move into its workspace.

- `SideRelay`: the relay. Request number `c` with request `r` is sent to the main challenger as
  `route c r`; the reply to `A` is `answer c r a` from the main challenger's reply `a`.
  `SideRelay.logs` relays a log register. The structure imposes nothing on the side requests; the
  intended use sends a side request as a request the main challenger answers without queries or
  assignments (an inert request), with `answer` ignoring its reply, and what `outLaw_absorb`
  needs is only the hypothesis `SideRelay.Relays` below (checked for a concrete relay through
  `SideRelay.RelaysChallenger`, `GordieHowe/Model/Quantum/Interactive/AbsorbRelay.lean`).
- `SideRelay.Relays F E ω E' ω'`: the environment `E` at tape `ω` (the challenger of `A`) is the
  relay `F` of the environment `E'` at tape `ω'` (the main challenger): at every log register its
  replies are the relayed replies and its oracle in force is the main oracle at the relayed logs.
- `AdaptiveIAlg.absorb A F`: the absorbed adversary. Its workspace holds `A`'s workspace, request
  and response registers, a copy of `A`'s logs and the main challenger's replies; before each slot
  it runs `A`'s step and writes the relayed request; after the slot it writes the relayed reply
  into `A`'s response register. Its shape is `AlgShape.absorbS` of `A`'s (`absorb_toShape`).
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum

/-! ### Events of the composed registers -/

/-- **An event of the composed registers has the coin average of the mixed game's diagonal on it**
(`KindAlg.outLaw_composeBothOut_some` with the output read as the composed registers). -/
theorem KindAlg.toOuterMeasure_outLaw_composeBothOut_id {X Y Req Resp O : Type} [Fintype X]
    [DecidableEq X] [Fintype Y] [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp]
    [DecidableEq Resp] [Nonempty X] [AddGroup Y] [Nonempty Y] {ksB : KindShape X Y Req Resp} (B : KindAlg ksB O)
    (C : Challenger X Y Req Resp) (H : X → Y) (P : B.CW C → Prop) [DecidablePred P] :
    ((B.composeBothOut C id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      ENNReal.ofReal (∑ c, (C.coins c).toReal * ∑ r : B.G,
        if P (B.emb C H c B.slots r).1 then (B.mgRun C.toPureEnv (H, c) true r r).re else 0) := by
  have hmap : (B.composeBothOut C (fun v => decide (P v))).outLaw H =
      ((B.composeBothOut C id).outLaw H).map (Option.map fun v => decide (P v)) := by
    simp only [Alg.outLaw]
    rw [PMF.map_comp, Option.map_comp_map]
    rfl
  have h := B.outLaw_composeBothOut_some C (fun v => decide (P v)) H true
  rw [hmap, PMF.map_apply] at h
  rw [PMF.toOuterMeasure_apply]
  have hs : ∀ o : Option (B.CW C), ({o | ∃ v ∈ o, P v} : Set _).indicator
      (((B.composeBothOut C id).outLaw H)) o =
      if some true = Option.map (fun v => decide (P v)) o then
        ((B.composeBothOut C id).outLaw H) o else 0 := by
    intro o
    rcases o with _ | v
    · simp
    · by_cases hv : P v <;> simp [Set.indicator, hv]
  simp only [hs]
  convert h using 1
  · exact tsum_congr fun x => by split_ifs <;> rfl
  · simp only [decide_eq_true_eq]

/-! ### The relay -/

/-- **A relay of requests to a main challenger**: request number `c` with request `r` is sent as
`route c r`, and the reply `a` of the main challenger is relayed back as `answer c r a`. The
structure imposes nothing more: in the intended use a side request is sent as an inert request
of the main challenger (answered without queries or assignments) and `answer c r` ignores its
reply, and the theorems take the relay condition `SideRelay.Relays` as a hypothesis. -/
structure SideRelay (Req Resp Req' Resp' : Type) where
  /-- The main request sent for request number `c` with request `r`. -/
  route : ℕ → Req → Req'
  /-- The reply to request number `c` with request `r`, from the main challenger's reply. -/
  answer : ℕ → Req → Option Resp' → Option Resp

namespace SideRelay

variable {Req Resp Req' Resp' : Type} (F : SideRelay Req Resp Req' Resp') {m : ℕ}

/-- **The relayed logs**: log `k` holding request `r` becomes the main request `route c r`, with
`c` the number of requests before slot `k`. -/
def logs (lg : LogReg Req m) : LogReg Req' m :=
  fun k => (lg k).map (F.route (requestsBefore lg k).length)

theorem logs_apply (lg : LogReg Req m) (k : Fin m) :
    F.logs lg k = (lg k).map (F.route (requestsBefore lg k).length) :=
  rfl

variable {X Y : Type} [AddGroup Y]

/-- **An environment is the relay of a main environment** (at fixed tapes): at every log
register, the reply of slot `k` holding request `r` is the relayed reply of the main
environment at the relayed logs, and the oracle in force is the main oracle in force at the
relayed logs. -/
structure Relays {Ω Ω' St St' : Type} {Q Q' : ℕ} [OracleState St X Y] [OracleState St' X Y]
    (E : Env Ω Req Resp X Y Q St) (ω : Ω) (E' : Env Ω' Req' Resp' X Y Q' St') (ω' : Ω') (m : ℕ) :
    Prop where
  /-- The replies are the relayed replies. -/
  answer_eq : ∀ (lg : LogReg Req m) (k : Fin m) (r : Req), lg k = some r →
    E.answer ω lg k = F.answer (requestsBefore lg k).length r (E'.answer ω' (F.logs lg) k)
  /-- The oracle in force is the main oracle in force at the relayed logs. -/
  oracle_eq : ∀ lg : LogReg Req m, E.oracle ω lg = E'.oracle ω' (F.logs lg)

end SideRelay

/-- **A composition of trace-preserving Kraus maps is trace preserving.** -/
theorem KrausMap.comp_tp {R₁ R₂ ι : Type*} [Fintype R₁] [Fintype R₂] [Fintype ι] [DecidableEq ι]
    {K₂ : KrausMap R₂ ι ι} {K₁ : KrausMap R₁ ι ι} (h₂ : ∑ r, (K₂.op r)ᴴ * K₂.op r = 1)
    (h₁ : ∑ r, (K₁.op r)ᴴ * K₁.op r = 1) :
    ∑ r, ((K₂.comp K₁).op r)ᴴ * (K₂.comp K₁).op r = 1 := by
  simp only [KrausMap.comp, Fintype.sum_prod_type, conjTranspose_mul]
  have h : ∀ r₁, ∑ r₂, (K₁.op r₁)ᴴ * (K₂.op r₂)ᴴ * (K₂.op r₂ * K₁.op r₁) =
      (K₁.op r₁)ᴴ * K₁.op r₁ := fun r₁ => by
    have : ∀ r₂, (K₁.op r₁)ᴴ * (K₂.op r₂)ᴴ * (K₂.op r₂ * K₁.op r₁) =
        (K₁.op r₁)ᴴ * ((K₂.op r₂)ᴴ * K₂.op r₂) * K₁.op r₁ := fun r₂ => by
      simp only [Matrix.mul_assoc]
    simp only [this, ← Finset.sum_mul, ← Finset.mul_sum, h₂, Matrix.mul_one]
  simp only [h, h₁]

namespace KrausMap

variable {R₁ R₂ ι : Type*} [Fintype R₁] [Fintype R₂] [Fintype ι] [DecidableEq ι]

/-- **A restricted Kraus map is the Kraus map conjugated by the projector** onto the set. -/
theorem restrict_apply (K : KrausMap R₁ ι ι) (p : ι → Bool) (ρ : Matrix ι ι ℂ) :
    (K.restrict p) ρ = Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) * K ρ *
      Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) := by
  simp only [apply, restrict, Matrix.mul_sum, Matrix.sum_mul, conjTranspose_mul,
    Matrix.diagonal_conjTranspose]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hs : star (fun i => if p i then (1 : ℂ) else 0) = fun i => if p i then (1 : ℂ) else 0 := by
    funext i
    by_cases h : p i <;> simp [h]
  rw [hs]
  simp only [Matrix.mul_assoc]

/-- The identity on a second factor distributes over composition. -/
theorem tensorId_comp (K₂ : KrausMap R₂ ι ι) (K₁ : KrausMap R₁ ι ι) (A : Type*) [Fintype A]
    [DecidableEq A] : (K₂.comp K₁).tensorId A = (K₂.tensorId A).comp (K₁.tensorId A) :=
  ext_op (funext fun _ => by
    simp only [tensorId, comp]
    rw [← mul_kronecker_mul, Matrix.one_mul])

/-- Moving along an equivalence distributes over composition. -/
theorem reindex_comp {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (K₂ : KrausMap R₂ ι ι)
    (K₁ : KrausMap R₁ ι ι) : (K₂.comp K₁).reindex e = (K₂.reindex e).comp (K₁.reindex e) :=
  ext_op (funext fun _ => by
    simp only [reindex, comp]
    rw [submatrix_mul_equiv])

/-- A basis permutation with the identity on a second factor. -/
theorem ofPerm_tensorId (π : Equiv.Perm ι) (A : Type*) [Fintype A] [DecidableEq A] :
    (ofPerm π).tensorId A = ofPerm (π.prodCongr (Equiv.refl A)) :=
  ext_op (funext fun _ => by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [tensorId, ofPerm, permConj, KrausMap.identity, kroneckerMap_apply, submatrix_apply,
      Matrix.one_apply, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.refl_symm, Prod.map,
      Equiv.coe_refl, id, Prod.mk.injEq]
    by_cases h1 : π.symm a = c <;> by_cases h2 : b = d <;> simp [h1, h2])

/-- A basis permutation moved along an equivalence. -/
theorem ofPerm_reindex {κ : Type*} [Fintype κ] [DecidableEq κ] (e : ι ≃ κ) (π : Equiv.Perm ι) :
    (ofPerm π).reindex e = ofPerm (e.permCongr π) :=
  ext_op (funext fun _ => by
    ext a b
    simp only [reindex, ofPerm, permConj, KrausMap.identity, submatrix_apply, Matrix.one_apply,
      Equiv.coe_refl, id]
    have key : ∀ a b : κ, π.symm (e.symm a) = e.symm b ↔ (e.permCongr π).symm a = b := by
      intro a b
      rw [Equiv.symm_apply_eq, Equiv.symm_apply_eq, Equiv.symm_apply_eq (e.permCongr π),
        Equiv.permCongr_apply]
    split_ifs with h1 h2 h2
    · rfl
    · exact absurd ((key a b).mp h1) h2
    · exact absurd ((key a b).mpr h2) h1
    · rfl)

/-- A restriction applied after a composition restricts the outer map. -/
theorem restrict_comp (K₂ : KrausMap R₂ ι ι) (K₁ : KrausMap R₁ ι ι) (p : ι → Bool) :
    (K₂.comp K₁).restrict p = (K₂.restrict p).comp K₁ :=
  ext_op (funext fun _ => by simp only [restrict, comp, Matrix.mul_assoc])

/-- A permutation applied after a composition conjugates the outer map. -/
theorem permConj_refl_comp (K₂ : KrausMap R₂ ι ι) (K₁ : KrausMap R₁ ι ι) (τ : Equiv.Perm ι) :
    (K₂.comp K₁).permConj (Equiv.refl ι) τ = (K₂.permConj (Equiv.refl ι) τ).comp K₁ :=
  ext_op (funext fun _ => by
    ext a b
    simp only [permConj, comp, submatrix_apply, Matrix.mul_apply, Equiv.coe_refl, id])

/-- **A basis permutation that keeps the set and commutes with `τ` commutes with the restriction
and the conjugation by `τ`.** -/
theorem permConj_restrict_ofPerm_comp_apply (K : KrausMap R₁ ι ι) (π τ : Equiv.Perm ι)
    (p : ι → Bool) (hp : ∀ i, p (π i) = p i) (hτ : ∀ i, τ (π i) = π (τ i)) (ρ : Matrix ι ι ℂ) :
    ((((ofPerm π).comp K).restrict p).permConj (Equiv.refl ι) τ) ρ =
      (((K.restrict p).permConj (Equiv.refl ι) τ) ρ).submatrix π.symm π.symm := by
  rw [permConj_apply, permConj_apply, restrict_apply, restrict_apply, comp_apply, ofPerm_apply]
  have hp' : ∀ i, p (π.symm i) = p i := fun i => by rw [← hp (π.symm i), Equiv.apply_symm_apply]
  have hτ' : ∀ i, τ.symm (π.symm i) = π.symm (τ.symm i) := fun i => by
    rw [Equiv.symm_apply_eq]
    have h := hτ (π.symm (τ.symm i))
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
    exact (Equiv.symm_apply_eq π).2 h
  ext i j
  simp only [submatrix_apply, Equiv.refl_symm, Equiv.coe_refl, Matrix.diagonal_mul,
    Matrix.mul_diagonal, hτ', hp']

/-- **A conjugated Kraus map stays conjugated under `⊗ 1`**: if `K` acts as `K₀` between the
basis permutations `π₁` and `π₂`, then `K ⊗ 1` acts as `K₀ ⊗ 1` between `π₁ × 1` and
`π₂ × 1`. -/
theorem tensorId_apply_of_conj {R₀ : Type*} [Fintype R₀] {K : KrausMap R₁ ι ι}
    {K₀ : KrausMap R₀ ι ι} {π₁ π₂ : Equiv.Perm ι}
    (h : ∀ ρ, K ρ = (K₀ (ρ.submatrix π₁.symm π₁.symm)).submatrix π₂.symm π₂.symm)
    (L : Type*) [Fintype L] [DecidableEq L] (M : Matrix (ι × L) (ι × L) ℂ) :
    (K.tensorId L) M = ((K₀.tensorId L) (M.submatrix (π₁.prodCongr (Equiv.refl L)).symm
      (π₁.prodCongr (Equiv.refl L)).symm)).submatrix (π₂.prodCongr (Equiv.refl L)).symm
      (π₂.prodCongr (Equiv.refl L)).symm := by
  ext ⟨i, a⟩ ⟨j, b⟩
  rw [tensorId_apply_apply]
  change K (Matrix.of fun k l => M (k, a) (l, b)) i j = _
  rw [h, submatrix_apply, submatrix_apply]
  simp only [Equiv.prodCongr_symm, Equiv.prodCongr_apply, Prod.map, Equiv.refl_symm,
    Equiv.coe_refl, id]
  rw [tensorId_apply_apply]
  rfl

/-- **A conjugated Kraus map stays conjugated when tensored and moved along an equivalence.** -/
theorem tensorId_reindex_apply_of_conj {R₀ κ : Type*} [Fintype R₀] [Fintype κ] [DecidableEq κ]
    {K : KrausMap R₁ ι ι} {K₀ : KrausMap R₀ ι ι} {π₁ π₂ : Equiv.Perm ι}
    (h : ∀ ρ, K ρ = (K₀ (ρ.submatrix π₁.symm π₁.symm)).submatrix π₂.symm π₂.symm)
    (L : Type*) [Fintype L] [DecidableEq L] (e : ι × L ≃ κ) (M : Matrix κ κ ℂ) :
    ((K.tensorId L).reindex e) M = (((K₀.tensorId L).reindex e)
      (M.submatrix (e.permCongr (π₁.prodCongr (Equiv.refl L))).symm
        (e.permCongr (π₁.prodCongr (Equiv.refl L))).symm)).submatrix
      (e.permCongr (π₂.prodCongr (Equiv.refl L))).symm
      (e.permCongr (π₂.prodCongr (Equiv.refl L))).symm := by
  have hp : ∀ (π : Equiv.Perm (ι × L)) (x : κ), (e.permCongr π).symm x = e (π.symm (e.symm x)) :=
    fun π x => by rw [Equiv.symm_apply_eq, Equiv.permCongr_apply, Equiv.symm_apply_apply,
      Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [reindex_apply, reindex_apply, tensorId_apply_of_conj h]
  have hM : (M.submatrix e e).submatrix (π₁.prodCongr (Equiv.refl L)).symm
      (π₁.prodCongr (Equiv.refl L)).symm =
      (M.submatrix (e.permCongr (π₁.prodCongr (Equiv.refl L))).symm
        (e.permCongr (π₁.prodCongr (Equiv.refl L))).symm).submatrix e e := by
    ext p q
    simp only [submatrix_apply, hp, Equiv.symm_apply_apply]
  rw [hM]
  ext x y
  simp only [submatrix_apply, hp, Equiv.symm_apply_apply]

/-- **`K ⊗ 1` commutes with a placement along `id × φ`, moved along equivalences**: placing a
matrix on `G ≃ D × L` into `G' ≃ D × M` by `φ` on the second factor commutes with `K` on `D`. -/
theorem tensorId_reindex_apply_embed {R D L M G G' : Type*} [Fintype R] [Fintype D] [DecidableEq D]
    [Fintype L] [DecidableEq L] [Fintype M] [DecidableEq M] [Fintype G] [DecidableEq G]
    [Fintype G'] [DecidableEq G'] (K : KrausMap R D D) (e₁ : D × L ≃ G) (e₂ : D × M ≃ G')
    (φ : L → M) (σ : Matrix G G ℂ) :
    ((K.tensorId M).reindex e₂) (embed (e₂ ∘ Prod.map _root_.id φ ∘ e₁.symm) σ) =
      embed (e₂ ∘ Prod.map _root_.id φ ∘ e₁.symm) (((K.tensorId L).reindex e₁) σ) := by
  rw [reindex_apply, reindex_apply, submatrix_embed_equiv]
  have h1 : (e₂.symm ∘ (e₂ ∘ Prod.map _root_.id φ ∘ e₁.symm)) = Prod.map _root_.id φ ∘ e₁.symm := by
    funext x
    simp
  rw [h1, embed_comp_equiv, tensorId_apply_embed, submatrix_embed_equiv]
  have h2 : (e₂.symm.symm ∘ Prod.map _root_.id φ) = (e₂ ∘ Prod.map _root_.id φ ∘ e₁.symm) ∘ e₁ := by
    funext x
    simp
  rw [h2, embed_comp_equiv, Equiv.symm_symm]

end KrausMap

/-- **Placing twice is placing along the composition.** -/
theorem embed_embed {κ ι ι' : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]
    [Fintype ι'] [DecidableEq ι'] (f : ι → ι') (g : κ → ι) (σ : Matrix κ κ ℂ) :
    embed f (embed g σ) = embed (f ∘ g) σ := by
  have hj : jmat f * jmat g = jmat (f ∘ g) := by
    ext i c
    simp only [jmat, Matrix.mul_apply, Function.comp, mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single (g c) (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
    simp
  rw [embed_eq_jmat, embed_eq_jmat, embed_eq_jmat, ← hj, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

/-- **A state with a register in a basis state appended, moved along an equivalence, is the state
placed along the map** `d ↦ e (d, z)`. -/
theorem MState.reindex_tensorKet_mat {ι κ E : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype E] [DecidableEq E] (e : ι × E ≃ κ) (ρ : MState ι) (z : E) :
    (MState.reindex e (ρ.tensorKet z)).mat = embed (fun d => e (d, z)) ρ.mat := by
  ext x y
  simp only [MState.reindex, MState.tensorKet_mat, submatrix_apply, kroneckerMap_apply,
    Matrix.single_apply, embed]
  rw [Finset.sum_eq_single (e.symm x).1 (fun a _ ha => Finset.sum_eq_zero fun b _ => by
      rw [if_neg]; rintro ⟨h1, -⟩; exact ha (by rw [← h1]; simp)) (by simp),
    Finset.sum_eq_single (e.symm y).1 (fun b _ hb => by
      rw [if_neg]; rintro ⟨-, h2⟩; exact hb (by rw [← h2]; simp)) (by simp)]
  have key : (e ((e.symm x).1, z) = x ∧ e ((e.symm y).1, z) = y) ↔
      (z = (e.symm x).2 ∧ z = (e.symm y).2) := by
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← h1]; simp, by rw [← h2]; simp⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [h1]; simp, by rw [h2]; simp⟩
  rw [if_congr key rfl rfl]
  split_ifs with h <;> simp [h]

/-! ### The registers of the absorbed adversary -/

/-- **The workspace of an absorbed adversary**: the adversary's workspace, request and response
registers, a copy of its logs, and a store of the main challenger's replies, one per slot. -/
@[ext]
structure AbsorbedWork (W Req Resp Resp' : Type) (m : ℕ) where
  /-- The adversary's workspace. -/
  work : W
  /-- The adversary's request register. -/
  request : Req
  /-- The adversary's response register. -/
  response : Option Resp
  /-- The copy of the adversary's logs. -/
  logs : LogReg Req m
  /-- The main challenger's reply of each slot. -/
  store : Fin m → Option Resp'

namespace AbsorbedWork

variable {W Req Resp Resp' : Type} {m : ℕ}

/-- The workspace as its parts. -/
def equivProd (W Req Resp Resp' : Type) (m : ℕ) :
    AbsorbedWork W Req Resp Resp' m ≃
      W × Req × Option Resp × LogReg Req m × (Fin m → Option Resp') where
  toFun a := (a.work, a.request, a.response, a.logs, a.store)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Fintype W] [Fintype Req] [DecidableEq Req] [Fintype Resp] [Fintype Resp'] :
    Fintype (AbsorbedWork W Req Resp Resp' m) :=
  Fintype.ofEquiv _ (equivProd W Req Resp Resp' m).symm

instance [DecidableEq W] [DecidableEq Req] [DecidableEq Resp] [DecidableEq Resp'] :
    DecidableEq (AbsorbedWork W Req Resp Resp' m) :=
  haveI : DecidableEq (LogReg Req m) := inferInstance
  haveI : DecidableEq (Fin m → Option Resp') := inferInstance
  haveI : DecidableEq (LogReg Req m × (Fin m → Option Resp')) := inferInstance
  haveI : DecidableEq (Option Resp × LogReg Req m × (Fin m → Option Resp')) := inferInstance
  haveI : DecidableEq (Req × Option Resp × LogReg Req m × (Fin m → Option Resp')) := inferInstance
  Equiv.decidableEq (equivProd W Req Resp Resp' m)

end AbsorbedWork

namespace AdaptiveIAlg

variable {X Y Req Resp O Req' Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Fintype Req'] [DecidableEq Req']
  [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req']
  {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O) (F : SideRelay Req Resp Req' Resp')

/-- The workspace of the absorbed adversary. -/
abbrev AbsW : Type := AbsorbedWork A.W Req Resp Resp' A.slots

/-- The registers of the absorbed adversary beside those of `A`: the copy of the logs, the store,
the main request register and the main response register. -/
abbrev AbsRest : Type := LogReg Req A.slots × (Fin A.slots → Option Resp') × Req' × Option Resp'

omit [Inhabited Req'] in
/-- The registers of the absorbed adversary at the shape `s` as those of `s` and the rest. -/
def _root_.GordieHowe.Quantum.AlgShape.absSplit (s : AlgShape X Y Req Resp) :
    DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp' ≃
      DReg s.W s.width X Y Req Resp ×
        (LogReg Req s.slots × (Fin s.slots → Option Resp') × Req' × Option Resp') where
  toFun d := (((d.1.1.work, d.1.1.request, d.1.1.response), d.2),
    (d.1.1.logs, d.1.1.store, d.1.2.1, d.1.2.2))
  invFun p := ((⟨p.1.1.1, p.1.1.2.1, p.1.1.2.2, p.2.1, p.2.2.1⟩, p.2.2.2.1, p.2.2.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The registers of the absorbed adversary as those of `A` and the rest (`AlgShape.absSplit`). -/
abbrev absSplit : DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp' ≃
    DReg A.W A.width X Y Req Resp × A.AbsRest (Req' := Req') (Resp' := Resp') :=
  shA.absSplit

/-- The number of requests before slot `k` in the copy of the logs. -/
abbrev reqCount (lg : LogReg Req A.slots) (k : Fin A.slots) : ℕ := (requestsBefore lg k).length

/-- **Writing the relayed request of slot `k`** at the shape `s` and the kind `kind`, on the
branches with a request: the request is copied into log `k` of the copy of the logs, and the main
request register (blank `default`) receives `route c r`, with `c` the number of requests before
slot `k`. An involution. -/
def _root_.GordieHowe.Quantum.AlgShape.setPerm (s : AlgShape X Y Req Resp) (kind : s.W → Bool)
    (F : SideRelay Req Resp Req' Resp') (k : Fin s.slots) :
    Equiv.Perm (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  Function.Involutive.toPerm
    (fun d => if kind d.1.1.work then
      ((⟨d.1.1.work, d.1.1.request, d.1.1.response,
          Function.update d.1.1.logs k (Equiv.swap none (some d.1.1.request) (d.1.1.logs k)),
          d.1.1.store⟩,
        Equiv.swap default (F.route (requestsBefore d.1.1.logs k).length d.1.1.request) d.1.2.1,
          d.1.2.2), d.2)
      else d)
    fun d => by
      by_cases h : kind d.1.1.work
      · simp only [h, ite_true]
        have hc : (requestsBefore (Function.update d.1.1.logs k
            (Equiv.swap none (some d.1.1.request) (d.1.1.logs k))) k).length =
              (requestsBefore d.1.1.logs k).length :=
          congrArg List.length (requestsBefore_congr fun k' hk' =>
            Function.update_of_ne (fun e => by subst e; omega) _ _)
        simp [hc]
      · simp [h]

/-- **Writing the relayed request of slot `k`** (`AlgShape.setPerm` at `A`'s kind). -/
abbrev setPerm (k : Fin A.slots) :
    Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.setPerm A.kind F k

/-- **Storing the main reply of slot `j`** at the shape `s`, on the branches whose copy of log `j`
holds a request: the main response register and the store of slot `j` are exchanged, so the reply
moves into the store and the register becomes blank. An involution. -/
def _root_.GordieHowe.Quantum.AlgShape.storePerm (s : AlgShape X Y Req Resp) (j : Fin s.slots) :
    Equiv.Perm (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  Function.Involutive.toPerm
    (fun d => if (d.1.1.logs j).isSome then
      ((⟨d.1.1.work, d.1.1.request, d.1.1.response, d.1.1.logs,
          Function.update d.1.1.store j d.1.2.2⟩, d.1.2.1, d.1.1.store j), d.2)
      else d)
    fun d => by
      by_cases h : (d.1.1.logs j).isSome
      · simp [h]
      · simp [h]

/-- **Storing the main reply of slot `j`** (`AlgShape.storePerm`). -/
abbrev storePerm (j : Fin A.slots) :
    Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.storePerm j

/-- **Writing the relayed reply of slot `j`** at the shape `s` into the adversary's response
register, on the branches whose copy of log `j` holds a request `r`: the swap of `none` and
`answer c r a`, with `a` the stored main reply and `c` the number of requests before slot `j`. An
involution. -/
def _root_.GordieHowe.Quantum.AlgShape.answerPerm (s : AlgShape X Y Req Resp)
    (F : SideRelay Req Resp Req' Resp') (j : Fin s.slots) :
    Equiv.Perm (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  Function.Involutive.toPerm
    (fun d => match d.1.1.logs j with
      | none => d
      | some r => ((⟨d.1.1.work, d.1.1.request,
          Equiv.swap none (F.answer (requestsBefore d.1.1.logs j).length r (d.1.1.store j))
            d.1.1.response,
          d.1.1.logs, d.1.1.store⟩, d.1.2), d.2))
    fun d => by
      rcases h : d.1.1.logs j with _ | r
      · simp [h]
      · simp [h]

/-- **Writing the relayed reply of slot `j`** (`AlgShape.answerPerm`). -/
abbrev answerPerm (j : Fin A.slots) :
    Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.answerPerm F j

/-- **Clearing the relayed request of slot `j`** at the shape `s` from the main request register,
on the branches whose copy of log `j` holds a request `r`: the swap of `default` and `route c r`.
An involution. -/
def _root_.GordieHowe.Quantum.AlgShape.clearPerm (s : AlgShape X Y Req Resp)
    (F : SideRelay Req Resp Req' Resp') (j : Fin s.slots) :
    Equiv.Perm (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  Function.Involutive.toPerm
    (fun d => match d.1.1.logs j with
      | none => d
      | some r => ((d.1.1, Equiv.swap default (F.route (requestsBefore d.1.1.logs j).length r)
          d.1.2.1, d.1.2.2), d.2))
    fun d => by
      rcases h : d.1.1.logs j with _ | r
      · simp [h]
      · simp [h]

/-- **Clearing the relayed request of slot `j`** (`AlgShape.clearPerm`). -/
abbrev clearPerm (j : Fin A.slots) :
    Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.clearPerm F j

/-- **After slot `j`** at the shape `s`: the main reply stored, the relayed reply written, the
relayed request cleared. -/
def _root_.GordieHowe.Quantum.AlgShape.afterPerm (s : AlgShape X Y Req Resp)
    (F : SideRelay Req Resp Req' Resp') (j : Fin s.slots) :
    Equiv.Perm (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  ((s.storePerm j).trans (s.answerPerm F j)).trans (s.clearPerm F j)

/-- **After slot `j`** (`AlgShape.afterPerm`). -/
abbrev afterPerm (j : Fin A.slots) :
    Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.afterPerm F j

/-- The permutation after slot `k - 1` at the shape `s`, applied before step `k` (the identity for
`k = 0` and after the last slot). -/
def _root_.GordieHowe.Quantum.AlgShape.afterAt (s : AlgShape X Y Req Resp)
    (F : SideRelay Req Resp Req' Resp') (k : ℕ) :
    Equiv.Perm (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  if h : 0 < k ∧ k - 1 < s.slots then s.afterPerm F ⟨k - 1, h.2⟩ else Equiv.refl _

/-- The permutation after slot `k - 1`, applied before step `k` (`AlgShape.afterAt`). -/
abbrev afterAt (k : ℕ) : Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.afterAt F k

/-- The permutation before slot `k` at the shape `s` and the kind `kind`, applied after step `k`
(the identity from the last slot on). -/
def _root_.GordieHowe.Quantum.AlgShape.setAt (s : AlgShape X Y Req Resp) (kind : s.W → Bool)
    (F : SideRelay Req Resp Req' Resp') (k : ℕ) :
    Equiv.Perm (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  if h : k < s.slots then s.setPerm kind F ⟨k, h⟩ else Equiv.refl _

/-- The permutation before slot `k`, applied after step `k` (`AlgShape.setAt` at `A`'s kind). -/
abbrev setAt (k : ℕ) : Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.setAt A.kind F k

omit [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] in
/-- The permutation before slot `k` through `A`'s helpers. -/
theorem setAt_def (k : ℕ) :
    A.setAt F k = if h : k < A.slots then A.setPerm F ⟨k, h⟩ else Equiv.refl _ :=
  rfl

omit [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] in
/-- The permutation after slot `k - 1` through `A`'s helpers. -/
theorem afterAt_def (k : ℕ) :
    A.afterAt F k = if h : 0 < k ∧ k - 1 < A.slots then A.afterPerm F ⟨k - 1, h.2⟩
      else Equiv.refl _ :=
  rfl

omit [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] in
/-- After slot `j` through `A`'s helpers. -/
theorem afterPerm_def (j : Fin A.slots) :
    A.afterPerm F j = ((A.storePerm j).trans (A.answerPerm F j)).trans (A.clearPerm F j) :=
  rfl

omit [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] in
/-- `setAt` below the last slot is the relayed request of the slot. -/
theorem setAt_of_lt {k : ℕ} (hk : k < A.slots) : A.setAt F k = A.setPerm F ⟨k, hk⟩ :=
  dif_pos hk

omit [Inhabited Req'] in
instance (s : AlgShape X Y Req Resp) :
    DecidableEq (LogReg Req s.slots × (Fin s.slots → Option Resp') × Req' × Option Resp') :=
  haveI : DecidableEq (LogReg Req s.slots) := inferInstance
  haveI : DecidableEq (Fin s.slots → Option Resp') := inferInstance
  inferInstance

omit [Inhabited Req'] in
instance (s : AlgShape X Y Req Resp) :
    DecidableEq (DReg s.W s.width X Y Req Resp ×
      (LogReg Req s.slots × (Fin s.slots → Option Resp') × Req' × Option Resp')) :=
  @instDecidableEqProd _ _ inferInstance inferInstance

omit [Inhabited Req'] in
/-- The step `step k` at the shape `s` on its registers, the identity on the rest. -/
def _root_.GordieHowe.Quantum.AlgShape.liftedStep (s : AlgShape X Y Req Resp)
    (step : StepIdx s.slots s.post →
      KrausMap s.R (DReg s.W s.width X Y Req Resp) (DReg s.W s.width X Y Req Resp))
    (k : StepIdx s.slots s.post) :
    KrausMap s.R (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp')
      (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  ((step k).tensorId
      (LogReg Req s.slots × (Fin s.slots → Option Resp') × Req' × Option Resp')).reindex
    (s.absSplit (Req' := Req') (Resp' := Resp')).symm

omit [Inhabited Req'] in
/-- The adversary's step `k` on its registers, the identity on the rest (`AlgShape.liftedStep`). -/
abbrev liftedStep (k : StepIdx A.slots A.post) :
    KrausMap A.R (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp')
      (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.liftedStep A.step k

/-- The blank values of the registers beside those of the adversary, at the shape `s`. -/
def _root_.GordieHowe.Quantum.AlgShape.absBlank (s : AlgShape X Y Req Resp) :
    LogReg Req s.slots × (Fin s.slots → Option Resp') × Req' × Option Resp' :=
  (fun _ => none, fun _ => none, default, none)

/-- The blank values of the registers beside those of the adversary (`AlgShape.absBlank`). -/
abbrev absBlank : A.AbsRest (Req' := Req') (Resp' := Resp') := shA.absBlank

/-- **Step `k` of the adversary with its side requests absorbed** at the shape `s`, for the kind
`kind`, the steps `step` and the relay `F`: the relayed reply of slot `k - 1` (`afterAt`), the step
`k`, the relayed request of slot `k` (`setAt`). Sealed, and of the kind and the steps only, so that
absorbed adversaries with different steps compare by their fields and a transformation that keeps
both (`mapOut`) keeps the step; it unfolds through `AlgShape.absorbStep_eq`. -/
@[irreducible, no_expose] def _root_.GordieHowe.Quantum.AlgShape.absorbStep
    (s : AlgShape X Y Req Resp) (kind : s.W → Bool)
    (step : StepIdx s.slots s.post →
      KrausMap s.R (DReg s.W s.width X Y Req Resp) (DReg s.W s.width X Y Req Resp))
    (F : SideRelay Req Resp Req' Resp') (k : StepIdx s.slots s.post) :
    KrausMap ((Unit × s.R) × Unit)
      (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp')
      (DReg (AbsorbedWork s.W Req Resp Resp' s.slots) s.width X Y Req' Resp') :=
  (KrausMap.ofPerm (s.setAt kind F k)).comp
    ((s.liftedStep step k).comp (KrausMap.ofPerm (s.afterAt F k)))

theorem _root_.GordieHowe.Quantum.AlgShape.absorbStep_eq (s : AlgShape X Y Req Resp)
    (kind : s.W → Bool)
    (step : StepIdx s.slots s.post →
      KrausMap s.R (DReg s.W s.width X Y Req Resp) (DReg s.W s.width X Y Req Resp))
    (F : SideRelay Req Resp Req' Resp') (k : StepIdx s.slots s.post) :
    s.absorbStep kind step F k = (KrausMap.ofPerm (s.setAt kind F k)).comp
      ((s.liftedStep step k).comp (KrausMap.ofPerm (s.afterAt F k))) := by
  unfold AlgShape.absorbStep
  rfl

/-- **Step `k` of the adversary with its side requests absorbed** (`AlgShape.absorbStep` at `A`'s
kind and steps). -/
abbrev absorbStep (F : SideRelay Req Resp Req' Resp') (k : StepIdx A.slots A.post) :
    KrausMap ((Unit × A.R) × Unit) (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp')
      (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :=
  shA.absorbStep A.kind A.step F k

theorem absorbStep_eq (F : SideRelay Req Resp Req' Resp') (k : StepIdx A.slots A.post) :
    A.absorbStep F k =
      (KrausMap.ofPerm (A.setAt F k)).comp
        ((A.liftedStep k).comp (KrausMap.ofPerm (A.afterAt F k))) :=
  shA.absorbStep_eq A.kind A.step F k

omit [Inhabited Req'] in
/-- **The shape of the absorbed adversary** (`absorb`): the workspace of `AbsorbedWork` over the
shape's workspace and slots, the Kraus index of `absorbStep`. -/
@[reducible] def _root_.GordieHowe.Quantum.AlgShape.absorbS (s : AlgShape X Y Req Resp) :
    AlgShape X Y Req' Resp' where
  W := AbsorbedWork s.W Req Resp Resp' s.slots
  width := s.width
  width_pos := s.width_pos
  slots := s.slots
  post := s.post
  budget := s.budget
  R := (Unit × s.R) × Unit

/-- **The initial state of the absorbed adversary** at the shape `s`: `init` with the blank
absorbed registers. Sealed; it unfolds through `AlgShape.absorbInit_eq`. -/
@[irreducible, no_expose] def _root_.GordieHowe.Quantum.AlgShape.absorbInit
    (s : AlgShape X Y Req Resp) (init : MState (DReg s.W s.width X Y Req Resp)) :
    MState (DReg (s.absorbS (Req' := Req') (Resp' := Resp')).W s.width X Y Req' Resp') :=
  MState.reindex (s.absSplit (Req' := Req') (Resp' := Resp')).symm
    (init.tensorKet (s.absBlank (Req' := Req') (Resp' := Resp')))

theorem _root_.GordieHowe.Quantum.AlgShape.absorbInit_eq (s : AlgShape X Y Req Resp)
    (init : MState (DReg s.W s.width X Y Req Resp)) :
    s.absorbInit (Req' := Req') (Resp' := Resp') init =
      MState.reindex (s.absSplit (Req' := Req') (Resp' := Resp')).symm
        (init.tensorKet (s.absBlank (Req' := Req') (Resp' := Resp'))) := by
  unfold AlgShape.absorbInit; rfl

/-- **The adversary with its side requests absorbed** (`SideRelay`): an adversary of the main
challenger's interface. Its workspace holds the adversary's registers, the copy of its logs and
the store of main replies (`AbsorbedWork`). Step `k` is: the relayed reply of slot `k - 1`
written into the adversary's response register (`afterAt`), the adversary's step `k`, and the
relayed request of slot `k` written into the main request register (`setAt`). The kind and the
output are read from the adversary's workspace; the width, the slots, the post batches and the
budget are the adversary's. This construction is the primitive; under the hypotheses of
`toOuterMeasure_absorbAssign_ofSide` (`GordieHowe/Model/Quantum/Interactive/AbsorbAssignSide.lean`)
its law is the law of `absorbAssign` at `AssignRelay.ofSide`, up to removing the idle main
requests.

Running time: that of `A`, plus, at each slot, the computation of `route` and of `answer` on
classical registers and a constant number of register exchanges. This running time is argued
here, not proved in Lean. -/
abbrev absorb : AdaptiveIAlg (shA.absorbS (Req' := Req') (Resp' := Resp')) O where
  kind w := A.kind w.work
  init := shA.absorbInit A.init
  step := A.absorbStep F
  out w := A.out w.work

theorem absorb_toShape : (A.absorb F).toShape = A.toShape.absorbS :=
  rfl

/-- The kind of the absorbed adversary, read from `A`'s workspace. -/
theorem absorb_kind : (A.absorb F).kind = fun w => A.kind w.work := rfl

/-- The initial state of the absorbed adversary: `A`'s with the blank absorbed registers. -/
theorem absorb_init :
    (A.absorb F).init = MState.reindex A.absSplit.symm (A.init.tensorKet A.absBlank) :=
  shA.absorbInit_eq A.init

/-- The steps of the absorbed adversary (`absorbStep`). -/
theorem absorb_step : (A.absorb F).step = A.absorbStep F := rfl

/-- The output of the absorbed adversary, read from `A`'s workspace. -/
theorem absorb_out : (A.absorb F).out = fun w => A.out w.work := rfl

/-! ### The steps of the absorbed adversary with its query counter -/

/-- The registers of the absorbed adversary with its query counter, as those of the adversary
with its query counter and the rest. -/
def absCntSplit :
    DReg (A.absorb F).toKindAlg.W (A.absorb F).toKindAlg.width X Y Req' Resp' ≃
    DReg A.toKindAlg.W A.toKindAlg.width X Y Req Resp × A.AbsRest (Req' := Req') (Resp' := Resp') where
  toFun d := ((((AlgShape.CntW.mk d.1.1.work.work d.1.1.cnt), d.1.1.work.request,
    d.1.1.work.response), d.2), (d.1.1.work.logs, d.1.1.work.store, d.1.2.1, d.1.2.2))
  invFun p := (((AlgShape.CntW.mk ⟨p.1.1.1.work, p.1.1.2.1, p.1.1.2.2, p.2.1, p.2.2.1⟩ p.1.1.1.cnt),
    p.2.2.2.1, p.2.2.2.2), p.1.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A permutation of the absorbed adversary's registers with the counter alongside. -/
def withCnt (π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp')) :
    Equiv.Perm (DReg (A.absorb F).CntW A.width X Y Req' Resp') :=
  (A.absorb F).cntSplit.symm.permCongr (π.prodCongr (Equiv.refl _))

@[simp] theorem withCnt_apply (π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp'))
    (w : A.AbsW (Resp' := Resp')) (c : Fin ((A.absorb F).budget + 2)) (rq : Req') (rs : Option Resp')
    (qs : Fin A.width → X × Y) :
    A.withCnt F π (((AlgShape.CntW.mk w c), rq, rs), qs) =
      (((AlgShape.CntW.mk (π ((w, rq, rs), qs)).1.1 c), (π ((w, rq, rs), qs)).1.2.1,
        (π ((w, rq, rs), qs)).1.2.2), (π ((w, rq, rs), qs)).2) := rfl

/-- **The adversary's step `k` with its query counter, on the absorbed registers**: the
adversary's step tensored with the identity, then for `k < slots` the projection onto the
branches within the budget and the counter advanced on the query branches. -/
noncomputable def cntStep (k : StepIdx A.slots A.post) :
    KrausMap A.R (DReg (A.absorb F).CntW A.width X Y Req' Resp')
      (DReg (A.absorb F).CntW A.width X Y Req' Resp') :=
  if (k : ℕ) < A.slots then
    ((((A.liftedStep k).tensorId (Fin ((A.absorb F).budget + 2))).reindex (A.absorb F).cntSplit.symm).restrict
      (A.absorb F).inBudget).permConj (Equiv.refl _) (A.absorb F).cntShift
  else ((A.liftedStep k).tensorId (Fin ((A.absorb F).budget + 2))).reindex (A.absorb F).cntSplit.symm

omit [Fintype Req'] [Fintype Resp'] [DecidableEq Resp'] in
/-- The permutation before slot `k` keeps the adversary's workspace. -/
theorem work_setAt (k : ℕ) (d : DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp') :
    ((A.setAt F k) d).1.1.work = d.1.1.work := by
  rw [AdaptiveIAlg.setAt_def]
  split_ifs
  · change (if A.kind d.1.1.work then _ else d).1.1.work = d.1.1.work
    split_ifs <;> rfl
  · rfl

/-- **A permutation that keeps the adversary's workspace keeps the budget test** of the absorbed
adversary with its counter. -/
theorem inBudget_withCnt {π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp')}
    (hπ : ∀ d, (π d).1.1.work = d.1.1.work)
    (d : DReg (A.absorb F).CntW A.width X Y Req' Resp') :
    (A.absorb F).inBudget (A.withCnt F π d) = (A.absorb F).inBudget d := by
  obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := d
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  rw [withCnt_apply, inBudget_mk, inBudget_mk]
  exact congrArg (· || _) (congrArg A.kind (hπ ((w, rq, rs), qs)))

/-- **A permutation that keeps the adversary's workspace commutes with the counter shift.** -/
theorem cntShift_withCnt {π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp')}
    (hπ : ∀ d, (π d).1.1.work = d.1.1.work)
    (d : DReg (A.absorb F).CntW A.width X Y Req' Resp') :
    (A.absorb F).cntShift (A.withCnt F π d) = A.withCnt F π ((A.absorb F).cntShift d) := by
  obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := d
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  have hk : (A.absorb F).kind (π ((w, rq, rs), qs)).1.1 = (A.absorb F).kind w :=
    congrArg A.kind (hπ ((w, rq, rs), qs))
  rw [withCnt_apply, cntShift_apply, cntShift_apply, withCnt_apply, hk]

/-- **The step of the absorbed adversary with its query counter** is the permutation after slot
`k - 1`, the adversary's step with its counter (`cntStep`), and the permutation before slot `k`:
the latter keeps the kind and the counter, so it commutes with the projection and the counter
shift. -/
theorem absorb_toKindAlg_step_apply (k : StepIdx A.slots A.post)
    (ρ : Matrix (DReg (A.absorb F).CntW A.width X Y Req' Resp')
      (DReg (A.absorb F).CntW A.width X Y Req' Resp') ℂ) :
    (A.absorb F).toKindAlg.step k ρ =
      ((A.cntStep F k) (ρ.submatrix (A.withCnt F (A.afterAt F k)).symm
        (A.withCnt F (A.afterAt F k)).symm)).submatrix (A.withCnt F (A.setAt F k)).symm
        (A.withCnt F (A.setAt F k)).symm := by
  have hstep : (((A.absorb F).step k).tensorId (Fin ((A.absorb F).budget + 2))).reindex
      (A.absorb F).cntSplit.symm = (KrausMap.ofPerm (A.withCnt F (A.setAt F k))).comp
        ((((A.liftedStep k).tensorId (Fin ((A.absorb F).budget + 2))).reindex (A.absorb F).cntSplit.symm).comp
          (KrausMap.ofPerm (A.withCnt F (A.afterAt F k)))) := by
    rw [show (A.absorb F).step k = _ from A.absorbStep_eq F k]
    rw [KrausMap.tensorId_comp, KrausMap.tensorId_comp, KrausMap.reindex_comp,
      KrausMap.reindex_comp, KrausMap.ofPerm_tensorId, KrausMap.ofPerm_tensorId,
      KrausMap.ofPerm_reindex, KrausMap.ofPerm_reindex]
    rfl
  by_cases hk : (k : ℕ) < A.slots
  · have hs : (A.absorb F).toKindAlg.step k = (((((A.absorb F).step k).tensorId
        (Fin ((A.absorb F).budget + 2))).reindex (A.absorb F).cntSplit.symm).restrict
        (A.absorb F).inBudget).permConj (Equiv.refl _) (A.absorb F).cntShift := by
      exact AdaptiveIAlg.toKindAlg_step_of_lt _ hk
    rw [hs, hstep]
    refine (KrausMap.permConj_restrict_ofPerm_comp_apply _ _ _ _ ?hp ?hτ ρ).trans ?_
    case hp => exact A.inBudget_withCnt F (A.work_setAt F k)
    case hτ => exact A.cntShift_withCnt F (A.work_setAt F k)
    rw [KrausMap.restrict_comp, KrausMap.permConj_refl_comp, KrausMap.comp_apply,
      KrausMap.ofPerm_apply]
    simp only [cntStep, if_pos hk]
  · have hs : (A.absorb F).toKindAlg.step k = (((A.absorb F).step k).tensorId
        (Fin ((A.absorb F).budget + 2))).reindex (A.absorb F).cntSplit.symm := by
      exact AdaptiveIAlg.toKindAlg_step_of_not_lt _ hk
    rw [hs, hstep]
    refine (KrausMap.comp_apply _ _ ρ).trans ?_
    rw [KrausMap.comp_apply, KrausMap.ofPerm_apply, KrausMap.ofPerm_apply]
    simp only [cntStep, if_neg hk]

/-- **The adversary's step with its counter, on the absorbed registers, lifts its step with its
counter** along the split of the absorbed registers (`KrausMap.Lifts`). -/
theorem cntStep_lifts (k : StepIdx A.slots A.post) :
    (A.cntStep F k).Lifts (A.absCntSplit F) (A.toKindAlg.step k) := by
  have hL : (A.liftedStep (Req' := Req') (Resp' := Resp') k).Lifts
      (A.absSplit (Req' := Req') (Resp' := Resp')) (A.step k) :=
    KrausMap.lifts_reindex_tensorId _ (A.step k)
  have hcnt : (((A.liftedStep k).tensorId (Fin ((A.absorb F).budget + 2))).reindex
      (A.absorb F).cntSplit.symm).Lifts (A.absCntSplit F)
      (((A.step k).tensorId (Fin (A.budget + 2))).reindex A.cntSplit.symm) :=
    (hL.tensorId (Fin (A.budget + 2)) (E₂ := liftProd (A.absSplit (Req' := Req') (Resp' := Resp')) (Fin (A.budget + 2)))
      fun _ _ => rfl).reindex
      fun _ => rfl
  rw [AdaptiveIAlg.toKindAlg_step_eq]
  change KrausMap.Lifts (A.absCntSplit F) (if (k : ℕ) < A.slots then _ else _)
    (if (k : ℕ) < A.slots then _ else _)
  refine KrausMap.Lifts.ite (fun _ => ?_) fun _ => hcnt
  refine (hcnt.restrict fun x => ?_).permConj (fun _ => rfl) (perm_symm_lift _ fun x => ?_)
  · obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := x
    obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
    rfl
  · obtain ⟨⟨wc_, rq, rs⟩, qs⟩ := x
    obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
    rfl

/-! ### The permutations on one basis state -/

/-- After slot `j` with no request logged, nothing changes. -/
theorem afterPerm_of_none (j : Fin A.slots) {d : DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp'}
    (h : d.1.1.logs j = none) : A.afterPerm F j d = d := by
  have h1 : A.storePerm j d = d := by
    change (if (d.1.1.logs j).isSome then _ else d) = d
    simp [h]
  have h2 : A.answerPerm F j d = d := by
    change (match d.1.1.logs j with | none => d | some r => _) = d
    rw [h]
  have h3 : A.clearPerm F j d = d := by
    change (match d.1.1.logs j with | none => d | some r => _) = d
    rw [h]
  rw [afterPerm, AlgShape.afterPerm, Equiv.trans_apply, Equiv.trans_apply, h1, h2, h3]

/-- Writing the relayed reply of slot `j` with request `r` logged. -/
theorem answerPerm_of_some (j : Fin A.slots) {r : Req}
    {d : DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp'} (h : d.1.1.logs j = some r) :
    A.answerPerm F j d = ((⟨d.1.1.work, d.1.1.request,
        Equiv.swap none (F.answer (A.reqCount d.1.1.logs j) r (d.1.1.store j)) d.1.1.response,
        d.1.1.logs, d.1.1.store⟩, d.1.2), d.2) := by
  change (match d.1.1.logs j with | none => d | some r => _) = _
  rw [h]

/-- Clearing the main request of slot `j` with request `r` logged. -/
theorem clearPerm_of_some (j : Fin A.slots) {r : Req}
    {d : DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp'} (h : d.1.1.logs j = some r) :
    A.clearPerm F j d =
      ((d.1.1, Equiv.swap default (F.route (A.reqCount d.1.1.logs j) r) d.1.2.1, d.1.2.2), d.2) := by
  change (match d.1.1.logs j with | none => d | some r => _) = _
  rw [h]

/-- **After slot `j` with request `r` logged**: the main reply into the store, the relayed reply
into the response register, the main request register cleared. -/
theorem afterPerm_of_some (j : Fin A.slots) {r : Req}
    {d : DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp'} (h : d.1.1.logs j = some r) :
    A.afterPerm F j d = ((⟨d.1.1.work, d.1.1.request,
        Equiv.swap none (F.answer (A.reqCount d.1.1.logs j) r d.1.2.2) d.1.1.response, d.1.1.logs,
        Function.update d.1.1.store j d.1.2.2⟩,
      Equiv.swap default (F.route (A.reqCount d.1.1.logs j) r) d.1.2.1, d.1.1.store j), d.2) := by
  have h1 : A.storePerm j d = ((⟨d.1.1.work, d.1.1.request, d.1.1.response, d.1.1.logs,
      Function.update d.1.1.store j d.1.2.2⟩, d.1.2.1, d.1.1.store j), d.2) := by
    change (if (d.1.1.logs j).isSome then _ else d) = _
    simp [h]
  rw [afterPerm, AlgShape.afterPerm, Equiv.trans_apply, Equiv.trans_apply, h1,
    A.answerPerm_of_some F j (r := r) ?h2, A.clearPerm_of_some F j (r := r) ?h3]
  · simp
  case h2 => exact h
  case h3 => exact h

/-- Before slot `k` on a branch with a request. -/
theorem setPerm_of_kind (k : Fin A.slots) {d : DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp'}
    (h : A.kind d.1.1.work = true) :
    A.setPerm F k d = ((⟨d.1.1.work, d.1.1.request, d.1.1.response,
        Function.update d.1.1.logs k (Equiv.swap none (some d.1.1.request) (d.1.1.logs k)),
        d.1.1.store⟩,
      Equiv.swap default (F.route (A.reqCount d.1.1.logs k) d.1.1.request) d.1.2.1, d.1.2.2), d.2) := by
  change (if A.kind d.1.1.work then _ else d) = _
  rw [if_pos h]

/-- Before slot `k` on a branch without a request, nothing changes. -/
theorem setPerm_of_not_kind (k : Fin A.slots)
    {d : DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp'} (h : A.kind d.1.1.work = false) :
    A.setPerm F k d = d := by
  change (if A.kind d.1.1.work then _ else d) = d
  rw [if_neg (by simp [h])]

/-! ### The adversary with its counter, with reducible fields -/

/-! ### The mixed game of the absorbed adversary -/

/-- A permutation of the absorbed registers with the counter, on the game registers (the logs
alongside). -/
def gamePerm (π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp')) :
    Equiv.Perm (A.absorb F).toKindAlg.G :=
  splitLogs.symm.permCongr ((A.withCnt F π).prodCongr (Equiv.refl (LogReg Req' A.slots)))

/-- The adversary's step with its counter on the absorbed game registers. -/
noncomputable def gameCntStep (k : StepIdx A.slots A.post) :
    KrausMap A.R (A.absorb F).toKindAlg.G (A.absorb F).toKindAlg.G :=
  ((A.cntStep F k).tensorId (LogReg Req' A.slots)).reindex splitLogs.symm

/-- **The step of the absorbed adversary on the game registers** (`KindAlg.liftG`): the
permutation after slot `k - 1`, the adversary's step with its counter (`gameCntStep`), the
permutation before slot `k`. -/
theorem absorb_liftG_apply (k : StepIdx A.slots A.post)
    (M : Matrix (A.absorb F).toKindAlg.G (A.absorb F).toKindAlg.G ℂ) :
    (A.absorb F).toKindAlg.liftG k M =
      ((A.gameCntStep F k) (M.submatrix (A.gamePerm F (A.afterAt F k)).symm
        (A.gamePerm F (A.afterAt F k)).symm)).submatrix (A.gamePerm F (A.setAt F k)).symm
        (A.gamePerm F (A.setAt F k)).symm :=
  KrausMap.tensorId_reindex_apply_of_conj (A.absorb_toKindAlg_step_apply F k) _ _ M

/-- The game registers of the absorbed adversary as the adversary's registers with its counter
and the rest (its own rest and the relayed logs). -/
def gameSplit : (A.absorb F).toKindAlg.G ≃
    DReg A.toKindAlg.W A.toKindAlg.width X Y Req Resp ×
      (A.AbsRest (Req' := Req') (Resp' := Resp') × LogReg Req' (A.absorb F).toKindAlg.slots) where
  toFun g := ((A.absCntSplit F (splitLogs g).1).1, ((A.absCntSplit F (splitLogs g).1).2, (splitLogs g).2))
  invFun p := splitLogs.symm ((A.absCntSplit F).symm (p.1, p.2.1), p.2.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The adversary's step with its counter on the absorbed game registers acts as its step
with its counter tensored with the identity** on the rest. -/
theorem gameCntStep_apply (k : StepIdx A.slots A.post)
    (M : Matrix (A.absorb F).toKindAlg.G (A.absorb F).toKindAlg.G ℂ) :
    A.gameCntStep F k M = (((A.toKindAlg.step k).tensorId
      (A.AbsRest (Req' := Req') (Resp' := Resp') × LogReg Req' A.slots)).reindex
        (A.gameSplit F).symm) M := by
  have h1 : (A.gameCntStep F k).Lifts (A.gameSplit F) (A.toKindAlg.step k) :=
    ((A.cntStep_lifts F k).tensorId_right (LogReg Req' A.slots)
      (E₂ := ((A.absCntSplit F).prodCongr (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _))
      fun _ _ => rfl).reindex_left fun _ => rfl
  exact h1.apply_eq (KrausMap.lifts_reindex_tensorId _ _) M

section Place

variable {Ω' St' : Type} {Q' : ℕ} [OracleState St' X Y] (E' : Env Ω' Req' Resp' X Y Q' St')
  (ω' : Ω')

/-- The main reply of slot `i` at the relayed logs. -/
def mainAns (lg : LogReg Req A.slots) (i : Fin A.slots) : Option Resp' :=
  E'.answer ω' (F.logs lg) i

/-- The store holding the main replies of the slots below `j`. -/
def storeBelow (j : ℕ) (lg : LogReg Req A.slots) : Fin A.slots → Option Resp' :=
  fun i => if (i : ℕ) < j then A.mainAns F E' ω' lg i else none

/-- **The placement of the adversary's game registers in the absorbed game registers**, given
the store, the adversary's response register, the main request and response registers and the
relayed logs as functions of the adversary's registers. -/
def placeWith (st : LogReg Req A.slots → Fin A.slots → Option Resp')
    (resp : A.toKindAlg.G → Option Resp) (rq : A.toKindAlg.G → Req')
    (rs : A.toKindAlg.G → Option Resp') (lg' : LogReg Req A.slots → LogReg Req' A.slots)
    (g : A.toKindAlg.G) : (A.absorb F).toKindAlg.G :=
  (((AlgShape.CntW.mk ⟨g.1.1.work, g.1.2.1, resp g, g.1.2.2.2, st g.1.2.2.2⟩ g.1.1.cnt), rq g, rs g,
    lg' g.1.2.2.2), g.2)

/-- **The placement between slots** with the main replies of the slots below `j` stored: the
main request and response registers blank, the relayed logs. -/
def placeClean (j : ℕ) : A.toKindAlg.G → (A.absorb F).toKindAlg.G :=
  A.placeWith F (A.storeBelow F E' ω' j) (fun g => g.1.2.2.1) (fun _ => default) (fun _ => none)
    F.logs

/-- **The adversary's step with its counter commutes with the placement between slots.** -/
theorem gameCntStep_placeClean (k : StepIdx A.slots A.post) (j : ℕ)
    (σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ) :
    A.gameCntStep F k (embed (A.placeClean F E' ω' j) σ) =
      embed (A.placeClean F E' ω' j) (A.toKindAlg.liftG k σ) := by
  have hp : A.placeClean F E' ω' j = (A.gameSplit F).symm ∘
      Prod.map _root_.id (fun lg => ((lg, A.storeBelow F E' ω' j lg, default, none), F.logs lg)) ∘
        splitLogs.symm.symm := by
    funext g
    rfl
  rw [gameCntStep_apply, hp]
  exact KrausMap.tensorId_reindex_apply_embed _ splitLogs.symm _ _ σ

/-- The relayed reply of slot `i`: the reply relayed from the main reply, on a logged
request. -/
def relayAns (lg : LogReg Req A.slots) (i : Fin A.slots) : Option Resp :=
  (lg i).elim none fun r => F.answer (A.reqCount lg i) r (A.mainAns F E' ω' lg i)

/-- The main request sent at slot `i`: `route c r` on a logged request `r`, blank otherwise. -/
def mainReq (lg : LogReg Req A.slots) (i : Fin A.slots) : Req' :=
  (lg i).elim default (F.route (A.reqCount lg i))

/-- **The placement after slot `i`**: the adversary's response register holds the relayed reply
(written by the main challenger into the main response register, not yet relayed), the main
request register the main request of slot `i`, the main response register its main reply, and the
store the main replies of the slots below `i`. -/
def placePending (i : Fin A.slots) : A.toKindAlg.G → (A.absorb F).toKindAlg.G :=
  A.placeWith F (A.storeBelow F E' ω' i)
    (fun g => Equiv.swap none (A.relayAns F E' ω' g.1.2.2.2 i) g.1.2.2.1)
    (fun g => A.mainReq F g.1.2.2.2 i) (fun g => A.mainAns F E' ω' g.1.2.2.2 i) F.logs

/-- The placement at the start of step `k`: after slot `k - 1`, or between slots for `k = 0` and
after the last slot's reply has been relayed. -/
def placeStart (k : ℕ) : A.toKindAlg.G → (A.absorb F).toKindAlg.G :=
  if h : 0 < k ∧ k - 1 < A.slots then A.placePending F E' ω' ⟨k - 1, h.2⟩
  else A.placeClean F E' ω' k

/-- **The placement after the main request of slot `k` is written**, before it is logged: the
relayed logs without slot `k`. -/
def placeSet (k : Fin A.slots) : A.toKindAlg.G → (A.absorb F).toKindAlg.G :=
  A.placeWith F (A.storeBelow F E' ω' k) (fun g => g.1.2.2.1) (fun g => A.mainReq F g.1.2.2.2 k)
    (fun _ => none) fun lg => F.logs (Function.update lg k none)

/-- **The placement after the main request of slot `k` is logged.** -/
def placeCopied (k : Fin A.slots) : A.toKindAlg.G → (A.absorb F).toKindAlg.G :=
  A.placeWith F (A.storeBelow F E' ω' k) (fun g => g.1.2.2.1) (fun g => A.mainReq F g.1.2.2.2 k)
    (fun _ => none) F.logs

/-- **A permutation of the absorbed registers on a placed game basis state** acts on the
absorbed registers and leaves the counter and the relayed logs. -/
theorem gamePerm_placeWith (π : Equiv.Perm (DReg (A.AbsW (Resp' := Resp')) A.width X Y Req' Resp'))
    (st : LogReg Req A.slots → Fin A.slots → Option Resp') (resp : A.toKindAlg.G → Option Resp)
    (rq : A.toKindAlg.G → Req') (rs : A.toKindAlg.G → Option Resp')
    (lg' : LogReg Req A.slots → LogReg Req' A.slots) (g : A.toKindAlg.G) :
    A.gamePerm F π (A.placeWith F st resp rq rs lg' g) =
      (((AlgShape.CntW.mk (π ((⟨g.1.1.work, g.1.2.1, resp g, g.1.2.2.2, st g.1.2.2.2⟩, rq g, rs g),
          g.2)).1.1 g.1.1.cnt : (A.absorb F).CntW),
        (π ((⟨g.1.1.work, g.1.2.1, resp g, g.1.2.2.2, st g.1.2.2.2⟩, rq g, rs g), g.2)).1.2.1,
        (π ((⟨g.1.1.work, g.1.2.1, resp g, g.1.2.2.2, st g.1.2.2.2⟩, rq g, rs g), g.2)).1.2.2,
        lg' g.1.2.2.2),
        (π ((⟨g.1.1.work, g.1.2.1, resp g, g.1.2.2.2, st g.1.2.2.2⟩, rq g, rs g), g.2)).2) :=
  rfl

/-- A blank log has no main reply. -/
theorem mainAns_of_none {lg : LogReg Req A.slots} {i : Fin A.slots} (h : lg i = none) :
    A.mainAns F E' ω' lg i = none := by
  simp [mainAns, Env.answer, SideRelay.logs, h]

/-- **After slot `k - 1`**: the main reply moves into the store and the relayed reply into the
adversary's response register, and the main request register is cleared. -/
theorem gamePerm_afterAt_placeStart (k : ℕ) (g : A.toKindAlg.G) :
    A.gamePerm F (A.afterAt F k) (A.placeStart F E' ω' k g) = A.placeClean F E' ω' k g := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  unfold placeStart
  rw [AdaptiveIAlg.afterAt_def]
  by_cases h : 0 < k ∧ k - 1 < A.slots
  · rw [dif_pos h, dif_pos h]
    set i : Fin A.slots := ⟨k - 1, h.2⟩
    have hst : ∀ j : Fin A.slots, A.storeBelow F E' ω' k lg j =
        Function.update (A.storeBelow F E' ω' i lg) i (A.mainAns F E' ω' lg i) j := fun j => by
      by_cases hj : j = i
      · subst hj
        simp [storeBelow, i]
        omega
      · rw [Function.update_of_ne hj]
        simp only [storeBelow]
        have : ((j : ℕ) < k ↔ (j : ℕ) < k - 1) := by
          have : (j : ℕ) ≠ k - 1 := fun e => hj (Fin.ext e)
          omega
        simp only [this, i]
    rcases hlg : lg i with _ | r
    · have hs : A.storeBelow F E' ω' (i : ℕ) lg = A.storeBelow F E' ω' k lg := funext fun j => by
        rw [hst j]
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, mainAns_of_none _ _ _ _ hlg]
          simp [storeBelow]
        · rw [Function.update_of_ne hj]
      rw [placePending, gamePerm_placeWith, A.afterPerm_of_none F i hlg]
      simp only [placeClean, placeWith, relayAns, mainReq, hlg, Option.elim,
        mainAns_of_none _ _ _ _ hlg, Equiv.swap_self, Equiv.refl_apply, hs]
    · rw [placePending, gamePerm_placeWith, A.afterPerm_of_some F i (r := r) hlg]
      have hs : Function.update (A.storeBelow F E' ω' (i : ℕ) lg) i (A.mainAns F E' ω' lg i) =
          A.storeBelow F E' ω' k lg := funext fun j => (hst j).symm
      have h0 : A.storeBelow F E' ω' (i : ℕ) lg i = none := by simp [storeBelow]
      simp only [placeClean, placeWith, relayAns, mainReq, hlg, Option.elim, hs, h0,
        Equiv.swap_apply_self, Equiv.swap_apply_right]
  · rw [dif_neg h, dif_neg h]
    rfl

/-- **The relayed logs below slot `k` do not see log `k`.** -/
theorem relayLogs_update_of_lt (lg : LogReg Req A.slots) (k : Fin A.slots) (v : Option Req)
    {i : Fin A.slots} (hi : (i : ℕ) < k) : F.logs (Function.update lg k v) i = F.logs lg i := by
  have hne : i ≠ k := fun e => by subst e; omega
  have hb : requestsBefore (Function.update lg k v) i = requestsBefore lg i :=
    requestsBefore_congr fun k' hk' => by
      rw [Function.update_of_ne]
      intro e
      subst e
      omega
  simp only [SideRelay.logs_apply, Function.update_of_ne hne, hb]

/-- **The main replies below slot `k` do not see log `k`.** -/
theorem mainAns_update_of_lt (lg : LogReg Req A.slots) (k : Fin A.slots) (v : Option Req)
    {i : Fin A.slots} (hi : (i : ℕ) < k) :
    A.mainAns F E' ω' (Function.update lg k v) i = A.mainAns F E' ω' lg i := by
  simp only [mainAns, Env.answer]
  rw [A.relayLogs_update_of_lt F lg k v hi,
    requestsBefore_congr fun k' hk' => A.relayLogs_update_of_lt F lg k v (by omega)]

/-- **The store below slot `k` does not see log `k`.** -/
theorem storeBelow_update (lg : LogReg Req A.slots) (k : Fin A.slots) (v : Option Req) :
    A.storeBelow F E' ω' k (Function.update lg k v) = A.storeBelow F E' ω' k lg := by
  funext i
  simp only [storeBelow]
  split_ifs with hi
  · exact A.mainAns_update_of_lt F E' ω' lg k v hi
  · rfl

/-- **Before slot `k`**: writing the relayed request is the copy of the request into log `k`,
placed. -/
theorem gamePerm_setAt_placeClean (k : Fin A.slots) {g : A.toKindAlg.G}
    (hg : (splitLogs g).2 k = none) :
    A.gamePerm F (A.setAt F k) (A.placeClean F E' ω' k g) =
      A.placeSet F E' ω' k (A.toKindAlg.copyG k g) := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  change LogReg Req A.slots at lg
  simp only [splitLogs, Equiv.coe_fn_mk] at hg
  have hset : A.setAt F (k : ℕ) = A.setPerm F k := A.setAt_of_lt F k.2
  rw [placeClean, gamePerm_placeWith, hset]
  have hu : Function.update lg k none = lg := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp [hg]
    · simp [Function.update_of_ne hj]
  by_cases hk : A.kind w = true
  · rw [A.setPerm_of_kind F k hk]
    have hc : A.toKindAlg.copyG k ((AlgShape.CntW.mk w c, rq, rs, lg), qs) =
        ((AlgShape.CntW.mk w c, rq, rs, Function.update lg k (some rq)), qs) := by
      show (copyPerm A.toKindAlg.kind k ((AlgShape.CntW.mk w c), rq, rs, lg), qs) = _
      rw [copyPerm_apply]
      simp [toKindAlg_kind_mk, hk, hg]
    rw [hc]
    simp only [placeSet, placeWith, hg, Equiv.swap_apply_left, storeBelow_update,
      Function.update_idem, hu, mainReq, Function.update_self, Option.elim]
    have hr : A.reqCount (Function.update lg k (some rq)) k = A.reqCount lg k :=
      congrArg List.length (requestsBefore_congr fun k' hk' => by
        rw [Function.update_of_ne]
        intro e
        subst e
        omega)
    simp only [hr]
  · have hk' : A.kind w = false := by simpa using hk
    rw [A.setPerm_of_not_kind F k hk']
    have hc : A.toKindAlg.copyG k ((AlgShape.CntW.mk w c, rq, rs, lg), qs) = ((AlgShape.CntW.mk w c, rq, rs, lg), qs) := by
      show (copyPerm A.toKindAlg.kind k ((AlgShape.CntW.mk w c), rq, rs, lg), qs) = _
      rw [copyPerm_apply]
      simp [toKindAlg_kind_mk, hk']
    rw [hc]
    simp only [placeSet, placeWith, hu, mainReq, hg, Option.elim]

/-- **Logging the relayed request of slot `k`** in the main challenger's log. -/
theorem copyG_placeSet (k : Fin A.slots) {g : A.toKindAlg.G} (hg : g ∈ A.toKindAlg.TSet k) :
    (A.absorb F).toKindAlg.copyG k (A.placeSet F E' ω' k g) = A.placeCopied F E' ω' k g := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  change LogReg Req A.slots at lg
  simp only [KindAlg.TSet, Set.mem_setOf_eq, splitLogs, Equiv.coe_fn_mk, KindAlg.reqOutG] at hg
  obtain ⟨hlater, hk⟩ := hg
  by_cases hkind : A.kind w = true
  · have hlk : lg k = some rq := by simpa [toKindAlg_kind_mk, hkind] using hk
    show ((if (A.absorb F).toKindAlg.kind (⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩, c) then _
      else _), qs) = _
    rw [if_pos (show (A.absorb F).toKindAlg.kind (⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩, c) =
      true from hkind)]
    have hl : Function.update (F.logs (Function.update lg k none)) k
        (Equiv.swap none (some (F.route (A.reqCount lg k) rq)) (F.logs (Function.update lg k none) k)) =
        F.logs lg := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [SideRelay.logs_apply, hlk]
      · rw [Function.update_of_ne hj]
        rcases lt_or_gt_of_ne (fun e : (j : ℕ) = k => hj (Fin.ext e)) with h | h
        · exact A.relayLogs_update_of_lt F lg k none h
        · simp [SideRelay.logs_apply, Function.update_of_ne hj, hlater j h]
    simp only [placeCopied, placeWith, mainReq, hlk, Option.elim]
    exact congrArg (fun L => ((((⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩ : A.AbsW), c),
      F.route (A.reqCount lg k) rq, (none : Option Resp'), L), qs)) hl
  · have hkind' : A.kind w = false := by simpa using hkind
    have hlk : lg k = none := by simpa [toKindAlg_kind_mk, hkind'] using hk
    show ((if (A.absorb F).toKindAlg.kind (⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩, c) then _
      else _), qs) = _
    rw [if_neg (show ¬ (A.absorb F).toKindAlg.kind (⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩, c) =
      true from hkind)]
    have hu : Function.update lg k none = lg := by
      funext j
      by_cases hj : j = k
      · subst hj
        simp [hlk]
      · simp [Function.update_of_ne hj]
    simp only [placeSet, placeCopied, placeWith, hu]

/-- **The dephasing of the relayed log is that of the log**, on matrices dephased in the logs
below `k`, for an injective relay of requests. -/
theorem dephase_placeCopied (hinj : ∀ c, Function.Injective (F.route c)) (k : Fin A.slots)
    {τ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ} (hτ : dephase (A.toKindAlg.logsBelow k) τ = τ) :
    dephase ((A.absorb F).toKindAlg.logAt k ∘ A.placeCopied F E' ω' k) τ =
      dephase (A.toKindAlg.logAt k) τ := by
  ext a b
  by_cases hab : A.toKindAlg.logsBelow k a = A.toKindAlg.logsBelow k b
  · have hc : A.reqCount (splitLogs a).2 k = A.reqCount (splitLogs b).2 k :=
      congrArg List.length (requestsBefore_congr fun j hj => by
        have := congrFun hab j
        simpa [KindAlg.logsBelow, hj] using this)
    have key : ((A.absorb F).toKindAlg.logAt k (A.placeCopied F E' ω' k a) =
        (A.absorb F).toKindAlg.logAt k (A.placeCopied F E' ω' k b)) ↔
        (A.toKindAlg.logAt k a = A.toKindAlg.logAt k b) := by
      change (Option.map (F.route (A.reqCount (splitLogs a).2 k)) ((splitLogs a).2 k) =
        Option.map (F.route (A.reqCount (splitLogs b).2 k)) ((splitLogs b).2 k)) ↔
        ((splitLogs a).2 k = (splitLogs b).2 k)
      rw [hc, (Option.map_injective (hinj _)).eq_iff]
    simp only [dephase, Function.comp]
    exact if_congr key rfl rfl
  · rw [← hτ]
    simp only [dephase, if_neg hab]
    split_ifs <;> rfl

variable {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St) (ω : Ω)

/-- **The reply of slot `k`**: the main reply written into the main response register is, placed,
the relayed reply written into the adversary's response register. -/
theorem respG_placeCopied (hR : F.Relays E ω E' ω' A.slots) (k : Fin A.slots) {g : A.toKindAlg.G}
    (hg : g ∈ A.toKindAlg.TSet k) :
    (A.absorb F).toKindAlg.respG E' ω' k (A.placeCopied F E' ω' k g) =
      A.placePending F E' ω' k (A.toKindAlg.respG E ω k g) := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  change LogReg Req A.slots at lg
  simp only [KindAlg.TSet, Set.mem_setOf_eq, splitLogs, Equiv.coe_fn_mk, KindAlg.reqOutG] at hg
  obtain ⟨-, hk⟩ := hg
  by_cases hkind : A.kind w = true
  · have hlk : lg k = some rq := by simpa [toKindAlg_kind_mk, hkind] using hk
    have ha : E.answer ω lg k = A.relayAns F E' ω' lg k := by
      rw [hR.answer_eq lg k rq hlk]
      simp only [relayAns, hlk, Option.elim]
      rfl
    show ((if (A.absorb F).toKindAlg.kind (⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩, c) then _
      else _), qs) = A.placePending F E' ω' k ((if A.toKindAlg.kind (AlgShape.CntW.mk w c) then _ else _), qs)
    rw [if_pos (show (A.absorb F).toKindAlg.kind (⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩, c) =
      true from hkind), if_pos (show A.toKindAlg.kind (AlgShape.CntW.mk w c) = true from hkind)]
    simp only [placePending, placeWith, Equiv.swap_apply_left]
    erw [ha, Equiv.swap_apply_self]
    rfl
  · have hkind' : A.kind w = false := by simpa using hkind
    have hlk : lg k = none := by simpa [toKindAlg_kind_mk, hkind'] using hk
    show ((if (A.absorb F).toKindAlg.kind (⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩, c) then _
      else _), qs) = A.placePending F E' ω' k ((if A.toKindAlg.kind (AlgShape.CntW.mk w c) then _ else _), qs)
    rw [if_neg (show ¬ (A.absorb F).toKindAlg.kind (⟨w, rq, rs, lg, A.storeBelow F E' ω' k lg⟩, c) =
      true from hkind), if_neg (show ¬ A.toKindAlg.kind (AlgShape.CntW.mk w c) = true from hkind)]
    simp only [placePending, placeWith, relayAns, hlk, Option.elim, Equiv.swap_self,
      Equiv.refl_apply, mainAns_of_none _ _ _ _ hlk]

variable [AddGroup Y] [Nonempty X]

/-- **The oracle of slot `k`**, on the query branches, is the main oracle at the relayed logs. -/
theorem oraclePerm_placePending (hR : F.Relays E ω E' ω' A.slots) (k : Fin A.slots)
    (g : A.toKindAlg.G) :
    E'.oraclePerm (A.absorb F).toKindAlg.kind ω' (A.placePending F E' ω' k g) =
      A.placePending F E' ω' k (E.oraclePerm A.toKindAlg.kind ω g) := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  change LogReg Req A.slots at lg
  simp only [Env.oraclePerm, queryPermOf_apply]
  refine Prod.ext rfl (funext fun j => ?_)
  show (_, _ + (if A.kind w then 0 else E'.oracle ω' (F.logs lg)) _) =
    (_, _ + (if A.kind w then 0 else E.oracle ω lg) _)
  rw [hR.oracle_eq lg]
  rfl

/-- **The post-phase query** is the main oracle at the relayed logs. -/
theorem postG_placeClean (hR : F.Relays E ω E' ω' A.slots) (j : ℕ) (g : A.toKindAlg.G) :
    (A.absorb F).toKindAlg.postG E' ω' (A.placeClean F E' ω' j g) =
      A.placeClean F E' ω' j (A.toKindAlg.postG E ω g) := by
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := g
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  change LogReg Req A.slots at lg
  simp only [KindAlg.postG, queryPermOf_apply]
  refine Prod.ext rfl (funext fun i => ?_)
  show (_, _ + E'.oracle ω' (F.logs lg) _) = (_, _ + E.oracle ω lg _)
  rw [hR.oracle_eq lg]
  rfl

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] in
theorem respG_mem_TSet' (k : Fin A.slots) {g : A.toKindAlg.G} (hg : g ∈ A.toKindAlg.TSet k) :
    A.toKindAlg.respG E ω k g ∈ A.toKindAlg.TSet k := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := g
  have h' : A.toKindAlg.respG E ω k ((w, req, resp, lg), prs) =
      ((w, req, if A.kind w.work then Equiv.swap none (E.answer ω lg k) resp else resp, lg), prs) := by
    show ((if A.kind w.work then _ else _), prs) = _
    by_cases h : A.kind w.work <;> simp [h]
  rw [h']
  simpa [KindAlg.TSet, splitLogs, KindAlg.reqOutG] using hg

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] in
theorem oraclePerm_mem_TSet' (k : Fin A.slots) {g : A.toKindAlg.G}
    (hg : g ∈ A.toKindAlg.TSet k) : E.oraclePerm A.toKindAlg.kind ω g ∈ A.toKindAlg.TSet k := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := g
  simpa [KindAlg.TSet, Env.oraclePerm, queryPermOf_apply, splitLogs, KindAlg.reqOutG] using hg

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] in
/-- A basis permutation that keeps the logs below `j` keeps matrices dephased in them. -/
theorem dephase_logsBelow_submatrix {j : ℕ} {π : Equiv.Perm A.toKindAlg.G}
    (hπ : ∀ g, A.toKindAlg.logsBelow j (π g) = A.toKindAlg.logsBelow j g)
    {τ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ} (hτ : dephase (A.toKindAlg.logsBelow j) τ = τ) :
    dephase (A.toKindAlg.logsBelow j) (τ.submatrix π.symm π.symm) = τ.submatrix π.symm π.symm := by
  have hπ' : ∀ g, A.toKindAlg.logsBelow j (π.symm g) = A.toKindAlg.logsBelow j g := fun g => by
    rw [← hπ (π.symm g), Equiv.apply_symm_apply]
  ext a b
  rw [← hτ]
  simp only [dephase, submatrix_apply, hπ']
  split_ifs <;> rfl

/-- **One slot of the mixed game of the absorbed adversary is the placed slot of the adversary's
mixed game**, on matrices whose logs from slot `k` on are blank and that are dephased in the
logs below `k`, for an injective relay of requests. -/
theorem slot_absorb (hR : F.Relays E ω E' ω' A.slots) (hinj : ∀ c, Function.Injective (F.route c))
    (k : Fin A.slots) {σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ}
    (hσ : SuppIn (A.toKindAlg.blankFrom k) σ) (hd : dephase (A.toKindAlg.logsBelow k) σ = σ) :
    (Circuit.kraus ((A.absorb F).toKindAlg.liftG (slotStep k))
        ((A.absorb F).toKindAlg.eventCirc E' ω' k true)).run (Equiv.refl _)
        (embed (A.placeStart F E' ω' k) σ) =
      embed (A.placePending F E' ω' k) ((Circuit.kraus (A.toKindAlg.liftG (slotStep k))
        (A.toKindAlg.eventCirc E ω k true)).run (Equiv.refl _) σ) := by
  simp only [KindAlg.eventCirc, Circuit.run, ↓reduceIte, KrausMap.ofPerm_apply,
    KrausMap.measureFn_apply]
  set τ := A.toKindAlg.liftG (slotStep k) σ with hτdef
  have hτ : SuppIn (A.toKindAlg.blankFrom k) τ := KindAlg.SuppIn.liftG A.toKindAlg hσ _
  have hτd : dephase (A.toKindAlg.logsBelow k) τ = τ := by
    rw [hτdef, ← KrausMap.apply_dephase (A.toKindAlg.blockDiag_liftG_logsBelow _ _), hd]
  rw [absorb_liftG_apply,
    submatrix_embed_of_forall (fun a => A.gamePerm_afterAt_placeStart F E' ω' k a),
    gameCntStep_placeClean, ← hτdef,
    submatrix_embed (π' := A.toKindAlg.copyG k) (S := A.toKindAlg.blankFrom k)
      (fun a ha => A.gamePerm_setAt_placeClean F E' ω' k (ha k le_rfl)) hτ]
  set τ₁ := τ.submatrix (A.toKindAlg.copyG k).symm (A.toKindAlg.copyG k).symm with hτ₁def
  have hτ₁ : SuppIn (A.toKindAlg.TSet k) τ₁ :=
    hτ.submatrix_perm fun a ha => A.toKindAlg.copyG_mem_TSet k ha
  have hτ₁d : dephase (A.toKindAlg.logsBelow k) τ₁ = τ₁ :=
    A.dephase_logsBelow_submatrix (fun g => A.toKindAlg.logsBelow_copyG k le_rfl g) hτd
  rw [submatrix_embed_of_mem (fun a ha => A.copyG_placeSet F E' ω' k ha) hτ₁, dephase_embed,
    A.dephase_placeCopied F E' ω' hinj k hτ₁d,
    submatrix_embed (π' := A.toKindAlg.respG E ω k) (S := A.toKindAlg.TSet k)
      (fun a ha => A.respG_placeCopied F E' ω' E ω hR k ha) (hτ₁.dephase _),
    submatrix_embed (π' := E.oraclePerm A.toKindAlg.kind ω) (S := Set.univ)
      (fun a _ => A.oraclePerm_placePending F E' ω' E ω hR k a) (fun a b h => by simp at h)]

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] in
/-- **One slot of the adversary's mixed game keeps the blank later logs** (`KindAlg.suppIn_slot`,
for any environment). -/
theorem suppIn_slot' (k : Fin A.slots) {σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ}
    (hσ : SuppIn (A.toKindAlg.blankFrom k) σ) :
    SuppIn (A.toKindAlg.blankFrom (k + 1)) ((Circuit.kraus (A.toKindAlg.liftG (slotStep k))
        (A.toKindAlg.eventCirc E ω k true)).run (Equiv.refl _) σ) := by
  have hσ1 := KindAlg.SuppIn.liftG A.toKindAlg hσ (slotStep k)
  simp only [KindAlg.eventCirc, Circuit.run, ↓reduceIte, KrausMap.ofPerm_apply,
    KrausMap.measureFn_apply]
  rw [A.toKindAlg.copy_measure k hσ1]
  refine (((hσ1.dephase _).submatrix_perm fun r hr => A.toKindAlg.copyG_mem_TSet k hr).submatrix_perm
    fun r hr => A.respG_mem_TSet' E ω k hr).submatrix_perm fun r hr => ?_
  exact A.toKindAlg.TSet_subset k (A.oraclePerm_mem_TSet' E ω k hr)

omit [Fintype Req'] [DecidableEq Req'] [Fintype Resp'] [DecidableEq Resp'] [Inhabited Req'] in
/-- **One slot of the adversary's mixed game keeps the dephasing in the logs of the slots
done** (`KindAlg.slot_run_deph`). -/
theorem dephase_slot (k : Fin A.slots) {σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ}
    (hd : dephase (A.toKindAlg.logsBelow k) σ = σ) :
    dephase (A.toKindAlg.logsBelow (k + 1)) ((Circuit.kraus (A.toKindAlg.liftG (slotStep k))
        (A.toKindAlg.eventCirc E ω k true)).run (Equiv.refl _) σ) =
      (Circuit.kraus (A.toKindAlg.liftG (slotStep k))
        (A.toKindAlg.eventCirc E ω k true)).run (Equiv.refl _) σ := by
  have h := A.toKindAlg.slot_run_deph E ω k σ
  rw [hd] at h
  rw [h]
  ext a b
  simp only [dephase]
  split_ifs <;> rfl

/-- The permutation before step `k` is the identity from the last slot on. -/
theorem setAt_of_le {k : ℕ} (hk : A.slots ≤ k) : A.setAt F k = Equiv.refl _ := by
  simp [setAt, AlgShape.setAt, show ¬ k < A.slots by omega]

/-- The identity of the absorbed registers on the game registers. -/
theorem gamePerm_refl : A.gamePerm F (Equiv.refl _) = Equiv.refl _ :=
  Equiv.ext fun _ => rfl

/-- **From the last slot on, the placements between slots agree.** -/
theorem placeClean_of_le {j j' : ℕ} (hj : A.slots ≤ j) (hj' : A.slots ≤ j') :
    A.placeClean F E' ω' j = A.placeClean F E' ω' j' := by
  have : A.storeBelow F E' ω' j = A.storeBelow F E' ω' j' := by
    funext lg i
    simp only [storeBelow]
    rw [if_pos (by omega), if_pos (by omega)]
  simp only [placeClean, this]

/-- **A step from the last slot on**: the relayed reply of the last slot written, the adversary's
step. -/
theorem liftG_placeStart_of_le (k : StepIdx A.slots A.post) (hk : A.slots ≤ (k : ℕ))
    (τ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ) :
    (A.absorb F).toKindAlg.liftG k (embed (A.placeStart F E' ω' k) τ) =
      embed (A.placeClean F E' ω' k) (A.toKindAlg.liftG k τ) := by
  rw [absorb_liftG_apply, submatrix_embed_of_forall (fun a => A.gamePerm_afterAt_placeStart F E' ω' k a),
    gameCntStep_placeClean, A.setAt_of_le F hk, gamePerm_refl]
  rfl

/-- **The initial state of the absorbed adversary's mixed game is the placed initial state.** -/
theorem mgInit_absorb :
    (A.absorb F).toKindAlg.mgInit = embed (A.placeClean F E' ω' 0) A.toKindAlg.mgInit := by
  rw [KindAlg.mgInit, KindAlg.mgInit, toKindAlg_init, toKindAlg_init, absorb_init]
  refine ((MState.reindex_tensorKet_mat _ _ _).trans (congrArg _
    ((MState.reindex_tensorKet_mat _ _ _).trans (congrArg _ (MState.reindex_tensorKet_mat _ _ _))))).trans
    (Eq.trans ?_ (congrArg _ ((MState.reindex_tensorKet_mat _ _ _).trans
      (congrArg _ (MState.reindex_tensorKet_mat _ _ _)))).symm)
  simp only [embed_embed]
  congr 1

theorem run_slots_absorb (hR : F.Relays E ω E' ω' A.slots)
    (hinj : ∀ c, Function.Injective (F.route c)) (l : List (Fin A.slots)) (j : ℕ)
    (hl : l.map Fin.val = List.range' j l.length) {σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ}
    (hσ : SuppIn (A.toKindAlg.blankFrom j) σ) (hd : dephase (A.toKindAlg.logsBelow j) σ = σ) :
    (Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus ((A.absorb F).toKindAlg.liftG (slotStep k))
          ((A.absorb F).toKindAlg.eventCirc E' ω' k true))).run (Equiv.refl _)
        (embed (A.placeStart F E' ω' j) σ) =
      embed (A.placeStart F E' ω' (j + l.length)) ((Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus (A.toKindAlg.liftG (slotStep k))
          (A.toKindAlg.eventCirc E ω k true))).run (Equiv.refl _) σ) ∧
    SuppIn (A.toKindAlg.blankFrom (j + l.length)) ((Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus (A.toKindAlg.liftG (slotStep k))
          (A.toKindAlg.eventCirc E ω k true))).run (Equiv.refl _) σ) ∧
    dephase (A.toKindAlg.logsBelow (j + l.length)) ((Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus (A.toKindAlg.liftG (slotStep k))
          (A.toKindAlg.eventCirc E ω k true))).run (Equiv.refl _) σ) =
      (Circuit.concat (l.map fun k : Fin A.slots =>
        Circuit.kraus (A.toKindAlg.liftG (slotStep k))
          (A.toKindAlg.eventCirc E ω k true))).run (Equiv.refl _) σ := by
  induction l generalizing j σ with
  | nil => exact ⟨rfl, hσ, hd⟩
  | cons k l ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
    have hσ' : SuppIn (A.toKindAlg.blankFrom k) σ := by rw [hl.1]; exact hσ
    have hd' : dephase (A.toKindAlg.logsBelow k) σ = σ := by rw [hl.1]; exact hd
    have h1 := A.slot_absorb F E' ω' E ω hR hinj k hσ' hd'
    have hstart : A.placeStart F E' ω' j = A.placeStart F E' ω' k := by rw [hl.1]
    have hnext : A.placePending F E' ω' k = A.placeStart F E' ω' (k + 1) := by
      simp only [placeStart]
      rw [dif_pos ⟨by omega, by simp⟩]
      rfl
    obtain ⟨ih1, ih2, ih3⟩ := ih (k + 1) (by rw [hl.2, hl.1]) (A.suppIn_slot' E ω k hσ')
      (A.dephase_slot E ω k hd')
    rw [Circuit.concat, Circuit.run_append, Circuit.run_concat, hstart, h1, hnext, ih1]
    rw [show (k : ℕ) + 1 + l.length = j + (l.length + 1) by rw [hl.1]; omega] at ih2 ih3 ⊢
    exact ⟨rfl, ih2, ih3⟩

theorem run_posts_absorb (hR : F.Relays E ω E' ω' A.slots) (l : List (Fin A.post)) (b₀ : ℕ)
    (hl : l.map Fin.val = List.range' b₀ l.length) (τ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ) :
    (Circuit.concat (l.map fun b : Fin A.post =>
        Circuit.kraus ((A.absorb F).toKindAlg.liftG (postStep b))
          (.kraus (KrausMap.ofPerm ((A.absorb F).toKindAlg.postG E' ω')) .nil))).run (Equiv.refl _)
        (embed (A.placeStart F E' ω' (A.slots + b₀)) τ) =
      embed (A.placeStart F E' ω' (A.slots + (b₀ + l.length)))
        ((Circuit.concat (l.map fun b : Fin A.post =>
          Circuit.kraus (A.toKindAlg.liftG (postStep b))
            (.kraus (KrausMap.ofPerm (A.toKindAlg.postG E ω)) .nil))).run (Equiv.refl _) τ) := by
  induction l generalizing b₀ τ with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
    have hs : A.placeStart F E' ω' (A.slots + b₀) = A.placeStart F E' ω' (postStep (slots := A.slots) b : ℕ) := by
      simp [hl.1]
    have hnext : A.placeClean F E' ω' (postStep (slots := A.slots) b : ℕ) = A.placeStart F E' ω' (A.slots + (b₀ + 1)) := by
      have : ¬ (0 < A.slots + (b₀ + 1) ∧ A.slots + (b₀ + 1) - 1 < A.slots) := by omega
      simp only [placeStart, dif_neg this]
      exact A.placeClean_of_le F E' ω' (by simp) (by omega)
    rw [Circuit.concat, Circuit.run_append, Circuit.run_concat, hs]
    simp only [Circuit.run, KrausMap.ofPerm_apply]
    rw [A.liftG_placeStart_of_le F E' ω' _ (by simp),
      submatrix_embed (π' := A.toKindAlg.postG E ω) (S := Set.univ)
        (fun a _ => A.postG_placeClean F E' ω' E ω hR _ a) (fun a b h => by simp at h),
      hnext, ih (b₀ + 1) (by simpa [hl.1] using hl.2)]
    rw [show b₀ + 1 + l.length = b₀ + (l.length + 1) by omega]

/-- **The mixed game of the absorbed adversary is the placed mixed game of the adversary**: on
the tape `ω'` of the main environment `E'`, its final state is the final state of the adversary's
mixed game against `E` on `ω`, placed (`placeClean`), when `E` at `ω` is the relay of `E'` at `ω'`
(`SideRelay.Relays`) and the relay of requests is injective. -/
theorem mgRun_absorb (hR : F.Relays E ω E' ω' A.slots)
    (hinj : ∀ c, Function.Injective (F.route c)) :
    (A.absorb F).toKindAlg.mgRun E' ω' true =
      embed (A.placeClean F E' ω' (A.slots + A.post)) (A.toKindAlg.mgRun E ω true) := by
  obtain ⟨h1, -, -⟩ := A.run_slots_absorb F E' ω' E ω hR hinj (List.finRange A.slots) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange])
    A.toKindAlg.suppIn_mgInit (by
      have hl : ∀ a b, A.toKindAlg.logsBelow 0 a = A.toKindAlg.logsBelow 0 b := fun a b =>
        funext fun k => by simp [KindAlg.logsBelow]
      ext a b
      simp [dephase, hl a b])
  rw [List.length_finRange, Nat.zero_add] at h1
  have h2 := A.run_posts_absorb F E' ω' E ω hR (List.finRange A.post) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange])
  rw [List.length_finRange, Nat.zero_add] at h2
  have h0 : A.placeStart F E' ω' 0 = A.placeClean F E' ω' 0 := by
    simp [placeStart]
  simp only [KindAlg.mgRun, KindAlg.mgCirc, Circuit.run_append]
  rw [A.mgInit_absorb F E' ω', ← h0, h1]
  erw [h2]
  simp only [Circuit.run]
  exact A.liftG_placeStart_of_le F E' ω' lastStep (by simp) _

end Place

/-! ### The output law -/

/-- The adversary's registers read from the absorbed adversary's registers. -/
def absorbedAdv (F : SideRelay Req Resp Req' Resp')
    (d : DReg (A.absorb F).toKindAlg.W A.width X Y Req' Resp') :
    DReg A.toKindAlg.W A.width X Y Req Resp :=
  (((AlgShape.CntW.mk d.1.1.work.work d.1.1.cnt), d.1.1.work.request, d.1.1.work.response), d.2)

section Out

variable {Ω' St' : Type} {Q' : ℕ} [OracleState St' X Y] (E' : Env Ω' Req' Resp' X Y Q' St')
  (ω' : Ω')

/-- **The placement between slots is injective.** -/
theorem placeClean_injective (j : ℕ) : Function.Injective (A.placeClean F E' ω' j) := by
  rintro ⟨⟨wc, rq, rs, lg⟩, qs⟩ ⟨⟨wc', rq', rs', lg'⟩, qs'⟩ h
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc
  obtain ⟨w', c', rfl⟩ := AlgShape.CntW.exists_eq_mk wc'
  simp only [placeClean, placeWith, Prod.mk.injEq, AlgShape.CntW.work_mk, AlgShape.CntW.cnt_mk] at h
  obtain ⟨⟨hm, -⟩, h6⟩ := h
  obtain ⟨hw, h5⟩ := AlgShape.CntW.mk_inj.1 hm
  obtain ⟨h1, h2, h3, h4, -⟩ := AbsorbedWork.mk.inj hw
  subst h1 h2 h3 h4 h5 h6
  rfl

variable {Ω St : Type} {Q : ℕ} [OracleState St X Y] (E : Env Ω Req Resp X Y Q St) (ω : Ω)
  [AddGroup Y] [Nonempty X]

/-- **The diagonal of the absorbed adversary's mixed game** is that of the adversary's, read
through the placement. -/
theorem sum_diag_mgRun_absorb (hR : F.Relays E ω E' ω' A.slots)
    (hinj : ∀ c, Function.Injective (F.route c)) (g : (A.absorb F).toKindAlg.G → ℝ) :
    ∑ r', g r' * ((A.absorb F).toKindAlg.mgRun E' ω' true r' r').re =
      ∑ r, g (A.placeClean F E' ω' (A.slots + A.post) r) * (A.toKindAlg.mgRun E ω true r r).re := by
  rw [A.mgRun_absorb F E' ω' E ω hR hinj, embed_diag_of_injective (A.placeClean_injective F E' ω' _)]

end Out

section Law

variable [Nonempty X] [AddGroup Y] [Nonempty Y] {C : Challenger X Y Req Resp}
  {C' : Challenger X Y Req' Resp'}

/-- **The final oracle of the absorbed adversary's composition, at a placed state, is the
adversary's**, when the challenger's environment is the relay of the main challenger's. -/
theorem finalOracle_placeClean {c : C.Coins} {c' : C'.Coins} (H : X → Y)
    (hR : F.Relays C.toPureEnv (H, c) C'.toPureEnv (H, c') A.slots) (j : ℕ) (r : A.toKindAlg.G) :
    H.reprogram ((A.absorb F).toKindAlg.postAss C'
        ((A.absorb F).toKindAlg.emb C' H c' A.slots (A.placeClean F C'.toPureEnv (H, c') j r)).1.chal) =
      H.reprogram (A.toKindAlg.postAss C (A.toKindAlg.emb C H c A.slots r).1.chal) := by
  have h1 := (A.absorb F).toKindAlg.postAss_eq C' H c' (A.placeClean F C'.toPureEnv (H, c') j r)
  have h2 := A.toKindAlg.postAss_eq C H c r
  obtain ⟨⟨wc_, rq, rs, lg⟩, qs⟩ := r
  obtain ⟨w, k, rfl⟩ := AlgShape.CntW.exists_eq_mk wc_
  exact h1.trans ((hR.oracle_eq lg).symm.trans h2.symm)

variable {S : Type} [Fintype S] (σ : PMF S) (F' : S → SideRelay Req Resp Req' Resp')
  (e : C.Coins ≃ S × C'.Coins)

/-- **The output law of an adversary against a challenger that relays a main challenger is the
average, over the side coins, of the absorbed adversary's against the main challenger**
(`absorb`), on every event of the adversary's registers, its logs, the main challenger's logs (the relayed
logs `(F' s).logs`, at the side coins `s` of the challenger's coins), the coins and the final
oracle. Hypotheses: the challenger's coins are the side coins `σ` and the main coins
(`hcoins`, along `e`); at every oracle and coins its environment is the relay `F' s` of the main
challenger's (`hR`); each relay of requests is injective (`hinj`). -/
theorem outLaw_absorb (hcoins : ∀ s c', C.coins (e.symm (s, c')) = σ s * C'.coins c')
    (hR : ∀ H s c', (F' s).Relays C.toPureEnv (H, e.symm (s, c')) C'.toPureEnv (H, c') A.slots)
    (hinj : ∀ s c, Function.Injective ((F' s).route c)) (H : X → Y)
    (P : DReg A.toKindAlg.W A.width X Y Req Resp → LogReg Req A.slots → LogReg Req' A.slots →
      C.Coins → (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut C id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs ((F' (e v.chal.coins).1).logs v.chal.logs) v.chal.coins
          (H.reprogram (A.toKindAlg.postAss C v.chal))} =
      ∑ s, σ s * (((A.absorb (F' s)).toKindAlg.composeBothOut C' id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P (A.absorbedAdv (F' s) v.adv) v.adv.1.1.work.logs v.chal.logs
          (e.symm (s, v.chal.coins))
          (H.reprogram ((A.absorb (F' s)).toKindAlg.postAss C' v.chal))} := by
  classical
  have hite : ∀ (p : Prop) [Decidable p] (x : ℝ), (if p then x else 0) = (if p then 1 else 0) * x :=
    fun p _ x => by split_ifs <;> simp
  have hdiag : ∀ (c : C.Coins) (r : A.toKindAlg.G),
      0 ≤ (A.toKindAlg.mgRun C.toPureEnv (H, c) true r r).re := fun c r =>
    (Complex.nonneg_iff.1 ((Circuit.posSemidef_run _ _ A.toKindAlg.mgInitM.posSemidef).diag_nonneg
      (i := r))).1
  rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_id]
  have hs : ∀ s, (((A.absorb (F' s)).toKindAlg.composeBothOut C' id).outLaw H).toOuterMeasure
      {o | ∃ v ∈ o, P (A.absorbedAdv (F' s) v.adv) v.adv.1.1.work.logs v.chal.logs
        (e.symm (s, v.chal.coins))
        (H.reprogram ((A.absorb (F' s)).toKindAlg.postAss C' v.chal))} =
      ENNReal.ofReal (∑ c', (C'.coins c').toReal * ∑ r : A.toKindAlg.G,
        if P (A.toKindAlg.emb C H (e.symm (s, c')) A.slots r).1.adv
          (A.toKindAlg.emb C H (e.symm (s, c')) A.slots r).1.chal.logs
          ((F' s).logs (A.toKindAlg.emb C H (e.symm (s, c')) A.slots r).1.chal.logs)
          (A.toKindAlg.emb C H (e.symm (s, c')) A.slots r).1.chal.coins
          (H.reprogram (A.toKindAlg.postAss C (A.toKindAlg.emb C H (e.symm (s, c')) A.slots r).1.chal))
        then (A.toKindAlg.mgRun C.toPureEnv (H, e.symm (s, c')) true r r).re else 0) := by
    intro s
    rw [KindAlg.toOuterMeasure_outLaw_composeBothOut_id]
    congr 1
    refine Finset.sum_congr rfl fun c' _ => ?_
    congr 1
    rw [Finset.sum_congr rfl fun r' _ => hite _ _, Finset.sum_congr rfl fun r _ => hite _ _,
      A.sum_diag_mgRun_absorb (F' s) C'.toPureEnv (H, c') C.toPureEnv (H, e.symm (s, c'))
        (hR H s c') (hinj s)]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [A.finalOracle_placeClean (F' s) H (hR H s c')]
    rfl
  simp only [hs]
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  rw [ENNReal.ofReal_sum_of_nonneg fun s _ => Finset.sum_nonneg fun c' _ => mul_nonneg
    ENNReal.toReal_nonneg (Finset.sum_nonneg fun r _ => by split_ifs; exact hdiag _ r; exact le_rfl)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [hcoins, ENNReal.toReal_mul, mul_assoc]
  rw [← Finset.mul_sum, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (PMF.apply_ne_top σ s)]
  have hc : ∀ c' r, (A.toKindAlg.emb C H (e.symm (s, c')) A.slots r).1.chal.coins = e.symm (s, c') :=
    fun _ _ => rfl
  simp only [hc, Equiv.apply_symm_apply]

end Law

/-- **Absorbing keeps trace preservation**: the steps are the adversary's, tensored with the
identity, between basis permutations. -/
theorem absorb_tracePreserving (h : A.TracePreserving) : (A.absorb F).TracePreserving :=
    fun k => by
  rw [show (A.absorb F).step k = _ from A.absorbStep_eq F k]
  exact KrausMap.comp_tp (KrausMap.tp_ofPerm _)
    (KrausMap.comp_tp (KrausMap.reindex_tp _ (KrausMap.tensorId_tp (h k) _)) (KrausMap.tp_ofPerm _))

end AdaptiveIAlg

end GordieHowe.Quantum
