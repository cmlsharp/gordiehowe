-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.Pure

@[expose] public section

/-!
# The composed algorithm is the mixed game

Proof tools for `KindAlg.composeBoth_eq_pureGame` (`GordieHowe/Model/Quantum/Interactive/Adaptive.lean`): the composed core
algorithm of an interactive adversary and a challenger (`IAlg.compose`, through the adversary with a kind register `KindAlg`) has, for each oracle and
coins of the challenger, the final state of the mixed game with measured requests
(`Quantum.KindAlg.mgRun … true`, `GordieHowe/Model/Quantum/Interactive/Pure.lean`), placed in the larger registers of the
composition with the challenger's registers holding the answers to its queries.

- **Programs fed with answers** (`OracleProgAns`): fed the answers of an oracle `h` to its
  queries, a program returns its result `run h`, and makes its `i`-th query `trace h` at `i`.
- **The challenger's state read from the registers** (`Quantum.KindAlg.regState_eq`): with the answers of
  the oracle in force in its registers, the history and the assignments read from the registers
  are those of the challenger in the pure game (`Challenger.toPureEnv`).
-/

open Finset Matrix
open scoped BigOperators ENNReal Kronecker ComplexOrder

namespace GordieHowe.Quantum


/-! ### Programs fed with answers -/

namespace OracleProgAns

variable {A B R : Type*} (h : A → B)

theorem result_trace_append :
    ∀ (p : OracleProg A B R) (l : List B), result p ((p.trace h).map h ++ l) = some (p.run h)
  | .pure _, _ => rfl
  | .query a k, l => result_trace_append (k (h a)) l

theorem wants_trace_append :
    ∀ (p : OracleProg A B R) (l : List B), wants p ((p.trace h).map h ++ l) = false
  | .pure _, _ => rfl
  | .query a k, l => wants_trace_append (k (h a)) l

theorem next_trace_append (pad : A) :
    ∀ (p : OracleProg A B R) (l : List B), p.next pad ((p.trace h).map h ++ l) = pad
  | .pure _, _ => rfl
  | .query a k, l => next_trace_append pad (k (h a)) l

theorem wants_take :
    ∀ (p : OracleProg A B R) (i : ℕ), i < (p.trace h).length →
      wants p (((p.trace h).map h).take i) = true
  | .pure _, _, hi => by simp at hi
  | .query _ _, 0, _ => rfl
  | .query a k, i + 1, hi => by
    simp only [OracleProg.trace_query, List.length_cons, List.map_cons, List.take_succ_cons] at hi ⊢
    exact wants_take (k (h a)) i (by omega)

theorem result_of_prefix (p : OracleProg A B R) {l : List B} (hl : (p.trace h).map h <+: l) :
    result p l = some (p.run h) := by
  obtain ⟨l', rfl⟩ := hl
  exact result_trace_append h p l'

theorem next_take (pad : A) :
    ∀ (p : OracleProg A B R) (i : ℕ) (hi : i < (p.trace h).length),
      p.next pad (((p.trace h).map h).take i) = (p.trace h)[i]
  | .pure _, _, hi => by simp at hi
  | .query _ _, 0, _ => rfl
  | .query a k, i + 1, hi => by
    simp only [OracleProg.trace_query, List.length_cons, List.map_cons, List.take_succ_cons,
      List.getElem_cons_succ] at hi ⊢
    exact next_take pad (k (h a)) i (by omega)

end OracleProgAns

@[simp]
theorem _root_.Function.Involutive.toPerm_apply' {α : Sort*} {f : α → α}
    (h : Function.Involutive f) (x : α) : Function.Involutive.toPerm f h x = f x :=
  rfl

/-! ### Matrices placed along an injective map, and supports -/

section Embed

variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

/-- **A matrix placed along a map of bases**: `embed e σ (e a) (e b) = σ a b` for injective `e`,
zero outside the image. -/
def embed (e : κ → ι) (σ : Matrix κ κ ℂ) : Matrix ι ι ℂ :=
  fun i j => ∑ a, ∑ b, if e a = i ∧ e b = j then σ a b else 0

theorem embed_apply_of_injective {e : κ → ι} (he : Function.Injective e) (σ : Matrix κ κ ℂ)
    (a b : κ) : embed e σ (e a) (e b) = σ a b := by
  simp only [embed]
  rw [Finset.sum_eq_single a (fun a' _ ha' => Finset.sum_eq_zero fun b' _ => by
    simp [he.ne ha']) (by simp)]
  rw [Finset.sum_eq_single b (fun b' _ hb' => by simp [he.ne hb']) (by simp)]
  simp

theorem embed_apply_of_notMem_left {e : κ → ι} (σ : Matrix κ κ ℂ) {i : ι} (hi : ∀ a, e a ≠ i)
    (j : ι) : embed e σ i j = 0 :=
  Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by simp [hi a]

theorem embed_apply_of_notMem_right {e : κ → ι} (σ : Matrix κ κ ℂ) (i : ι) {j : ι}
    (hj : ∀ b, e b ≠ j) : embed e σ i j = 0 :=
  Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => by simp [hj b]

/-- A matrix supported in `S`: its entries vanish unless both indices lie in `S`. -/
def SuppIn (S : Set κ) (σ : Matrix κ κ ℂ) : Prop :=
  ∀ a b, (a ∉ S ∨ b ∉ S) → σ a b = 0

/-- **Basis permutations intertwined along maps on a support**: if `π (e a) = e' (π' a)` for
`a ∈ S` and `σ` is supported in `S`, conjugating the placed matrix by `π` is placing the
conjugated matrix. -/
theorem submatrix_embed {κ' : Type*} [Fintype κ'] {e : κ → ι} {e' : κ' → ι} {π : Equiv.Perm ι}
    {π' : κ ≃ κ'} {S : Set κ} (hπ : ∀ a ∈ S, π (e a) = e' (π' a)) {σ : Matrix κ κ ℂ}
    (hσ : SuppIn S σ) :
    (embed e σ).submatrix π.symm π.symm = embed e' (σ.submatrix π'.symm π'.symm) := by
  ext i j
  simp only [submatrix_apply, embed]
  rw [← π'.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← π'.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Equiv.symm_apply_apply]
  by_cases hab : a ∈ S ∧ b ∈ S
  · rw [← hπ a hab.1, ← hπ b hab.2]
    simp only [Equiv.eq_symm_apply]
  · rw [hσ a b (by tauto)]
    simp

/-- Dephasing commutes with placing: `dephase g (embed e σ) = embed e (dephase (g ∘ e) σ)`. -/
theorem dephase_embed {L : Type*} [DecidableEq L] (e : κ → ι) (g : ι → L) (σ : Matrix κ κ ℂ) :
    dephase g (embed e σ) = embed e (dephase (g ∘ e) σ) := by
  ext i j
  simp only [dephase, embed, Function.comp]
  split_ifs with h
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    by_cases hab : e a = i ∧ e b = j
    · rw [if_pos hab, if_pos hab, if_pos (by rw [hab.1, hab.2]; exact h)]
    · rw [if_neg hab, if_neg hab]
  · symm
    refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
    by_cases hab : e a = i ∧ e b = j
    · rw [if_pos hab, if_neg (by rw [hab.1, hab.2]; exact h)]
    · rw [if_neg hab]

/-- The matrix of a map of bases: `jmat e i a = 1` if `e a = i`. -/
def jmat (e : κ → ι) : Matrix ι κ ℂ :=
  fun i a => if e a = i then 1 else 0

theorem embed_eq_jmat [DecidableEq κ] (e : κ → ι) (σ : Matrix κ κ ℂ) :
    embed e σ = jmat e * σ * (jmat e)ᴴ := by
  ext i j
  simp only [embed, jmat, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : e a = i <;> by_cases hb : e b = j <;> simp [ha, hb]

/-- **Kraus maps intertwined along a map of bases**: if `op r * jmat e = jmat e * op' r`, applying
`K` to the placed matrix is placing `K'` applied. -/
theorem KrausMap.apply_embed_of_intertwine [DecidableEq κ] {R : Type*} [Fintype R]
    {K : KrausMap R ι ι} {K' : KrausMap R κ κ} {e : κ → ι}
    (h : ∀ r, K.op r * jmat e = jmat e * K'.op r) (σ : Matrix κ κ ℂ) :
    K (embed e σ) = embed e (K' σ) := by
  rw [embed_eq_jmat, embed_eq_jmat, KrausMap.apply, KrausMap.apply, Matrix.mul_sum,
    Matrix.sum_mul]
  refine Finset.sum_congr rfl fun r _ => ?_
  have h' : (jmat e)ᴴ * (K.op r)ᴴ = (K'.op r)ᴴ * (jmat e)ᴴ := by
    rw [← conjTranspose_mul, h r, conjTranspose_mul]
  calc K.op r * (jmat e * σ * (jmat e)ᴴ) * (K.op r)ᴴ
      = (K.op r * jmat e) * σ * ((jmat e)ᴴ * (K.op r)ᴴ) := by simp only [Matrix.mul_assoc]
    _ = (jmat e * K'.op r) * σ * ((K'.op r)ᴴ * (jmat e)ᴴ) := by rw [h r, h']
    _ = jmat e * (K'.op r * σ * (K'.op r)ᴴ) * (jmat e)ᴴ := by simp only [Matrix.mul_assoc]

/-- Placing along `id × φ` commutes with a Kraus map on the first factor. -/
theorem KrausMap.tensorId_apply_embed {R D L M : Type*} [Fintype R] [Fintype D] [DecidableEq D]
    [Fintype L] [DecidableEq L] [Fintype M] [DecidableEq M] (K : KrausMap R D D) (φ : L → M)
    (σ : Matrix (D × L) (D × L) ℂ) :
    (K.tensorId M) (embed (Prod.map _root_.id φ) σ) =
      embed (Prod.map _root_.id φ) ((K.tensorId L) σ) := by
  refine KrausMap.apply_embed_of_intertwine (fun r => ?_) σ
  ext ⟨x, m⟩ ⟨d, l⟩
  simp only [KrausMap.tensorId, Matrix.mul_apply, kroneckerMap_apply, Matrix.one_apply, jmat,
    Prod.map, _root_.id, Prod.mk.injEq, Fintype.sum_prod_type]
  simp [ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', mul_ite, ite_mul, eq_comm]

omit [Fintype ι] in
theorem submatrix_embed_equiv {ι' : Type*} [Fintype ι'] [DecidableEq ι'] (e : κ → ι) (f : ι' ≃ ι)
    (σ : Matrix κ κ ℂ) : (embed e σ).submatrix f f = embed (f.symm ∘ e) σ := by
  ext i j
  simp only [submatrix_apply, embed, Function.comp, Equiv.symm_apply_eq]
omit [Fintype ι] in
theorem embed_comp_equiv {κ' : Type*} [Fintype κ'] (e : κ → ι) (g : κ' ≃ κ)
    (σ : Matrix κ' κ' ℂ) : embed (e ∘ g) σ = embed e (σ.submatrix g.symm g.symm) := by
  ext i j
  simp only [embed, Function.comp, submatrix_apply]
  rw [← g.sum_comp]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← g.sum_comp]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp

theorem embed_diag_of_injective {e : κ → ι} (he : Function.Injective e) (σ : Matrix κ κ ℂ)
    (g : ι → ℝ) : ∑ i, g i * (embed e σ i i).re = ∑ a, g (e a) * (σ a a).re := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image e)) fun i _ hi => by
    rw [embed_apply_of_notMem_left _ (fun a ha => hi (Finset.mem_image.2 ⟨a, Finset.mem_univ _, ha⟩)),
      Complex.zero_re, mul_zero]]
  rw [Finset.sum_image fun a _ b _ h => he h]
  exact Finset.sum_congr rfl fun a _ => by rw [embed_apply_of_injective he]

/-- A basis permutation carrying `e` to `e'` carries the placement along `e` to that along `e'`. -/
theorem submatrix_embed_of_forall {e e' : κ → ι} {π : Equiv.Perm ι} (hπ : ∀ a, π (e a) = e' a)
    (σ : Matrix κ κ ℂ) : (embed e σ).submatrix π.symm π.symm = embed e' σ := by
  rw [submatrix_embed (π' := Equiv.refl κ) (S := Set.univ) (fun a _ => hπ a)
    (fun a b h => by simp at h)]
  simp

/-- The same on a support. -/
theorem submatrix_embed_of_mem {e e' : κ → ι} {π : Equiv.Perm ι} {S : Set κ}
    (hπ : ∀ a ∈ S, π (e a) = e' a) {σ : Matrix κ κ ℂ} (hσ : SuppIn S σ) :
    (embed e σ).submatrix π.symm π.symm = embed e' σ := by
  rw [submatrix_embed (π' := Equiv.refl κ) hπ hσ]
  simp

theorem SuppIn.submatrix_perm {S S' : Set κ} {σ : Matrix κ κ ℂ} (hσ : SuppIn S σ)
    {π : Equiv.Perm κ} (hπ : ∀ a ∈ S, π a ∈ S') : SuppIn S' (σ.submatrix π.symm π.symm) := by
  intro a b hab
  simp only [submatrix_apply]
  refine hσ _ _ ?_
  rcases hab with ha | hb
  · exact Or.inl fun h => ha (by simpa using hπ _ h)
  · exact Or.inr fun h => hb (by simpa using hπ _ h)

theorem SuppIn.dephase {L : Type*} [DecidableEq L] {S : Set κ} {σ : Matrix κ κ ℂ}
    (hσ : SuppIn S σ) (g : κ → L) : SuppIn S (Quantum.dephase g σ) := by
  intro a b hab
  simp only [Quantum.dephase]
  split_ifs
  · exact hσ a b hab
  · rfl

/-- A Kraus map whose operators connect only basis states with the same value of `g` preserves
supports defined by `g`. -/
theorem SuppIn.krausApply_of_blockDiag [DecidableEq κ] {L : Type*} [DecidableEq L] {R : Type*}
    [Fintype R] {g : κ → L} {K : KrausMap R κ κ} (hK : K.BlockDiag g) {T : Set L}
    {σ : Matrix κ κ ℂ} (hσ : SuppIn (g ⁻¹' T) σ) : SuppIn (g ⁻¹' T) (K σ) := by
  intro a b hab
  simp only [KrausMap.apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : g a = g k
  · by_cases hl : g b = g l
    · rw [hσ k l (by simpa [Set.mem_preimage, ← hk, ← hl] using hab)]
      simp
    · simp [hK r b l hl]
  · simp [hK r a k hk]

omit [DecidableEq ι] in
theorem embed_prodMap_kronecker_single {D L M : Type*} [Fintype D] [DecidableEq D] [Fintype L]
    [DecidableEq L]
    [Fintype M] [DecidableEq M] (φ : L → M) (ρ : Matrix D D ℂ) (b : L) :
    embed (Prod.map _root_.id φ) (ρ ⊗ₖ Matrix.single b b 1) = ρ ⊗ₖ Matrix.single (φ b) (φ b) 1 := by
  ext ⟨x, m⟩ ⟨y, m'⟩
  simp only [embed, Prod.map, _root_.id, Prod.mk.injEq, kroneckerMap_apply, Matrix.single_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_eq_single x (fun a _ ha => by simp [ha]) (by simp)]
  rw [Finset.sum_eq_single b (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  rw [Finset.sum_eq_single y (fun a _ ha => by simp [ha]) (by simp)]
  rw [Finset.sum_eq_single b (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  by_cases h1 : φ b = m <;> by_cases h2 : φ b = m' <;> simp [h1, h2]

theorem SuppIn.mono {S T : Set κ} {σ : Matrix κ κ ℂ} (hσ : SuppIn S σ) (h : S ⊆ T) :
    SuppIn T σ :=
  fun a b hab => hσ a b (hab.imp (fun ha h' => ha (h h')) fun hb h' => hb (h h'))

theorem SuppIn.inter {S T : Set κ} {σ : Matrix κ κ ℂ} (hS : SuppIn S σ) (hT : SuppIn T σ) :
    SuppIn (S ∩ T) σ := by
  intro a b hab
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · refine hT a b ?_
      rcases hab with h | h
      · exact Or.inl fun h' => h ⟨ha, h'⟩
      · exact Or.inr fun h' => h ⟨hb, h'⟩
    · exact hS a b (Or.inr hb)
  · exact hS a b (Or.inl ha)

/-- **A basis permutation that fixes every point of the support leaves the matrix unchanged.** -/
theorem SuppIn.submatrix_perm_eq_self {S : Set κ} {σ : Matrix κ κ ℂ} (hσ : SuppIn S σ)
    {π : Equiv.Perm κ} (hπ : ∀ a ∈ S, π a = a) : σ.submatrix π.symm π.symm = σ := by
  have hπ' : ∀ a, a ∈ S ∨ π.symm a ∈ S → π.symm a = a := by
    intro a ha
    rcases ha with ha | ha
    · rw [Equiv.symm_apply_eq]; exact (hπ a ha).symm
    · have := hπ _ ha
      rw [Equiv.apply_symm_apply] at this
      exact this.symm
  ext a b
  simp only [submatrix_apply]
  by_cases ha : a ∈ S ∨ π.symm a ∈ S
  · by_cases hb : b ∈ S ∨ π.symm b ∈ S
    · rw [hπ' a ha, hπ' b hb]
    · push_neg at hb
      rw [hσ _ _ (Or.inr hb.2), hσ _ _ (Or.inr hb.1)]
  · push_neg at ha
    rw [hσ _ _ (Or.inl ha.2), hσ _ _ (Or.inl ha.1)]

/-- **Placing a matrix along two maps that agree on its support gives the same matrix.** -/
theorem embed_congr_of_suppIn {S : Set κ} {σ : Matrix κ κ ℂ} (hσ : SuppIn S σ) {e e' : κ → ι}
    (h : ∀ a ∈ S, e a = e' a) : embed e σ = embed e' σ := by
  ext i j
  simp only [embed]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases ha : a ∈ S
  · by_cases hb : b ∈ S
    · rw [h a ha, h b hb]
    · simp [hσ a b (Or.inr hb)]
  · simp [hσ a b (Or.inl ha)]

/-- **A Kraus map whose operators send the support `S` into `T` maps matrices supported in `S`
to matrices supported in `T`.** -/
theorem SuppIn.krausApply_of_op [DecidableEq κ] {R : Type*} [Fintype R] {K : KrausMap R κ κ}
    {S T : Set κ} (hK : ∀ r a b, a ∉ T → b ∈ S → K.op r a b = 0) {σ : Matrix κ κ ℂ}
    (hσ : SuppIn S σ) : SuppIn T (K σ) := by
  intro a b hab
  simp only [KrausMap.apply, Matrix.sum_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  refine Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun l _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : k ∈ S
  · by_cases hl : l ∈ S
    · rcases hab with ha | hb
      · simp [hK r a k ha hk]
      · simp [hK r b l hb hl]
    · simp [hσ k l (Or.inr hl)]
  · simp [hσ k l (Or.inl hk)]

end Embed

/-! ### The challenger's state in the pure game -/

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C : Challenger X Y Req Resp)

/-- The state of the challenger after the requests `rs`. -/
noncomputable abbrev stateAfter (H : X → Y) (c : C.Coins) (rs : List Req) : ChallengerState X Y Req Resp :=
  C.toPureEnv.oracleIn (H, c) rs

theorem stateAfter_base (H : X → Y) (c : C.Coins) (rs : List Req) :
    (C.stateAfter H c rs).base = H := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [stateAfter, Env.oracleIn_append_singleton, Env.update]
    split_ifs
    · exact ih
    · exact ih

theorem stateAfter_hist_length (H : X → Y) (c : C.Coins) (rs : List Req) :
    (C.stateAfter H c rs).hist.length = min rs.length C.Q := by
  induction rs using List.reverseRecOn with
  | nil => simp [stateAfter, Env.oracleIn_nil, Challenger.toPureEnv]
  | append_singleton rs r ih =>
    rw [stateAfter, Env.oracleIn_append_singleton, Env.update]
    split_ifs with h
    · have key : ∀ (st : ChallengerState X Y Req Resp) (i : Fin C.Q),
          (C.toPureEnv.respond (H, c) i r st).state.hist.length = st.hist.length + 1 :=
        fun st i => by simp [Challenger.toPureEnv]
      have := ih
      simp only [stateAfter] at this
      rw [key, this, List.length_append, List.length_singleton]
      omega
    · have := ih
      simp only [stateAfter] at this
      simp only [this, List.length_append, List.length_singleton]
      omega

theorem toPureEnv_respond_response (ω : (X → Y) × C.Coins) (i : Fin C.Q) (r : Req)
    (st : ChallengerState X Y Req Resp) :
    (C.toPureEnv.respond ω i r st).response =
      ((C.respond ω.2 st.hist r).run (st.base.reprogram st.ass)).response :=
  rfl

theorem toPureEnv_respond_state (ω : (X → Y) × C.Coins) (i : Fin C.Q) (r : Req)
    (st : ChallengerState X Y Req Resp) :
    (C.toPureEnv.respond ω i r st).state =
      ⟨st.base, st.hist ++ [⟨r, ((C.respond ω.2 st.hist r).run (st.base.reprogram st.ass)).response⟩],
        st.ass ++ ((C.respond ω.2 st.hist r).run (st.base.reprogram st.ass)).assignments⟩ :=
  rfl

/-- The program of request `r` after the requests `rs`. -/
noncomputable abbrev progAfter (H : X → Y) (c : C.Coins) (rs : List Req) (r : Req) :
    OracleProg X Y (Reply X Y Resp) :=
  C.respond c (C.stateAfter H c rs).hist r

/-- The oracle in force after the requests `rs`. -/
noncomputable abbrev oracleAfter (H : X → Y) (c : C.Coins) (rs : List Req) : X → Y :=
  H.reprogram (C.stateAfter H c rs).ass

end Challenger

/-! ### The challenger's registers in the composition -/

namespace KindAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (A : KindAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-- The `i`-th query pair of the challenger's program for request `r` after the requests `rs`,
with its answer from the oracle in force; `(x₀, 0)` after the last query and for requests numbered
`Q` or later. -/
noncomputable def ansEntry (H : X → Y) (c : C.Coins) (rs : List Req) (r : Req) (i : ℕ) : X × Y :=
  if rs.length < C.Q then
    if h : i < ((C.progAfter H c rs r).trace (C.oracleAfter H c rs)).length then
      (((C.progAfter H c rs r).trace (C.oracleAfter H c rs))[i],
        C.oracleAfter H c rs ((C.progAfter H c rs r).trace (C.oracleAfter H c rs))[i])
    else (x₀, 0)
  else (x₀, 0)

/-- The challenger's registers once the slots below `J` are done: the query pairs of each
logged request's program with their answers. -/
noncomputable def garFill (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) (J : ℕ) :
    Fin A.slots → Fin C.q → X × Y :=
  fun j i => if (j : ℕ) < J then
    match lg j with
    | none => (x₀, 0)
    | some r => ansEntry C H c (requestsBefore lg j) r i
    else (x₀, 0)

/-- The answers of a program's queries are a prefix of the answers in the registers. -/
theorem trace_prefix_ansOf (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) {J : ℕ}
    (j : Fin A.slots) (hj : (j : ℕ) < J) {r : Req} (hr : lg j = some r)
    (hQ : (requestsBefore lg j).length < C.Q) :
    ((C.progAfter H c (requestsBefore lg j) r).trace
        (C.oracleAfter H c (requestsBefore lg j))).map (C.oracleAfter H c (requestsBefore lg j)) <+:
      A.ansOf C ⟨lg, A.garFill C H c lg J, c⟩ j := by
  have hlen : ((C.progAfter H c (requestsBefore lg j) r).trace
      (C.oracleAfter H c (requestsBefore lg j))).length ≤ C.q := C.respond_queries _ _ _ _
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem (by simp [ansOf]; omega) fun i h1 h2 => ?_
  simp only [List.length_map] at h1
  simp only [ansOf, List.getElem_map, List.getElem_take, List.getElem_ofFn, garFill, hj,
    ite_true, hr, ansEntry, hQ, dif_pos h1]

/-- **The challenger's state read from the registers is its state in the pure game.** -/
theorem regState_eq (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) {J : ℕ} :
    ∀ j ≤ J, C.regState c lg (A.ansOf C ⟨lg, A.garFill C H c lg J, c⟩) j =
      ⟨(C.stateAfter H c (requestsBefore lg j)).hist,
        (C.stateAfter H c (requestsBefore lg j)).ass⟩
  | 0, _ => rfl
  | j + 1, hj => by
    have ih := regState_eq H c lg (J := J) j (by omega)
    rw [Challenger.regState_add_one]
    by_cases h : j < A.slots
    · rw [dif_pos h, requestsBefore_succ_of_lt lg h]
      rcases hr : lg ⟨j, h⟩ with _ | r
      · simp only [ih, Option.toList_none, List.append_nil]
      · simp only [ih, Option.toList_some]
        rw [Challenger.stateAfter_hist_length]
        simp only [Challenger.stateAfter]
        rw [Env.oracleIn_append_singleton, Env.update]
        by_cases hQ : (requestsBefore lg j).length < C.Q
        · rw [if_pos (by omega), dif_pos hQ]
          have hout : C.outWith c (C.stateAfter H c (requestsBefore lg j)).hist r
              (A.ansOf C ⟨lg, A.garFill C H c lg J, c⟩ ⟨j, h⟩) =
              (C.progAfter H c (requestsBefore lg j) r).run (C.oracleAfter H c (requestsBefore lg j)) := by
            rw [Challenger.outWith, Challenger.outWithOf, OracleProgAns.result_of_prefix _ _
              (A.trace_prefix_ansOf C H c lg ⟨j, h⟩ (by simp; omega) hr hQ)]
            rfl
          rw [hout]
          have hb := C.stateAfter_base H c (requestsBefore lg j)
          simp only [Challenger.stateAfter] at hb
          rw [Challenger.toPureEnv_respond_state]
          simp only [hb, Challenger.progAfter, Challenger.oracleAfter, Challenger.stateAfter]
        · rw [if_neg (by omega), dif_neg hQ]
    · rw [dif_neg h, requestsBefore, dif_neg h, List.append_nil, ih]

/-- The challenger's state read from the registers at slot `j` depends only on the logs and the
answers of the slots below `j`. -/
theorem _root_.GordieHowe.Quantum.Challenger.regState_congr {m : ℕ} (ω : C.Coins) (lg : LogReg Req m)
    {ans ans' : Fin m → List Y} :
    ∀ {j : ℕ}, (∀ k : Fin m, (k : ℕ) < j → ans k = ans' k) →
      C.regState ω lg ans j = C.regState ω lg ans' j
  | 0, _ => rfl
  | j + 1, h => by
    rw [Challenger.regState_add_one, Challenger.regState_add_one,
      Challenger.regState_congr ω lg fun k hk => h k (by omega)]
    by_cases hj : j < m
    · simp only [dif_pos hj, h ⟨j, hj⟩ (by simp)]
    · simp only [dif_neg hj]

/-- The challenger's registers during slot `J`: the slots below `J` done, the first `I` queries
of slot `J` done. -/
noncomputable def garPart (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) (J I : ℕ) :
    Fin A.slots → Fin C.q → X × Y :=
  fun j i => if (j : ℕ) < J ∨ ((j : ℕ) = J ∧ (i : ℕ) < I) then
    match lg j with
    | none => (x₀, 0)
    | some r => ansEntry C H c (requestsBefore lg j) r i
    else (x₀, 0)

theorem garPart_zero (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) (J : ℕ) :
    A.garPart C H c lg J 0 = A.garFill C H c lg J := by
  funext j i
  simp [garPart, garFill]

theorem garPart_q (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) (J : ℕ) :
    A.garPart C H c lg J C.q = A.garFill C H c lg (J + 1) := by
  funext j i
  simp only [garPart, garFill]
  congr 1
  apply propext
  have := i.2
  omega

theorem stateAt_garPart (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) {J : ℕ} (I : ℕ)
    {j : ℕ} (hj : j ≤ J) :
    A.stateAt C ⟨lg, A.garPart C H c lg J I, c⟩ j =
      ⟨(C.stateAfter H c (requestsBefore lg j)).hist,
        (C.stateAfter H c (requestsBefore lg j)).ass⟩ := by
  rw [stateAt, Challenger.regState_congr (ans' := A.ansOf C ⟨lg, A.garFill C H c lg J, c⟩)]
  · exact A.regState_eq C H c lg j hj
  · intro k hk
    simp only [ansOf, garPart, garFill]
    congr 1
    funext i
    simp [show (k : ℕ) < J by omega]

/-! ### The composed registers as a placement of the game registers -/

/-- **The game registers placed in the composed registers** once the slots below `J` are done:
the adversary's registers and the logs as they are, the challenger's registers holding the query
pairs and answers of the logged requests below `J` (`garFill`), its coins `c`, and a clean query
register. -/
noncomputable def emb (H : X → Y) (c : C.Coins) (J : ℕ) (r : A.G) : QueryReg (A.CW C) 1 X Y :=
  A.advSplit C ((splitLogs r).1, (⟨(splitLogs r).2, A.garFill C H c (splitLogs r).2 J, c⟩,
    fun _ => (x₀, 0)))

theorem emb_injective (H : X → Y) (c : C.Coins) (J : ℕ) : Function.Injective (A.emb C H c J) := by
  intro r r' h
  apply splitLogs.injective
  have h1 := congrArg (fun q => q.1.adv) h
  have h2 := congrArg (fun q => q.1.chal.logs) h
  exact Prod.ext h1 h2

/-- The adversary's Kraus map commutes with the placement. -/
theorem advKraus_apply_embed (H : X → Y) (c : C.Coins) (J : ℕ) (k : StepIdx A.slots A.post)
    (σ : Matrix A.G A.G ℂ) :
    (A.advKraus C k) (embed (A.emb C H c J) σ) = embed (A.emb C H c J) ((A.liftG k) σ) := by
  have he : A.emb C H c J = A.advSplit C ∘ Prod.map _root_.id
      (fun lg => (⟨lg, A.garFill C H c lg J, c⟩, fun _ => (x₀, 0))) ∘ splitLogs := rfl
  rw [advKraus, KrausMap.reindex_apply, he, submatrix_embed_equiv, liftG, KrausMap.reindex_apply]
  simp only [← Function.comp_assoc, Equiv.symm_comp_self, Function.id_comp]
  rw [embed_comp_equiv, KrausMap.tensorId_apply_embed, submatrix_embed_equiv, embed_comp_equiv]
  simp [submatrix_submatrix]

/-- The game registers placed in the composed registers during slot `J`, after the first `I`
classical queries of the challenger in slot `J` (`garPart`). -/
noncomputable def embPart (H : X → Y) (c : C.Coins) (J I : ℕ) (r : A.G) :
    QueryReg (A.CW C) 1 X Y :=
  A.advSplit C ((splitLogs r).1, (⟨(splitLogs r).2, A.garPart C H c (splitLogs r).2 J I, c⟩,
    fun _ => (x₀, 0)))

theorem embPart_zero (H : X → Y) (c : C.Coins) (J : ℕ) : A.embPart C H c J 0 = A.emb C H c J := by
  funext r
  simp [embPart, emb, garPart_zero]

theorem embPart_q (H : X → Y) (c : C.Coins) (J : ℕ) :
    A.embPart C H c J C.q = A.emb C H c (J + 1) := by
  funext r
  simp [embPart, emb, garPart_q]

/-- The answers in the challenger's registers of slot `j` during its first `i` queries: those of
the program's queries made so far, then zeros. -/
theorem take_ansOf_garPart (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) (j : Fin A.slots)
    {r : Req} (hr : lg j = some r) (hQ : (requestsBefore lg j).length < C.Q) {i : ℕ}
    (hi : i ≤ C.q) :
    (A.ansOf C ⟨lg, A.garPart C H c lg j i, c⟩ j).take i =
      (((C.progAfter H c (requestsBefore lg j) r).trace (C.oracleAfter H c (requestsBefore lg j))).map
        (C.oracleAfter H c (requestsBefore lg j))).take i ++
      List.replicate (i - ((C.progAfter H c (requestsBefore lg j) r).trace
        (C.oracleAfter H c (requestsBefore lg j))).length) 0 := by
  set tr := (C.progAfter H c (requestsBefore lg j) r).trace (C.oracleAfter H c (requestsBefore lg j))
  refine List.ext_getElem (by simp [ansOf]; omega) fun k h1 h2 => ?_
  simp only [List.length_take, ansOf, List.length_ofFn] at h1
  simp only [ansOf, List.getElem_take, List.getElem_ofFn, garPart, lt_irrefl, false_or, true_and,
    show k < i by omega, if_true, hr]
  by_cases hk : k < tr.length
  · rw [List.getElem_append_left (by simp; omega)]
    simp [ansEntry, hQ, hk, tr]
  · rw [List.getElem_append_right (by simp; omega)]
    simp [ansEntry, hQ, hk, tr]

/-- The input of the challenger's query `i` of slot `j`, read from the registers during slot `j`,
is the `i`-th query pair's input. -/
theorem chalInput_garPart (H : X → Y) (c : C.Coins) (d : DReg A.W A.width X Y Req Resp)
    (lg : LogReg Req A.slots) (j : Fin A.slots) (i : Fin C.q) {r : Req} (hr : lg j = some r) :
    A.chalInput C j i ⟨lg, A.garPart C H c lg j i, c⟩ =
      (ansEntry C H c (requestsBefore lg j) r i).1 := by
  have hst := A.stateAt_garPart C H c lg (J := j) i (le_refl (j : ℕ))
  have hlen := C.stateAfter_hist_length H c (requestsBefore lg j)
  simp only [chalInput, hr]
  rw [hst]
  simp only [hlen]
  by_cases hQ : (requestsBefore lg j).length < C.Q
  · rw [if_pos (by omega), A.take_ansOf_garPart C H c lg j hr hQ i.2.le]
    simp only [ansEntry, if_pos hQ]
    by_cases hi : (i : ℕ) < ((C.progAfter H c (requestsBefore lg j) r).trace
        (C.oracleAfter H c (requestsBefore lg j))).length
    · rw [dif_pos hi, show (i : ℕ) - _ = 0 by omega, List.replicate_zero, List.append_nil]
      exact OracleProgAns.next_take _ _ _ _ hi
    · rw [dif_neg hi, List.take_of_length_le (by simp; omega)]
      exact OracleProgAns.next_trace_append _ _ _ _
  · rw [if_neg (by omega)]
    simp [ansEntry, hQ]

/-- The answer of the challenger's query `i` of slot `j` from the reprogrammed query is the
`i`-th answer. -/
theorem chalAss_garPart (H : X → Y) (c : C.Coins) (d : DReg A.W A.width X Y Req Resp)
    (lg : LogReg Req A.slots) (j : Fin A.slots) (i : Fin C.q) {r : Req} (hr : lg j = some r) :
    H.reprogram (A.chalAss C j i ⟨lg, A.garPart C H c lg j i, c⟩)
        (ansEntry C H c (requestsBefore lg j) r i).1 =
      (ansEntry C H c (requestsBefore lg j) r i).2 := by
  have hst := A.stateAt_garPart C H c lg (J := j) i (le_refl (j : ℕ))
  have hlen := C.stateAfter_hist_length H c (requestsBefore lg j)
  simp only [chalAss, hr]
  rw [hst]
  simp only [hlen]
  by_cases hQ : (requestsBefore lg j).length < C.Q
  · rw [A.take_ansOf_garPart C H c lg j hr hQ i.2.le]
    simp only [ansEntry, if_pos hQ]
    by_cases hi : (i : ℕ) < ((C.progAfter H c (requestsBefore lg j) r).trace
        (C.oracleAfter H c (requestsBefore lg j))).length
    · rw [dif_pos hi, show (i : ℕ) - _ = 0 by omega, List.replicate_zero, List.append_nil,
        if_pos ⟨by omega, OracleProgAns.wants_take _ _ _ hi⟩]
    · rw [dif_neg hi, List.take_of_length_le (by simp; omega),
        if_neg fun h => by simp [OracleProgAns.wants_trace_append] at h, reprogram_paddingAssignments]
      rfl
  · rw [if_neg fun h => by omega]
    simp [ansEntry, hQ, reprogram_paddingAssignments]

/-- The challenger's query `i` of slot `j` as one basis permutation: prepare the input, the
reprogrammed query, move the pair into the challenger's register. -/
noncomputable def chalStepPerm (H : X → Y) (j : Fin A.slots) (i : Fin C.q) :
    Equiv.Perm (QueryReg (A.CW C) 1 X Y) :=
  (A.prepChal C j i).trans ((queryPermOf (n := 1) fun s => H.reprogram (A.chalAss C j i s.chal)).trans
    (A.garSwap C j i))

theorem garPart_self (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) (j : Fin A.slots)
    (i : Fin C.q) : A.garPart C H c lg j i j i = (x₀, 0) := by
  simp [garPart]

/-- **One classical query of the challenger** fills the next entry of its register. -/
theorem chalStepPerm_embPart (H : X → Y) (c : C.Coins) (j : Fin A.slots) (i : Fin C.q) (r : A.G) :
    A.chalStepPerm C H j i (A.embPart C H c j i r) = A.embPart C H c j (i + 1) r := by
  simp only [embPart]
  generalize splitLogs r = dl
  obtain ⟨d, lg⟩ := dl
  simp only [chalStepPerm, Equiv.trans_apply, advSplit, Equiv.coe_fn_mk, prepChal,
    Function.Involutive.toPerm, garSwap, pairSwap, queryPermOf_apply, Equiv.swap_apply_left,
    zero_add, garPart_self]
  have hentry : (A.chalInput C j i ⟨lg, A.garPart C H c lg j i, c⟩,
      H.reprogram (A.chalAss C j i ⟨lg, A.garPart C H c lg j i, c⟩)
        (A.chalInput C j i ⟨lg, A.garPart C H c lg j i, c⟩)) =
      A.garPart C H c lg j (i + 1) j i := by
    rcases hr : lg j with _ | r
    · simp [chalInput, chalAss, hr, garPart, reprogram_paddingAssignments]
    · rw [A.chalInput_garPart C H c d lg j i hr, A.chalAss_garPart C H c d lg j i hr]
      simp [garPart, hr]
  rw [hentry]
  have hg : Function.update (A.garPart C H c lg j i) j
      (Function.update (A.garPart C H c lg j i j) i (A.garPart C H c lg j (i + 1) j i)) =
      A.garPart C H c lg j (i + 1) := by
    funext j' i'
    by_cases hj : j' = j
    · subst hj
      by_cases hi : i' = i
      · subst hi
        simp
      · rw [Function.update_self, Function.update_of_ne hi]
        simp only [garPart, lt_irrefl, false_or, true_and]
        have : ((i' : ℕ) < i ↔ (i' : ℕ) < i + 1) := by
          have : (i' : ℕ) ≠ i := fun h => hi (Fin.ext h)
          omega
        simp only [this]
    · rw [Function.update_of_ne hj]
      simp only [garPart]
      have : (j' : ℕ) ≠ j := fun h => hj (Fin.ext h)
      simp [this]
  rw [hg]

theorem run_chalSub (H : X → Y) (j : Fin A.slots) (i : Fin C.q)
    (ρ : Matrix (QueryReg (A.CW C) 1 X Y) (QueryReg (A.CW C) 1 X Y) ℂ) :
    (ReprogrammedCircuit.kraus (KrausMap.ofPerm (A.prepChal C j i))
      (.rquery (fun v => A.chalAss C j i v.chal) (.kraus (KrausMap.ofPerm (A.garSwap C j i)) .nil))).run H ρ =
      ρ.submatrix (A.chalStepPerm C H j i).symm (A.chalStepPerm C H j i).symm := by
  simp only [ReprogrammedCircuit.run, KrausMap.ofPerm_apply, submatrix_perm_submatrix_perm]
  rfl

/-- **The challenger's queries of slot `j`** fill its registers for slot `j`. -/
theorem run_chalQueries (H : X → Y) (c : C.Coins) (j : Fin A.slots) (σ : Matrix A.G A.G ℂ) :
    (A.chalQueries C j).run H (embed (A.emb C H c j) σ) = embed (A.emb C H c (j + 1)) σ := by
  have key : ∀ (l : List (Fin C.q)) (i₀ : ℕ), l.map Fin.val = List.range' i₀ l.length →
      (ReprogrammedCircuit.concat (l.map fun i => ReprogrammedCircuit.kraus (KrausMap.ofPerm (A.prepChal C j i))
        (.rquery (fun v => A.chalAss C j i v.chal) (.kraus (KrausMap.ofPerm (A.garSwap C j i)) .nil)))).run H
          (embed (A.embPart C H c j i₀) σ) = embed (A.embPart C H c j (i₀ + l.length)) σ := by
    intro l
    induction l with
    | nil => intro i₀ _; rfl
    | cons i l ih =>
      intro i₀ hl
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
      rw [ReprogrammedCircuit.concat, ReprogrammedCircuit.run_append, run_chalSub, ← hl.1,
        submatrix_embed_of_forall (A.chalStepPerm_embPart C H c j i) σ, ih (i + 1) (by rw [hl.2, hl.1])]
      congr 2
      omega
  rw [← embPart_zero, chalQueries, key _ 0 (by rw [List.map_coe_finRange_eq_range,
    List.range_eq_range', List.length_finRange]), List.length_finRange, Nat.zero_add, embPart_q]

/-! #### The reply and the adversary's queries -/

/-- The request outcome of a game basis state: the request if `kind = true`. -/
def reqOutG (r : A.G) : Option Req :=
  if A.kind r.1.1 then some r.1.2.1 else none

/-- The game basis states just after the copy of slot `j`: the later logs blank, log `j` the
request outcome. -/
def TSet (j : Fin A.slots) : Set A.G :=
  {r | (∀ k : Fin A.slots, (j : ℕ) < k → (splitLogs r).2 k = none) ∧
    (splitLogs r).2 j = A.reqOutG r}

/-- **The reply read from the registers is the reply of the pure game.** -/
theorem reply_emb (H : X → Y) (c : C.Coins) (lg : LogReg Req A.slots) (j : Fin A.slots) :
    A.reply C j ⟨lg, A.garFill C H c lg (j + 1), c⟩ = C.toPureEnv.answer (H, c) lg j := by
  have hst := A.regState_eq C H c lg (J := j + 1) j (by omega)
  have hlen := C.stateAfter_hist_length H c (requestsBefore lg j)
  simp only [reply, Env.answer, Env.answerAfter]
  rcases hr : lg j with _ | r
  · rfl
  · simp only [Option.elim]
    rw [show A.stateAt C ⟨lg, A.garFill C H c lg (j + 1), c⟩ j = _ from hst]
    simp only [hlen]
    by_cases hQ : (requestsBefore lg j).length < C.Q
    · rw [if_pos (by omega), Env.answerAfter, dif_pos hQ, Challenger.outWith, Challenger.outWithOf,
        OracleProgAns.result_of_prefix _ _
        (A.trace_prefix_ansOf C H c lg j (by omega) hr hQ)]
      have hb := C.stateAfter_base H c (requestsBefore lg j)
      simp only [Challenger.stateAfter] at hb
      rw [Challenger.toPureEnv_respond_response, hb]
      rfl
    · rw [if_neg (by omega), Env.answerAfter, dif_neg hQ]

theorem writeReply_emb (H : X → Y) (c : C.Coins) (j : Fin A.slots) {r : A.G}
    (hr : r ∈ A.TSet j) :
    A.writeReply C j (A.emb C H c (j + 1) r) =
      A.emb C H c (j + 1) (A.respG C.toPureEnv (H, c) j r) := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  simp only [TSet, Set.mem_setOf_eq, splitLogs, Equiv.coe_fn_mk, reqOutG] at hr
  simp only [writeReply, Function.Involutive.toPerm, Equiv.coe_fn_mk, emb, advSplit, splitLogs,
    respG, Equiv.prodCongr_apply, Prod.map, respondPerm_apply, Equiv.refl_apply]
  by_cases hk : A.kind w
  · simp only [hk, if_true] at hr ⊢
    rw [hr.2]
    simp only [Option.isSome_some, if_true]
    rw [A.reply_emb C H c lg j]
  · simp only [hk, Bool.false_eq_true, if_false] at hr ⊢
    rw [hr.2]
    simp

/-- The query to `f w` on the query pairs with index below `k`. -/
def _root_.GordieHowe.Quantum.partialQueryPermOf {W : Type*} {n : ℕ} (f : W → X → Y) (k : ℕ) :
    Equiv.Perm (QueryReg W n X Y) :=
  Equiv.prodShear (Equiv.refl W) fun w => Equiv.piCongrRight fun i =>
    if (i : ℕ) < k then Equiv.prodShear (Equiv.refl X) fun x => Equiv.addRight (f w x)
    else Equiv.refl _

theorem _root_.GordieHowe.Quantum.partialQueryPermOf_apply {W : Type*} {n : ℕ} (f : W → X → Y) (k : ℕ)
    (r : QueryReg W n X Y) :
    partialQueryPermOf f k r =
      (r.1, fun i : Fin n => if (i : ℕ) < k then ((r.2 i).1, (r.2 i).2 + f r.1 (r.2 i).1)
        else r.2 i) := by
  refine Prod.ext rfl (funext fun i => ?_)
  by_cases h : (i : ℕ) < k <;> simp [partialQueryPermOf, h]

theorem _root_.GordieHowe.Quantum.partialQueryPermOf_zero {W : Type*} {n : ℕ} (f : W → X → Y) :
    partialQueryPermOf (n := n) f 0 = Equiv.refl _ :=
  Equiv.ext fun r => by simp [partialQueryPermOf_apply]

theorem _root_.GordieHowe.Quantum.partialQueryPermOf_self {W : Type*} {n : ℕ} (f : W → X → Y) :
    partialQueryPermOf (n := n) f n = queryPermOf f :=
  Equiv.ext fun r => by simp [partialQueryPermOf_apply]

/-- The adversary's query `k` as one basis permutation: exchange pair `k` into the query
register, the reprogrammed query, exchange it back. -/
def advStepPerm (H : X → Y) (ass : A.CW C → List (Assignment X Y)) (k : Fin A.width) :
    Equiv.Perm (QueryReg (A.CW C) 1 X Y) :=
  (A.advSwap C k).trans ((queryPermOf (n := 1) fun s => H.reprogram (ass s)).trans (A.advSwap C k))

theorem run_advSub (H : X → Y) (ass : A.CW C → List (Assignment X Y)) (k : Fin A.width)
    (ρ : Matrix (QueryReg (A.CW C) 1 X Y) (QueryReg (A.CW C) 1 X Y) ℂ) :
    (ReprogrammedCircuit.kraus (KrausMap.ofPerm (A.advSwap C k)) (.rquery ass
      (.kraus (KrausMap.ofPerm (A.advSwap C k)) .nil))).run H ρ =
      ρ.submatrix (A.advStepPerm C H ass k).symm (A.advStepPerm C H ass k).symm := by
  simp only [ReprogrammedCircuit.run, KrausMap.ofPerm_apply, submatrix_perm_submatrix_perm]
  rfl

/-- **The adversary's query `k`**, when the reprogrammed query reads the function `F w` of the
workspace and logs: it queries pair `k`. -/
theorem advStepPerm_emb (H : X → Y) (c : C.Coins) (J : ℕ) (ass : A.CW C → List (Assignment X Y))
    (F : (A.W × Req × Option Resp × LogReg Req A.slots) → X → Y) (r : A.G)
    (hF : ∀ d : DReg A.W A.width X Y Req Resp,
      H.reprogram (ass ⟨d, ⟨(splitLogs r).2, A.garFill C H c (splitLogs r).2 J, c⟩⟩) = F r.1)
    (k : Fin A.width) :
    A.advStepPerm C H ass k (A.emb C H c J (partialQueryPermOf F k r)) =
      A.emb C H c J (partialQueryPermOf F (k + 1) r) := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  simp only [splitLogs, Equiv.coe_fn_mk] at hF
  simp only [advStepPerm, Equiv.trans_apply, emb, advSplit, splitLogs, Equiv.coe_fn_mk,
    partialQueryPermOf_apply, advSwap, pairSwap, Function.Involutive.toPerm, queryPermOf_apply,
    hF, lt_irrefl, if_false, Function.update_self, Function.update_idem]
  refine Prod.ext (CWork.ext (Prod.ext rfl (funext fun i => ?_)) rfl) rfl
  dsimp only
  by_cases hi : i = k
  · subst hi
    simp
  · rw [Function.update_of_ne hi]
    have : ((i : ℕ) < k ↔ (i : ℕ) < k + 1) := by
      have : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
      omega
    simp only [this]

/-- **The adversary's queries of a slot**, when the reprogrammed queries read `F w` on the support:
the parallel query to `F` on all pairs (the serialization, HHM22 p. 16). -/
theorem run_advQueries (H : X → Y) (c : C.Coins) (J : ℕ) (ass : A.CW C → List (Assignment X Y))
    (F : (A.W × Req × Option Resp × LogReg Req A.slots) → X → Y) {S : Set A.G}
    (hF : ∀ r ∈ S, ∀ d : DReg A.W A.width X Y Req Resp,
      H.reprogram (ass ⟨d, ⟨(splitLogs r).2, A.garFill C H c (splitLogs r).2 J, c⟩⟩) = F r.1)
    {σ : Matrix A.G A.G ℂ} (hσ : SuppIn S σ) :
    (A.advQueries C ass).run H (embed (A.emb C H c J) σ) =
      embed (A.emb C H c J) (σ.submatrix (queryPermOf F).symm (queryPermOf F).symm) := by
  have key : ∀ (l : List (Fin A.width)) (k₀ : ℕ), l.map Fin.val = List.range' k₀ l.length →
      (ReprogrammedCircuit.concat (l.map fun k => ReprogrammedCircuit.kraus (KrausMap.ofPerm (A.advSwap C k))
        (.rquery ass (.kraus (KrausMap.ofPerm (A.advSwap C k)) .nil)))).run H
          (embed (A.emb C H c J ∘ partialQueryPermOf F k₀) σ) =
        embed (A.emb C H c J ∘ partialQueryPermOf F (k₀ + l.length)) σ := by
    intro l
    induction l with
    | nil => intro k₀ _; rfl
    | cons k l ih =>
      intro k₀ hl
      simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
      rw [ReprogrammedCircuit.concat, ReprogrammedCircuit.run_append, run_advSub, ← hl.1,
        submatrix_embed_of_mem (e := A.emb C H c J ∘ partialQueryPermOf F k)
          (e' := A.emb C H c J ∘ partialQueryPermOf F (k + 1))
          (fun r hr => A.advStepPerm_emb C H c J ass F r (hF r hr) k) hσ,
        ih (k + 1) (by rw [hl.2, hl.1]), show (k : ℕ) + 1 + l.length = k + (l.length + 1) by omega]
  have h0 := key (List.finRange A.width) 0 (by rw [List.map_coe_finRange_eq_range,
    List.range_eq_range', List.length_finRange])
  rw [List.length_finRange, Nat.zero_add, partialQueryPermOf_self, partialQueryPermOf_zero] at h0
  rw [advQueries, show A.emb C H c J = A.emb C H c J ∘ Equiv.refl _ from rfl, h0, embed_comp_equiv]
  rfl

/-! #### One slot -/

/-- The game basis states whose logs from slot `j` on are blank. -/
def blankFrom (j : ℕ) : Set A.G :=
  (fun r => (splitLogs r).2) ⁻¹' {lg | ∀ k : Fin A.slots, j ≤ k → lg k = none}

theorem SuppIn.liftG {j : ℕ} {σ : Matrix A.G A.G ℂ} (hσ : SuppIn (A.blankFrom j) σ)
    (k : StepIdx A.slots A.post) : SuppIn (A.blankFrom j) ((A.liftG k) σ) :=
  SuppIn.krausApply_of_blockDiag (A.blockDiag_liftG k _root_.id) hσ

theorem copyG_copyG (j : Fin A.slots) (r : A.G) : A.copyG j (A.copyG j r) = r := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  by_cases h : A.kind w <;> simp [copyG, copyPerm_apply, h]

theorem copyG_symm (j : Fin A.slots) : (A.copyG j).symm = A.copyG j :=
  Equiv.ext fun r => by rw [Equiv.symm_apply_eq, A.copyG_copyG]

theorem logAt_copyG_of_blank (j : Fin A.slots) {r : A.G} (hr : (splitLogs r).2 j = none) :
    A.logAt j (A.copyG j r) = A.reqOutG r := by
  by_cases h : A.kind r.1.1 <;>
    simp_all [logAt, copyG, copyPerm_apply, reqOutG, splitLogs]

theorem copyG_mem_TSet (j : Fin A.slots) {r : A.G} (hr : r ∈ A.blankFrom j) :
    A.copyG j r ∈ A.TSet j := by
  simp only [blankFrom, Set.mem_preimage, Set.mem_setOf_eq] at hr
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [A.logs_copyG j r k (fun e => by subst e; omega)]
    exact hr k (by omega)
  · have := A.logAt_copyG_of_blank j (hr j le_rfl)
    rw [logAt] at this
    rw [this]
    by_cases h : A.kind r.1.1 <;> simp [reqOutG, copyG, copyPerm_apply, h]

/-- **The measurement of the request before the copy is the measurement of the log after it**,
on states whose log `j` is blank. -/
theorem copy_measure (j : Fin A.slots) {σ : Matrix A.G A.G ℂ} (hσ : SuppIn (A.blankFrom j) σ) :
    dephase (A.logAt j) (σ.submatrix (A.copyG j).symm (A.copyG j).symm) =
      (dephase (A.reqOutG) σ).submatrix (A.copyG j).symm (A.copyG j).symm := by
  ext a b
  simp only [dephase, submatrix_apply, copyG_symm]
  by_cases hab : A.copyG j a ∈ A.blankFrom j ∧ A.copyG j b ∈ A.blankFrom j
  · have ha : A.logAt j a = A.reqOutG (A.copyG j a) := by
      conv_lhs => rw [← A.copyG_copyG j a]
      exact A.logAt_copyG_of_blank j (hab.1 j le_rfl)
    have hb : A.logAt j b = A.reqOutG (A.copyG j b) := by
      conv_lhs => rw [← A.copyG_copyG j b]
      exact A.logAt_copyG_of_blank j (hab.2 j le_rfl)
    rw [ha, hb]
  · rw [hσ _ _ (by tauto)]
    simp

theorem garFill_congr (H : X → Y) (c : C.Coins) {lg lg' : LogReg Req A.slots} {J : ℕ}
    (h : ∀ k : Fin A.slots, (k : ℕ) < J → lg k = lg' k) :
    A.garFill C H c lg J = A.garFill C H c lg' J := by
  funext k i
  simp only [garFill]
  split_ifs with hk
  · rw [h k hk, requestsBefore_congr fun k' hk' => h k' (by omega)]
  · rfl

theorem copyReq_emb (H : X → Y) (c : C.Coins) (j : Fin A.slots) (r : A.G) :
    A.copyReq C j (A.emb C H c j r) = A.emb C H c j (A.copyG j r) := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  by_cases h : A.kind w
  · simp only [copyReq, Function.Involutive.toPerm, Equiv.coe_fn_mk, emb, advSplit, splitLogs,
      copyG, Equiv.prodCongr_apply, Prod.map, copyPerm_apply, h, if_true, Equiv.refl_apply,
      ChallengerRegs.swapLog, DReg.request, DReg.workspace]
    rw [A.garFill_congr C H c (lg' := Function.update lg j (Equiv.swap none (some req) (lg j)))
      fun k hk => by rw [Function.update_of_ne (fun e => by subst e; omega)]]
  · simp [copyReq, Function.Involutive.toPerm, emb, advSplit, splitLogs, copyG, copyPerm_apply, h]

theorem reqOutcome_emb (H : X → Y) (c : C.Coins) (J : ℕ) :
    A.reqOutcome C ∘ A.emb C H c J = A.reqOutG :=
  rfl

theorem respG_mem_TSet (j : Fin A.slots) (ω : (X → Y) × C.Coins) {r : A.G} (hr : r ∈ A.TSet j) :
    A.respG C.toPureEnv ω j r ∈ A.TSet j := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  by_cases h : A.kind w <;>
    simpa [TSet, respG, respondPerm_apply, h, splitLogs, reqOutG] using hr

theorem oraclePerm_mem_TSet (j : Fin A.slots) (ω : (X → Y) × C.Coins) {r : A.G}
    (hr : r ∈ A.TSet j) : C.toPureEnv.oraclePerm A.kind ω r ∈ A.TSet j := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  simpa [TSet, Env.oraclePerm, queryPermOf_apply, splitLogs, reqOutG] using hr

theorem TSet_subset (j : Fin A.slots) : A.TSet j ⊆ A.blankFrom (j + 1) :=
  fun r hr k hk => hr.1 k (by omega)

/-- The adversary's queries of slot `j` read, on the states after the copy, the oracle in force
on branches without a request and the padding on branches with one. -/
theorem advAss_eq (H : X → Y) (c : C.Coins) (j : Fin A.slots) {r : A.G} (hr : r ∈ A.TSet j) :
    H.reprogram (A.advAss C j ⟨(splitLogs r).2, A.garFill C H c (splitLogs r).2 (j + 1), c⟩) =
      (fun s : A.W × Req × Option Resp × LogReg Req A.slots =>
        if A.kind s.1 then 0 else C.toPureEnv.oracle (H, c) s.2.2.2) r.1 := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  simp only [TSet, Set.mem_setOf_eq, splitLogs, Equiv.coe_fn_mk, reqOutG] at hr
  simp only [advAss, splitLogs, Equiv.coe_fn_mk]
  by_cases h : A.kind w
  · simp only [h, if_true] at hr ⊢
    rw [hr.2, reprogram_paddingAssignments]
  · simp only [h, Bool.false_eq_true, if_false] at hr ⊢
    rw [hr.2]
    have hst := A.regState_eq C H c lg (J := j + 1) (j + 1) le_rfl
    simp only [stateAt]
    rw [hst, Env.oracle, requests_eq_requestsBefore (k := j + 1)
      (fun k hk => hr.1 k (by omega))]
    have hb := C.stateAfter_base H c (requestsBefore lg (j + 1))
    simp only [Challenger.stateAfter] at hb
    simp only [Challenger.stateAfter, OracleState.toOracle, hb]

/-- Before the reply of slot `j`, the challenger's registers of slot `j` are clean on the branches
without a request: placing the game registers for the slots below `j` or below `j + 1` agrees. -/
theorem emb_succ_of_log_none (H : X → Y) (c : C.Coins) (j : Fin A.slots) {r : A.G}
    (hr : (splitLogs r).2 j = none) : A.emb C H c j r = A.emb C H c (j + 1) r := by
  have hg : A.garFill C H c (splitLogs r).2 j = A.garFill C H c (splitLogs r).2 (j + 1) := by
    funext k i
    simp only [garFill]
    by_cases hk : k = j
    · subst hk
      simp [hr]
    · have : ((k : ℕ) < j ↔ (k : ℕ) < j + 1) := by
        have : (k : ℕ) ≠ j := fun h => hk (Fin.ext h)
        omega
      simp only [this]
  simp only [emb, hg]

/-- The query to the oracle in force on the branches without a request does nothing on the
branches with one. -/
theorem oraclePerm_of_kind (ω : (X → Y) × C.Coins) {r : A.G} (hr : A.kind r.1.1 = true) :
    C.toPureEnv.oraclePerm A.kind ω r = r := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  simp only at hr
  simp [Env.oraclePerm, queryPermOf_apply, hr]

theorem copyG_workspace (j : Fin A.slots) (r : A.G) : (A.copyG j r).1.1 = r.1.1 := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  by_cases h : A.kind w <;> simp [copyG, copyPerm_apply, h]

theorem respG_workspace (ω : (X → Y) × C.Coins) (j : Fin A.slots) (r : A.G) :
    (A.respG C.toPureEnv ω j r).1.1 = r.1.1 := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  by_cases h : A.kind w <;> simp [respG, respondPerm_apply, h]

theorem oraclePerm_workspace (ω : (X → Y) × C.Coins) (r : A.G) :
    (C.toPureEnv.oraclePerm A.kind ω r).1.1 = r.1.1 := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  simp [Env.oraclePerm, queryPermOf_apply]

/-- **One slot of the composition is one slot of the mixed game with the measured request**,
placed in the composed registers, when the slot is scheduled as a request (`b = true`) or as a
query batch (`b = false`) and the kind after the adversary's Kraus map agrees with `b` on the
support. -/
theorem run_slotCirc (H : X → Y) (c : C.Coins) (b : Bool) (j : Fin A.slots)
    {σ : Matrix A.G A.G ℂ} (hσ : SuppIn (A.blankFrom j) σ)
    (hb : SuppIn {r | A.kind r.1.1 = b} ((A.liftG (slotStep j)) σ)) :
    (A.slotCirc C b j).run H (embed (A.emb C H c j) σ) =
      embed (A.emb C H c (j + 1)) ((Circuit.kraus (A.liftG (slotStep j))
        (A.eventCirc C.toPureEnv (H, c) j true)).run (Equiv.refl _) σ) := by
  have hσ1 := SuppIn.liftG A hσ ⟨j, by omega⟩
  set σ1 := (A.liftG (slotStep j)) σ
  have hσ2 : SuppIn (A.TSet j ∩ {r | A.kind r.1.1 = b})
      ((dephase A.reqOutG σ1).submatrix (A.copyG j).symm (A.copyG j).symm) :=
    ((hσ1.dephase _).submatrix_perm fun r hr => A.copyG_mem_TSet j hr).inter
      ((hb.dephase _).submatrix_perm fun r hr => by
        simp only [Set.mem_setOf_eq] at hr ⊢
        rw [A.copyG_workspace]; exact hr)
  set σ2 := (dephase A.reqOutG σ1).submatrix (A.copyG j).symm (A.copyG j).symm
  have hσ3 : SuppIn (A.TSet j ∩ {r | A.kind r.1.1 = b}) (σ2.submatrix
      (A.respG C.toPureEnv (H, c) j).symm (A.respG C.toPureEnv (H, c) j).symm) :=
    hσ2.submatrix_perm fun r hr => ⟨A.respG_mem_TSet C j (H, c) hr.1, by
      simp only [Set.mem_setOf_eq] at hr ⊢
      rw [A.respG_workspace]; exact hr.2⟩
  have hfront : (ReprogrammedCircuit.kraus (A.advKraus C (slotStep j)) (ReprogrammedCircuit.kraus (A.measReq C j) ReprogrammedCircuit.nil)).run
      H (embed (A.emb C H c j) σ) = embed (A.emb C H c j) σ2 := by
    simp only [ReprogrammedCircuit.run]
    rw [advKraus_apply_embed, measReq, KrausMap.comp_apply, KrausMap.measureFn_apply,
      dephase_embed, reqOutcome_emb, KrausMap.ofPerm_apply (A.copyReq C j),
      submatrix_embed (π' := A.copyG j) (S := Set.univ) (fun r _ => A.copyReq_emb C H c j r)
        (fun a b h => by simp at h)]
  have hgame : (Circuit.kraus (A.liftG (slotStep j))
      (A.eventCirc C.toPureEnv (H, c) j true)).run (Equiv.refl _) σ =
      (σ2.submatrix (A.respG C.toPureEnv (H, c) j).symm (A.respG C.toPureEnv (H, c) j).symm).submatrix
        (C.toPureEnv.oraclePerm A.kind (H, c)).symm (C.toPureEnv.oraclePerm A.kind (H, c)).symm := by
    simp only [eventCirc, Circuit.run, ↓reduceIte, KrausMap.ofPerm_apply, KrausMap.measureFn_apply]
    rw [A.copy_measure j hσ1]
  rw [hgame]
  cases b with
  | true =>
    have hrun : (A.slotCirc C true j).run H (embed (A.emb C H c j) σ) =
        (ReprogrammedCircuit.kraus (KrausMap.ofPerm (A.writeReply C j)) ReprogrammedCircuit.nil).run H
          ((A.chalQueries C j).run H ((ReprogrammedCircuit.kraus (A.advKraus C (slotStep j))
            (ReprogrammedCircuit.kraus (A.measReq C j) ReprogrammedCircuit.nil)).run H (embed (A.emb C H c j) σ))) := by
      simp only [slotCirc, if_true, ReprogrammedCircuit.run, ReprogrammedCircuit.run_append]
    rw [hrun, hfront, run_chalQueries]
    simp only [ReprogrammedCircuit.run]
    rw [KrausMap.ofPerm_apply, submatrix_embed (π' := A.respG C.toPureEnv (H, c) j) (S := A.TSet j)
      (fun r hr => A.writeReply_emb C H c j hr) (hσ2.mono Set.inter_subset_left),
      hσ3.submatrix_perm_eq_self fun r hr => A.oraclePerm_of_kind C (H, c) hr.2]
  | false =>
    have hrun : (A.slotCirc C false j).run H (embed (A.emb C H c j) σ) =
        (ReprogrammedCircuit.kraus (KrausMap.ofPerm (A.writeReply C j)) (A.advQueries C fun v => A.advAss C j v.chal)).run H
          ((ReprogrammedCircuit.kraus (A.advKraus C (slotStep j))
            (ReprogrammedCircuit.kraus (A.measReq C j) ReprogrammedCircuit.nil)).run H (embed (A.emb C H c j) σ)) := by
      simp only [slotCirc, Bool.false_eq_true, if_false, ReprogrammedCircuit.run, ReprogrammedCircuit.run_append]
    have hnone : ∀ r ∈ A.TSet j ∩ {r | A.kind r.1.1 = false}, (splitLogs r).2 j = none :=
      fun r hr => by
        have hk : A.kind r.1.1 = false := hr.2
        rw [hr.1.2]
        simp [reqOutG, hk]
    rw [hrun, hfront, embed_congr_of_suppIn hσ2 fun r hr => A.emb_succ_of_log_none C H c j (hnone r hr)]
    simp only [ReprogrammedCircuit.run]
    rw [KrausMap.ofPerm_apply, submatrix_embed (π' := A.respG C.toPureEnv (H, c) j) (S := A.TSet j)
      (fun r hr => A.writeReply_emb C H c j hr) (hσ2.mono Set.inter_subset_left),
      A.run_advQueries C H c (j + 1) _
        (fun s => if A.kind s.1 then 0 else C.toPureEnv.oracle (H, c) s.2.2.2)
        (fun r hr _ => A.advAss_eq C H c j hr) (hσ3.mono Set.inter_subset_left)]
    rfl

theorem suppIn_slot (H : X → Y) (c : C.Coins) (j : Fin A.slots) {σ : Matrix A.G A.G ℂ}
    (hσ : SuppIn (A.blankFrom j) σ) :
    SuppIn (A.blankFrom (j + 1)) ((Circuit.kraus (A.liftG (slotStep j))
        (A.eventCirc C.toPureEnv (H, c) j true)).run (Equiv.refl _) σ) := by
  have hσ1 := SuppIn.liftG A hσ ⟨j, by omega⟩
  simp only [eventCirc, Circuit.run, ↓reduceIte, KrausMap.ofPerm_apply, KrausMap.measureFn_apply]
  rw [A.copy_measure j hσ1]
  refine (((hσ1.dephase _).submatrix_perm fun r hr => A.copyG_mem_TSet j hr).submatrix_perm
    fun r hr => A.respG_mem_TSet C j (H, c) hr).submatrix_perm fun r hr => ?_
  exact A.TSet_subset j (A.oraclePerm_mem_TSet C j (H, c) hr)

/-! #### The post phase and the whole run -/

theorem postAss_eq (H : X → Y) (c : C.Coins) (r : A.G) :
    H.reprogram (A.postAss C ⟨(splitLogs r).2, A.garFill C H c (splitLogs r).2 A.slots, c⟩) =
      (fun s : A.W × Req × Option Resp × LogReg Req A.slots =>
        C.toPureEnv.oracle (H, c) s.2.2.2) r.1 := by
  obtain ⟨⟨w, req, resp, lg⟩, prs⟩ := r
  simp only [postAss, splitLogs, Equiv.coe_fn_mk, stateAt]
  rw [A.regState_eq C H c lg (J := A.slots) A.slots le_rfl, Env.oracle, requests]
  have hb := C.stateAfter_base H c (requestsBefore lg A.slots)
  simp only [Challenger.stateAfter] at hb
  simp only [Challenger.stateAfter, OracleState.toOracle, hb]

theorem run_postCirc (H : X → Y) (c : C.Coins) (b : Fin A.post) (σ : Matrix A.G A.G ℂ) :
    (A.postCirc C b).run H (embed (A.emb C H c A.slots) σ) =
      embed (A.emb C H c A.slots) ((Circuit.kraus (A.liftG (postStep b))
        (.kraus (KrausMap.ofPerm (A.postG C.toPureEnv (H, c))) .nil)).run (Equiv.refl _) σ) := by
  simp only [postCirc, ReprogrammedCircuit.run]
  rw [advKraus_apply_embed, A.run_advQueries C H c A.slots _
    (fun s => C.toPureEnv.oracle (H, c) s.2.2.2) (S := Set.univ)
    (fun r _ _ => A.postAss_eq C H c r) (fun a b h => by simp at h)]
  simp only [Circuit.run, KrausMap.ofPerm_apply]
  rfl

/-- The slot `k` of the mixed game with measured requests, as a circuit on the game registers. -/
noncomputable abbrev gameSlot (H : X → Y) (c : C.Coins) (k : Fin A.slots) : Circuit A.G :=
  Circuit.kraus (A.liftG (slotStep k)) (A.eventCirc C.toPureEnv (H, c) k true)

/-- **A schedule respected along the run**: a family `Inv` of sets of game basis states such that,
from a state supported in `Inv k` with the logs from slot `k` on blank, the adversary's Kraus map
number `k` gives kind `sched k` on its support and the slot of the mixed game gives a state
supported in `Inv (k + 1)`. -/
structure Respects (sched : Fin A.slots → Bool) (Inv : ℕ → Set A.G) : Prop where
  kind : ∀ (k : Fin A.slots) {σ : Matrix A.G A.G ℂ}, SuppIn (A.blankFrom k ∩ Inv k) σ →
    SuppIn {r | A.kind r.1.1 = sched k} ((A.liftG (slotStep k)) σ)
  step : ∀ (H : X → Y) (c : C.Coins) (k : Fin A.slots) {σ : Matrix A.G A.G ℂ},
    SuppIn (A.blankFrom k ∩ Inv k) σ →
    SuppIn (Inv (k + 1)) ((A.gameSlot C H c k).run (Equiv.refl _) σ)

theorem run_slots {sched : Fin A.slots → Bool} {Inv : ℕ → Set A.G} (hInv : A.Respects C sched Inv)
    (H : X → Y) (c : C.Coins) (l : List (Fin A.slots)) (j : ℕ)
    (hl : l.map Fin.val = List.range' j l.length) {σ : Matrix A.G A.G ℂ}
    (hσ : SuppIn (A.blankFrom j ∩ Inv j) σ) :
    (ReprogrammedCircuit.concat (l.map fun k => A.slotCirc C (sched k) k)).run H (embed (A.emb C H c j) σ) =
      embed (A.emb C H c (j + l.length))
        ((Circuit.concat (l.map (A.gameSlot C H c))).run (Equiv.refl _) σ) ∧
    SuppIn (A.blankFrom (j + l.length) ∩ Inv (j + l.length))
        ((Circuit.concat (l.map (A.gameSlot C H c))).run (Equiv.refl _) σ) := by
  induction l generalizing j σ with
  | nil => exact ⟨rfl, hσ⟩
  | cons k l ih =>
    simp only [List.map_cons, List.length_cons, List.range'_succ, List.cons.injEq] at hl ⊢
    have hσ' : SuppIn (A.blankFrom k ∩ Inv k) σ := by rw [hl.1]; exact hσ
    have h1 := A.run_slotCirc C H c (sched k) k (hσ'.mono Set.inter_subset_left) (hInv.kind k hσ')
    have h2 : SuppIn (A.blankFrom (k + 1) ∩ Inv (k + 1))
        ((A.gameSlot C H c k).run (Equiv.refl _) σ) :=
      (A.suppIn_slot C H c k (hσ'.mono Set.inter_subset_left)).inter (hInv.step H c k hσ')
    obtain ⟨ih1, ih2⟩ := ih (↑k + 1) (by rw [hl.2, hl.1]) h2
    rw [ReprogrammedCircuit.concat, ReprogrammedCircuit.run_append, Circuit.run_concat, ← hl.1, h1, ih1]
    rw [show (k : ℕ) + 1 + l.length = k + (l.length + 1) by omega] at ih2 ⊢
    exact ⟨rfl, ih2⟩

theorem run_posts (H : X → Y) (c : C.Coins) (l : List (Fin A.post)) (σ : Matrix A.G A.G ℂ) :
    (ReprogrammedCircuit.concat (l.map (A.postCirc C))).run H (embed (A.emb C H c A.slots) σ) =
      embed (A.emb C H c A.slots) ((Circuit.concat (l.map fun b : Fin A.post =>
        Circuit.kraus (A.liftG (postStep b))
          (.kraus (KrausMap.ofPerm (A.postG C.toPureEnv (H, c))) .nil))).run (Equiv.refl _) σ) := by
  induction l generalizing σ with
  | nil => rfl
  | cons b l ih =>
    simp only [List.map_cons]
    rw [ReprogrammedCircuit.concat, ReprogrammedCircuit.run_append, Circuit.run_concat, run_postCirc, ih]

theorem suppIn_mgInit : SuppIn (A.blankFrom 0) A.mgInit := by
  intro a b hab
  simp only [mgInit, MState.reindex, MState.tensorKet_mat, submatrix_apply, kroneckerMap_apply,
    Matrix.single_apply]
  rcases hab with ha | hb
  · have : (splitLogs a).2 ≠ fun _ => none := fun h => ha (by simp [blankFrom, h])
    simp only [Equiv.symm_symm]
    rw [if_neg fun h => this h.1.symm, mul_zero]
  · have : (splitLogs b).2 ≠ fun _ => none := fun h => hb (by simp [blankFrom, h])
    simp only [Equiv.symm_symm]
    rw [if_neg fun h => this h.2.symm, mul_zero]

/-- **The composition runs the mixed game with measured requests**: on the coins `c`, the run of
the composed circuit at a schedule respected along the run, from the placed initial state, is the
placed final state of the mixed game. -/
theorem fullCirc_run {sched : Fin A.slots → Bool} {Inv : ℕ → Set A.G}
    (hInv : A.Respects C sched Inv) (h0 : SuppIn (Inv 0) A.mgInit) (H : X → Y) (c : C.Coins) :
    (A.fullCirc C sched).run H (embed (A.emb C H c 0) A.mgInit) =
      embed (A.emb C H c A.slots) (A.mgRun C.toPureEnv (H, c) true) := by
  obtain ⟨h1, -⟩ := A.run_slots C hInv H c (List.finRange A.slots) 0
    (by rw [List.map_coe_finRange_eq_range, List.range_eq_range', List.length_finRange])
    (A.suppIn_mgInit.inter h0)
  rw [List.length_finRange, Nat.zero_add] at h1
  simp only [fullCirc, mgRun, mgCirc, ReprogrammedCircuit.run_append, Circuit.run_append]
  rw [h1, run_posts]
  simp only [ReprogrammedCircuit.run, Circuit.run]
  rw [advKraus_apply_embed]

/-- **The initial state of the composition on coins `c`** is the placed initial state of the mixed
game. -/
theorem initSys_coin (H : X → Y) (c : C.Coins) :
    (MState.reindex (A.advSplit C) (A.init.tensorKet
      (⟨fun _ => none, fun _ _ => (x₀, 0), c⟩, fun _ => (x₀, 0)))).mat =
      embed (A.emb C H c 0) A.mgInit := by
  have he : A.emb C H c 0 = A.advSplit C ∘ Prod.map _root_.id
      (fun lg => (⟨lg, A.garFill C H c lg 0, c⟩, fun _ => (x₀, 0))) ∘ splitLogs := rfl
  rw [he, mgInit, ← Function.comp_assoc, embed_comp_equiv]
  simp only [MState.reindex, MState.tensorKet_mat, submatrix_submatrix, Equiv.symm_symm,
    Equiv.self_comp_symm, submatrix_id_id]
  rw [← Equiv.symm_symm (A.advSplit C), ← submatrix_embed_equiv, Equiv.symm_symm,
    embed_prodMap_kronecker_single]
  have hg : A.garFill C H c (fun _ => none) 0 = fun _ _ => (x₀, 0) := by
    funext k i
    simp [garFill]
  simp only [hg]

end KindAlg

/-! ### Linearity of runs -/

namespace ReprogrammedCircuit

variable {V X Y : Type} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [AddGroup Y]

theorem run_sum_smul {Ω : Type*} (H : X → Y) (c : ReprogrammedCircuit V X Y) (s : Finset Ω) (a : Ω → ℂ)
    (ρ : Ω → Matrix (QueryReg V 1 X Y) (QueryReg V 1 X Y) ℂ) :
    c.run H (∑ ω ∈ s, a ω • ρ ω) = ∑ ω ∈ s, a ω • c.run H (ρ ω) := by
  induction c generalizing ρ with
  | nil => rfl
  | kraus K c ih =>
    simp only [run]
    rw [← ih]
    congr 1
    simp only [KrausMap.apply, Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [Finset.sum_comm]
    simp only [Finset.smul_sum]
  | rquery a' c ih =>
    simp only [run]
    rw [← ih]
    congr 1
    ext i j
    simp [Matrix.sum_apply]

end ReprogrammedCircuit

end GordieHowe.Quantum

namespace GordieHowe.Quantum

theorem re_sum_smul_apply {ι Ω : Type*} [Fintype Ω] (a : Ω → ℝ) (M : Ω → Matrix ι ι ℂ) (q : ι) :
    ((∑ c, (a c : ℂ) • M c) q q).re = ∑ c, a c * (M c q q).re := by
  simp [Matrix.sum_apply, Complex.re_sum]

theorem sum_re_reprogAnc {X Y : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    (x₀' : X) : ∑ a, (reprogAnc (Y := Y) x₀' a a).re = 1 := by
  rw [← re_trace_eq_sum, trace_reprogAnc, Complex.one_re]

namespace IAlg

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] (A : IAlg X Y Req Resp O) (C : Challenger X Y Req Resp)

/-! ### The slot counter of `toKindAlg` -/

/-- The slot counter of a game basis state of `toKindAlg`. -/
def cnt (r : A.toKindAlg.G) : ℕ := ((r.1.1 : A.W × Fin (A.slots + 1)).2 : ℕ)

/-- **The Kraus map before slot `j` advances the counter**: its operators send the states with
counter `j` to states with counter `j + 1`. -/
theorem liftG_op_eq_zero (j : Fin A.slots) (r : A.R) (a b : A.toKindAlg.G) (ha : A.cnt a ≠ j + 1)
    (hb : A.cnt b = j) : (A.toKindAlg.liftG (slotStep j)).op r a b = 0 := by
  have hj : (j : ℕ) < A.slots := j.2
  obtain ⟨⟨⟨w, ca⟩, ra, sa, la⟩, pa⟩ := a
  obtain ⟨⟨⟨w', cb⟩, rb, sb, lb⟩, pb⟩ := b
  simp only [cnt] at ha hb
  have hne : (finRotate (A.slots + 1)).symm ca ≠ cb := by
    intro h
    apply ha
    rw [Equiv.symm_apply_eq] at h
    rw [h, coe_finRotate_of_ne_last (fun hl => by rw [hl, Fin.val_last] at hb; omega), hb]
  simp only [KindAlg.liftG, KrausMap.reindex, toKindAlg, KrausMap.permConj, KrausMap.tensorId,
    cntPerm, if_pos hj, Equiv.symm_symm, cntSplit, Equiv.coe_fn_mk, Equiv.prodCongr_symm,
    Equiv.refl_symm]
  change (_ * (1 : Matrix (Fin (A.slots + 1)) (Fin (A.slots + 1)) ℂ)
    ((finRotate (A.slots + 1)).symm ca) cb) * _ = 0
  rw [Matrix.one_apply_ne hne, mul_zero, zero_mul]

theorem suppIn_liftG_cnt (j : Fin A.slots) {σ : Matrix A.toKindAlg.G A.toKindAlg.G ℂ}
    (hσ : SuppIn {r | A.cnt r = j} σ) :
    SuppIn {r | A.cnt r = j + 1}
      ((A.toKindAlg.liftG (slotStep j)) σ) :=
  SuppIn.krausApply_of_op (fun r a b ha hb => A.liftG_op_eq_zero j r a b ha hb) hσ

/-- After the Kraus map number `j`, the kind read from the counter is `sched j`. -/
theorem kind_of_cnt (j : Fin A.slots) {r : A.toKindAlg.G} (h : A.cnt r = j + 1) :
    A.toKindAlg.kind r.1.1 = A.sched j := by
  change A.cntKind r.1.1 = A.sched j
  simp only [cnt] at h
  simp only [cntKind, h, Nat.add_one_ne_zero, dite_false, Nat.add_sub_cancel]

/-- The game events of a slot do not touch the counter. -/
theorem cnt_eq_of_workspace {r r' : A.toKindAlg.G} (h : r'.1.1 = r.1.1) : A.cnt r' = A.cnt r := by
  simp only [cnt, h]

/-- **The schedule is respected along the run of `toKindAlg`**, with the counter at `k` before the
Kraus map number `k`. -/
theorem respects : A.toKindAlg.Respects C A.sched fun k => {r | A.cnt r = k} where
  kind k σ hσ :=
    (A.suppIn_liftG_cnt k (hσ.mono Set.inter_subset_right)).mono fun r hr => A.kind_of_cnt k hr
  step H c k σ hσ := by
    have h1 := A.suppIn_liftG_cnt k (hσ.mono Set.inter_subset_right)
    simp only [KindAlg.gameSlot, KindAlg.eventCirc, Circuit.run, ↓reduceIte, KrausMap.ofPerm_apply,
      KrausMap.measureFn_apply]
    refine ((((h1.submatrix_perm (S' := {r | A.cnt r = k + 1}) fun r hr => ?_).dephase _).submatrix_perm
      (S' := {r | A.cnt r = k + 1}) fun r hr => ?_).submatrix_perm (S' := {r | A.cnt r = k + 1})
      fun r hr => ?_)
    · exact (A.cnt_eq_of_workspace (A.toKindAlg.copyG_workspace k r)).trans hr
    · exact (A.cnt_eq_of_workspace (A.toKindAlg.respG_workspace C (H, c) k r)).trans hr
    · exact (A.cnt_eq_of_workspace (A.toKindAlg.oraclePerm_workspace C (H, c) r)).trans hr

/-- The initial state of the mixed game of `toKindAlg` has counter `0`. -/
theorem suppIn_mgInit_cnt : SuppIn {r | A.cnt r = 0} A.toKindAlg.mgInit := by
  intro a b hab
  obtain ⟨⟨⟨w, ca⟩, ra, sa, la⟩, pa⟩ := a
  obtain ⟨⟨⟨w', cb⟩, rb, sb, lb⟩, pb⟩ := b
  simp only [Set.mem_setOf_eq, cnt] at hab
  change (_ * Matrix.single (0 : Fin (A.slots + 1)) 0 (1 : ℂ) ca cb) * _ = 0
  rw [Matrix.single_apply, if_neg, mul_zero, zero_mul]
  rintro ⟨h1, h2⟩
  rcases hab with h | h
  · exact h (by rw [← h1]; rfl)
  · exact h (by rw [← h2]; rfl)

/-- **The final state of the composition**: the clean ancilla and the coin-mixture of the placed
final states of the mixed game of `toKindAlg` with measured requests. -/
theorem compose_final (H : X → Y) :
    (A.compose C).final H = withAnc KindAlg.x₀ (∑ c, ((C.coins c).toReal : ℂ) •
      embed (A.toKindAlg.emb C H c A.slots) (A.toKindAlg.mgRun C.toPureEnv (H, c) true)) := by
  rw [Circuit.toAlg_final]
  change (A.fullCirc C).toCircuit.run (queryPerm H) (withAnc KindAlg.x₀ (A.toKindAlg.initSys C).mat) = _
  rw [ReprogrammedCircuit.run_toCircuit]
  congr 1
  simp only [KindAlg.initSys, MState.mix, A.toKindAlg.initSys_coin C H]
  rw [ReprogrammedCircuit.run_sum_smul]
  simp only [fullCirc, A.toKindAlg.fullCirc_run C (A.respects C) A.suppIn_mgInit_cnt]
  rfl

/-- **The output law of the composition** is the coin-average of the acceptance probabilities of
the mixed game of `toKindAlg` with measured requests. -/
theorem outLaw_compose_some [DecidableEq O] (H : X → Y) (o : O) :
    (A.compose C).outLaw H (some o) =
      ENNReal.ofReal (∑ c, (C.coins c).toReal * A.toKindAlg.mgAccept C.toPureEnv o (H, c) true) := by
  have hpsd := (A.compose C).posSemidef_stage H (A.compose C).depth
  rw [Alg.outLaw]
  refine (map_basisLaw_apply_some _ _ _ _ o).trans ?_
  have hdiag : ∀ p, 0 ≤ ((A.compose C).final H p p).re := fun p =>
    (Complex.nonneg_iff.1 (hpsd.diag_nonneg (i := p))).1
  have hite : ∀ p, (if some o = some ((A.compose C).out p.1) then
      ENNReal.ofReal ((A.compose C).final H p p).re else 0) =
      ENNReal.ofReal (if o = (A.compose C).out p.1 then ((A.compose C).final H p p).re else 0) :=
    fun p => by split_ifs with h1 h2 h2 <;> simp_all
  refine (Finset.sum_congr rfl fun p _ => hite p).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun p _ => by split_ifs; exact hdiag p; exact le_rfl]
  congr 1
  rw [compose_final]
  have hanc : ∀ a : X × Y × Bool, (reprogAnc (Y := Y) (KindAlg.x₀ : X) a a).im = 0 := fun a => by
    simp only [reprogAnc, ancWeight]
    split_ifs <;> simp
  have hstep : ∀ σ : Matrix (QueryReg (A.toKindAlg.CW C) 1 X Y) (QueryReg (A.toKindAlg.CW C) 1 X Y) ℂ,
      (∑ p : ReprogrammedQueryReg (A.toKindAlg.CW C) X Y,
        if o = A.out p.1.1.adv.workspace.1 then (withAnc KindAlg.x₀ σ p p).re else 0) =
        ∑ q : QueryReg (A.toKindAlg.CW C) 1 X Y, if o = A.out q.1.adv.workspace.1 then (σ q q).re else 0 := by
    intro σ
    rw [← (ancSplit (A.toKindAlg.CW C) X Y).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun q _ => ?_
    simp only [ancSplit, Equiv.coe_fn_symm_mk, withAnc, Complex.mul_re, hanc, mul_zero, sub_zero]
    split_ifs
    · rw [← Finset.mul_sum, sum_re_reprogAnc, mul_one]
    · simp
  refine (hstep _).trans ?_
  simp only [re_sum_smul_apply]
  have hg : ∀ q : QueryReg (A.toKindAlg.CW C) 1 X Y, ∀ x : ℝ,
      (if o = A.out q.1.adv.workspace.1 then x else 0) = (if o = A.out q.1.adv.workspace.1 then 1 else 0) * x :=
    fun q x => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun q _ => hg q _]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [mul_left_comm _ (C.coins c).toReal, ← Finset.mul_sum]
  congr 1
  rw [embed_diag_of_injective (A.toKindAlg.emb_injective C H c A.slots)]
  simp only [KindAlg.mgAccept]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hw : A.out (A.toKindAlg.emb C H c A.slots r).1.adv.workspace.1 = A.toKindAlg.out r.1.1 := rfl
  simp only [hw]
  by_cases h : A.toKindAlg.out r.1.1 = o
  · simp [h]
  · simp [h, Ne.symm h]

end IAlg

end GordieHowe.Quantum
