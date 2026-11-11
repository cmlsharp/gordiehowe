-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1HiddenPoints
public import GordieHowe.Applications.Ring.MLDSAW1KeyFree
public import GordieHowe.Applications.Ring.KeyFreeRelay
public import GordieHowe.Model.Quantum.Interactive.FreshCoinsAssign
public import GordieHowe.Foundations.ToMathlib.PMFCoupling
public import GordieHowe.Foundations.ToMathlib.UniformFunction

@[expose] public section

/-!
# The key-free signer of the ML-DSA ring publishing `w₁`, request by request

The hop from the kept-only reprogramming challenger `C₁′` of the fresh-mask ring game
(`Challenger.preReprogKeep`, `GordieHowe/Model/Quantum/Interactive/PreReprog.lean`, with the points
`w1Pts` and the kept points `w1KeptPts`) to the challenger `C₂` of the key-free relay
(`GordieHowe/Applications/Ring/KeyFreeRelay.lean`) at the key-free signer `w1KFSign`. Both read a
fresh coin per request (`Challenger.FreshCoinsIn`,
`GordieHowe/Model/Quantum/Interactive/FreshCoinsAssign.lean`), and at every oracle, history and
request their replies (response and assignments) have laws within total variation
`C(k T, 2) · commitPointMax(Â_s)` at a signing request of user `s` and equal laws otherwise.

At a signing request by a member of a supported ring passing the checks, `C₁′` answers by the
ring loop at the commitment hash reprogrammed on all the points `H(µ, ·)` to the fresh base
function `Z`: attempt `(c, t)` with mask `y` reads the commitment hash of the base value
`Z (H(µ, w₁(y)))`, and the kept attempt's assignment carries that value. Replacing these values
by independent uniform values changes the law only when two of the `k T` masks share a
commitment-hash point. With independent values, a permutation of the masks at each commitment
hash (the shift `y ↦ y + c·s₁`) carries the ideal attempts to the key-free attempts of the
published key, so the two laws are equal; the key-free relay answers by the key-free loop, with
the main prover's proof on the kept proof query.

- `PMF.tvDist_map_pullback_le`, `PMF.toReal_not_injective_le`: a uniform function read at the
  points of uniform values against independent uniform values, identical until two points
  collide; the probability of a collision among `|ι|` values, at most `C(|ι|, 2) · δ`.
- `exists_equiv_keyFreeAttempt_fiber`: at each commitment hash, a permutation of the masks
  carries the ideal attempt to the key-free attempt.
- `chOf`, `intAttV`, `kfAttV`, `attLoop`, `callOut_eq_keptCall`, `loopOut_eq_attLoop`: attempts
  carrying a base value, with the commitment hash `chOf v` of their base value, and loops of
  calls of them; the ring loop is such a loop of ideal attempts.
- `KFCoins`, `kfLoop`, `w1KFSign`, `w1KFSign_queries`, `run_w1KFSign`: **the key-free signer**:
  the public checks, the members' commitment hashes at the attempts' key-free commitments, the
  key-free loop, and for a kept output `(w₁, σ, v)` the published value `w1Of pk σ`, the
  signature and the assignment at `H(µ, w1Of pk σ)` of the value with base component `v`; at most
  `w1KFq` queries; it reads no secret key.
- `w1C1`, `w1C1FreshCoins`, `run_w1C1_sign`, `run_w1C1_corrupt`, `run_w1C1_sign_not_mem`: the
  kept-only challenger, its fresh coins, and its replies; at a signing request, `repOf` of the
  loop of ideal attempts at the fresh base values of the masks' points.
- `intRep`, `tvDist_w1C1_intRep_le`: the intermediate reply with independent base values, within
  `C(k T, 2) · commitPointMax(Â_s)` of the kept-only challenger at a signing request.
- `kfRep`, `map_intRep_eq_map_kfRep`: the key-free reply, with the intermediate's law.
- `w1C2`, `w1C2FreshCoins`, `run_w1C2_const`, `run_w1C2_sign`: the key-free relay challenger, its
  fresh coins and its replies; at a signing request, `kfRep`.
- `keptQuery`, `ProverRelays`, `KeptInRel`, `proverRelays_of_factor`, `keptInRel_of_forall`:
  the route-2 hypotheses (the ring prover is the main prover after the statement program; kept
  signatures are in the relation) and their satisfiability; `ringVerify_kfLoop`: a kept key-free
  signature verifies at the oracle reprogrammed by its kept assignment.
- `w1ReqBound`, `tvDist_w1C1_w1C2_le`: **the per-request bound**;
  `transcriptLawIn_w1C1_le_w1C2`: **the hop** on transcripts with the final oracle in force, at
  most `Q · C(k T, 2) · Σ_s commitPointMax(Â_s)`.
- `KeyFree.run_kfGame_respond`, `KeyFree.run_kfGame_sign_some`, `KeyFree.run_kfGame_sign_none`,
  `KeyFree.run_kfGame_corrupt`: the replies of the key-free outer challenger at a generic base
  signer.
-/

open Finset
open scoped ENNReal BigOperators

/-! ### Uniform laws -/

namespace PMF

/-- **A uniform function pulled back along an embedding is uniform.** -/
theorem map_comp_embedding_uniformOfFintype {A X' Y' : Type*} [Fintype A] [DecidableEq A]
    [Fintype X'] [DecidableEq X'] [Fintype Y'] [Nonempty Y'] (f : A ↪ X') :
    (uniformOfFintype (X' → Y')).map (fun G a => G (f a)) = uniformOfFintype (A → Y') := by
  have h : (fun G : X' → Y' => fun a => G (f a)) = Prod.snd ∘ GordieHowe.splitAlong f := by
    funext G a
    conv_lhs => rw [← (GordieHowe.splitAlong f).symm_apply_apply G]
    exact GordieHowe.splitAlong_symm_apply_embed f _ _ a
  rw [h, ← map_comp, map_uniformOfFintype_equiv, map_snd_uniformOfFintype]

/-- **A uniform function decoded pointwise by a map pushing the uniform law to the uniform law**
is uniform. -/
theorem map_comp_uniformOfFintype {A V W : Type*} [Fintype A] [DecidableEq A] [Fintype V]
    [Nonempty V] [Fintype W] [Nonempty W] (f : V → W)
    (hf : (uniformOfFintype V).map f = uniformOfFintype W) :
    (uniformOfFintype (A → V)).map (fun g a => f (g a)) = uniformOfFintype (A → W) := by
  rw [← pi_uniformOfFintype, ← pi_uniformOfFintype]
  rw [pi_map]
  simp only [hf]

/-- **A uniform pair read through its first component** has the first component's uniform
law. -/
theorem toOuterMeasure_uniformOfFintype_fst {A B : Type*} [Fintype A] [Nonempty A] [Fintype B]
    [Nonempty B] (S : Set A) :
    (uniformOfFintype (A × B)).toOuterMeasure {x | x.1 ∈ S} =
      (uniformOfFintype A).toOuterMeasure S := by
  rw [← map_fst_uniformOfFintype (α := A) (β := B), toOuterMeasure_map_apply]
  rfl

/-- **Pulling a uniform function back at the points of uniform values, against independent
uniform values** (identical until two of the points collide): the law of
`F (a ↦ (y_a, Z (pt y_a))) w` for a uniform function `Z`, values `y = ys g` of uniform coins `g`
with the uniform law and uniform `w`, is within total variation the probability that the points
`pt y_a` are not distinct of the law of `F x w` for uniform `x` and `w`. -/
theorem tvDist_map_pullback_le {ι G W V X' Y' β : Type*} [Fintype ι] [DecidableEq ι] [Fintype G]
    [Nonempty G] [Fintype W] [Nonempty W] [Fintype V] [Nonempty V] [Fintype X'] [DecidableEq X']
    [Fintype Y'] [Nonempty Y'] (ys : G → ι → V)
    (hys : (uniformOfFintype G).map ys = uniformOfFintype (ι → V)) (pt : V → X')
    (F : (ι → V × Y') → W → β) :
    tvDist ((uniformOfFintype ((X' → Y') × G × W)).map
        fun u => F (fun a => (ys u.2.1 a, u.1 (pt (ys u.2.1 a)))) u.2.2)
      ((uniformOfFintype ((ι → V × Y') × W)).map fun x => F x.1 x.2) ≤
      ((uniformOfFintype (ι → V)).toOuterMeasure
        {y | ¬ Function.Injective fun a => pt (y a)}).toReal := by
  classical
  set k₁ : (ι → V) × W → PMF β := fun yw =>
    (uniformOfFintype (X' → Y')).map fun Z => F (fun a => (yw.1 a, Z (pt (yw.1 a)))) yw.2
  set k₂ : (ι → V) × W → PMF β := fun yw =>
    (uniformOfFintype (ι → Y')).map fun vs => F (fun a => (yw.1 a, vs a)) yw.2
  have h₁ : (uniformOfFintype ((X' → Y') × G × W)).map
      (fun u => F (fun a => (ys u.2.1 a, u.1 (pt (ys u.2.1 a)))) u.2.2) =
      (uniformOfFintype ((ι → V) × W)).bind k₁ := by
    rw [uniformOfFintype_prod_eq_bind, map_bind]
    simp only [← bind_pure_comp, bind_bind, Function.comp_apply, pure_bind]
    rw [bind_comm, ← map_prodMap_uniformOfFintype (h := id) hys (map_id _), bind_map]
    congr 1
  have h₂ : (uniformOfFintype ((ι → V × Y') × W)).map (fun x => F x.1 x.2) =
      (uniformOfFintype ((ι → V) × W)).bind k₂ := by
    let e : ((ι → V) × W) × (ι → Y') ≃ (ι → V × Y') × W :=
      { toFun := fun q => (fun a => (q.1.1 a, q.2 a), q.1.2)
        invFun := fun x => ((fun a => (x.1 a).1, x.2), fun a => (x.1 a).2)
        left_inv := fun q => rfl
        right_inv := fun x => rfl }
    rw [← map_uniformOfFintype_equiv e, map_comp, uniformOfFintype_prod_eq_bind, map_bind]
    congr 1
    funext yw
    rw [map_comp]
    rfl
  rw [h₁, h₂]
  refine (tvDist_bind_le_toOuterMeasure_ne _ k₁ k₂).trans ?_
  rw [← toOuterMeasure_uniformOfFintype_fst (A := ι → V) (B := W)
    {y : ι → V | ¬ Function.Injective fun a => pt (y a)}]
  have hsub : {yw : (ι → V) × W | k₁ yw ≠ k₂ yw} ⊆
      {yw | yw.1 ∈ {y : ι → V | ¬ Function.Injective fun a => pt (y a)}} := by
    intro yw hne hinj
    refine hne ?_
    simp only [k₁, k₂]
    rw [← map_comp_embedding_uniformOfFintype (Y' := Y') ⟨fun a => pt (yw.1 a), hinj⟩, map_comp]
    rfl
  exact ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (toOuterMeasure_apply_le_one _ _)) (MeasureTheory.measure_mono hsub)

/-- **Some two of independent uniform values have the same point** with probability at most
`C(|ι|, 2) · δ`, for `δ` bounding the probability of each point of a uniform value. -/
theorem toReal_not_injective_le {ι V X' : Type*} [Fintype ι] [DecidableEq ι] [Fintype V]
    [Nonempty V] (pt : V → X') {δ : ℝ}
    (hδ : ∀ x, ((uniformOfFintype V).toOuterMeasure {y | pt y = x}).toReal ≤ δ) :
    ((uniformOfFintype (ι → V)).toOuterMeasure
        {y | ¬ Function.Injective fun a => pt (y a)}).toReal ≤
      ((Fintype.card ι).choose 2 : ℝ) * δ := by
  classical
  set e := Fintype.equivFin ι
  set P : Finset (Fin (Fintype.card ι) × Fin (Fintype.card ι)) := {x | x.1 < x.2} with hP
  have hsub : {y : ι → V | ¬ Function.Injective fun a => pt (y a)} ⊆
      ⋃ ij ∈ P, {y | pt (y (e.symm ij.1)) = pt (y (e.symm ij.2))} := by
    intro y hy
    simp only [Function.Injective, not_forall] at hy
    obtain ⟨a, b, hab, hne⟩ := hy
    rcases lt_or_gt_of_ne (fun h : e a = e b => hne (e.injective h)) with h | h
    · exact Set.mem_biUnion (x := (e a, e b)) (by simp [hP, h]) (by simp [hab])
    · exact Set.mem_biUnion (x := (e b, e a)) (by simp [hP, h]) (by simp [hab])
  have hpair : ∀ ij ∈ P, ((uniformOfFintype (ι → V)).toOuterMeasure
      {y | pt (y (e.symm ij.1)) = pt (y (e.symm ij.2))}).toReal ≤ δ := by
    intro ij hij
    have hne : e.symm ij.1 ≠ e.symm ij.2 := fun h => by
      simp only [hP, Finset.mem_filter, Finset.mem_univ, true_and] at hij
      exact absurd (e.symm.injective h) (ne_of_lt hij)
    rw [← pi_uniformOfFintype]
    exact toReal_pt_eq_of_update_le (fun _ => uniformOfFintype V) (fun _ => pt) (fun _ => hδ)
      (e.symm ij.1) (fun u => pt (u (e.symm ij.2))) fun u y => by
        rw [Function.update_of_ne (Ne.symm hne)]
  have hfin : ∀ ij ∈ P, (uniformOfFintype (ι → V)).toOuterMeasure
      {y | pt (y (e.symm ij.1)) = pt (y (e.symm ij.2))} ≠ ⊤ := fun _ _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_apply_le_one _ _)
  calc ((uniformOfFintype (ι → V)).toOuterMeasure
        {y | ¬ Function.Injective fun a => pt (y a)}).toReal
      ≤ (∑ ij ∈ P, (uniformOfFintype (ι → V)).toOuterMeasure
          {y | pt (y (e.symm ij.1)) = pt (y (e.symm ij.2))}).toReal :=
        ENNReal.toReal_mono (ENNReal.sum_ne_top.2 hfin)
          ((MeasureTheory.measure_mono hsub).trans (MeasureTheory.measure_biUnion_finset_le _ _))
    _ = ∑ ij ∈ P, ((uniformOfFintype (ι → V)).toOuterMeasure
          {y | pt (y (e.symm ij.1)) = pt (y (e.symm ij.2))}).toReal :=
        ENNReal.toReal_sum hfin
    _ ≤ ∑ _ij ∈ P, δ := Finset.sum_le_sum hpair
    _ = ((Fintype.card ι).choose 2 : ℝ) * δ := by
        rw [Finset.sum_const, nsmul_eq_mul, hP, Fintype.card_product_filter_lt, Fintype.card_fin]

/-- A uniform law pushed through `f ∘ e` for an equivalence `e` is pushed through `f`. -/
theorem map_uniformOfFintype_comp_equiv' {A B β : Type*} [Fintype A] [Nonempty A] [Fintype B]
    [Nonempty B] (e : A ≃ B) (f : B → β) :
    (uniformOfFintype A).map (fun a => f (e a)) = (uniformOfFintype B).map f := by
  rw [← map_uniformOfFintype_equiv e, map_comp]
  rfl

/-- **The product of two uniform laws is the uniform law on the product.** -/
theorem prodLaw_uniformOfFintype {A B : Type*} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B] :
    GordieHowe.Quantum.prodLaw (uniformOfFintype A) (uniformOfFintype B) =
      uniformOfFintype (A × B) :=
  (uniformOfFintype_prod_eq_bind).symm

/-- **Two laws pushed through constant maps to the same value are equal**, so their total
variation is `0`. -/
theorem tvDist_map_const_eq_zero {α β γ : Type*} (p : PMF α) (q : PMF β) (f : α → γ) (g : β → γ)
    (v : γ) (hf : ∀ a, f a = v) (hg : ∀ b, g b = v) : tvDist (p.map f) (q.map g) = 0 := by
  rw [show f = Function.const α v from funext hf, show g = Function.const β v from funext hg,
    map_const, map_const, tvDist_self]

end PMF

namespace GordieHowe.RingSignature.KeyFree

open GordieHowe.Quantum GordieHowe.OracleProg

variable {X Y Req' Resp' Ro Rs : Type} [DecidableEq X]

omit [DecidableEq X] in
/-- **The reply of the outer challenger of an assigning relay**: the relay's program of number
`|hist|`, its main requests answered by the main challenger's responses after the padded main
history, at the oracle in force. -/
theorem run_kfGame_respond (C' : Challenger X Y Req' Resp') (G : AssignRelay X Y Ro Rs Req' Resp')
    (Q : ℕ) (c' : C'.Coins) (hist : List (HistoryEntry Ro Rs)) (r : Ro) (H : X → Y) :
    ((kfGame C' G Q).respond c' hist r).run H =
      (G.elimProg (fun _ => none) hist.length r).run (combineAns H fun r' =>
        ((C'.respond c' (AssignRelay.mainHist (padHist G (Q := Q) hist)) r').run H).response) := by
  simp only [kfGame, run_mapOutput, AssignRelay.relayProg]
  rw [run_lower, run_recMain_fst, reprogT_none]
  simp only [run_mapOutput]

omit [DecidableEq X] in
/-- The padded main history reads the relay only through its padding request. -/
theorem padHist_congr (G G' : AssignRelay X Y Ro Rs Req' Resp') {Q : ℕ}
    (hist : List (HistoryEntry Ro Rs)) (h : G.idle = G'.idle) :
    padHist G (Q := Q) hist = padHist G' (Q := Q) hist := by
  simp only [padHist, h]

omit [DecidableEq X] in
/-- The padded main history has the length of the outer history. -/
theorem length_mainHist_padHist (G : AssignRelay X Y Ro Rs Req' Resp') {Q : ℕ}
    (hist : List (HistoryEntry Ro Rs)) :
    (AssignRelay.mainHist (padHist G (Q := Q) hist)).length = hist.length := by
  simp [AssignRelay.mainHist, padHist, List.filterMap_map]

section Sign

open GordieHowe.Signature

variable [Zero Y] {N n : ℕ} {TB : BaseTypes} [DecidableEq TB.PK]
  (B : RingSignature.BaseSigner X Y N TB)
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : RingSignature.ProofSystem X Y (RingSignature.RingStmt B) (RingSignature.RingWit B) ⟨Pf, PC⟩}
  {adm : KeyRing B.PK N → Prop} [DecidablePred adm] {Stmt Wit Coins SC X₀ R : Type}
  [Fintype Coins] [DecidableEq Coins] (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (P : NARG.Prover X Y Stmt Wit Pf Coins) (μ : PMF Coins)
  (penc : MURequest (SignOracle.none B.core) n ⊕ R → QROM.ProofQuery Stmt Wit)
  (keys : Fin n → B.KeyCoins) (pks : Fin n → B.PK)
  (ksign : B.PK → KeyRing B.PK N → ℕ → B.Msg → SC →
    OracleProg X Y (Option (B.Pub × B.BSig × List (Assignment X Y))))
  (stmtP : RingSignature.RingStmt B → OracleProg X Y X₀)
  (toR : X₀ → RingSignature.Insider.Req B PS adm n × ℕ → B.BSig → R)
  (dummyR : RingSignature.Insider.Req B PS adm n × ℕ → R) {qk qs : ℕ}
  (hk : ∀ pk Rg c msg s, (ksign pk Rg c msg s).QueriesLE qk)
  (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none B.core) n ⊕ R)

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **A signing request answered with a signature by the key-free outer challenger**: for a
signer in a supported ring below the cap whose key-free signer outputs `(y, σ, asg)` at the
oracle `H`, and an in-relation proof request, the reply is the signature `(y, π)` with the main
prover's proof `π` on the request's proof coins, and the assignments `asg`. -/
theorem run_kfGame_sign_some {Q : ℕ} (sc : Fin Q → SC)
    (c' : (RingSignature.kfMain B rel P μ penc keys Q).Coins) (hist : List (HistoryEntry
      (RingSignature.Insider.Req B PS adm n)
      (RingSignature.Insider.Resp B PS adm)))
    (s : Fin n) (Rg : KeyRing B.PK N) (m : B.Msg) (hc : hist.length < Q ∧ pks s ∈ Rg.1 ∧ adm Rg)
    (H : X → Y) (y : B.Pub) (σ : B.BSig) (asg : List (Assignment X Y))
    (ho : (ksign (pks s) Rg hist.length m (sc ⟨hist.length, hc.1⟩)).run H = some (y, σ, asg))
    (hrel : rel (penc (.inr (toR ((stmtP ⟨Rg, m, y⟩).run (H.reprogram asg))
      (.sign s Rg m, hist.length) σ))).stmt (penc (.inr (toR ((stmtP ⟨Rg, m, y⟩).run
        (H.reprogram asg)) (.sign s Rg m, hist.length) σ))).wit) :
    ((kfGame (RingSignature.kfMain B rel P μ penc keys Q)
        (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle) Q).respond c' hist
        (.sign s Rg m)).run H =
      ⟨some (.signature (y, (P.prog (penc (.inr (toR ((stmtP ⟨Rg, m, y⟩).run (H.reprogram asg))
          (.sign s Rg m, hist.length) σ))).stmt (penc (.inr (toR ((stmtP ⟨Rg, m, y⟩).run
            (H.reprogram asg)) (.sign s Rg m, hist.length) σ))).wit (c'.2 ⟨hist.length, hc.1⟩)).run
                H)), asg⟩ := by
  rw [run_kfGame_respond, elimProg_kfRelay]
  rw [run_kfProg]
  have hsig : (sigP (PS := PS) (adm := adm) B pks ksign sc hist.length (.sign s Rg m)).run H =
      some (y, σ, asg) := by
    simp only [sigP]
    exact (congrArg (OracleProg.run H) (dite_eq_left_of_eq_true (eq_true hc))).trans ho
  rw [hsig]
  have hl : (dummyHist penc (AssignRelay.mainHist (padHist (kfRelay B pks ksign stmtP toR
      dummyR sc hk hs idle) (Q := Q) hist))).length < Q := by
    simp only [dummyHist, List.length_map, length_mainHist_padHist]
    exact hc.1
  have hidx : (⟨(dummyHist penc (AssignRelay.mainHist (padHist (kfRelay B pks ksign stmtP toR
      dummyR sc hk hs idle) (Q := Q) hist))).length, hl⟩ : Fin Q) = ⟨hist.length, hc.1⟩ :=
    Fin.ext (by simp only [dummyHist, List.length_map, length_mainHist_padHist])
  simp only [xP, run_mapOutput, reqOf, asgOf, Option.elim, RingSignature.kfMain,
    Challenger.sumDummy, QROM.realChallenger, hl, ↓reduceDIte, hrel, ↓reduceIte, run_bind,
    run_pure, Option.map, replyOf, Option.bind, Sum.getRight?, hidx]

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **A signing request the key-free signer refuses**: no response and no assignments. -/
theorem run_kfGame_sign_none {Q : ℕ} (sc : Fin Q → SC) (c' : (RingSignature.kfMain B rel P μ penc
      keys Q).Coins)
    (hist : List (HistoryEntry (RingSignature.Insider.Req B PS adm n)
      (RingSignature.Insider.Resp B PS adm)))
    (s : Fin n) (Rg : KeyRing B.PK N) (m : B.Msg) (H : X → Y)
    (ho : (sigP (PS := PS) (adm := adm) B pks ksign sc hist.length (.sign s Rg m)).run H =
      none) :
    ((kfGame (RingSignature.kfMain B rel P μ penc keys Q)
        (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle) Q).respond c' hist
        (.sign s Rg m)).run H = ⟨none, []⟩ := by
  rw [run_kfGame_respond, elimProg_kfRelay]
  rw [run_kfProg, ho]
  rfl

omit [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC] [Nonempty PC] in
/-- **A corruption answered by the key-free outer challenger**: the user's key coins, below the
cap. -/
theorem run_kfGame_corrupt {Q : ℕ} (sc : Fin Q → SC) (c' : (RingSignature.kfMain B rel P μ penc
      keys Q).Coins)
    (hist : List (HistoryEntry (RingSignature.Insider.Req B PS adm n)
      (RingSignature.Insider.Resp B PS adm)))
    (i : Fin n) (h : hist.length < Q) (H : X → Y) :
    ((kfGame (RingSignature.kfMain B rel P μ penc keys Q)
        (kfRelay B pks ksign stmtP toR dummyR sc hk hs idle) Q).respond c' hist
        (.corrupt i)).run H = ⟨some (.keyCoins (keys i)), []⟩ := by
  rw [run_kfGame_respond]
  change (kfProg B pks ksign stmtP toR dummyR sc hist.length (.corrupt i)).run _ = _
  rw [run_kfProg]
  have hl : (leftHist (AssignRelay.mainHist (padHist (kfRelay B pks ksign stmtP toR
      dummyR sc hk hs idle) (Q := Q) hist))).length < Q :=
    lt_of_le_of_lt (List.length_filterMap_le _ _) (by rw [length_mainHist_padHist]; exact h)
  simp only [reqOf, RingSignature.kfMain, Challenger.sumDummy, run_mapOutput,
    RingSignature.respond_muChallenger_none B keys Q _ _ _ _ hl]
  rfl

end Sign

end GordieHowe.RingSignature.KeyFree

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature
open GordieHowe.Quantum

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

/-! ### The key-free attempt, fiber by fiber of the commitment hash -/

section Fiber

open LatticeCrypto TransformOps

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)]

/-- **At each commitment hash, a permutation of the masks carries the ideal attempt to the
key-free one**: `keyFreeAttempt (σ y, c̃) = idealAttemptW1 (y, c̃)`, with `σ y = y + c·s₁` on the
masks accepted at `c̃` (`exists_equiv_keyFreeAttempt` with the commitment hash kept). For the key
of `seed` with `‖s₁‖∞, ‖s₂‖∞ ≤ η`, given the signing and verification laws and an encoding `enc`
coherent with `bucketsOf`. -/
theorem exists_equiv_keyFreeAttempt_fiber (h_laws : SigningLaws prims)
    (hv : VerifyLaws prims) {enc : Vector prims.High p.k → BucketVec p}
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    {seed : Bytes 32} {pk : PublicKey p prims} {sk : SecretKey p}
    (hkeygen : keyGenFromSeed p prims seed = (pk, sk)) (hs1 : polyVecBounded sk.s1 p.eta)
    (hs2 : polyVecBounded sk.s2 p.eta) (c : CommitHashBytes p) :
    ∃ σ : MaskBox p ≃ MaskBox p, ∀ y,
      keyFreeAttempt prims pk sk.t0 (σ y, c) =
        idealAttemptW1 prims sk (prims.expandA pk.rho) (y, c) := by
  have hcs : polyVecNorm (prims.sampleInBall c • sk.s1) ≤ p.beta :=
    h_laws.polyVecNorm_sampleInBall_smul_le prims c sk.s1 hs1
  refine exists_equiv_comp_eq_of_isSome
    (fun y => idealAttemptW1 prims sk (prims.expandA pk.rho) (y, c))
    (fun z => keyFreeAttempt prims pk sk.t0 (z, c)) (maskAdd (prims.sampleInBall c • sk.s1))
    (maskSub (prims.sampleInBall c • sk.s1)) ?_ ?_
  · intro y hsome
    have hacc : signAccept prims sk (prims.expandA pk.rho) y.1 c = true := by
      by_contra h
      simp [idealAttemptW1, attemptAccept, h] at hsome
    have hbox : InMaskBox p.gamma1 (y.1 + (prims.sampleInBall c • sk.s1)) := by
      refine inMaskBox_of_zCheck ?_
      rw [← keyFreeAccept_add hv hkeygen] at hacc
      simp only [keyFreeAccept, Bool.and_eq_true] at hacc
      exact hacc.1.1.1
    have hadd : maskAdd (prims.sampleInBall c • sk.s1) y =
        ⟨y.1 + (prims.sampleInBall c • sk.s1), hbox⟩ := dite_eq_left hbox
    refine ⟨?_, ?_⟩
    · rw [hadd]
      exact (idealAttemptW1_eq_keyFreeAttempt h_laws hv henc hkeygen hs2 y _ c rfl).symm
    · rw [hadd]
      have hsub : InMaskBox p.gamma1 (y.1 + (prims.sampleInBall c • sk.s1) -
        (prims.sampleInBall c • sk.s1)) := by
        rw [rqVec_add_sub_cancel]; exact y.2
      rw [maskSub, dite_eq_left hsub]
      exact Subtype.ext (rqVec_add_sub_cancel _ _)
  · intro z hsome
    have hacc : keyFreeAccept prims pk sk.t0 z.1 c = true := by
      by_contra h
      simp [keyFreeAttempt, h] at hsome
    have hz : zCheck z.1 = true := by
      simp only [keyFreeAccept, Bool.and_eq_true] at hacc
      exact hacc.1.1.1
    have hbox : InMaskBox p.gamma1 (z.1 - (prims.sampleInBall c • sk.s1)) :=
      inMaskBox_sub_of_zCheck hz hcs
    have hsub : maskSub (prims.sampleInBall c • sk.s1) z =
        ⟨z.1 - (prims.sampleInBall c • sk.s1), hbox⟩ := dite_eq_left hbox
    refine ⟨?_, ?_⟩
    · rw [hsub]
      exact idealAttemptW1_eq_keyFreeAttempt h_laws hv henc hkeygen hs2 _ z c
        (rqVec_sub_add_cancel _ _).symm
    · rw [hsub]
      have hadd : InMaskBox p.gamma1 (z.1 - (prims.sampleInBall c • sk.s1) +
        (prims.sampleInBall c • sk.s1)) := by
        rw [rqVec_sub_add_cancel]; exact z.2
      rw [maskAdd, dite_eq_left hadd]
      exact Subtype.ext (rqVec_sub_add_cancel _ _)

end Fiber

/-! ### Attempts carrying a base value, and loops of calls -/

section Loops

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (O : W1Oracles X Y p prims Msg N reps) (sp : Y ≃+ Y₁ × Y₂)

variable {prims} in
/-- **The commitment hash of a base value** `v`: the decoding of the value with base component
`v` and second component `0` (for a decoding reading only the base component, the commitment
hash of every value with base component `v`). -/
def chOf (v : Y₁) : CommitHashBytes p :=
  O.chAns (sp.symm (v, 0))

/-- **An ideal attempt at a mask and a base value** `(y, v)`: the ideal attempt at `y` and the
commitment hash `chOf v`, its output carrying `v`. -/
def intAttV (sk : SecretKey p) (aHat : TqMatrix p.k p.l) (yv : MaskBox p × Y₁) :
    Option (BucketVec p × FIPSSignature p prims × Y₁) :=
  (idealAttemptW1 prims sk aHat (yv.1, chOf O sp yv.2)).map fun a => (a.1, a.2, yv.2)

/-- **A key-free attempt at a response and a base value** `(z, v)`: the key-free attempt at `z`
and the commitment hash `chOf v`, its output carrying `v`. -/
def kfAttV (pk : PublicKey p prims) (t0 : RqVec p.k) (zv : MaskBox p × Y₁) :
    Option (BucketVec p × FIPSSignature p prims × Y₁) :=
  (keyFreeAttempt prims pk t0 (zv.1, chOf O sp zv.2)).map fun a => (a.1, a.2, zv.2)

variable {prims} in
/-- The keep weight `wt (w₁, c̃)` of an output `(w₁, σ, v)`, read at the signature's `c̃`. -/
def outWt (wt : BucketVec p × CommitHashBytes p → ℝ≥0∞)
    (s : BucketVec p × FIPSSignature p prims × Y₁) : ℝ≥0∞ :=
  wt (s.1, s.2.1.cTilde)

/-- **`k` calls of `T` attempts with keep coins**: call `c` keeps the first accepted output of its
attempts `att c` with the coin `uv c` (`keptCall`); the first kept output. -/
noncomputable def attLoop {S : Type*} {k D : ℕ} (κ : S → ℝ≥0∞) (att : Fin k → Fin T → Option S)
    (uv : Fin k → Fin D) : Option S :=
  (List.finRange k).findSome? fun c => keptCall κ (att c) (uv c)

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- A kept output is the output of one of the attempts. -/
theorem exists_of_keptCall_eq_some {S : Type*} {D : ℕ} {κ : S → ℝ≥0∞} {att : Fin T → Option S}
    {u : Fin D} {s : S} (h : keptCall κ att u = some s) : ∃ t, att t = some s := by
  unfold keptCall at h
  split at h
  · exact absurd h (by simp)
  · rename_i s' hs'
    split_ifs at h
    obtain ⟨t, -, ht⟩ := List.exists_of_findSome?_eq_some hs'
    exact ⟨t, (Option.some.inj h) ▸ ht⟩

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- An output of the loop is the output of one of the attempts. -/
theorem exists_of_attLoop_eq_some {S : Type*} {k D : ℕ} {κ : S → ℝ≥0∞}
    {att : Fin k → Fin T → Option S} {uv : Fin k → Fin D} {s : S}
    (h : attLoop κ att uv = some s) : ∃ c t, att c t = some s := by
  obtain ⟨c, -, hc⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨t, ht⟩ := exists_of_keptCall_eq_some hc
  exact ⟨c, t, ht⟩

omit [Nonempty (MaskBox p)] in
/-- **An output of an ideal attempt**: the mask's commitment, the attempt's signature at the
commitment hash `chOf v`, and `v`, on acceptance. -/
theorem intAttV_eq_some {sk : SecretKey p} {aHat : TqMatrix p.k p.l} {yv : MaskBox p × Y₁}
    {s : BucketVec p × FIPSSignature p prims × Y₁} (h : intAttV prims O sp sk aHat yv = some s) :
    attemptAccept prims sk aHat yv.1 (chOf O sp yv.2) = true ∧
      s = (realBuckets aHat yv.1, attemptOutput prims sk aHat (yv.1, chOf O sp yv.2), yv.2) := by
  unfold intAttV idealAttemptW1 at h
  split_ifs at h with ha
  · exact ⟨ha, (Option.some.inj h).symm⟩
  · exact absurd h (by simp)

omit [Nonempty (MaskBox p)] in
/-- **One call of the ring loop is a kept call of ideal attempts carrying base values**: at
masks `ys` and base values `vs` with the signer's commitment hash `hc (i, w₁(y_t)) = chOf v_t`,
`callOut` is the kept call of `intAttV` at the flattening weight, its signature. -/
theorem callOut_eq_keptCall (βmin : ℚ≥0) (D : ℕ) (sk : SecretKey p)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (ys : Fin T → MaskBox p)
    (vs : Fin T → Y₁)
    (h : ∀ t, hc (i, realBuckets (prims.expandA sk.rho) (ys t)) = chOf O sp (vs t))
    (u : Fin D) :
    callOut prims βmin D sk R i hc ys u =
      (keptCall (outWt (fun vc => flattenCoin prims sk (Cutoff.const βmin) vc *
          (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc vc.1))
        (fun t => intAttV prims O sp sk (prims.expandA sk.rho) (ys t, vs t)) u).map
        fun s => s.2.1 := by
  have hatt : (fun t => intAttV prims O sp sk (prims.expandA sk.rho) (ys t, vs t)) = fun t =>
      if attemptAccept prims sk (prims.expandA sk.rho) (ys t)
          (hc (i, realBuckets (prims.expandA sk.rho) (ys t))) then
        some (realBuckets (prims.expandA sk.rho) (ys t), attemptOutput prims sk
          (prims.expandA sk.rho) (ys t, hc (i, realBuckets (prims.expandA sk.rho) (ys t))), vs t)
      else none := by
    funext t
    rw [h t]
    unfold intAttV idealAttemptW1
    split_ifs <;> rfl
  unfold callOut keptCall
  rw [hatt, List.findSome?_ite_eq_map_find?]
  rcases (List.finRange T).find? _ with _ | t
  · rfl
  · simp only [Option.map_some, outWt, attemptOutput, ENNReal.natCast_lt_natCast_mul_mul_iff]
    split_ifs with hu <;> simp only [hu, ↓reduceIte, Option.map_some, Option.map_none]

omit [Nonempty (MaskBox p)] in
/-- **The ring loop is the loop of ideal attempts carrying base values** (`callOut_eq_keptCall`
call by call), its signature. -/
theorem loopOut_eq_attLoop (βmin : ℚ≥0) {k D : ℕ} (sk : SecretKey p)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (hc : Fin R.1.length × BucketVec p → CommitHashBytes p) (ys : Fin k → Fin T → MaskBox p)
    (vs : Fin k → Fin T → Y₁)
    (h : ∀ c t, hc (i, realBuckets (prims.expandA sk.rho) (ys c t)) = chOf O sp (vs c t))
    (uv : Fin k → Fin D) :
    loopOut prims βmin sk R i hc ys uv =
      (attLoop (outWt (fun vc => flattenCoin prims sk (Cutoff.const βmin) vc *
          (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc vc.1))
        (fun c t => intAttV prims O sp sk (prims.expandA sk.rho) (ys c t, vs c t)) uv).map
        fun s => s.2.1 := by
  unfold loopOut attLoop
  rw [List.option_map_findSome?]
  exact PMF.findSome?_congr_mem fun c _ => callOut_eq_keptCall prims O sp βmin D sk R i hc (ys c)
    (vs c) (h c) (uv c)

end Loops

/-! ### The key-free signer -/

/-- **An upper bound on the key-free signer's queries** (`w1KFSign_queries`), counting the two
checks, the members' and the signer's message representatives, the members' hashes at the
attempts and the kept point; the signer may make fewer. -/
abbrev w1KFq (N reps k T : ℕ) : ℕ := N * reps + (N + (N + (1 + (k * T * N + 1))))

section Signer

variable (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁]
  [AddGroup Y₂] (O : W1Oracles X Y p prims Msg N reps) (sp : Y ≃+ Y₁ × Y₂) (βmin : ℚ≥0)
  (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) {RMsg : Type}
  (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

/-- **The side coins of one key-free signature**: per call and attempt a response in the mask
box and a base value, and per call a keep coin. -/
abbrev KFCoins (Y₁ : Type) : Type :=
  (Fin k → Fin T → MaskBox p × Y₁) × (Fin k → Fin D)

omit [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] in
/-- The side coins have decidable equality. -/
instance instDecEqKFCoins [DecidableEq Y₁] : DecidableEq (KFCoins (p := p) (T := T) k D Y₁) :=
  @instDecidableEqProd _ _ (inferInstance : DecidableEq (Fin k → Fin T → MaskBox p × Y₁))
    (inferInstance : DecidableEq (Fin k → Fin D))

/-- The key-free commitments of the attempts, from the published key and the side coins. -/
def kfW1s (pk : PubKey p prims) (xs : Fin k → Fin T → MaskBox p × Y₁) (ct : Fin k × Fin T) :
    BucketVec p :=
  keyFreeW1 prims (pubPk prims pk) pk.2.2 (xs ct.1 ct.2).1.1 (chOf O sp (xs ct.1 ct.2).2)

variable {prims k} in
/-- **The members' commitment hashes from the queried values**: at the commitment of an attempt,
the value `cs (ct, j)` queried for the first such attempt `ct` and member `j`; a default
elsewhere. -/
noncomputable def kfHashes {n : ℕ} (ws : Fin k × Fin T → BucketVec p)
    (cs : (Fin k × Fin T) × Fin n →
    CommitHashBytes p) (x : Fin n × BucketVec p) : CommitHashBytes p :=
  match (Finset.univ.toList : List (Fin k × Fin T)).find? (fun ct => decide (ws ct = x.2)) with
  | some ct => cs (ct, x.1)
  | none => default

omit [NeZero (bucketCount p)] nttOps [Nonempty (MaskBox p)] in
/-- The hashes read back at an attempt's commitment are the queried ones. -/
theorem kfHashes_apply {n : ℕ} (ws : Fin k × Fin T → BucketVec p)
    (cs : (Fin k × Fin T) × Fin n → CommitHashBytes p) (F : Fin n → BucketVec p → CommitHashBytes p)
    (hcs : ∀ ct j, cs (ct, j) = F j (ws ct)) (ct : Fin k × Fin T) (j : Fin n) :
    kfHashes ws cs (j, ws ct) = F j (ws ct) := by
  obtain ⟨ct₀, ht₀, hv⟩ : ∃ ct₀, (Finset.univ.toList : List (Fin k × Fin T)).find?
      (fun ct' => decide (ws ct' = ws ct)) = some ct₀ ∧ ws ct₀ = ws ct := by
    rcases hf : (Finset.univ.toList : List (Fin k × Fin T)).find?
      (fun ct' => decide (ws ct' = ws ct)) with _ | ct₀
    · exact absurd (List.find?_eq_none.1 hf ct (Finset.mem_toList.2 (Finset.mem_univ _)))
        (by simp)
    · exact ⟨ct₀, rfl, by simpa using List.find?_some hf⟩
  unfold kfHashes
  dsimp only
  rw [ht₀]
  dsimp only
  rw [hcs, hv]

variable {k D} in
/-- **The key-free loop** of the published key `pk` at the position `i` of the ring `R`, at the
members' commitment hashes `hc` and the side coins `sc`: `k` calls of `T` key-free attempts with
the commitment hashes of the attempts' base values, call `c` keeping its first accepted output
with its coin when it is below `D` times the flattening weight read from the published `t₀` and
the other members' weights. -/
noncomputable def kfLoop (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (hc : Fin R.1.length × BucketVec p → CommitHashBytes p)
    (sc : KFCoins (p := p) (T := T) k D Y₁) : Option (BucketVec p × FIPSSignature p prims × Y₁) :=
  attLoop (outWt (fun vc => PMF.flattenKeep (fun a => (t0Weight prims pk.2.2 a : ℝ≥0∞)) βmin vc *
      (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc vc.1))
    (fun c t => kfAttV prims O sp (pubPk prims pk) pk.2.2 (sc.1 c t)) sc.2

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] in
/-- **The key-free loop reads the commitment hashes only at the attempts' commitments.** -/
theorem kfLoop_congr {k D : ℕ} (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) {hc hc' : Fin R.1.length × BucketVec p → CommitHashBytes p}
    (sc : KFCoins (p := p) (T := T) k D Y₁)
    (h : ∀ ct j, hc (j, kfW1s prims O sp k pk sc.1 ct) = hc' (j, kfW1s prims O sp k pk sc.1 ct)) :
    kfLoop prims O sp βmin pk R i hc sc = kfLoop prims O sp βmin pk R i hc' sc := by
  unfold kfLoop attLoop
  refine PMF.findSome?_congr_mem fun c _ => ?_
  unfold keptCall
  rcases hs : (List.finRange T).findSome? (fun t => kfAttV prims O sp (pubPk prims pk) pk.2.2
    (sc.1 c t)) with _ | s
  · rfl
  · obtain ⟨t, -, ht⟩ := List.exists_of_findSome?_eq_some hs
    have hs1 : s.1 = kfW1s prims O sp k pk sc.1 (c, t) := by
      unfold kfAttV keyFreeAttempt at ht
      split_ifs at ht
      · rw [← Option.some.inj ht]
        rfl
      · exact absurd ht (by simp)
    have hw : (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc s.1 =
        (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i hc' s.1 :=
      Finset.prod_congr rfl fun j _ => by rw [hs1, h (c, t) j]
    simp only [outWt, hw]
    split_ifs with hu <;> simp only [hu, ↓reduceIte]

variable [Fintype Msg] [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg]

/-- **The key-free signer of the ML-DSA ring publishing `w₁`** (the `ksign` of the key-free relay,
`GordieHowe/Applications/Ring/KeyFreeRelay.lean`), at the published key `pk`, the ring `R`, the
message `m` and the side coins `sc`: the public ring check and the distinct-µ check of the base
signer (`ringCheckProg`, `muDistinctProg`); on a ring holding `pk` passing both, the members'
message representatives `µ_j` (one query per member), the signer's `µ` (one query), every
member's commitment hash at every attempt's key-free commitment (one query each), and the
key-free loop (`kfLoop`) at the hashes read; for a kept output `(w₁, σ, v)`, one query at the
commitment-hash point `x = H(µ, w1Of pk σ)` of the published value, and the output: the
published value, the signature and the assignment of the value with base component `v` and the
second component of the oracle at `x`. It refuses otherwise. It reads no secret key. -/
noncomputable def w1KFSign (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (_c : ℕ)
    (m : RMsg) (sc : KFCoins (p := p) (T := T) k D Y₁) :
    OracleProg X Y (Option (BucketVec p × FIPSSignature p prims × List (Assignment X Y))) :=
  (ringCheckProg prims O βmin tol R).bind fun ok =>
    (muDistinctProg prims O R (bmsg R m)).bind fun ok' =>
      if ok ∧ ok' then
        if hi : R.1.idxOf pk < R.1.length then
          (OracleProg.queryAll (R.1.map fun x => O.muPt (pubTr prims x, bmsg R m))).bind fun ans =>
            .query (O.muPt (pubTr prims pk, bmsg R m)) fun yMu =>
              (OracleProg.tabulate (fun _ => default)
                  (Finset.univ.toList : List ((Fin k × Fin T) × Fin R.1.length)) fun ctj =>
                .query (O.chPt ((ans.map O.muAns).getD ctj.2 default,
                  kfW1s prims O sp k pk sc.1 ctj.1)) fun y => .pure (O.chAns y)).bind fun cs =>
                match kfLoop prims O sp βmin pk R ⟨_, hi⟩ (kfHashes (kfW1s prims O sp k pk sc.1) cs)
                    sc with
                | none => .pure none
                | some s => .query (O.chPt (O.muAns yMu, w1Of prims enc pk s.2.1)) fun y =>
                    .pure (some (w1Of prims enc pk s.2.1, s.2.1,
                      [⟨O.chPt (O.muAns yMu, w1Of prims enc pk s.2.1), sp.symm (s.2.2, (sp y).2)⟩]))
        else .pure none
      else .pure none

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)]
  [Fintype Msg] [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg] in
/-- **The key-free signer makes at most `w1KFq` queries.** -/
theorem w1KFSign_queries (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ) (m : RMsg)
    (sc : KFCoins (p := p) (T := T) k D Y₁) :
    (w1KFSign prims O sp βmin tol enc k D bmsg pk R c m sc).QueriesLE (w1KFq N reps k T) := by
  refine (ringCheckProg_queries prims O βmin tol R).bind fun ok =>
    (muDistinctProg_queries prims O R (bmsg R m)).bind fun ok' => ?_
  split_ifs with h hi
  · refine ((OracleProg.QueriesLE.queryAll _).mono (by simpa using R.2)).bind fun ans => ?_
    refine (OracleProg.QueriesLE.query (q := k * T * N + 1) _ fun yMu => ?_).mono (by omega)
    have h₂ := OracleProg.QueriesLE.tabulate (fun _ => (default : CommitHashBytes p))
      (Finset.univ.toList : List ((Fin k × Fin T) × Fin R.1.length)) (q := 1)
      (P := fun ctj => .query (O.chPt ((ans.map O.muAns).getD ctj.2 default,
        kfW1s prims O sp k pk sc.1 ctj.1)) fun y => .pure (O.chAns y))
      fun ctj h => by simp [OracleProg.trace_query, OracleProg.trace_pure]
    refine (h₂.mono ?_).bind fun cs => ?_
    · simp only [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        mul_one]
      exact Nat.mul_le_mul_left _ R.2
    · split
      · exact OracleProg.QueriesLE.pure _ _
      · exact OracleProg.QueriesLE.query _ fun y => OracleProg.QueriesLE.pure _ _
  · exact OracleProg.QueriesLE.pure _ _
  · exact OracleProg.QueriesLE.pure _ _

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)]
  [Fintype Msg] [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg] in
open Classical in
/-- **The key-free signer at the oracle `H`**: `none` unless the ring passes the public check and
its members' message representatives are distinct, and `pk` is in the ring; otherwise the key-free
loop at the members' commitment hashes read from `H`, a kept output `(w₁, σ, v)` giving the
published value `w1Of pk σ`, the signature and the assignment at `x = H(µ, w1Of pk σ)` of the value
with base component `v` and the second component of `H x`, for the signer's message
representative `µ` read from `H`. -/
theorem run_w1KFSign (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ) (m : RMsg)
    (sc : KFCoins (p := p) (T := T) k D Y₁) (H : X → Y) :
    (w1KFSign prims O sp βmin tol enc k D bmsg pk R c m sc).run H =
      if RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m) then
        if hi : R.1.idxOf pk < R.1.length then
          (kfLoop prims O sp βmin pk R ⟨_, hi⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) sc).map fun s =>
            (w1Of prims enc pk s.2.1, s.2.1,
              [⟨O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bmsg R m))), w1Of prims enc pk s.2.1),
                sp.symm (s.2.2, (sp (H (O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bmsg R m))),
                  w1Of prims enc pk s.2.1)))).2)⟩])
        else none
      else none := by
  have hg := run_ringCheckProg prims O βmin tol R H
  have hm := run_muDistinctProg prims O R (bmsg R m) H
  have hinner : ∀ hi : R.1.idxOf pk < R.1.length,
      ((OracleProg.queryAll (R.1.map fun x => O.muPt (pubTr prims x, bmsg R m))).bind fun ans =>
        OracleProg.query (O.muPt (pubTr prims pk, bmsg R m)) fun yMu =>
          (OracleProg.tabulate (fun _ => default)
              (Finset.univ.toList : List ((Fin k × Fin T) × Fin R.1.length)) fun ctj =>
            OracleProg.query (O.chPt ((ans.map O.muAns).getD ctj.2 default,
              kfW1s prims O sp k pk sc.1 ctj.1)) fun y => OracleProg.pure (O.chAns y)).bind
            fun cs =>
            match kfLoop prims O sp βmin pk R ⟨_, hi⟩ (kfHashes (kfW1s prims O sp k pk sc.1) cs)
                sc with
            | none => OracleProg.pure none
            | some s => OracleProg.query (O.chPt (O.muAns yMu, w1Of prims enc pk s.2.1)) fun y =>
                OracleProg.pure (some (w1Of prims enc pk s.2.1, s.2.1,
                  [(⟨O.chPt (O.muAns yMu, w1Of prims enc pk s.2.1),
                    sp.symm (s.2.2, (sp y).2)⟩ : Assignment X Y)]))).run H =
        (kfLoop prims O sp βmin pk R ⟨_, hi⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) sc).map fun s =>
          (w1Of prims enc pk s.2.1, s.2.1,
            [(⟨O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bmsg R m))), w1Of prims enc pk s.2.1),
              sp.symm (s.2.2, (sp (H (O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bmsg R m))),
                w1Of prims enc pk s.2.1)))).2)⟩ : Assignment X Y)]) := by
    intro hi
    simp only [OracleProg.run_bind, OracleProg.run_queryAll, OracleProg.run_query,
      OracleProg.run_tabulate, OracleProg.run_pure, Finset.mem_toList, Finset.mem_univ, ite_true]
    have hloop : kfLoop prims O sp βmin pk R ⟨_, hi⟩ (kfHashes (kfW1s prims O sp k pk sc.1)
        fun ctj => O.chAns (H (O.chPt ((((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map
          H).map O.muAns).getD ctj.2 default, kfW1s prims O sp k pk sc.1 ctj.1)))) sc =
        kfLoop prims O sp βmin pk R ⟨_, hi⟩
          (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) sc :=
      kfLoop_congr prims O sp βmin pk R _ sc fun ct j =>
        kfHashes_apply k (kfW1s prims O sp k pk sc.1) _
          (fun j w => PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H) (j, w))
          (fun ct j => chOrc_getD_eq prims O R (bmsg R m) H (j, _)) ct j
    rw [hloop]
    rcases kfLoop prims O sp βmin pk R ⟨_, hi⟩
      (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) sc with _ | s
    · rfl
    · rfl
  simp only [w1KFSign, OracleProg.run_bind]
  rcases hg' : (ringCheckProg prims O βmin tol R).run H <;>
    rcases hm' : (muDistinctProg prims O R (bmsg R m)).run H
  · have : ¬ RingCheck prims βmin tol (O.gOrc H) R := fun h => by simp_all
    simp [this]
  · have : ¬ RingCheck prims βmin tol (O.gOrc H) R := fun h => by simp_all
    simp [this]
  · have : ¬ MuDistinct prims (O.muOrc H) R (bmsg R m) := fun h => by simp_all
    simp [this]
  · have h1 : RingCheck prims βmin tol (O.gOrc H) R := hg.1 hg'
    have h2 : MuDistinct prims (O.muOrc H) R (bmsg R m) := hm.1 hm'
    simp only [and_self, ↓reduceIte, h1, h2]
    split_ifs with hi
    · exact hinner hi
    · rfl

end Signer

/-! ### The kept-only reprogramming challenger reads one coin per request -/

section KeptOnly

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {Pf PC : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC]
  {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg))
    (RingSignature.RingWitOf (FIPSSignature p prims)) ⟨Pf, PC⟩}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm]
  {Of : SideOracle (freshScheme prims O M βmin tol enc k D bmsg PS adm)} {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]

local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg

variable (Of) in
/-- **The kept-only reprogramming challenger of the fresh-mask ring game** (`C₁′`):
`Challenger.preReprogKeep` at the unforgeability challenger, the points `w1Pts` and the kept
points `w1KeptPts`. -/
noncomputable abbrev w1C1 (sp : Y ≃+ Y₁ × Y₂) (keys : Fin n → (Sf).KeyCoins) (Q : ℕ) :
    Challenger X Y (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of) :=
  (unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
    (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)

omit [Fintype X] [AddGroup Y] [Fintype Pf] [DecidableEq Pf] [Fintype PC] [DecidableEq PC]
  [Nonempty PC] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- The points read only the coins of request `|hist|`. -/
theorem w1Pts_eq_const (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) (h : hist.length < Q) :
    w1Pts Of keys c hist req = w1Pts Of keys (fun _ : Fin Q => c ⟨hist.length, h⟩) hist req := by
  unfold w1Pts
  simp only [h, ↓reduceDIte]

omit [Fintype X] [DecidableEq X] [AddGroup Y] [Fintype Pf] [DecidableEq Pf] in
/-- The unforgeability challenger reads only the coins of request `|hist|`. -/
theorem unforgeChallenger_respond_eq_const (keys : Fin n → (Sf).KeyCoins) {Q : ℕ}
    (c : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) (h : hist.length < Q) :
    (unforgeChallenger Sf n Of keys Q).respond c hist req =
      (unforgeChallenger Sf n Of keys Q).respond (fun _ : Fin Q => c ⟨hist.length, h⟩)
        hist req := by
  unfold unforgeChallenger
  simp only [h, ↓reduceDIte]

omit [Fintype Pf] [DecidableEq Pf] in
/-- **The kept-only reprogramming challenger reads only the coins of request `|hist|`**: its fresh
base values and its signing coins. -/
theorem run_w1C1_respond_eq_const (sp : Y ≃+ Y₁ × Y₂) (keys : Fin n → (Sf).KeyCoins) {Q : ℕ}
    (Z : Fin Q → X → Y₁) (c : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) (h : hist.length < Q) (H : X → Y) :
    ((w1C1 Of sp keys Q).respond (Z, c) hist req).run H =
      ((w1C1 Of sp keys Q).respond
        (fun _ : Fin Q => Z ⟨hist.length, h⟩, fun _ : Fin Q => c ⟨hist.length, h⟩)
        hist req).run H := by
  refine (Challenger.run_respond_preReprogKeep (C₀ := unforgeChallenger Sf n Of keys Q) _ Z c
    hist req H h).trans (Eq.trans ?_ (Challenger.run_respond_preReprogKeep
      (C₀ := unforgeChallenger Sf n Of keys Q) _ _ _ hist req H h).symm)
  simp only [w1KeptPts]
  rw [w1Pts_eq_const keys c hist req h, unforgeChallenger_respond_eq_const keys c hist req h]
  rfl

variable (Of) in
/-- **The kept-only reprogramming challenger reads a fresh coin per request**
(`Challenger.FreshCoinsIn`): no key, the coin of request `j` its fresh base function and its
signing coins, both uniform, and the reply the challenger's at the constant coins. -/
noncomputable def w1C1FreshCoins (sp : Y ≃+ Y₁ × Y₂) (keys : Fin n → (Sf).KeyCoins) (Q : ℕ) :
    (w1C1 Of sp keys Q).FreshCoinsIn (PMF.pure ())
      (prodLaw (PMF.uniformOfFintype (X → Y₁)) (PMF.uniformOfFintype (Sf).SignCoins)) where
  equiv :=
    { toFun := fun ω => ((), fun j => (ω.1 j, ω.2 j))
      invFun := fun x => (fun j => (x.2 j).1, fun j => (x.2 j).2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  coins_eq c := by
    rcases c with ⟨Z, cs⟩
    refine (prodLaw_apply (PMF.uniformOfFintype (Fin Q → X → Y₁))
      (PMF.uniformOfFintype (Fin Q → (Sf).SignCoins)) Z cs).trans ?_
    simp only [PMF.pure_apply, ↓reduceIte, one_mul]
    have h1 : PMF.uniformOfFintype (Fin Q → X → Y₁) Z =
        ∏ j, PMF.uniformOfFintype (X → Y₁) (Z j) := by
      rw [← PMF.pi_uniformOfFintype (β := fun _ : Fin Q => X → Y₁)]; rfl
    have h2 : PMF.uniformOfFintype (Fin Q → (Sf).SignCoins) cs =
        ∏ j, PMF.uniformOfFintype (Sf).SignCoins (cs j) := by
      rw [← PMF.pi_uniformOfFintype (β := fun _ : Fin Q => (Sf).SignCoins)]; rfl
    rw [h1, h2]
    exact Finset.prod_mul_distrib.symm.trans
      (Finset.prod_congr rfl fun j _ => (prodLaw_apply _ _ _ _).symm)
  kernel _ H hist r u :=
    ((w1C1 Of sp keys Q).respond (fun _ : Fin Q => u.1, fun _ : Fin Q => u.2) hist r).run H
  respond_eq H c hist r hj := by
    rcases c with ⟨Z, cs⟩
    exact run_w1C1_respond_eq_const sp keys Z cs hist r hj H

/-! ### The reply of the kept-only challenger to a signing request -/

omit [Fintype X] nttOps [Fintype Y] [DecidableEq Y] [Nonempty Y] [AddGroup Y] in
/-- An oracle reprogrammed by one assignment. -/
theorem reprogram_singleton_apply (H : X → Y) (a : Assignment X Y) (x : X) :
    H.reprogram [a] x = if a.input = x then a.output else H x := by
  rw [reprogram_apply_eq_lastAssign, show [a] = [] ++ [a] from rfl, lastAssign_append_singleton]
  split_ifs <;> rfl

omit [Fintype X] nttOps in
/-- **The points of a list without repetition in a set holding exactly one of them.** -/
theorem filter_toList_eq_singleton {S T : Finset X} {x : X} (h : S ∩ T = {x}) :
    S.toList.filter (fun z => decide (z ∈ T)) = [x] := by
  have hnd : (S.toList.filter fun z => decide (z ∈ T)).Nodup := (Finset.nodup_toList S).filter _
  have hmem : ∀ z, z ∈ S.toList.filter (fun z => decide (z ∈ T)) ↔ z ∈ [x] := fun z => by
    rw [List.mem_filter, Finset.mem_toList, decide_eq_true_iff, List.mem_singleton,
      ← Finset.mem_inter, h, Finset.mem_singleton]
  exact List.perm_singleton.1 ((List.perm_ext_iff_of_nodup hnd (List.nodup_singleton x)).2 hmem)

variable (O enc) in
/-- **The kept assignment of an output** `(σ, v)` of the published key `pk` on the base message
`bm` at the oracle `H`: at the commitment-hash point `x = H(µ, w1Of pk σ)` of the signer's
message representative `µ` read from `H`, the value with base component `v` and the second
component of `H x`. -/
def keptAsg (sp : Y ≃+ Y₁ × Y₂) (H : X → Y) (pk : PubKey p prims) (bm : Msg)
    (σ : FIPSSignature p prims) (v : Y₁) :
    Assignment X Y :=
  ⟨O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bm))), w1Of prims enc pk σ),
    sp.symm (v, (sp (H (O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bm))),
      w1Of prims enc pk σ)))).2)⟩

variable (O enc PS Of) in
/-- **The reply to a signing request from an output carrying a base value**: for an output
`(w₁, σ, v)` the signature with the published value `w1Of pk σ` and the proof at the oracle
reprogrammed by the kept assignment (`keptAsg`), and that assignment; nothing for no output. -/
noncomputable def repOf (sp : Y ≃+ Y₁ × Y₂) (H : X → Y) (pk : PubKey p prims)
    (R : KeyRing (PubKey p prims) N)
    (m : RMsg) (cp : (PS).Coins) :
    Option (BucketVec p × FIPSSignature p prims × Y₁) →
      Reply X Y (UnforgeResponse (S := Sf) Of)
  | none => ⟨none, []⟩
  | some s => ⟨some (.signature (w1Of prims enc pk s.2.1,
      ((PS).prove ⟨R, m, w1Of prims enc pk s.2.1⟩
          ⟨R.1.idxOf pk, s.2.1⟩ cp).run
        (H.reprogram [keptAsg O enc sp H pk (bmsg R m) s.2.1 s.2.2]))),
      [keptAsg O enc sp H pk (bmsg R m) s.2.1 s.2.2]⟩

variable (O βmin) in
/-- The keep weight of the ring loop of the signer at position `i` at the oracle `H`: the
signer's flattening coin times the other members' weights at their commitment hashes read
from `H`. -/
noncomputable def ringWt (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (bm : Msg) (H : X → Y) : BucketVec p × CommitHashBytes p → ℝ≥0∞ :=
  fun vc => flattenCoin prims sk (Cutoff.const βmin) vc *
    (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i
      (PMF.ringOf (ringPts prims R.1 bm) (O.hOrc H)) vc.1

omit [Fintype X] [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] in
/-- **The signer's commitment hash at the oracle reprogrammed on its message representative's
commitment-hash points** is the commitment hash of the fresh base value there, for decodings
reading only the base component. -/
theorem ringOf_reprogBase_self (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (R : KeyRing (PubKey p prims) N) (bm : Msg)
    (Z : X → Y₁) (H : X → Y) (pk : PubKey p prims) (i : Fin R.1.length) (hi : R.1.get i = pk)
    (w : BucketVec p) :
    PMF.ringOf (ringPts prims R.1 bm) (O.hOrc (reprogBase sp (muChPts O (O.muAns (H (O.muPt
        (pubTr prims pk, bm))))) Z H)) (i, w) =
      chOf O sp (Z (O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bm))), w))) := by
  subst hi
  have hmu : ∀ a, reprogBase sp (muChPts O (O.muAns (H (O.muPt (pubTr prims (R.1.get i), bm)))))
      Z H (O.muPt a) = H (O.muPt a) := fun a => by
    simp only [reprogBase]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun hx => ?_)
    obtain ⟨w', -, hw'⟩ := Finset.mem_image.1 hx
    exact hdisj _ _ hw'.symm
  simp only [PMF.ringOf, ringPts, MLDSAOracles.hOrc, schemeOrc, MLDSAOracles.muOrc,
    MLDSAOracles.chOrc]
  rw [hmu]
  have hin : O.chPt (O.muAns (H (O.muPt (pubTr prims (R.1.get i), bm))), w) ∈
      muChPts O (O.muAns (H (O.muPt (pubTr prims (R.1.get i), bm)))) :=
    Finset.mem_image.2 ⟨w, Finset.mem_univ _, rfl⟩
  simp only [reprogBase, hin, ↓reduceIte, chOf]
  exact hO.chAns_eq _ _ (by simp)

omit [Fintype X] [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] in
/-- **Another member's commitment hash is not reprogrammed** when its message representative
differs from the signer's. -/
theorem ringOf_reprogBase_other (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (R : KeyRing (PubKey p prims) N) (bm : Msg) (Z : X → Y₁) (H : X → Y) (mu : Bytes 64)
    (j : Fin R.1.length) (hj : O.muAns (H (O.muPt (pubTr prims (R.1.get j), bm))) ≠ mu)
    (w : BucketVec p) :
    PMF.ringOf (ringPts prims R.1 bm) (O.hOrc (reprogBase sp (muChPts O mu) Z H)) (j, w) =
      PMF.ringOf (ringPts prims R.1 bm) (O.hOrc H) (j, w) := by
  have hmu : ∀ a, reprogBase sp (muChPts O mu) Z H (O.muPt a) = H (O.muPt a) := fun a => by
    simp only [reprogBase]
    refine ite_eq_right_of_eq_false _ _ (eq_false fun hx => ?_)
    obtain ⟨w', -, hw'⟩ := Finset.mem_image.1 hx
    exact hdisj _ _ hw'.symm
  simp only [PMF.ringOf, ringPts, MLDSAOracles.hOrc, schemeOrc, MLDSAOracles.muOrc,
    MLDSAOracles.chOrc]
  rw [hmu]
  have hout : O.chPt (O.muAns (H (O.muPt (pubTr prims (R.1.get j), bm))), w) ∉ muChPts O mu :=
    fun hx => by
      obtain ⟨w', -, hw'⟩ := Finset.mem_image.1 hx
      exact hj (Prod.mk.inj (hch hw')).1.symm
  simp only [reprogBase, hout, ↓reduceIte]

omit [Fintype X] [Fintype Y₁] [DecidableEq Y₁] [Fintype Pf] [DecidableEq Pf] [Fintype PC]
  [DecidableEq PC] [Nonempty PC] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **The prover at the oracle reprogrammed on a message representative's commitment-hash points
runs as at the oracle with only the public value's point reprogrammed**, for a prover reading
first components only at the public value's points (`ProverReadsPub`) and an injective
commitment-hash point map. -/
theorem prove_run_reprogBase_eq (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hPS : ProverReadsPub O PS sp)
    (x : RingSignature.RingStmt (freshBase prims O M βmin tol enc k D bmsg))
    (w : RingSignature.RingWitOf (FIPSSignature p prims))
    (cp : (PS).Coins) (mu : Bytes 64) (Z : X → Y₁)
    (H : X → Y) :
    ((PS).prove x w cp).run
        (reprogBase sp (muChPts O mu) Z H) =
      ((PS).prove x w cp).run
        (H.reprogram [⟨O.chPt (mu, x.pub), sp.symm (Z (O.chPt (mu, x.pub)),
          (sp (H (O.chPt (mu, x.pub)))).2)⟩]) := by
  refine hPS x w cp _ _ (fun z => ?_) fun z hz => ?_
  · have h1 : (sp (reprogBase sp (muChPts O mu) Z H z)).2 = (sp (H z)).2 := by
      simp only [reprogBase]
      split_ifs
      · rw [AddEquiv.apply_symm_apply]
      · rfl
    rw [h1, reprogram_singleton_apply]
    by_cases ha : O.chPt (mu, x.pub) = z
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ha), AddEquiv.apply_symm_apply, ha]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false ha)]
  · rw [reprogram_singleton_apply]
    simp only [reprogBase]
    rcases hz with hz | ⟨u, rfl⟩
    · have h1 : z ∉ muChPts O mu := fun hx => by
        obtain ⟨w', -, hw'⟩ := Finset.mem_image.1 hx
        exact hz ⟨_, hw'⟩
      have h2 : ¬ O.chPt (mu, x.pub) = z := fun he => hz ⟨_, he⟩
      simp only [h1, h2, ↓reduceIte]
    · by_cases hu : u = mu
      · subst hu
        have h1 : O.chPt (u, x.pub) ∈ muChPts O u := Finset.mem_image.2 ⟨_, Finset.mem_univ _, rfl⟩
        simp only [h1, ↓reduceIte]
      · have h1 : O.chPt (u, x.pub) ∉ muChPts O mu := fun hx => by
          obtain ⟨w', -, hw'⟩ := Finset.mem_image.1 hx
          exact hu (Prod.mk.inj (hch hw')).1.symm
        have h2 : ¬ O.chPt (mu, x.pub) = O.chPt (u, x.pub) := fun he =>
          hu (Prod.mk.inj (hch he)).1.symm
        simp only [h1, h2, ↓reduceIte]

open Classical in
omit [Fintype Pf] [DecidableEq Pf] in
/-- **The reply of the kept-only challenger to a signing request** at the constant coins `Z` and
`c'`, for a signer in the ring with an honest key: on a supported ring passing the checks at the
oracle `H`, `repOf` of the loop of ideal attempts carrying base values, the attempt at mask `y`
carrying the fresh base value `Z (H(µ, w₁(y)))` of its commitment-hash point; a refusal with no
assignment otherwise. The loop reads the signer's commitment hashes at the reprogrammed points
(`ringOf_reprogBase_self`) and the other members' at `H` (distinct message representatives,
`ringOf_reprogBase_other`); the prover reads the reprogrammed oracle only at the kept point
(`ProverReadsPub`), whose assignment the challenger keeps (`w1Pts_inter_keepOf_eq`). -/
theorem run_w1C1_sign (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (Z : X → Y₁) (c' : (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (s : Fin n) (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hR : (Bf).pk (keys s) ∈ R.1) (h : hist.length < Q) (H : X → Y) :
    ((w1C1 Of sp keys Q).respond (fun _ : Fin Q => Z, fun _ : Fin Q => c') hist
        (.sign s R m)).run H =
      if adm R ∧ RingCheck prims βmin tol (O.gOrc H) R ∧
          MuDistinct prims (O.muOrc H) R (bmsg R m) then
        repOf O enc PS Of sp H ((Bf).pk (keys s)) R m c'.2
          (attLoop (outWt (ringWt O βmin ((Sf).sk (keys s)) R ⟨_, idxOf_lt_of_mem keys hR⟩
              (bmsg R m) H))
            (fun cc t => intAttV prims O sp ((Sf).sk (keys s))
              (prims.expandA ((Sf).sk (keys s)).rho)
              (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m c'.1.1 cc t,
                Z (O.chPt (O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))),
                  realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
                    (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m c'.1.1 cc t)))))
            c'.1.2)
      else ⟨none, []⟩ := by
  set rs := hist.map HistoryEntry.request with hrs
  have hl : hist.length = (Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs).length := by
    simp [Challenger.histOf, rs]
  have h' : rs.length < Q := by simpa [rs] using h
  refine (Challenger.run_respond_preReprogKeep (C₀ := unforgeChallenger Sf n Of keys Q) (sp := sp)
    (pts := w1Pts Of keys) (qp := 1) (K := k * T) (hqp := w1Pts_queries keys)
    (hK := card_w1Pts_le keys) (w1KeptPts Of) (fun _ => Z) (fun _ => c') hist (.sign s R m) H
    h).trans ?_
  simp only [w1KeptPts]
  rw [w1Pts_congr keys _ hist (Challenger.histOf rs) _ hl]
  erw [unforgeChallenger_respond_congr keys Q _ hist (Challenger.histOf rs) _ hl]
  erw [unforgeChallenger_plain keys Q]
  rw [List.append_nil]
  have hw0 := w1Resp_sign_eq sp hch hdisj hdisjg hPS h_laws hv henc keys (fun _ => c') rs s R m
    (hs2 s) hR h' Z H
  have hw := hw0
  unfold w1Resp at hw
  rw [hw]
  by_cases hc : adm R ∧ RingCheck prims βmin tol (O.gOrc H) R ∧
    MuDistinct prims (O.muOrc H) R (bmsg R m)
  swap
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)]
    erw [replyOf_eq_none _ hc]
    simp [keepOf]
  rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
  have hi := idxOf_lt_of_mem keys hR
  have hget : R.1.get ⟨_, hi⟩ = (Bf).pk (keys s) := List.getElem_idxOf hi
  set mu := O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))) with hmu
  have hne : ∀ j : Fin R.1.length, j ∈ Finset.univ.erase ⟨_, hi⟩ →
      O.muAns (H (O.muPt (pubTr prims (R.1.get j), bmsg R m))) ≠ mu := by
    intro j hj he
    refine (Finset.mem_erase.1 hj).1 (Fin.ext ?_)
    refine (List.Nodup.getElem_inj_iff hc.2.2 (hi := by simp) (hj := by simpa using hi)).1 ?_
    simp only [List.getElem_map, MLDSAOracles.muOrc]
    exact he.trans (congrArg (fun x => O.muAns (H (O.muPt (pubTr prims x, bmsg R m)))) hget.symm)
  have hwt : outWt (prims := prims) (Y₁ := Y₁)
      (fun vc => flattenCoin prims ((Sf).sk (keys s)) (Cutoff.const βmin) vc *
      (ringWeights prims βmin (ringT0s prims R.1)).otherWeight ⟨_, hi⟩
        (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (reprogBase sp (muChPts O mu) Z H)))
        vc.1) = outWt (ringWt O βmin ((Sf).sk (keys s)) R ⟨_, hi⟩ (bmsg R m) H) := by
    funext x
    simp only [outWt, ringWt]
    refine congrArg (HMul.hMul _) ?_
    rw [ENNReal.nnratCast_inj]
    exact Finset.prod_congr rfl fun j hj => by
      rw [ringOf_reprogBase_other sp hch hdisj R (bmsg R m) Z H mu j (hne j hj)]
  rw [loopOut_eq_attLoop prims O sp βmin _ R _ _ _
    (fun cc t => Z (O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
      (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m c'.1.1 cc t))))
    (fun cc t => ringOf_reprogBase_self sp hO hdisj R (bmsg R m) Z H _ _ hget _), hwt]
  rcases hA : attLoop (outWt (ringWt O βmin ((Sf).sk (keys s)) R ⟨_, hi⟩ (bmsg R m) H))
      (fun cc t => intAttV prims O sp ((Sf).sk (keys s)) (prims.expandA ((Sf).sk (keys s)).rho)
        (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m c'.1.1 cc t,
          Z (O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
            (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m c'.1.1 cc t))))) c'.1.2
    with _ | ⟨w, σ, v⟩
  · simp only [Option.map_none]
    erw [replyOf_none]
    simp [keepOf, repOf]
  obtain ⟨cc0, t0, hatt⟩ := exists_of_attLoop_eq_some hA
  obtain ⟨hacc, hsv⟩ := intAttV_eq_some prims O sp hatt
  simp only [Prod.mk.injEq] at hsv
  obtain ⟨rfl, rfl, rfl⟩ := hsv
  set y := reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m c'.1.1 cc0 t0 with hy
  set σ₀ := attemptOutput prims ((Sf).sk (keys s)) (prims.expandA ((Sf).sk (keys s)).rho)
    (y, chOf O sp (Z (O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho) y))))
    with hσ₀
  have hw1 : w1Of prims enc ((Bf).pk (keys s)) σ₀ =
      realBuckets (prims.expandA ((Sf).sk (keys s)).rho) y :=
    w1Of_attemptOutput prims enc h_laws hv henc (hs2 s) y _ hacc
  have hr := hw0
  rw [loopOut_eq_attLoop prims O sp βmin _ R _ _ _
    (fun cc t => Z (O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
      (reqMasks (M := M) (bmsg := bmsg) ((Sf).sk (keys s)) R m c'.1.1 cc t))))
    (fun cc t => ringOf_reprogBase_self sp hO hdisj R (bmsg R m) Z H _ _ hget _), hwt, hA,
    Option.map_some] at hr
  simp only [replyOf, hc.1, hc.2, and_self, ↓reduceIte, Option.map] at hr
  have hinter := w1Pts_inter_keepOf_eq sp hch hdisj hdisjg hPS h_laws hv henc keys hs2
    (fun _ => c') rs (.sign s R m) h' Z H hr
  simp only [keptPt] at hinter
  split_ifs at hinter with hR'
  swap
  · exact absurd hR hR'
  simp only [Option.map, replyOf, hc.1, hc.2, and_self, ↓reduceIte]
  rw [filter_reprogAssigns sp Z H, filter_toList_eq_singleton hinter]
  simp only [repOf, keptAsg, reprogAssigns, List.map_cons, List.map_nil, List.zip_cons_cons,
    List.zip_nil_left]
  rw [prove_run_reprogBase_eq sp hch hPS _ _ _ mu Z H]
  simp only [hw1]
  rfl

/-! ### The kept-only challenger against independent base values -/

omit [Fintype X] [NeZero (bucketCount p)] nttOps [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [DecidableEq X] [AddGroup Y] [Fintype Y₁]
  [DecidableEq Y₁] [NeZero D] in
/-- **The masks of the attempts at one point of the mask functions are uniform**, for a uniform
mask decoding. -/
theorem map_masks_uniformOfFintype [Fintype Y] [Nonempty Y] [DecidableEq Y]
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (b₀ : Bytes 32 × (Bytes 64 × Msg)) :
    (PMF.uniformOfFintype (Fin k → MaskPt T Msg → Y)).map
        (fun g (a : Fin k × Fin T) => M.ans (g a.1 (a.2, b₀))) =
      PMF.uniformOfFintype (Fin k × Fin T → MaskBox p) := by
  classical
  let emb : Fin k × Fin T ↪ Fin k × MaskPt T Msg :=
    ⟨fun a => (a.1, (a.2, b₀)), fun a b h => by
      simp only [Prod.mk.injEq] at h
      exact Prod.ext h.1 h.2.1⟩
  have h : (fun g : Fin k → MaskPt T Msg → Y => fun a : Fin k × Fin T => M.ans (g a.1 (a.2, b₀))) =
      (fun f a => M.ans (f a)) ∘ (fun G a => G (emb a)) ∘ (Equiv.curry _ _ _).symm := rfl
  rw [h, ← PMF.map_comp, ← PMF.map_comp, PMF.map_uniformOfFintype_equiv,
    PMF.map_comp_embedding_uniformOfFintype, PMF.map_comp_uniformOfFintype _ hMask]

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [Fintype X] [AddGroup Y] in
/-- **The commitment-hash point of a uniform mask is a given point** with probability at most
`commitPointMax`, for an injective point map. -/
theorem toReal_chPt_maskBox_le (hch : Function.Injective O.chPt) (aHat : TqMatrix p.k p.l)
    (mu : Bytes 64) (x : X) :
    ((PMF.uniformOfFintype (MaskBox p)).toOuterMeasure
      {y | O.chPt (mu, realBuckets aHat y) = x}).toReal ≤ commitPointMax aHat := by
  classical
  by_cases hx : ∃ w, O.chPt (mu, w) = x
  · obtain ⟨w, rfl⟩ := hx
    have hiff : {y : MaskBox p | O.chPt (mu, realBuckets aHat y) = O.chPt (mu, w)} =
        {b | realBuckets aHat b = w} := by
      ext y
      exact ⟨fun he => (Prod.mk.inj (hch he)).2, fun he => by
        change O.chPt (mu, realBuckets aHat y) = O.chPt (mu, w)
        rw [show realBuckets aHat y = w from he]⟩
    rw [hiff]
    have : (PMF.uniformOfFintype (MaskBox p)).toOuterMeasure {b | realBuckets aHat b = w} =
        ((maskUniform p).map (realBuckets aHat)) w := by
      rw [PMF.map_apply, PMF.toOuterMeasure_apply, maskUniform]
      refine tsum_congr fun b => ?_
      by_cases hb : realBuckets aHat b = w
      · simp [Set.indicator, hb]
      · have hb' : ¬ w = realBuckets aHat b := fun h => hb h.symm
        simp [Set.indicator, hb, hb']
    rw [this]
    exact toReal_map_realBuckets_le_commitPointMax aHat w
  · push Not at hx
    have hemp : {y : MaskBox p | O.chPt (mu, realBuckets aHat y) = x} = ∅ :=
      Set.eq_empty_of_forall_notMem fun y hy => hx _ hy
    rw [hemp, MeasureTheory.measure_empty, ENNReal.toReal_zero]
    exact (ENNReal.toReal_nonneg).trans
      (toReal_map_realBuckets_le_commitPointMax aHat (Classical.arbitrary _))

variable (O enc PS Of βmin) in
/-- **The intermediate reply to a signing request**: `repOf` of the loop of ideal attempts at
independent pairs of a mask and a base value (the side coins `x.1`), with the prover coins
`x.2`. -/
noncomputable def intRep (sp : Y ≃+ Y₁ × Y₂) (H : X → Y) (pk : PubKey p prims) (sk : SecretKey p)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length) (m : RMsg)
    (x : KFCoins (p := p) (T := T) k D Y₁ × (PS).Coins) :
    Reply X Y (UnforgeResponse (S := Sf) Of) :=
  repOf O enc PS Of sp H pk R m x.2
    (attLoop (outWt (ringWt O βmin sk R i (bmsg R m) H))
      (fun c t => intAttV prims O sp sk (prims.expandA sk.rho) (x.1.1 c t)) x.1.2)

open Classical in
omit [Fintype Pf] [DecidableEq Pf] in
/-- **The kept-only challenger against the intermediate, at a signing request** (identical until
two attempts share a commitment-hash point): for a signer in a supported ring passing the checks
at the oracle `H`, with honest keys, the law of the challenger's reply over the request's coins
(a fresh base function and the signing coins, uniform) is within total variation
`C(k T, 2) · commitPointMax(Â_s)` of the law of `intRep` over uniform side and prover coins. The
reply is `intRep` at the masks and the fresh base values at the masks' points
(`run_w1C1_sign`); those values are independent and uniform when the points are distinct
(`PMF.tvDist_map_pullback_le`), and two of the `k T` uniform masks share a point with
probability at most `C(k T, 2) · commitPointMax` (`PMF.toReal_not_injective_le`). -/
theorem tvDist_w1C1_intRep_le (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    {Q : ℕ}
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (s : Fin n) (R : KeyRing (PubKey p prims) N) (m : RMsg) (hR : (Bf).pk (keys s) ∈ R.1)
    (h : hist.length < Q) (H : X → Y)
    (hc : adm R ∧ RingCheck prims βmin tol (O.gOrc H) R ∧
      MuDistinct prims (O.muOrc H) R (bmsg R m)) :
    PMF.tvDist ((prodLaw (PMF.uniformOfFintype (X → Y₁)) (PMF.uniformOfFintype (Sf).SignCoins)).map
        fun u => ((w1C1 Of sp keys Q).respond (fun _ : Fin Q => u.1, fun _ : Fin Q => u.2) hist
          (.sign s R m)).run H)
      ((PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁ ×
          (PS).Coins)).map
        (intRep O βmin enc PS Of sp H ((Bf).pk (keys s)) ((Sf).sk (keys s)) R
          ⟨_, idxOf_lt_of_mem keys hR⟩ m)) ≤
      ((k * T).choose 2 : ℝ) * commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := by
  let _ : Fintype (Fin k → MaskPt T Msg → Y) := Pi.instFintype
  set b₀ : Bytes 32 × (Bytes 64 × Msg) :=
    (((Sf).sk (keys s)).key, (((Sf).sk (keys s)).tr, bmsg R m)) with hb₀
  set mu := O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m))) with hmu
  set F : (Fin k × Fin T → MaskBox p × Y₁) →
      (Fin k → Fin D) × (PS).Coins →
      Reply X Y (UnforgeResponse (S := Sf) Of) := fun xs w =>
    intRep O βmin enc PS Of sp H ((Bf).pk (keys s)) ((Sf).sk (keys s)) R
      ⟨_, idxOf_lt_of_mem keys hR⟩ m ((fun c t => xs (c, t), w.1), w.2) with hF
  have hL : (prodLaw (PMF.uniformOfFintype (X → Y₁)) (PMF.uniformOfFintype (Sf).SignCoins)).map
      (fun u => ((w1C1 Of sp keys Q).respond (fun _ : Fin Q => u.1, fun _ : Fin Q => u.2) hist
        (.sign s R m)).run H) =
      (PMF.uniformOfFintype ((X → Y₁) × (Fin k → MaskPt T Msg → Y) ×
          ((Fin k → Fin D) × (PS).Coins))).map
        fun u => F (fun a => (M.ans (u.2.1 a.1 (a.2, b₀)),
          u.1 (O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
            (M.ans (u.2.1 a.1 (a.2, b₀))))))) u.2.2 := by
    rw [PMF.prodLaw_uniformOfFintype]
    let e : (X → Y₁) × (Sf).SignCoins ≃ (X → Y₁) × (Fin k → MaskPt T Msg → Y) ×
        ((Fin k → Fin D) × (PS).Coins) :=
      { toFun := fun u => (u.1, u.2.1.1, u.2.1.2, u.2.2)
        invFun := fun u => (u.1, (u.2.1, u.2.2.1), u.2.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← PMF.map_uniformOfFintype_comp_equiv' e]
    congr 1
    funext u
    refine (run_w1C1_sign sp hO hch hdisj hdisjg hPS h_laws hv henc keys u.1 u.2 hist s R m hs2
      hR h H).trans ?_
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    rfl
  have hR' : (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁ ×
        (PS).Coins)).map
      (intRep O βmin enc PS Of sp H ((Bf).pk (keys s)) ((Sf).sk (keys s)) R
        ⟨_, idxOf_lt_of_mem keys hR⟩ m) =
      (PMF.uniformOfFintype ((Fin k × Fin T → MaskBox p × Y₁) ×
          ((Fin k → Fin D) × (PS).Coins))).map fun x => F x.1 x.2 := by
    let e : KFCoins (p := p) (T := T) k D Y₁ × (PS).Coins ≃
        (Fin k × Fin T → MaskBox p × Y₁) × ((Fin k → Fin D) ×
          (PS).Coins) :=
      { toFun := fun x => (fun a => x.1.1 a.1 a.2, x.1.2, x.2)
        invFun := fun x => ((fun c t => x.1 (c, t), x.2.1), x.2.2)
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    rw [← PMF.map_uniformOfFintype_comp_equiv' e]
    rfl
  rw [hL, hR']
  have key := PMF.tvDist_map_pullback_le (ι := Fin k × Fin T) (G := Fin k → MaskPt T Msg → Y)
    (W := (Fin k → Fin D) × (PS).Coins) (V := MaskBox p) (X' := X) (Y' := Y₁)
    (fun g a => M.ans (g a.1 (a.2, b₀))) (map_masks_uniformOfFintype hMask b₀)
    (fun y => O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho) y)) F
  refine le_trans (le_of_eq ?_) (key.trans ?_)
  · congr 1
  · have hcard : Fintype.card (Fin k × Fin T) = k * T := by simp
    rw [← hcard]
    have hδ : ∀ x, ((PMF.uniformOfFintype (MaskBox p)).toOuterMeasure
        {y | O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho) y) = x}).toReal ≤
        commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := fun x =>
      toReal_chPt_maskBox_le hch (prims.expandA ((Sf).sk (keys s)).rho) mu x
    have key2 := PMF.toReal_not_injective_le (ι := Fin k × Fin T)
      (fun y => O.chPt (mu, realBuckets (prims.expandA ((Sf).sk (keys s)).rho) y)) hδ
    convert key2 using 4

/-! ### The intermediate and the key-free signer -/

omit [Fintype X] [NeZero (bucketCount p)] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] [DecidableEq X] [AddGroup Y] in
/-- The keep weight of the ring loop from the signer's `t₀`. -/
theorem ringWt_eq (sk : SecretKey p) (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length)
    (bm : Msg) (H : X → Y) :
    ringWt O βmin sk R i bm H =
      fun vc => PMF.flattenKeep (fun a => (t0Weight prims sk.t0 a : ℝ≥0∞)) βmin vc *
      (ringWeights prims βmin (ringT0s prims R.1)).otherWeight i
        (PMF.ringOf (ringPts prims R.1 bm) (O.hOrc H)) vc.1 :=
  funext fun vc => by
    rw [ringWt, coe_flattenCoin]
    rfl

variable (O βmin enc PS Of) in
/-- **The key-free reply to a signing request**: `repOf` of the key-free loop of the published key
`pk` (`kfLoop`) at the members' commitment hashes read from `H`, with the prover coins `x.2`. -/
noncomputable def kfRep (sp : Y ≃+ Y₁ × Y₂) (H : X → Y) (pk : PubKey p prims)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length) (m : RMsg)
    (x : KFCoins (p := p) (T := T) k D Y₁ × (PS).Coins) :
    Reply X Y (UnforgeResponse (S := Sf) Of) :=
  repOf O enc PS Of sp H pk R m x.2
    (kfLoop prims O sp βmin pk R i (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) x.1)

omit [Fintype X] [DecidableEq Y₁] [Fintype Pf] [DecidableEq Pf] [DecidableEq PC] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The intermediate and the key-free reply have the same law** over uniform side and prover
coins, for an honest key (`‖s₁‖∞, ‖s₂‖∞ ≤ η`, the signing and verification laws, a coherent
encoding): at each commitment hash, a permutation of the masks carries the ideal attempt to the
key-free one (`exists_equiv_keyFreeAttempt_fiber`); applied to every attempt with its base value
kept, it carries the intermediate loop to the key-free loop, the signer's flattening coin being a
function of its published `t₀`. -/
theorem map_intRep_eq_map_kfRep [Nonempty Y₁] (sp : Y ≃+ Y₁ × Y₂)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (seed : Bytes 32) (hs1 : polyVecBounded (keyGen prims seed).2.s1 p.eta)
    (hs2 : polyVecBounded (keyGen prims seed).2.s2 p.eta) (H : X → Y)
    (R : KeyRing (PubKey p prims) N) (i : Fin R.1.length) (m : RMsg) :
    (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁ ×
        (PS).Coins)).map
        (intRep O βmin enc PS Of sp H (keyGen prims seed).1 (keyGen prims seed).2 R i m) =
      (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁ ×
        (PS).Coins)).map
        (kfRep O βmin enc PS Of sp H (keyGen prims seed).1 R i m) := by
  have hfib : ∀ c : CommitHashBytes p, ∃ σ : MaskBox p ≃ MaskBox p, ∀ y,
      keyFreeAttempt prims (pubPk prims (keyGen prims seed).1) (keyGen prims seed).1.2.2 (σ y, c) =
        idealAttemptW1 prims (keyGen prims seed).2 (prims.expandA (keyGen prims seed).2.rho)
          (y, c) := fun c =>
    exists_equiv_keyFreeAttempt_fiber h_laws hv henc (seed := seed)
      (pk := (keyGenFromSeed p prims seed).1) (sk := (keyGenFromSeed p prims seed).2) rfl hs1 hs2 c
  choose τf hτf using hfib
  let τ : MaskBox p × Y₁ ≃ MaskBox p × Y₁ :=
    { toFun := fun yv => (τf (chOf O sp yv.2) yv.1, yv.2)
      invFun := fun zv => ((τf (chOf O sp zv.2)).symm zv.1, zv.2)
      left_inv := fun yv => by simp
      right_inv := fun zv => by simp }
  let e : KFCoins (p := p) (T := T) k D Y₁ × (PS).Coins ≃
      KFCoins (p := p) (T := T) k D Y₁ × (PS).Coins :=
    { toFun := fun x => ((fun c t => τ (x.1.1 c t), x.1.2), x.2)
      invFun := fun x => ((fun c t => τ.symm (x.1.1 c t), x.1.2), x.2)
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  rw [← PMF.map_uniformOfFintype_comp_equiv' e
    (kfRep O βmin enc PS Of sp H (keyGen prims seed).1 R i m)]
  refine congrArg (fun f => PMF.map f _) (funext fun x => ?_)
  unfold intRep kfRep kfLoop
  have hatt : (fun c t => kfAttV prims O sp (pubPk prims (keyGen prims seed).1)
      (keyGen prims seed).1.2.2 ((e x).1.1 c t)) = fun c t => intAttV prims O sp
        (keyGen prims seed).2 (prims.expandA (keyGen prims seed).2.rho) (x.1.1 c t) := by
    funext c t
    simp only [intAttV, kfAttV, e, τ, Equiv.coe_fn_mk, hτf]
  have ht0 : (keyGen prims seed).1.2.2 = (keyGen prims seed).2.t0 := rfl
  rw [hatt, ht0, ringWt_eq]
  rfl

/-! ### The kept-only challenger's other replies -/

omit [Fintype Pf] [DecidableEq Pf] in
/-- **The kept-only challenger's reply to a corruption**: the user's key coins, no assignment. -/
theorem run_w1C1_corrupt (sp : Y ≃+ Y₁ × Y₂) (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (Z : X → Y₁)
    (c' : (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (i : Fin n) (h : hist.length < Q) (H : X → Y) :
    ((w1C1 Of sp keys Q).respond (fun _ : Fin Q => Z, fun _ : Fin Q => c') hist
        (.corrupt i)).run H = ⟨some (.keyCoins (keys i)), []⟩ := by
  refine (Challenger.run_respond_preReprogKeep (C₀ := unforgeChallenger Sf n Of keys Q) (sp := sp)
    (pts := w1Pts Of keys) (qp := 1) (K := k * T) (hqp := w1Pts_queries keys)
    (hK := card_w1Pts_le keys) (w1KeptPts Of) (fun _ => Z) (fun _ => c') hist (.corrupt i) H
    h).trans ?_
  have hp : (w1Pts Of keys (fun _ : Fin Q => c') hist (.corrupt i)).run H = ∅ := by
    simp [w1Pts]
  have hr : ∀ H' : X → Y, ((unforgeChallenger Sf n Of keys Q).respond (fun _ : Fin Q => c') hist
      (.corrupt i)).run H' = ⟨some (.keyCoins (keys i)), []⟩ := fun H' => by
    simp only [unforgeChallenger, h, ↓reduceDIte]
    rfl
  simp only [hp, hr, Finset.toList_empty, List.map_nil]
  rfl

omit [Fintype Pf] [DecidableEq Pf] in
/-- **The kept-only challenger's reply to a signing request by a user outside the ring**: no
response, no assignment. -/
theorem run_w1C1_sign_not_mem (sp : Y ≃+ Y₁ × Y₂) (keys : Fin n → (Sf).KeyCoins) {Q : ℕ}
    (Z : X → Y₁) (c' : (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (s : Fin n) (R : KeyRing (PubKey p prims) N) (m : RMsg) (hR : (Bf).pk (keys s) ∉ R.1)
    (h : hist.length < Q) (H : X → Y) :
    ((w1C1 Of sp keys Q).respond (fun _ : Fin Q => Z, fun _ : Fin Q => c') hist
        (.sign s R m)).run H = ⟨none, []⟩ := by
  refine (Challenger.run_respond_preReprogKeep (C₀ := unforgeChallenger Sf n Of keys Q) (sp := sp)
    (pts := w1Pts Of keys) (qp := 1) (K := k * T) (hqp := w1Pts_queries keys)
    (hK := card_w1Pts_le keys) (w1KeptPts Of) (fun _ => Z) (fun _ => c') hist (.sign s R m) H
    h).trans ?_
  have hp : (w1Pts Of keys (fun _ : Fin Q => c') hist (.sign s R m)).run H = ∅ := by
    unfold w1Pts
    simp only [h, ↓reduceDIte]
    split_ifs with hR'
    · exact absurd hR' hR
    · rfl
  have hr : ∀ H' : X → Y, ((unforgeChallenger Sf n Of keys Q).respond (fun _ : Fin Q => c') hist
      (.sign s R m)).run H' = ⟨none, []⟩ := fun H' => by
    simp only [unforgeChallenger, h, ↓reduceDIte]
    split_ifs with hR'
    · exact absurd hR' hR
    · rfl
  simp only [hp, hr, Finset.toList_empty, List.map_nil]
  rfl

end KeptOnly

/-! ### The key-free relay challenger -/

section KeyFreeChal

open GordieHowe.Signature

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {Pf PCs : Type} [Fintype Pf] [DecidableEq Pf] [Fintype PCs]
  [DecidableEq PCs] [Nonempty PCs]
  {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg))
    (RingSignature.RingWitOf (FIPSSignature p prims)) ⟨Pf, PCs⟩}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  {Stmt Wit X₀ Rq PC : Type} [Fintype PC] [DecidableEq PC]

local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg
local notation "PSf" => PS

omit [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Y] [DecidableEq Y] [Nonempty Y] [NeZero D] [Fintype RMsg]
  [DecidableEq RMsg] in
/-- The decidability of the supported rings at the fresh base signer's ring type. -/
abbrev admDecF : DecidablePred (α := KeyRing (PubKey p prims) N) adm := hadm

attribute [local instance] admDecF


variable (prims O M βmin tol enc k D bmsg PS adm) in
/-- **The key-free relay challenger of the fresh-mask ring game** (`C₂`): coins the side coins of
each request and the coins of the main challenger `kfMain` (the multi-user challenger without
messages and the real proof challenger of `P` on the relation `rel`, proof queries encoded by
`penc`); request `r` after the history `hist` answered by the outer challenger of the key-free
relay (`KeyFree.kfGame`) at the side coins, with the key-free signer `w1KFSign`, the statement
program `stmtP`, the proof requests `toR` and the dummy requests `dummyR`. -/
noncomputable def w1C2 (sp : Y ≃+ Y₁ × Y₂) (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf PC) (μ : PMF PC)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (keys : Fin n → (Bf).KeyCoins) (Q : ℕ) :
    Challenger X Y (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm)
    where
  Coins := (Fin Q → KFCoins (p := p) (T := T) k D Y₁) ×
    (RingSignature.kfMain Bf rel P μ penc keys Q).Coins
  coins := prodLaw (PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁))
    (RingSignature.kfMain Bf rel P μ penc keys Q).coins
  Q := Q
  q := w1KFq N reps k T + qs + (RingSignature.kfMain Bf rel P μ penc keys Q).q
  respond ω hist r :=
    (RingSignature.KeyFree.kfGame (RingSignature.kfMain Bf rel P μ penc keys Q)
      (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
        (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR ω.1
        (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle)
          Q).respond ω.2 hist r
  respond_queries ω hist r H :=
    (RingSignature.KeyFree.kfGame (RingSignature.kfMain Bf rel P μ penc keys Q)
      (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
        (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR ω.1
        (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle)
          Q).respond_queries ω.2 hist r H

omit [Fintype X] [DecidableEq X] [AddGroup Y] [Fintype Pf] [DecidableEq Pf] [Fintype Msg]
  [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The main challenger reads only the proof coins of the request count**, below the cap (its
multi-user coins are trivial). -/
theorem kfMain_respond_eq_const (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf PC) (μ : PMF PC)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (keys : Fin n → (Bf).KeyCoins) {Q : ℕ} (u : Fin Q → Unit) (pc : Fin Q → PC)
    (hM : List (HistoryEntry (MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
      (MUResponse (Bf).core ⊕ Pf))) (r' : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (h : hM.length < Q) :
    (RingSignature.kfMain Bf rel P μ penc keys Q).respond (u, pc) hM r' =
      (RingSignature.kfMain Bf rel P μ penc keys Q).respond
        (fun _ : Fin Q => (), fun _ : Fin Q => pc ⟨hM.length, h⟩) hM r' := by
  have hu : u = fun _ => () := funext fun _ => rfl
  subst hu
  rcases r' with r' | q
  · rfl
  · have h' : (dummyHist penc hM).length < Q := by simpa [dummyHist] using h
    simp only [RingSignature.kfMain, Challenger.sumDummy, QROM.realChallenger, h', ↓reduceDIte]
    simp [dummyHist]

omit [Fintype X] [DecidableEq X] [AddGroup Y] [Fintype Pf] [DecidableEq Pf] [Fintype PCs]
  [DecidableEq PCs] [Nonempty PCs] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **The key-free signature of request number `c` reads only the side coins of that number.** -/
theorem sigP_eq_const {SC : Type}
    (ksign : (Bf).PK → KeyRing (PubKey p prims) N → ℕ → (Bf).Msg → SC →
      OracleProg X Y (Option ((Bf).Pub × (Bf).BSig × List (Assignment X Y))))
    (keys : Fin n → (Bf).KeyCoins) {Q : ℕ} (sc : Fin Q → SC) (c : ℕ) (hc : c < Q)
    (r : RingSignature.Insider.Req Bf PSf adm n) :
    RingSignature.KeyFree.sigP Bf (fun i => (Bf).pk (keys i)) ksign sc c r =
      RingSignature.KeyFree.sigP Bf (fun i => (Bf).pk (keys i)) ksign
        (fun _ : Fin Q => sc ⟨c, hc⟩) c r := by
  rcases r with i | ⟨s, Rg, m⟩ | ⟨i, bm⟩
  · rfl
  · simp only [RingSignature.KeyFree.sigP]
  · rfl

omit [Fintype X] [Fintype Pf] [DecidableEq Pf] [Fintype PCs] [DecidableEq PCs] [Nonempty PCs]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The key-free relay challenger at constant coins reads the coins of request `|hist|`.** -/
theorem run_w1C2_respond_eq_const (sp : Y ≃+ Y₁ × Y₂) (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf PC) (μ : PMF PC)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (keys : Fin n → (Bf).KeyCoins) {Q : ℕ} (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (u : Fin Q → Unit) (pc : Fin Q → PC)
    (hist : List (HistoryEntry (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)))
    (r : RingSignature.Insider.Req Bf PSf adm n) (h : hist.length < Q) (H : X → Y) :
    ((w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs idle keys
        Q).respond (sc, (u, pc)) hist r).run H =
      ((w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs idle keys
        Q).respond (fun _ : Fin Q => sc ⟨hist.length, h⟩,
          (fun _ : Fin Q => (), fun _ : Fin Q => pc ⟨hist.length, h⟩)) hist r).run H := by
  refine (RingSignature.KeyFree.run_kfGame_respond (RingSignature.kfMain Bf rel P μ penc keys Q)
    (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
      (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
      (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) Q (u, pc)
        hist r H).trans
    (Eq.trans ?_ (RingSignature.KeyFree.run_kfGame_respond
      (RingSignature.kfMain Bf rel P μ penc keys Q)
      (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
        (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
        (fun _ : Fin Q => sc ⟨hist.length, h⟩)
        (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) Q
      (fun _ : Fin Q => (), fun _ : Fin Q => pc ⟨hist.length, h⟩) hist r H).symm)
  have hM := RingSignature.KeyFree.length_mainHist_padHist (Q := Q)
    (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
      (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
      (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) hist
  have hm : (fun r' => (((RingSignature.kfMain Bf rel P μ penc keys Q).respond (u, pc)
      (AssignRelay.mainHist (RingSignature.KeyFree.padHist (Q := Q)
        (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
          (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
          (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) hist))
            r').run H).response) =
      fun r' => (((RingSignature.kfMain Bf rel P μ penc keys Q).respond
        (fun _ : Fin Q => (), fun _ : Fin Q => pc ⟨hist.length, h⟩)
        (AssignRelay.mainHist (RingSignature.KeyFree.padHist (Q := Q)
          (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
            (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
            (fun _ : Fin Q => sc ⟨hist.length, h⟩)
            (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) hist))
              r').run
          H).response := by
    funext r'
    have hp : RingSignature.KeyFree.padHist (Q := Q)
        (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
          (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR sc
          (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) hist =
        RingSignature.KeyFree.padHist (Q := Q)
          (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
            (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
            (fun _ : Fin Q => sc ⟨hist.length, h⟩)
            (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) hist :=
      RingSignature.KeyFree.padHist_congr _ _ hist
        ((RingSignature.KeyFree.idle_kfRelay ..).trans (RingSignature.KeyFree.idle_kfRelay ..).symm)
    simp only [hp]
    have hM' := RingSignature.KeyFree.length_mainHist_padHist (Q := Q)
      (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
        (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
        (fun _ : Fin Q => sc ⟨hist.length, h⟩)
        (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) hist
    have hl : (AssignRelay.mainHist (RingSignature.KeyFree.padHist (Q := Q)
        (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
          (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
          (fun _ : Fin Q => sc ⟨hist.length, h⟩)
          (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle)
            hist)).length < Q := by
      rw [hM']
      exact h
    simp only [kfMain_respond_eq_const rel P μ penc keys u pc _ r' hl]
    have hfin : (⟨(AssignRelay.mainHist (RingSignature.KeyFree.padHist (Q := Q)
        (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
          (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
          (fun _ : Fin Q => sc ⟨hist.length, h⟩)
          (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle)
            hist)).length, hl⟩ : Fin Q) =
        ⟨hist.length, h⟩ := Fin.ext hM'
    simp only [hfin]
  rw [hm]
  rw [RingSignature.KeyFree.elimProg_kfRelay (PS := PSf) (adm := adm) Bf
      (fun i => (Bf).pk (keys i)) (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg)
      stmtP toR dummyR sc (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs
      idle,
    RingSignature.KeyFree.elimProg_kfRelay (PS := PSf) (adm := adm) Bf
      (fun i => (Bf).pk (keys i)) (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg)
      stmtP toR dummyR (fun _ : Fin Q => sc ⟨hist.length, h⟩)
      (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle]
  simp only [RingSignature.KeyFree.kfProg]
  rw [sigP_eq_const (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg)
    keys sc hist.length h r]

variable (prims O M βmin tol enc k D bmsg PS adm) in
/-- **The key-free relay challenger reads a fresh coin per request** (`Challenger.FreshCoinsIn`):
no key, the coin of request `j` its side coins (uniform) and its proof coins (law `μ`), the
reply the challenger's at the constant coins. -/
noncomputable def w1C2FreshCoins (sp : Y ≃+ Y₁ × Y₂) (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf PC) (μ : PMF PC)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (keys : Fin n → (Bf).KeyCoins) (Q : ℕ) :
    (w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs idle keys
      Q).FreshCoinsIn (PMF.pure ())
      (prodLaw (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)) μ) where
  equiv :=
    { toFun := fun ω => ((), fun j => (ω.1 j, ω.2.2 j))
      invFun := fun x => (fun j => (x.2 j).1, (fun _ => (), fun j => (x.2 j).2))
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  coins_eq c := by
    rcases c with ⟨sc, u, pc⟩
    refine (prodLaw_apply (PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁))
      (RingSignature.kfMain Bf rel P μ penc keys Q).coins sc (u, pc)).trans ?_
    have hmain : (RingSignature.kfMain Bf rel P μ penc keys Q).coins (u, pc) =
        ∏ j, μ (pc j) := by
      refine (Challenger.coins_sumDummy (C₁ := muChallenger (X := X) (Y := Y) (SignOracle.none (Bf).core)
        n keys Q) (C₂ := QROM.realChallenger rel P μ Q) (enc := penc) u pc).trans ?_
      have h1 : (muChallenger (X := X) (Y := Y) (SignOracle.none (Bf).core) n keys Q).coins u = 1 := by
        exact (PMF.uniformOfFintype_apply (α := Fin Q → Unit) _).trans (by simp)
      rw [h1, one_mul]
      rfl
    have h2 : PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc =
        ∏ j, PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁) (sc j) := by
      rw [← PMF.pi_uniformOfFintype (β := fun _ : Fin Q => KFCoins (p := p) (T := T) k D Y₁)]; rfl
    rw [hmain, h2]
    simp only [PMF.pure_apply, ↓reduceIte, one_mul]
    exact Finset.prod_mul_distrib.symm.trans
      (Finset.prod_congr rfl fun j _ => (prodLaw_apply _ _ _ _).symm)
  kernel _ H hist r u :=
    ((w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs idle keys
      Q).respond (fun _ : Fin Q => u.1, (fun _ : Fin Q => (), fun _ : Fin Q => u.2)) hist r).run H
  respond_eq H c hist r hj := by
    rcases c with ⟨sc, u, pc⟩
    exact run_w1C2_respond_eq_const sp rel P μ penc stmtP toR dummyR hs idle keys sc u pc hist r hj H

omit [Fintype X] [Fintype Pf] [DecidableEq Pf] [Fintype PCs] [DecidableEq PCs] [Nonempty PCs]
  [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The reply of the key-free relay challenger at constant coins**: the relay's reply
(`KeyFree.replyOf`) of the key-free signature of the request (`KeyFree.sigP`) and the main
challenger's response to its main request. -/
theorem run_w1C2_const (sp : Y ≃+ Y₁ × Y₂) (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf PC) (μ : PMF PC)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (keys : Fin n → (Bf).KeyCoins) {Q : ℕ} (sc : KFCoins (p := p) (T := T) k D Y₁) (pc : PC)
    (hist : List (HistoryEntry (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)))
    (r : RingSignature.Insider.Req Bf PSf adm n) (H : X → Y) :
    ((w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs idle keys
        Q).respond (fun _ : Fin Q => sc, (fun _ : Fin Q => (), fun _ : Fin Q => pc)) hist r).run H =
      RingSignature.KeyFree.replyOf Bf r
        ((RingSignature.KeyFree.sigP Bf (fun i => (Bf).pk (keys i))
          (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (fun _ : Fin Q => sc)
            hist.length r).run H)
        (((RingSignature.kfMain Bf rel P μ penc keys Q).respond
          (fun _ : Fin Q => (), fun _ : Fin Q => pc)
          (AssignRelay.mainHist (RingSignature.KeyFree.padHist (Q := Q)
            (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
              (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
                (fun _ : Fin Q => sc)
              (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle) hist))
          (RingSignature.KeyFree.reqOf Bf toR dummyR hist.length r
            ((RingSignature.KeyFree.sigP Bf (fun i => (Bf).pk (keys i))
              (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (fun _ : Fin Q => sc)
                hist.length r).run
                H)
            ((RingSignature.KeyFree.xP Bf stmtP r
              ((RingSignature.KeyFree.sigP Bf (fun i => (Bf).pk (keys i))
                (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (fun _ : Fin Q => sc)
                  hist.length
                  r).run H)).run
              (H.reprogram (RingSignature.KeyFree.asgOf Bf
                ((RingSignature.KeyFree.sigP Bf (fun i => (Bf).pk (keys i))
                  (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (fun _ : Fin Q => sc)
                    hist.length
                    r).run H)))))).run H).response :=
  (RingSignature.KeyFree.run_kfGame_respond (RingSignature.kfMain Bf rel P μ penc keys Q)
    (RingSignature.KeyFree.kfRelay Bf (fun i => (Bf).pk (keys i))
      (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
        (fun _ : Fin Q => sc)
      (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle)
        Q _ hist r H).trans <| by
  erw [RingSignature.KeyFree.elimProg_kfRelay]
  exact RingSignature.KeyFree.run_kfProg Bf (fun i => (Bf).pk (keys i))
      (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
        (fun _ : Fin Q => sc) H _
      hist.length r

omit [Fintype X] [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [NeZero D]
  [Fintype Y₁] [DecidableEq Y₁] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **A kept key-free signature verifies at the oracle reprogrammed by its kept assignment**: its
response passes the z-check and its hint the hint count, its recomputed commitment is its
published value, and the commitment hash at the kept point is the commitment hash of its base
value, for decodings reading only the base component and message-representative points that are
not commitment-hash points. -/
theorem ringVerify_kfLoop (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N)
    (i : Fin R.1.length) (hc : Fin R.1.length × BucketVec p → CommitHashBytes p)
    (sc : KFCoins (p := p) (T := T) k D Y₁) {s : BucketVec p × FIPSSignature p prims × Y₁}
    (hs : kfLoop prims O sp βmin pk R i hc sc = some s) (H : X → Y) (bm : Msg) :
    ringVerify prims (O.hOrc (H.reprogram [keptAsg O enc sp H pk bm s.2.1 s.2.2])) enc
      (pubPk prims pk) bm (w1Of prims enc pk s.2.1) s.2.1 = true := by
  obtain ⟨c, t, hatt⟩ := exists_of_attLoop_eq_some hs
  unfold kfAttV keyFreeAttempt at hatt
  split_ifs at hatt with hacc
  swap
  · exact absurd hatt (by simp)
  obtain rfl := (Option.some.inj hatt).symm
  simp only [keyFreeAccept, Bool.and_eq_true, zCheck, hintCheck, decide_eq_true_eq] at hacc
  obtain ⟨⟨⟨hz, -⟩, -⟩, hh⟩ := hacc
  set σk := keyFreeSig prims (pubPk prims pk) pk.2.2 (sc.1 c t).1.1 (chOf O sp (sc.1 c t).2)
    with hσk
  set pt := O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bm))), w1Of prims enc pk σk) with hpt
  have hmu : (H.reprogram [keptAsg O enc sp H pk bm σk (sc.1 c t).2])
      (O.muPt (pubTr prims pk, bm)) = H (O.muPt (pubTr prims pk, bm)) := by
    rw [reprogram_singleton_apply]
    exact ite_eq_right_of_eq_false _ _ (eq_false (Ne.symm (hdisj _ _)))
  have hch : (H.reprogram [keptAsg O enc sp H pk bm σk (sc.1 c t).2]) pt =
      sp.symm ((sc.1 c t).2, (sp (H pt)).2) := by
    rw [reprogram_singleton_apply]
    exact ite_eq_left_of_eq_true _ _ (eq_true rfl)
  unfold ringVerify
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨hz, rfl⟩, ?_⟩, hh⟩
  simp only [MLDSAOracles.hOrc, schemeOrc, MLDSAOracles.muOrc, MLDSAOracles.chOrc]
  change O.chAns ((H.reprogram [keptAsg O enc sp H pk bm σk (sc.1 c t).2])
    (O.chPt (O.muAns ((H.reprogram [keptAsg O enc sp H pk bm σk (sc.1 c t).2])
      (O.muPt (pubTr prims pk, bm))), w1Of prims enc pk σk))) = chOf O sp (sc.1 c t).2
  rw [hmu, hch]
  exact hO.chAns_eq _ _ (by simp)

/-! ### The route-2 hypotheses -/

variable (enc) in
/-- **The proof query of a kept signature**: the encoded proof request of the statement program's
output on `(R, m, w1Of pk σ)` at the oracle `H'`, for the signing request `(s, R, m)` and the
signature `σ`. -/
noncomputable def keptQuery (penc : MURequest (SignOracle.none (Bf).core)
  n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (keys : Fin n → (Bf).KeyCoins) (s : Fin n) (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (c : ℕ) (σ : FIPSSignature p prims) (H' : X → Y) : QROM.ProofQuery Stmt Wit :=
  penc (.inr (toR ((stmtP ⟨R, m, w1Of prims enc ((Bf).pk (keys s)) σ⟩).run H') (.sign s R m, c)
    σ))

variable (O enc) in
/-- **The ring prover is the explicit-statement prover after the statement program** (route 2), at
the oracle reprogrammed by one assignment changing only a base component: the ring proof of
`(R, m, w1Of pk σ)` with the witness `(idx pk, σ)` at `H.reprogram [a]` is the main prover's proof
of the kept proof query (`keptQuery`, the statement read at `H.reprogram [a]`) at `H`. -/
def ProverRelays (sp : Y ≃+ Y₁ × Y₂) (P : NARG.Prover X Y Stmt Wit Pf (PSf).Coins)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (keys : Fin n → (Bf).KeyCoins) : Prop :=
  ∀ (s : Fin n) (R : KeyRing (PubKey p prims) N) (m : RMsg) (c : ℕ) (σ : FIPSSignature p prims)
    (cp : (PSf).Coins) (H : X → Y) (a : Assignment X Y), (sp a.output).2 = (sp (H a.input)).2 →
    ((PSf).prove ⟨R, m, w1Of prims enc ((Bf).pk (keys s)) σ⟩
        ⟨R.1.idxOf (α := PubKey p prims) ((Bf).pk (keys s)), σ⟩ cp).run (H.reprogram [a]) =
      (P.prog (keptQuery enc penc stmtP toR keys s R m c σ (H.reprogram [a])).stmt
        (keptQuery enc penc stmtP toR keys s R m c σ (H.reprogram [a])).wit cp).run H

variable (enc) in
/-- **Kept signatures are in the explicit relation**: a base signature of user `s`, a member of the
supported ring `R`, verifying on `bmsg R m` at an oracle `H'` makes its kept proof query
(`keptQuery`, at `H'`) a member of the relation `rel` (the completeness of the explicit relation).
-/
def KeptInRel (rel : Stmt → Wit → Prop)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (keys : Fin n → (Bf).KeyCoins) : Prop :=
  ∀ (s : Fin n) (R : KeyRing (PubKey p prims) N) (m : RMsg) (c : ℕ) (σ : FIPSSignature p prims)
    (H' : X → Y), (Bf).pk (keys s) ∈ R.1 → adm R →
    (Bf).bverify H' ((Bf).pk (keys s)) ((Bf).bmsg R m) σ = true →
    rel (keptQuery enc penc stmtP toR keys s R m c σ H').stmt
      (keptQuery enc penc stmtP toR keys s R m c σ H').wit

omit [Fintype X] [Fintype Y₁] [DecidableEq Y₁] [Fintype Pf] [DecidableEq Pf] [Fintype PCs]
  [DecidableEq PCs] [Nonempty PCs] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **`ProverRelays` holds for a factored ring prover** (its satisfiability): when the ring prover
runs the statement program and then the main prover on a statement and witness read from the
program's output (`hfac`), the kept proof query encodes that statement and witness (`hq`), and
the main prover reads only the second components of the oracle (`hP`). -/
theorem proverRelays_of_factor (sp : Y ≃+ Y₁ × Y₂)
    (P : NARG.Prover X Y Stmt Wit Pf (PSf).Coins)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (keys : Fin n → (Bf).KeyCoins) (st : X₀ → RingSignature.RingWitOf (FIPSSignature p prims) → Stmt)
    (wt : X₀ → RingSignature.RingWitOf (FIPSSignature p prims) → Wit)
    (hfac : ∀ x w cp, (PSf).prove x w cp = (stmtP x).bind fun x₀ => P.prog (st x₀ w) (wt x₀ w) cp)
    (hq : ∀ s (R : KeyRing (PubKey p prims) N) (m : RMsg) (c : ℕ) (σ : FIPSSignature p prims)
      (x₀ : X₀), penc (.inr (toR x₀ (.sign s R m, c) σ)) =
        ⟨st x₀ ⟨R.1.idxOf (α := PubKey p prims) ((Bf).pk (keys s)), σ⟩,
          wt x₀ ⟨R.1.idxOf (α := PubKey p prims) ((Bf).pk (keys s)), σ⟩⟩)
    (hP : ∀ x w cp (H H' : X → Y), (∀ z, (sp (H z)).2 = (sp (H' z)).2) →
      (P.prog x w cp).run H = (P.prog x w cp).run H') :
    ProverRelays O enc sp P penc stmtP toR keys := by
  intro s R m c σ cp H a ha
  rw [hfac, OracleProg.run_bind]
  unfold keptQuery
  rw [hq]
  refine hP _ _ _ _ _ fun z => ?_
  rw [reprogram_singleton_apply]
  split_ifs with hz
  · rw [ha, hz]
  · rfl

omit [Fintype X] [DecidableEq X] [AddGroup Y] [Fintype Pf] [DecidableEq Pf] [Fintype PCs]
  [DecidableEq PCs] [Nonempty PCs] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] in
/-- **`KeptInRel` holds for a relation holding on every proof query** (its satisfiability). -/
theorem keptInRel_of_forall (rel : Stmt → Wit → Prop)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (keys : Fin n → (Bf).KeyCoins) (h : ∀ q : QROM.ProofQuery Stmt Wit, rel q.stmt q.wit) :
    KeptInRel enc rel penc stmtP toR keys :=
  fun _ _ _ _ _ _ _ _ _ => h _

/-! ### The key-free relay challenger's reply to a signing request -/

omit [Fintype X] [Fintype Pf] [DecidableEq Pf] [Nonempty PCs] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] in
open Classical in
/-- **The reply of the key-free relay challenger to a signing request** at constant coins, for a
signer in a supported ring: on a ring passing the checks at the oracle `H`, the key-free reply
`kfRep`; a refusal with no assignment otherwise. The relay's proof is the main prover's on the
kept proof query, which is the ring prover's at the oracle reprogrammed by the kept assignment
(`ProverRelays`); the query is in the relation since the kept signature verifies there
(`ringVerify_kfLoop`, `KeptInRel`). -/
theorem run_w1C2_sign (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf (PSf).Coins) (μ : PMF (PSf).Coins)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (keys : Fin n → (Bf).KeyCoins) (hPR : ProverRelays O enc sp P penc stmtP toR keys)
    (hKR : KeptInRel enc rel penc stmtP toR keys) {Q : ℕ}
    (sc : KFCoins (p := p) (T := T) k D Y₁) (pc : (PSf).Coins)
    (hist : List (HistoryEntry (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm)))
    (s : Fin n) (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (hi : R.1.idxOf (α := PubKey p prims) ((Bf).pk (keys s)) < R.1.length) (ha : adm R)
    (h : hist.length < Q) (H : X → Y) :
    ((w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs idle keys
        Q).respond (fun _ : Fin Q => sc, (fun _ : Fin Q => (), fun _ : Fin Q => pc)) hist
        (.sign s R m)).run H =
      if RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m) then
        kfRep O βmin enc PS (SideOracle.none (freshScheme prims O M βmin tol enc k D bmsg PS adm))
          sp H ((Bf).pk (keys s)) R ⟨_, hi⟩ m (sc, pc)
      else ⟨none, []⟩ := by
  have hR : (Bf).pk (keys s) ∈ R.1 := (List.idxOf_lt_length_iff (α := PubKey p prims)).1 hi
  have hc0 : hist.length < Q ∧ (fun i => (Bf).pk (keys i)) s ∈ R.1 ∧ adm R := ⟨h, hR, ha⟩
  have hrun := run_w1KFSign prims O sp βmin tol enc k D bmsg ((Bf).pk (keys s)) R hist.length m sc H
  by_cases hc : RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m)
  swap
  · have ho : (RingSignature.KeyFree.sigP (PS := PSf) (adm := adm) Bf (fun i => (Bf).pk (keys i))
        (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (fun _ : Fin Q => sc)
        hist.length (.sign s R m)).run H = none := by
      simp only [RingSignature.KeyFree.sigP]
      refine (congrArg (OracleProg.run H) (dite_eq_left_of_eq_true (eq_true hc0))).trans
        (hrun.trans ?_)
      exact ite_eq_right_of_eq_false _ _ (eq_false hc)
    refine (RingSignature.KeyFree.run_kfGame_sign_none Bf rel P μ penc keys
      (fun i => (Bf).pk (keys i)) (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP
      toR dummyR (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle
      (fun _ : Fin Q => sc) _ hist s R m H ho).trans ?_
    exact (ite_eq_right_of_eq_false _ _ (eq_false hc)).symm
  have hloop : (w1KFSign prims O sp βmin tol enc k D bmsg ((Bf).pk (keys s)) R hist.length m
      sc).run H = (kfLoop prims O sp βmin ((Bf).pk (keys s)) R ⟨_, hi⟩
        (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) sc).map fun s' =>
        (w1Of prims enc ((Bf).pk (keys s)) s'.2.1, s'.2.1,
          [keptAsg O enc sp H ((Bf).pk (keys s)) (bmsg R m) s'.2.1 s'.2.2]) := by
    refine hrun.trans ?_
    rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
    exact dite_eq_left_of_eq_true (eq_true hi)
  rcases hk : kfLoop prims O sp βmin ((Bf).pk (keys s)) R ⟨_, hi⟩
    (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) sc with _ | sres
  · have ho : (RingSignature.KeyFree.sigP (PS := PSf) (adm := adm) Bf (fun i => (Bf).pk (keys i))
        (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (fun _ : Fin Q => sc)
        hist.length (.sign s R m)).run H = none := by
      simp only [RingSignature.KeyFree.sigP]
      refine (congrArg (OracleProg.run H) (dite_eq_left_of_eq_true (eq_true hc0))).trans
        (hloop.trans ?_)
      rw [hk]
      rfl
    refine (RingSignature.KeyFree.run_kfGame_sign_none Bf rel P μ penc keys
      (fun i => (Bf).pk (keys i)) (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP
      toR dummyR (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle
      (fun _ : Fin Q => sc) _ hist s R m H ho).trans ?_
    refine Eq.trans ?_ (ite_eq_left_of_eq_true _ _ (eq_true hc)).symm
    exact (congrArg (repOf O enc PS (SideOracle.none (freshScheme prims O M βmin tol enc k D bmsg
      PS adm)) sp H ((Bf).pk (keys s)) R m pc) hk).symm
  have ho : (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg ((Bf).pk (keys s)) R
      hist.length m sc).run H = some (w1Of prims enc ((Bf).pk (keys s)) sres.2.1, sres.2.1,
        [keptAsg O enc sp H ((Bf).pk (keys s)) (bmsg R m) sres.2.1 sres.2.2]) := by
    rw [hloop, hk]
    rfl
  have hrel := hKR s R m hist.length sres.2.1 (H.reprogram [keptAsg O enc sp H ((Bf).pk (keys s))
      (bmsg R m)
    sres.2.1 sres.2.2]) hR ha (ringVerify_kfLoop sp hO hdisj ((Bf).pk (keys s)) R ⟨_, hi⟩ _ sc hk H
      (bmsg R m))
  refine (RingSignature.KeyFree.run_kfGame_sign_some Bf rel P μ penc keys
    (fun i => (Bf).pk (keys i)) (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP
    toR dummyR (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle
    (fun _ : Fin Q => sc) (fun _ : Fin Q => (), fun _ : Fin Q => pc) hist s R m hc0 H _ _ _ ho
    hrel).trans ?_
  refine Eq.trans ?_ (ite_eq_left_of_eq_true _ _ (eq_true hc)).symm
  refine Eq.trans ?_ (congrArg (repOf O enc PS (SideOracle.none (freshScheme prims O M βmin tol enc
    k D bmsg PS adm)) sp H ((Bf).pk (keys s)) R m pc) hk).symm
  have hpa := hPR s R m hist.length sres.2.1 pc H (keptAsg O enc sp H ((Bf).pk (keys s)) (bmsg R m)
      sres.2.1
    sres.2.2) (by simp [keptAsg])
  exact congrArg (fun π => (⟨some (.signature (w1Of prims enc ((Bf).pk (keys s)) sres.2.1, π)),
    [keptAsg O enc sp H ((Bf).pk (keys s)) (bmsg R m) sres.2.1 sres.2.2]⟩ :
      Reply X Y (UnforgeResponse (S := freshScheme prims O M βmin tol enc k D bmsg PS adm)
        (SideOracle.none (freshScheme prims O M βmin tol enc k D bmsg PS adm))))) hpa.symm

/-! ### The per-request bound -/

local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm

variable (prims O M βmin tol enc k D bmsg PS adm) in
/-- **The per-request bound of the hop**: `C(k T, 2) · commitPointMax(Â_s)` at a signing request
of user `s`, `0` at the other requests. -/
noncomputable def w1ReqBound (keys : Fin n → (Sf).KeyCoins)
    (r : UnforgeRequest (S := Sf) n (SideOracle.none Sf)) : ℝ :=
  match r with
  | .sign s _ _ => ((k * T).choose 2 : ℝ) * commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)
  | _ => 0

open Classical in
omit [Fintype Pf] [DecidableEq Pf] in
/-- **The kept-only challenger against the key-free relay challenger, request by request**: at
every oracle `H`, history of fewer than `Q` entries and request `r`, the law of the kept-only
challenger's reply over request `|hist|`'s coins (`w1C1FreshCoins`) is within total variation
`w1ReqBound r` of the law of the key-free relay challenger's (`w1C2FreshCoins`): equal replies at
corruptions and at signing requests the two refuse, and at a signing request by a member of a
supported ring passing the checks, `C(k T, 2) · commitPointMax(Â_s)` against the intermediate
(`tvDist_w1C1_intRep_le`), whose law is the key-free reply's (`map_intRep_eq_map_kfRep`), which
is the relay challenger's (`run_w1C2_sign`). Hypotheses: the kept-only challenger's
(`ProverReadsPub` and the honest keys' `‖s₂‖∞ ≤ η`, the signing and verification laws, a coherent
encoding, distinct points), a uniform mask decoding, decodings reading only the base component,
honest keys' `‖s₁‖∞ ≤ η`, uniform main prover coins, and the route-2 hypotheses
`ProverRelays` and `KeptInRel`. -/
theorem tvDist_w1C1_w1C2_le (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf (PSf).Coins) (μ : PMF (PSf).Coins)
    (hPc : μ = PMF.uniformOfFintype (PSf).Coins)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (keys : Fin n → (Bf).KeyCoins)
    (hs1 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s1 p.eta)
    (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hPR : ProverRelays O enc sp P penc stmtP toR keys)
    (hKR : KeptInRel enc rel penc stmtP toR keys) (Q : ℕ) (H : X → Y)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n (SideOracle.none Sf))
      (UnforgeResponse (S := Sf) (SideOracle.none Sf))))
    (r : UnforgeRequest (S := Sf) n (SideOracle.none Sf)) (hl : hist.length < Q) :
    PMF.tvDist ((prodLaw (PMF.uniformOfFintype (X → Y₁)) (PMF.uniformOfFintype (Sf).SignCoins)).map
        ((w1C1FreshCoins (SideOracle.none Sf) sp keys Q).kernel () H hist r))
      ((prodLaw (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)) μ).map
        ((w1C2FreshCoins prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs
          idle keys Q).kernel () H hist r)) ≤
      w1ReqBound prims O M βmin tol enc k D bmsg PS adm keys r := by
  have hnn : ∀ s, 0 ≤ ((k * T).choose 2 : ℝ) *
      commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := fun s =>
    mul_nonneg (by positivity) ((ENNReal.toReal_nonneg).trans
      (toReal_map_realBuckets_le_commitPointMax _ (Classical.arbitrary _)))
  rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · refine le_of_eq (PMF.tvDist_map_const_eq_zero _ _ _ _ ⟨some (.keyCoins (keys i)), []⟩
      (fun u => run_w1C1_corrupt sp keys u.1 u.2 hist i hl H) fun u => ?_)
    exact RingSignature.KeyFree.run_kfGame_corrupt Bf rel P μ penc keys (fun i => (Bf).pk (keys i))
      (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
      (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle
      (fun _ : Fin Q => u.1) _ hist i hl H
  · have hnone : ∀ (u : KFCoins (p := p) (T := T) k D Y₁ × (PSf).Coins),
        ¬ (hist.length < Q ∧ (Bf).pk (keys s) ∈ R.1 ∧ adm R) →
        ((w1C2FreshCoins prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs
          idle keys Q).kernel () H hist (.sign s R m) u) = ⟨none, []⟩ := fun u hn =>
      RingSignature.KeyFree.run_kfGame_sign_none Bf rel P μ penc keys (fun i => (Bf).pk (keys i))
        (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) stmtP toR dummyR
        (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) hs idle
        (fun _ : Fin Q => u.1) _ hist s R m H (by
          simp only [RingSignature.KeyFree.sigP]
          exact congrArg (OracleProg.run H) (dite_eq_right_of_eq_false (eq_false hn)))
    by_cases hR : (Bf).pk (keys s) ∈ R.1
    swap
    · refine le_of_eq_of_le (PMF.tvDist_map_const_eq_zero _ _ _ _ ⟨none, []⟩
        (fun u => run_w1C1_sign_not_mem sp keys u.1 u.2 hist s R m hR hl H)
        fun u => hnone u fun h => hR h.2.1) (hnn s)
    by_cases ha : adm R
    swap
    · refine le_of_eq_of_le (PMF.tvDist_map_const_eq_zero _ _ _ _ ⟨none, []⟩
        (fun u => (run_w1C1_sign sp hO hch hdisj hdisjg hPS h_laws hv henc keys u.1 u.2 hist s R m
          hs2 hR hl H).trans (ite_eq_right_of_eq_false _ _ (eq_false fun h => ha h.1)))
        fun u => hnone u fun h => ha h.2.2) (hnn s)
    have hi2 : R.1.idxOf (α := PubKey p prims) ((Bf).pk (keys s)) < R.1.length :=
      (List.idxOf_lt_length_iff (α := PubKey p prims)).2 hR
    by_cases hc : RingCheck prims βmin tol (O.gOrc H) R ∧
      MuDistinct prims (O.muOrc H) R (bmsg R m)
    swap
    · refine le_of_eq_of_le (PMF.tvDist_map_const_eq_zero _ _ _ _ ⟨none, []⟩
        (fun u => (run_w1C1_sign sp hO hch hdisj hdisjg hPS h_laws hv henc keys u.1 u.2 hist s R m
          hs2 hR hl H).trans (ite_eq_right_of_eq_false _ _ (eq_false fun h => hc h.2)))
        fun u => (run_w1C2_sign sp hO hdisj rel P μ penc stmtP toR dummyR hs idle keys hPR hKR u.1
          u.2 hist s R m hi2 ha hl H).trans (ite_eq_right_of_eq_false _ _ (eq_false hc))) (hnn s)
    have hi1 := idxOf_lt_of_mem keys hR
    have hi12 : (⟨_, hi1⟩ : Fin R.1.length) = ⟨_, hi2⟩ :=
      rfl
    have hB := tvDist_w1C1_intRep_le sp hO hMask hch hdisj hdisjg hPS h_laws hv henc keys hs2 hist s
      R m hR hl H ⟨ha, hc⟩
    have hC : (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁ × (PSf).Coins)).map
        (intRep O βmin enc PS (SideOracle.none Sf) sp H ((Bf).pk (keys s)) ((Sf).sk (keys s)) R
          ⟨_, hi1⟩ m) =
        (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁ × (PSf).Coins)).map
          (kfRep O βmin enc PS (SideOracle.none Sf) sp H ((Bf).pk (keys s)) R ⟨_, hi1⟩ m) :=
      map_intRep_eq_map_kfRep (PS := PS) (adm := adm) (Of := SideOracle.none Sf) sp h_laws hv
        henc (keys s) (hs1 s) (hs2 s) H R ⟨_, hi1⟩ m
    have hζ : prodLaw (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)) μ =
        PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁ × (PSf).Coins) := by
      rw [hPc, PMF.prodLaw_uniformOfFintype]
    have hK : (w1C2FreshCoins prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR
        dummyR hs idle keys Q).kernel () H hist (.sign s R m) =
        kfRep O βmin enc PS (SideOracle.none Sf) sp H ((Bf).pk (keys s)) R ⟨_, hi1⟩ m := by
      funext u
      refine (run_w1C2_sign sp hO hdisj rel P μ penc stmtP toR dummyR hs idle keys hPR hKR u.1
          u.2 hist s R m hi2 ha hl H).trans ((ite_eq_left_of_eq_true _ _ (eq_true hc)).trans ?_)
      exact congrArg (fun i => kfRep O βmin enc PS (SideOracle.none Sf) sp H ((Bf).pk (keys s)) R i
        m u) hi12.symm
    refine le_of_eq_of_le (congrArg (PMF.tvDist _) ((congrArg₂ PMF.map hK hζ).trans hC.symm)) ?_
    exact hB
  · exact bm.elim

open Classical in
/-- **The hop from the kept-only to the key-free relay challenger** (R3 → R4 of converted `w₁`
unforgeability): against every query-bounded adversary, the transcript with the answered
requests and the final oracle in force lies in every event with probability at most the
key-free relay challenger's plus `Q · C(k T, 2) · Σ_s commitPointMax(Â_s)`
(`transcriptLawIn_le_add_of_freshCoinsIn` at the per-request bound `tvDist_w1C1_w1C2_le`), under
its hypotheses. -/
theorem transcriptLawIn_w1C1_le_w1C2 [Nonempty X] (sp : Y ≃+ Y₁ × Y₂)
    (hO : O.ReadsFst sp)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (rel : Stmt → Wit → Prop) [DecidableRel rel]
    (P : NARG.Prover X Y Stmt Wit Pf (PSf).Coins) (μ : PMF (PSf).Coins)
    (hPc : μ = PMF.uniformOfFintype (PSf).Coins)
    (penc : MURequest (SignOracle.none (Bf).core) n ⊕ Rq → QROM.ProofQuery Stmt Wit)
    (stmtP : RingSignature.RingStmt Bf → OracleProg X Y X₀)
    (toR : X₀ → RingSignature.Insider.Req Bf PSf adm n × ℕ → (Bf).BSig → Rq)
    (dummyR : RingSignature.Insider.Req Bf PSf adm n × ℕ → Rq) {qs : ℕ}
    (hs : ∀ x, (stmtP x).QueriesLE qs) (idle : MURequest (SignOracle.none (Bf).core) n ⊕ Rq)
    (keys : Fin n → (Bf).KeyCoins)
    (hs1 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s1 p.eta)
    (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (hPR : ProverRelays O enc sp P penc stmtP toR keys)
    (hKR : KeptInRel enc rel penc stmtP toR keys) (Q : ℕ) {Out : Type} {t : ℕ}
    (𝒜 : QueryBoundedAdversary X Y (UnforgeRequest (S := Sf) n (SideOracle.none Sf))
      (UnforgeResponse (S := Sf) (SideOracle.none Sf)) Out t) (H : X → Y)
    (S : Set (Option (Out × List (UnforgeRequest (S := Sf) n (SideOracle.none Sf)) × (X → Y)))) :
    (𝒜.transcriptLawIn (w1C1 (SideOracle.none Sf) sp keys Q) H).toOuterMeasure S ≤
      (𝒜.transcriptLawIn (w1C2 prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR
        dummyR hs idle keys Q) H).toOuterMeasure S +
      Q * ENNReal.ofReal (((k * T).choose 2 : ℝ) *
        ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)) := by
  have hcp : ∀ s, 0 ≤ commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := fun s =>
    (ENNReal.toReal_nonneg).trans
      (toReal_map_realBuckets_le_commitPointMax _ (Classical.arbitrary _))
  have h := transcriptLawIn_le_add_of_freshCoinsIn (w1C1FreshCoins (SideOracle.none Sf) sp keys Q)
    (w1C2FreshCoins prims O M βmin tol enc k D bmsg PS adm sp rel P μ penc stmtP toR dummyR hs idle
      keys Q) rfl (fun _ => ENNReal.ofReal (((k * T).choose 2 : ℝ) *
        ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)))
    (fun κ O' hist r hl => by
      refine ENNReal.ofReal_le_ofReal ((tvDist_w1C1_w1C2_le sp hO hMask hch hdisj hdisjg hPS
        h_laws hv henc rel P μ hPc penc stmtP toR dummyR hs idle keys hs1 hs2 hPR hKR Q O' hist r
          hl).trans ?_)
      rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
      · exact mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => hcp s)
      · exact mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun s =>
          commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)) (fun s _ => hcp s)
          (Finset.mem_univ s)) (by positivity)
      · exact bm.elim) 𝒜 H S
  refine h.trans_eq ?_
  congr 1
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rfl

end KeyFreeChal

end GordieHowe.Ring.MLDSAW1
