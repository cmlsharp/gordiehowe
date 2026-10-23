-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.FullPast.ZeroKnowledge
public import GordieHowe.Model.IOP.FiatShamirLaw
public import GordieHowe.SPBCS.Merkle.LeafHidingAdaptive
public import GordieHowe.Foundations.ToMathlib.PMFTVJoint

@[expose] public section

/-!
# Unconditional witness indistinguishability: the series–parallel base model

Adaptive, multi-theorem, everlasting (statistical) witness indistinguishability (CY24 Definition
33.1.1, p. 426, at unbounded queries) of the compiled composite against a distinguisher that
receives the whole random oracle, for every compiler datum. This file holds the pieces at the
series–parallel base model (`GordieHowe.SPBCS.FullPast`); the namespace `GordieHowe.SPBCS` states the
theorem for the spBCS compiler with them (`GordieHowe/SPBCS/WitnessIndist.lean`). The argument, per
proof query at a fixed oracle:

1. *Leaf equivocation* (`GordieHowe.SPBCS.close_realLaw_idealLaw`): the honest proof is a function of
   its leaf (Merkle salt, digest) pairs (`GordieHowe.SPBCS.prove_eq_proofTr`); replacing them by
   uniform digests with Merkle salts drawn from their preimages, tree by tree in global round order,
   costs at most `|Pos| · leafDist h` (`GordieHowe.SPBCS.tvDist_leafPairs_causal_le`). A column
   reads only the digests of earlier rounds (`GordieHowe.SPBCS.rankCausal_colD`).
2. *The fixed-point laws* (`GordieHowe.SPBCS.close_idealLaw`): in the ideal law the proof is a kernel
   applied to the composite view, the digests and the Fiat–Shamir challenges, which are the unique
   self-consistent challenges (`GordieHowe.SPBCS.fsD_eq_iff`).
3. *The salt bound* (`GordieHowe.SPBCS.expect_sup'_fpDist_le`): the salt slices of the oracle are
   independent given its unlabeled part; on each slice the challenges are dominated by uniform ones
   up to `overrun + keyCollision (t.size n) k`.
4. *The leaf term* (`GordieHowe.SPBCS.expect_leafDist_le`) and *the hybrid* over the `Q` proof queries
   (`close_wiGameWith`).

The theorem (`GordieHowe.SPBCS.wiAdvantage_le`): `wiAdvantage ≤ Q · wiError δ |choices|`, `wiError δ c =
2 · leafTerm + 2δ + overrun + keyCollision (t.size n) k + saltTerm kS c`, from the observations of
two witnesses being at average distance at most `2δ` (`ObsClose`), which honest-verifier zero
knowledge of the composite at error `δ` gives (`obsClose_of_causalHVZK`).
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal BigOperators

variable {k kN kS L e : ℕ}

namespace Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X W : Type}
  {M : Base P t X k kN kS L e}

/-! ### Positions in global round order, and what the proof reveals -/

/-- **The global round of a position**: the global round of its message, its leaf's offset plus
the message's round. -/
def Pos.gIdx (q : M.Pos) : ℕ := q.leaf.off n + q.pos.msg.1.1

section Reveal

variable {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x}

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The view determines every write**, at any roots. -/
theorem Reveal.write_congr (Rv : M.Reveal E Qs) (x : X) (ρ : Chs P t) {tr tr' : FullTr P t}
    (h : Rv.MV.view tr = Rv.MV.view tr') (p : t.Leaf) (i : (P p.label).MessageIdx)
    (rts : Fin ((M.comp p.label).nTrees i) → Digest k) :
    (E p.label).write i (tr p i.1) rts = (E p.label).write i (tr' p i.1) rts := by
  have e := (Rv.writesOf_obs x ρ tr).symm.trans (h ▸ Rv.writesOf_obs x ρ tr')
  exact congrFun (congrFun (congrFun (Option.some_injective _ e) p) i) rts

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The view determines the column of every opened leaf.** -/
theorem Reveal.col_congr (Rv : M.Reveal E Qs) (x : X) (chs : (p : t.Leaf) → M.Items p)
    (ρ : Chs P t) {tr tr' : FullTr P t} (hρ : tr.challenges = ρ)
    (h : Rv.MV.view tr = Rv.MV.view tr') (q : M.Pos) (hq : q ∈ (Qs x).pos chs ρ) :
    (E q.leaf.label).cols q.pos.msg (tr q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf =
      (E q.leaf.label).cols q.pos.msg (tr' q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf := by
  have hρ' : tr'.challenges = ρ := by
    have := congrArg CausalView.challenges h
    simp only [CausalViews.view] at this
    rw [← this, hρ]
  rw [← Rv.colOf_obs x chs ρ tr hρ q hq, h, Rv.colOf_obs x chs ρ tr' hρ' q hq]

/-- **The law of the view** of the run of `prv` on `x` at the challenges `ρ`, under uniform
prover coins. -/
noncomputable def obsLaw (Rv : M.Reveal E Qs) (x : X) {R : Type} [Fintype R] [Nonempty R]
    (prv : R → CausalProver P t X) (ρ : Chs P t) : PMF (CausalView Rv.MV) :=
  (PMF.uniformOfFintype R).map fun r => Rv.MV.view ((prv r).run x ρ)

/-- **The views of two witnesses are close** at `2δ`: for every statement and two
witnesses with it in the relation, the average over uniform challenges `ρ` of the distance between
the two laws of the view (`obsLaw`) is at most `2δ`. It is the hypothesis of the
witness-indistinguishability theorem (`wiAdvantage_le`); honest-verifier zero knowledge of the
composite at error `δ` gives it (`obsClose_of_causalHVZK`). -/
def ObsClose (Rv : M.Reveal E Qs) (rel : Set (X × W)) {R : Type} [Fintype R] [Nonempty R]
    (prv : W → R → CausalProver P t X) (δ : ℝ≥0) : Prop :=
  ∀ x w w', (x, w) ∈ rel → (x, w') ∈ rel →
    𝔼 ρ : Chs P t, PMF.tvDist (obsLaw Rv x (prv w) ρ) (obsLaw Rv x (prv w') ρ) ≤ 2 * δ

end Reveal

/-! ### Two witnesses under honest-verifier zero knowledge -/

section HVZK

variable {MV : CausalViews P t}

/-- A composite view as its challenges and its seen entries. -/
def _root_.GordieHowe.IOP.CausalView.equivProd :
    CausalView MV ≃ Chs P t × (∀ p (i : (P p.label).MessageIdx), MV.Idx p i → Option (MV.Ans p i)) where
  toFun v := (v.challenges, v.entries)
  invFun a := ⟨a.1, a.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Pairing with a fixed first component keeps the distance of two laws. -/
theorem _root_.PMF.tvDist_map_prodMk {α β : Type*} (a : α) (p q : PMF β) :
    PMF.tvDist (p.map (Prod.mk a)) (q.map (Prod.mk a)) = PMF.tvDist p q := by
  refine le_antisymm (PMF.tvDist_map_le _ _ _) ?_
  have h := PMF.tvDist_map_le (p.map (Prod.mk a)) (q.map (Prod.mk a)) Prod.snd
  rwa [PMF.map_comp, PMF.map_comp, show (Prod.snd ∘ Prod.mk a : β → β) = id from rfl, PMF.map_id,
    PMF.map_id] at h

omit [∀ j i, DecidableEq ((P j).Challenge i)] in
/-- **The honest views of two witnesses are at the average distance of the views at the
challenges**: both honest views draw uniform challenges, which the view records. -/
theorem tvDist_honestView {R : Type} [Fintype R] [Nonempty R] (honest : W → R → CausalProver P t X)
    (x : X) (w w' : W) :
    PMF.tvDist (MV.honestView honest x w) (MV.honestView honest x w') =
      𝔼 ρ : Chs P t, PMF.tvDist ((PMF.uniformOfFintype R).map fun r => MV.view ((honest w r).run x ρ))
        ((PMF.uniformOfFintype R).map fun r => MV.view ((honest w' r).run x ρ)) := by
  have hview : ∀ (v : W) ρ, ((PMF.uniformOfFintype R).map fun r => MV.view ((honest v r).run x ρ)).map
      CausalView.equivProd = ((PMF.uniformOfFintype R).map fun r =>
        (MV.view ((honest v r).run x ρ)).entries).map (Prod.mk ρ) := fun v ρ => by
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    funext r
    simp only [Function.comp_apply, CausalView.equivProd, Equiv.coe_fn_mk, CausalViews.view,
      CausalProver.challenges_run]
  have hhv : ∀ v : W, (MV.honestView honest x v).map CausalView.equivProd =
      (PMF.uniformOfFintype (Chs P t)).bind fun ρ => ((PMF.uniformOfFintype R).map fun r =>
        (MV.view ((honest v r).run x ρ)).entries).map (Prod.mk ρ) := fun v => by
    rw [CausalViews.honestView, PMF.map_bind]
    exact congrArg _ (funext fun ρ => hview v ρ)
  rw [← PMF.tvDist_map_equiv CausalView.equivProd, hhv, hhv,
    PMF.tvDist_uniformOfFintype_bind_map_prodMk]
  refine Finset.expect_congr rfl fun ρ _ => ?_
  rw [← PMF.tvDist_map_equiv CausalView.equivProd, hview, hview, PMF.tvDist_map_prodMk]

end HVZK

variable {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x}

/-- **Honest-verifier zero knowledge of the composite makes the views of two witnesses close**: for
two witnesses of a statement the average over uniform challenges of the distance between their
view laws is the distance of the two honest views, at most `2δ` when both are within `δ` of the
simulated law (CY24 Definition 23.1.8 for composites, `CausalHVZK`). -/
theorem obsClose_of_causalHVZK (Rv : M.Reveal E Qs) {rel : Set (X × W)} {R : Type} [Fintype R]
    [Nonempty R] {honest : W → R → CausalProver P t X} {Pub : Type} {pub : X → Pub}
    {S : CausalJointSimulator Rv.MV Pub} {δ : ℝ≥0} (h : CausalHVZK Rv.MV rel honest pub S δ) :
    ObsClose Rv rel honest δ := fun x w w' hw hw' => by
  show 𝔼 ρ : Chs P t, PMF.tvDist ((PMF.uniformOfFintype R).map fun r => Rv.MV.view ((honest w r).run x ρ))
    ((PMF.uniformOfFintype R).map fun r => Rv.MV.view ((honest w' r).run x ρ)) ≤ 2 * δ
  rw [← tvDist_honestView]
  calc PMF.tvDist (Rv.MV.honestView honest x w) (Rv.MV.honestView honest x w')
      ≤ PMF.tvDist (Rv.MV.honestView honest x w) (S.law (pub x)) +
          PMF.tvDist (S.law (pub x)) (Rv.MV.honestView honest x w') := PMF.tvDist_triangle _ _ _
    _ ≤ δ + δ := add_le_add (h x w hw) ((PMF.tvDist_comm _ _).trans_le (h x w' hw'))
    _ = 2 * δ := (two_mul _).symm

/-! ### The proof read from what it reveals -/

section Observation

variable (E) (Qs) (h : Query k kN kS L → Out k e) (x : X) (σ : FiatShamirSalt kS)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem map_fst_openedIn (f g : M.Pos → MerkleLeaf kN L) (τ : M.Tree) (ps : List M.Pos) :
    (M.openedIn τ ps (ps.map f)).map Prod.fst = (M.openedIn τ ps (ps.map g)).map Prod.fst := by
  rw [openedIn_map, openedIn_map, List.map_map, List.map_map]
  rfl

end Observation

/-! ### The experiment -/

variable (M) in
/-- **An adaptive multi-theorem witness-indistinguishability adversary** of the composite with
`Q` proof queries: in round `j` it chooses a statement and two witnesses from its finite choice
set, both valid, as a function of the whole oracle and the earlier proofs. -/
structure WIAdversary (rel : Set (X × W)) (Q : ℕ) where
  /-- The finite choice set. -/
  choices : Finset (SPBCS.WIChoice X W)
  /-- Both witnesses of every choice are valid for its statement. -/
  admissible : ∀ c ∈ choices, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel
  /-- The choice of round `j` from the oracle and the earlier proofs. -/
  choose : (j : Fin Q) → (Query k kN kS L → Out k e) → (Fin j → M.NIProof) → SPBCS.WIChoice X W
  /-- Every choice is in the choice set. -/
  choose_mem : ∀ j h πs, choose j h πs ∈ choices

section Game

omit [∀ j i, Nonempty ((P j).Challenge i)]

variable (law : (Query k kN kS L → Out k e) → X → W → PMF M.NIProof) {rel : Set (X × W)} {Q : ℕ}
  (A : M.WIAdversary rel Q)

/-- Round `j` of the experiment with the proof laws `law` (the law of the proof at an oracle, a
statement and a witness) from the state `s` (the oracle and the earlier proofs), answering
with the witness `w_{j,1}` when `b`. -/
noncomputable def wiStep (b : Bool) (j : Fin Q)
    (s : (Query k kN kS L → Out k e) × (Fin j → M.NIProof)) :
    PMF ((Query k kN kS L → Out k e) × (Fin (j + 1) → M.NIProof)) :=
  (law s.1 (A.choose j s.1 s.2).stmt
      (if b then (A.choose j s.1 s.2).wit₁ else (A.choose j s.1 s.2).wit₀)).map
    fun π => (s.1, Fin.snoc (α := fun _ => M.NIProof) s.2 π)

/-- The experiment after `j` rounds, round `i` answering with the witness `w_{i,1}` when `bs i`. -/
noncomputable def wiRun (bs : ℕ → Bool) :
    (j : ℕ) → j ≤ Q → PMF ((Query k kN kS L → Out k e) × (Fin j → M.NIProof))
  | 0, _ => (PMF.uniformOfFintype _).map fun h => (h, Fin.elim0)
  | j + 1, hj => (wiRun bs j (by omega)).bind (wiStep law A (bs j) ⟨j, by omega⟩)

/-- **The witness-indistinguishability experiment** `D_b` (CY24 Definition 33.1.1 at `t = ∞`, for
many proofs) with the proof laws `law`: the whole oracle and the `Q` proofs, every proof query answered
with the witness `w_{j,b}`. -/
noncomputable def wiGameWith (b : Bool) : PMF ((Query k kN kS L → Out k e) × (Fin Q → M.NIProof)) :=
  wiRun law A (fun _ => b) Q le_rfl

/-- **The advantage of a distinguisher** `D` given the whole oracle and the proofs, with the proof
laws `law`: the `GordieHowe.gameAdvantage` of the event `D` between the two experiments. -/
noncomputable def wiAdvantageWith (D : (Query k kN kS L → Out k e) → (Fin Q → M.NIProof) → Prop) : ℝ :=
  GordieHowe.gameAdvantage (wiGameWith law A false) (wiGameWith law A true) {s | D s.1 s.2}

/-- The oracle of every intermediate state is uniform: proofs are drawn given the oracle. -/
theorem map_fst_wiRun (bs : ℕ → Bool) : ∀ j (hj : j ≤ Q),
    (wiRun law A bs j hj).map Prod.fst = PMF.uniformOfFintype _
  | 0, _ => by rw [wiRun, PMF.map_comp]; exact PMF.map_id _
  | j + 1, hj => by
    rw [wiRun, PMF.map_bind]
    simp_rw [wiStep, PMF.map_comp]
    rw [← map_fst_wiRun bs j (by omega), ← PMF.bind_pure_comp]
    congr 1
    funext s
    exact PMF.map_const _ _

/-- Two runs whose answer bits agree before round `j` agree after `j` rounds. -/
theorem wiRun_congr {bs bs' : ℕ → Bool} : ∀ j (hj : j ≤ Q), (∀ i < j, bs i = bs' i) →
    wiRun law A bs j hj = wiRun law A bs' j hj
  | 0, _, _ => rfl
  | j + 1, hj, hb => by
    rw [wiRun, wiRun, wiRun_congr j (by omega) fun i hi => hb i (by omega), hb j (by omega)]

/-- The average of a function of the oracle under an intermediate state is its uniform average. -/
theorem tsum_wiRun_mul (bs : ℕ → Bool) (j : ℕ) (hj : j ≤ Q)
    {f : (Query k kN kS L → Out k e) → ℝ} (hf : ∀ h, 0 ≤ f h) :
    𝔼[s ~ wiRun law A bs j hj : f s.1] = 𝔼[h ← (Query k kN kS L → Out k e) : f h] :=
  PMF.tsum_toReal_mul_comp_eq_expect _ Prod.fst (map_fst_wiRun law A bs j hj) hf

/-- **One hybrid step**: two runs whose answer bits differ only at round `i`, where every choice
of the adversary gives proof laws within `ε h` at the oracle `h`, are within the uniform average
of `ε` after every later round. -/
theorem close_wiRun_step {bs bs' : ℕ → Bool} {i : ℕ} (hi : i < Q)
    (hb : ∀ j, j ≠ i → bs j = bs' j) {ε : (Query k kN kS L → Out k e) → ℝ} (hε0 : ∀ h, 0 ≤ ε h)
    (hε : ∀ s, wiStep law A (bs i) ⟨i, hi⟩ s ≈[ε s.1] wiStep law A (bs' i) ⟨i, hi⟩ s) :
    ∀ j (hj : j ≤ Q), i < j →
      wiRun law A bs j hj ≈[𝔼[h ← (Query k kN kS L → Out k e) : ε h]]
        wiRun law A bs' j hj
  | 0, _, h0 => absurd h0 (Nat.not_lt_zero _)
  | j + 1, hj, hij => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with hij | rfl
    · rw [wiRun, wiRun, hb j (by omega)]
      exact (PMF.tvDist_bind_right_le _ _ _).trans (close_wiRun_step hi hb hε0 hε j (by omega) hij)
    · rw [wiRun, wiRun, wiRun_congr law A i (by omega) fun j hj => hb j (by omega)]
      refine (PMF.tvDist_bind_left_le' _ _ _).trans ?_
      rw [← tsum_wiRun_mul law A bs' i (by omega) hε0]
      exact PMF.tsum_toReal_mul_le_tsum_toReal_mul _ (fun s => PMF.tvDist_nonneg _ _) hε
        (fun s => Finset.single_le_sum (fun h _ => hε0 h) (Finset.mem_univ s.1))

/-- **The hybrid argument**: if at every oracle `h` and every choice of the adversary the proof
laws of the two witnesses are within `ε h`, the experiments answering with the first and with the
second witnesses are within `Q · 𝔼[h ← Oracle : ε h]`. -/
theorem close_wiGameWith {ε : (Query k kN kS L → Out k e) → ℝ} (hε0 : ∀ h, 0 ≤ ε h)
    (hε : ∀ h c, c ∈ A.choices →
      law h c.stmt c.wit₀ ≈[ε h] law h c.stmt c.wit₁) :
    wiGameWith law A false ≈[Q * 𝔼[h ← (Query k kN kS L → Out k e) : ε h]]
      wiGameWith law A true := by
  let hyb : ℕ → PMF ((Query k kN kS L → Out k e) × (Fin Q → M.NIProof)) := fun i =>
    wiRun law A (fun j => decide (j < i)) Q le_rfl
  have h0 : hyb 0 = wiGameWith law A false :=
    wiRun_congr law A Q le_rfl fun j _ => by simp
  have hQ : hyb Q = wiGameWith law A true :=
    wiRun_congr law A Q le_rfl fun j hj => by simp [hj]
  have hstep : ∀ i (hi : i < Q), hyb i ≈[𝔼[h ← (Query k kN kS L → Out k e) : ε h]] hyb (i + 1) := by
    intro i hi
    have hb : ∀ j, j ≠ i → decide (j < i) = decide (j < i + 1) := fun j hj => by
      rcases Nat.lt_or_ge j i with h | h
      · simp [h, Nat.lt_succ_of_lt h]
      · simp [not_lt.2 h, show ¬ j < i + 1 by omega]
    have hmem : ∀ s : (Query k kN kS L → Out k e) × (Fin i → M.NIProof),
        A.choose ⟨i, hi⟩ s.1 s.2 ∈ A.choices := fun s => A.choose_mem _ _ _
    refine close_wiRun_step law A hi hb hε0 (fun s => ?_) Q le_rfl hi
    simp only [lt_irrefl, decide_false, Nat.lt_succ_self, decide_true]
    exact (PMF.tvDist_map_le _ _ _).trans (hε s.1 _ (hmem s))
  have hfwd : ∀ i ≤ Q, hyb 0 ≈[i * 𝔼[h ← (Query k kN kS L → Out k e) : ε h]] hyb i := by
    intro i
    induction i with
    | zero => exact fun _ => by simp
    | succ i ih =>
      intro hi
      refine (PMF.tvDist_triangle _ (hyb i) _).trans ?_
      have := ih (by omega)
      have := hstep i (by omega)
      push_cast
      linarith
  rw [← h0, ← hQ]
  exact hfwd Q le_rfl

end Game

/-! ### Unconditional witness indistinguishability -/

variable (M) in
/-- **The leaf term** of one proof: `U · leafBound k kN L` for the `U = |Pos|` leaves (CY24 Claim
3.4.2 at salt length `8kN` and digest length `8k` bits). -/
noncomputable def leafTerm : ℝ := Fintype.card M.Pos * SPBCS.leafBound k kN L

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem leafTerm_nonneg : 0 ≤ M.leafTerm :=
  mul_nonneg (Nat.cast_nonneg _) SPBCS.leafBound_nonneg

variable (M) in
/-- **The witness-indistinguishability error of one proof query**: twice the leaf term (once per
witness), `2δ` for the two witnesses' views at statistical HVZK error `δ`, the overrun and
key-collision terms of the ideal challenges, and the salt term for `c` choices of the
adversary. -/
noncomputable def wiError (δ : ℝ≥0) (c : ℕ) : ℝ :=
  2 * M.leafTerm + 2 * δ + M.overrun.toReal + (SPBCS.keyCollision (t.size n) k).toReal +
    SPBCS.saltTerm kS c

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem wiError_nonneg (δ : ℝ≥0) (c : ℕ) : 0 ≤ M.wiError δ c := by
  have := leafTerm_nonneg (M := M)
  have := SPBCS.saltTerm_nonneg kS c
  unfold wiError
  positivity

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- The error grows with the number of choices. -/
theorem wiError_mono (δ : ℝ≥0) {c c' : ℕ} (h : c ≤ c') : M.wiError δ c ≤ M.wiError δ c' := by
  unfold wiError
  gcongr
  exact SPBCS.saltTerm_mono kS h

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The expected error of one proof query**, maximized over the choices: twice the leaf term,
and a per-choice distance `F` whose expected maximum is bounded by the salt bound (`hF`). -/
theorem expect_sup'_errors_le_of {δ : ℝ≥0} {choices : Finset (SPBCS.WIChoice X W)}
    (hne : choices.Nonempty) (F : (Query k kN kS L → Out k e) → SPBCS.WIChoice X W → ℝ)
    (hF : 𝔼 h : Query k kN kS L → Out k e, choices.sup' hne (F h) ≤
      min 1 (2 * δ + M.overrun.toReal + (SPBCS.keyCollision (t.size n) k).toReal) +
        SPBCS.saltTerm kS choices.card) :
    𝔼[h ← (Query k kN kS L → Out k e) : choices.sup' hne (fun c =>
        2 * (Fintype.card M.Pos * SPBCS.leafDist h) + F h c)] ≤
      M.wiError δ choices.card := by
  have hsup : ∀ h, choices.sup' hne (fun c =>
      2 * (Fintype.card M.Pos * SPBCS.leafDist h) + F h c) ≤
      2 * (Fintype.card M.Pos * SPBCS.leafDist h) + choices.sup' hne (F h) := fun h =>
    Finset.sup'_le _ _ fun c hc => add_le_add le_rfl (Finset.le_sup' (F h) hc)
  have hleaf : 𝔼 h : Query k kN kS L → Out k e,
      2 * (Fintype.card M.Pos * SPBCS.leafDist h) ≤ 2 * M.leafTerm := by
    rw [← Finset.mul_expect, ← Finset.mul_expect, leafTerm]
    have := SPBCS.expect_leafDist_le (k := k) (kN := kN) (kS := kS) (L := L) (e := e)
    gcongr
  calc _ ≤ 𝔼 h : Query k kN kS L → Out k e,
          (2 * (Fintype.card M.Pos * SPBCS.leafDist h) + choices.sup' hne (F h)) :=
        Finset.expect_le_expect fun h _ => hsup h
    _ = 𝔼 h : Query k kN kS L → Out k e, 2 * (Fintype.card M.Pos * SPBCS.leafDist h) +
          𝔼 h, choices.sup' hne (F h) := Finset.expect_add_distrib _ _ _
    _ ≤ 2 * M.leafTerm + (min 1 (2 * δ + M.overrun.toReal +
          (SPBCS.keyCollision (t.size n) k).toReal) +
          SPBCS.saltTerm kS choices.card) := add_le_add hleaf hF
    _ ≤ _ := by
        have := min_le_right (1 : ℝ)
          (2 * δ + M.overrun.toReal + (SPBCS.keyCollision (t.size n) k).toReal)
        unfold wiError
        linarith

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **Witness indistinguishability from one proof query** (the hybrid over the proof queries): for
proof laws `law` whose laws at the two witnesses of every choice are within twice the leaf term
plus a nonnegative per-choice distance `F h c` at every oracle `h` (`hlaw`), with the expected
maximum of `F` over the choices bounded by the salt bound (`hF`), the advantage of every
distinguisher is at most `Q · wiError δ |choices|`. -/
theorem wiAdvantageWith_le_of {law : (Query k kN kS L → Out k e) → X → W → PMF M.NIProof}
    {rel : Set (X × W)} {δ : ℝ≥0} {Q : ℕ}
    (A : M.WIAdversary rel Q) (F : (Query k kN kS L → Out k e) → SPBCS.WIChoice X W → ℝ)
    (hF0 : ∀ h c, 0 ≤ F h c)
    (hlaw : ∀ h, ∀ c ∈ A.choices, law h c.stmt c.wit₀ ≈[2 * (Fintype.card M.Pos *
      SPBCS.leafDist h) + F h c] law h c.stmt c.wit₁)
    (hF : ∀ hne : A.choices.Nonempty, 𝔼 h : Query k kN kS L → Out k e, A.choices.sup' hne (F h) ≤
      min 1 (2 * δ + M.overrun.toReal + (SPBCS.keyCollision (t.size n) k).toReal) +
        SPBCS.saltTerm kS A.choices.card)
    (D : (Query k kN kS L → Out k e) → (Fin Q → M.NIProof) → Prop) :
    wiAdvantageWith law A D ≤ Q * M.wiError δ A.choices.card := by
  classical
  have hadv : wiAdvantageWith law A D ≤
      PMF.tvDist (wiGameWith law A false) (wiGameWith law A true) :=
    PMF.abs_toOuterMeasure_sub_le_tvDist _ _ _
  rcases A.choices.eq_empty_or_nonempty with hempty | hne
  · -- no choices: no proof query can be made
    have hQ : Q = 0 := by
      by_contra hQ
      have := A.choose_mem ⟨0, Nat.pos_of_ne_zero hQ⟩ (fun _ => Classical.arbitrary _) Fin.elim0
      simp [hempty] at this
    subst hQ
    have : wiGameWith law A false = wiGameWith law A true := rfl
    rw [this, PMF.tvDist_self] at hadv
    have := wiError_nonneg (M := M) δ A.choices.card
    simpa using hadv
  let ε : (Query k kN kS L → Out k e) → ℝ := fun h => A.choices.sup' hne fun c =>
    2 * (Fintype.card M.Pos * SPBCS.leafDist h) + F h c
  have hε0 : ∀ h, 0 ≤ ε h := fun h => by
    obtain ⟨c, hc⟩ := hne
    refine le_trans ?_ (Finset.le_sup' _ hc)
    have := SPBCS.leafDist_nonneg (k := k) (kN := kN) (kS := kS) (L := L) (e := e) h
    have := hF0 h c
    positivity
  have hgame := close_wiGameWith law A hε0 fun h c hc =>
    (hlaw h c hc).trans (Finset.le_sup' (fun c =>
      2 * (Fintype.card M.Pos * SPBCS.leafDist h) + F h c) hc)
  have hE := expect_sup'_errors_le_of hne F (hF hne)
  calc wiAdvantageWith law A D ≤ Q * 𝔼[h ← (Query k kN kS L → Out k e) : ε h] :=
        hadv.trans hgame
    _ ≤ Q * M.wiError δ A.choices.card := mul_le_mul_of_nonneg_left hE (Nat.cast_nonneg _)

end Base

namespace FullPast

open Base

variable {ι : Type} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {t : SPTerm ι} {X W : Type}
  {M : FullPast P t X k kN kS L e}

/-! ### The fixed point of the Fiat–Shamir transformation -/

section FixedPoint

variable (prv : CausalProver P t X) (x : X) (σ : FiatShamirSalt kS)
  (h : Query k kN kS L → Out k e)

/-- **The writes of a write function at the challenges `ρ`**: the write of every prover round of
every leaf at the causal prover's message at `ρ`. -/
noncomputable def skeletonW (wr : M.WriteFn) (ρ : Chs P t) : M.Writes :=
  fun p i => wr p i (prv.run x ρ p i.1)

end FixedPoint

variable {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
  {Qs : ∀ x, M.IOPQueries V x}

/-! ### The prover at given leaf digests -/

section Digests

variable (E) (prv : CausalProver P t X) (x : X) (σ : FiatShamirSalt kS)
  (h : Query k kN kS L → Out k e)

/-- The write function at the roots over the leaf digests `d`. -/
def writeD (d : M.Pos → Digest k) : M.WriteFn :=
  fun p i m => (E p.label).write i m (M.rootsOf h d p i)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The write function at the roots over given leaf digests reads the oracle only at `leaf` and
`node` queries.** -/
theorem writeD_congr_leaf_node {h h' : Query k kN kS L → Out k e}
    (hleaf : ∀ a b, h (.leaf a b) = h' (.leaf a b)) (hnode : ∀ l r, h (.node l r) = h' (.node l r))
    (d : M.Pos → Digest k) : writeD E h d = writeD E h' d := by
  funext p i m
  unfold writeD
  rw [M.rootsOf_congr hleaf hnode]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The writes at given leaf digests read only the digests of their round**: digest vectors that
agree at the positions before global round `m` give the same write function at every prover round
before `m` (`rootsOf_congr_ld`). -/
theorem writeD_congr_digests {d d' : M.Pos → Digest k} {m : ℕ}
    (hd : ∀ q : M.Pos, q.gIdx < m → d q = d' q) (p : t.Leaf) (i : (P p.label).MessageIdx)
    (hi : p.off n + i.1.1 < m) : writeD E h d p i = writeD E h d' p i := by
  funext msg
  unfold writeD
  rw [rootsOf_congr_ld h p i fun τ j => hd _ hi]

end Digests

/-! ### The proof read from what it reveals -/

section Observation

variable (E) (Qs) (h : Query k kN kS L → Out k e) (x : X) (σ : FiatShamirSalt kS)

/-- The writes of a composite transcript `tr` at the leaf digests `d`: the write of every prover
message at the roots over `d`. -/
def skeletonTr (d : M.Pos → Digest k) (tr : FullTr P t) : M.Writes :=
  fun p i => (E p.label).write i (tr p i.1) (M.rootsOf h d p i)

/-- The opened leaf of position `q` of the transcript `tr` at the Merkle salts `ν`. -/
def leafTr (tr : FullTr P t) (ν : M.Pos → MerkleSalt kN) (q : M.Pos) : MerkleLeaf kN L :=
  MerkleLeaf.mk (ν q) ((E q.leaf.label).cols q.pos.msg (tr q.leaf q.pos.msg.1) q.pos.tree q.pos.leaf)

variable {E Qs} (Rv : M.Reveal E Qs)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
include x Rv in
/-- Transcripts with the same view have the same writes. -/
theorem skeletonTr_congr (d : M.Pos → Digest k) {tr tr' : FullTr P t}
    (ho : Rv.MV.view tr = Rv.MV.view tr') :
    skeletonTr E h d tr = skeletonTr E h d tr' := by
  funext p i
  exact Rv.write_congr x tr.challenges ho p i _

end Observation

/-! ### One proof query at a fixed oracle and salt -/

section OneProof

variable (E) (Qs) (h : Query k kN kS L → Out k e) (x : X)
  (σ : FiatShamirSalt kS) {R : Type} [Fintype R] [Nonempty R]

/-- The Merkle salts drawn from the preimages of the digests `d` at the columns `cols`
(`invert`). -/
noncomputable def merkleSaltLaw (h : Query k kN kS L → Out k e) (cols : M.Pos → Bytes L)
    (d : M.Pos → Digest k) : PMF (M.Pos → MerkleSalt kN) :=
  PMF.pi fun q => invert (SPBCS.digestOf h) (SPBCS.leafEnc (cols q)) (d q)

end OneProof

/-! ### Two witnesses in the ideal law: the fixed-point laws -/

section Coupling

variable (Rv : M.Reveal E Qs) (h : Query k kN kS L → Out k e) (x : X)
  (σ : FiatShamirSalt kS) {R : Type} [Fintype R] [Nonempty R]

/-- What the ideal proof reveals at the challenges `ρ`: the view of the composite run and the
leaf digests. -/
def obsD (prv : R → CausalProver P t X) (c : R × (M.Pos → Digest k)) (ρ : Chs P t) :
    CausalView Rv.MV × (M.Pos → Digest k) :=
  (Rv.MV.view ((prv c.1).run x ρ), c.2)

end Coupling

/-! ### The salt bound -/

section Salt

variable (x : X) (σ : FiatShamirSalt kS) {R : Type} [Fintype R] [Nonempty R]

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The revealed data with uniform leaf digests** are as close as the views: the leaf digests
are uniform and independent of the view. -/
theorem tvDist_obsD_le (Rv : M.Reveal E Qs) (prv prv' : R → CausalProver P t X) (ρ : Chs P t) :
    PMF.tvDist ((PMF.uniformOfFintype (R × (M.Pos → Digest k))).map (obsD Rv x prv · ρ))
        ((PMF.uniformOfFintype (R × (M.Pos → Digest k))).map (obsD Rv x prv' · ρ)) ≤
      PMF.tvDist (obsLaw Rv x prv ρ) (obsLaw Rv x prv' ρ) := by
  have hbind : ∀ q : R → CausalProver P t X,
      (PMF.uniformOfFintype (R × (M.Pos → Digest k))).map (obsD Rv x q · ρ) =
        (obsLaw Rv x q ρ).bind fun o =>
          (PMF.uniformOfFintype (M.Pos → Digest k)).map fun d => (o, d) := fun q => by
    rw [PMF.uniformOfFintype_prod_eq_bind, PMF.map_bind, obsLaw, PMF.bind_map]
    refine congrArg (PMF.bind _) (funext fun r => ?_)
    rw [PMF.map_comp]
    rfl
  rw [hbind, hbind]
  exact PMF.tvDist_bind_right_le _ _ _

end Salt

end FullPast

end GordieHowe.SPBCS
