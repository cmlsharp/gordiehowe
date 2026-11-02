-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Applications.Ring.PublicW1.Restrict
public import GordieHowe.Applications.Ring.PublicW1.CheckSearch

@[expose] public section

/-!
# Anonymity of the ring publishing `w₁` against adversaries with `q` check-oracle queries

The check term of `advantage_le` counts the adversary's candidate rings per key vector, because
the adversary sees the whole check oracle `G`. Here the adversary's choices read `G` through at
most `q` classical queries (`CheckQueryBounded`, `ROM.Alg`, CY24 p. 20); it still receives every
honest user's key-generation coins, and sees the oracles `H_µ`, `H` and the proof system's oracle
whole. The check term becomes `2 (q + 1) · checkError reps tol s x`, independent of the number of
candidate rings (`advantage_le_query`, one challenge).

The proof compares the signer with the signer that also refuses the rings of defect above `s`
(`lowOk`, `PubSigner.restrict`):
- against the restricted signer every admitted ring has defect at most `s`, so the anonymity
  bound needs no check term (`advantage_restrictLow_le`, `Q` challenges);
- the two games are identical until the chosen ring has defect above `s` and passes the check
  (`PubAnonAdversary.advantage_le_restrict_one`);
- the choice reads `G` through `q` queries, and the check of a ring `l` reads `G` only at the
  points `(l, j, r)`, so the search lemma (`ROM.expect_label_le`) bounds that event by
  `(q + 1) · checkError` (`expect_badChoice_le`).

- `lowOk`, `advantage_restrictLow_le`: the restricted signer and its bound.
- `CheckQueryBounded`, `localPred_highCheck`, `expect_badChoice_le`, `advantage_le_query`: the
  query-bounded adversary class, the search, and the bound.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA PMF Finset IOP GordieHowe.SPBCS GordieHowe.QROM
open scoped ENNReal BigOperators

/-- An average over pairs is the iterated average, for any `Fintype` instance on the pairs. -/
theorem _root_.Finset.expect_prod_eq_expect_expect {α β : Type*} [Fintype α] [Fintype β]
    [hαβ : Fintype (α × β)] (f : α × β → ℝ) : 𝔼 x : α × β, f x = 𝔼 a, 𝔼 b, f (a, b) := by
  obtain rfl : hαβ = instFintypeProd α β := Subsingleton.elim _ _
  rw [← Finset.univ_product_univ, Finset.expect_product]

variable {p : Params} (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Nonempty (MaskBox p)] {Msg : Type} [Fintype Msg] [DecidableEq Msg]
  [Inhabited prims.Hint] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High]

/-- **The rings of defect at most `s`**, as a refusal predicate of the game's oracles, the ring
and the message (it reads only the ring). -/
def lowOk (βmin : ℚ≥0) (s : ℝ) {N reps : ℕ} (_ : GameOrc prims Msg N reps)
    (R : RingOf (PubKey p prims) N) (_ : Msg) : Prop :=
  LowDefect prims βmin s R

section Main

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt k kN kS L e} {n Q : ℕ}

open Classical in
/-- **Anonymity against the signer that also refuses the rings of defect above `s`** (BKM06
Definition 4 as in `advantage_le`, `Q` adaptive challenges): every ring this signer admits has
defect at most `s`, so the bound is `advantage_le`'s without the check term,
`(Q + 1) · anonError + Q · wiError δ (Q · C)`. -/
theorem advantage_restrictLow_le
    (A : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n Q)
    (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) [NeZero n]
    {E : (j : ι) → (M.comp j).Encoder}
    {V : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt →
      FullTr P τ → Bool}
    {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
    {honest : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Wit →
      R → CausalProver P τ (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt}
    (Rv : ∀ H, M.Reveal E (Qs H)) {PubZ : Type}
    {pubZ : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt → PubZ}
    {sim : ∀ H, CausalJointSimulator (Rv H).MV PubZ} {δ : NNReal}
    (hz : ∀ H, CausalHVZK (Rv H).MV ((pubSigner prims (Msg := Msg) N βmin reps tol enc).rel H)
      (honest H) pubZ (sim H) δ) {C : ℕ} (hC : A.ValidCountLe C)
    (D : (Fin n → _root_.MLDSA.Bytes 32) → GameOrc prims Msg N reps →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) M.NIProof Q → Prop) :
    (A.restrict (lowOk prims βmin s)).advantage E Qs honest D ≤
      (Q + 1) * anonError (A := A) hp hβ0 hβt s θ C + Q * M.wiError δ (Q * C) := by
  have h := (A.restrict (lowOk prims βmin s)).advantage_le_of_signsValidly Rv hz hC
    (fun keys HG => Keeps prims A hp hβ0 hβt s keys HG.1)
    (fun keys HG hK c hcm hc hA b x hx =>
      validAt_of_keeps hp hβ0 hβt h_laws hv henc hs2 keys HG hK hcm hc hA.1 hA.2 b hx)
    (fun keys HG => oracleError prims A hp hβ0 hβt s θ keys HG.1)
    (fun keys HG => oracleError_nonneg hp hβ0 hβt hs1 hθ0 keys HG.1)
    (fun keys HG _ c hcm hc hA => tvDist_le_oracleError hp hβ0 hβt hs1 hθ0 hθ1 keys HG c hcm
      hc hA.2 hA.1) D
  have hind : 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
          (if Keeps prims A hp hβ0 hβt s keys HG.1 then 0 else 1 : ℝ) ≤
      𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
          oracleError prims A hp hβ0 hβt s θ keys HG.1 :=
    Finset.expect_le_expect fun keys _ => Finset.expect_le_expect fun HG _ =>
      ite_keeps_le_oracleError hp hβ0 hβt hs1 hθ0 hθ1 keys HG.1
  have hE : 𝔼 keys : Fin n → _root_.MLDSA.Bytes 32,
        𝔼 HG : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Orc,
          oracleError prims A hp hβ0 hβt s θ keys HG.1 ≤
      anonError (A := A) hp hβ0 hβt s θ C :=
    Finset.expect_le_expect fun keys _ =>
      (Finset.expect_comp_fst
        (hαβ := (pubSigner prims (Msg := Msg) N βmin reps tol enc).instFintypeOrc)
        (fun H => oracleError prims A hp hβ0 hβt s θ keys H)).trans_le
        (expect_schOrc_oracleError_le hp hβ0 hβt h_laws hs2 hθ0 hθ1 hs1 hC keys)
  have hQ : (0 : ℝ) ≤ Q := Nat.cast_nonneg _
  have key : ∀ {a X I W B q : ℝ}, a ≤ q * X + W + I → I ≤ X → X ≤ B → 0 ≤ q →
      a ≤ (q + 1) * B + W := fun h1 h2 h3 h4 => by nlinarith
  exact key h hind hE hQ

/-- **An adversary whose choices read the check oracle through `q` queries**: every choice, at
every value of the users' coins, the scheme's oracles `(H_µ, H)`, the proof system's oracle and
the history, is the output of a deterministic classical algorithm making `q` queries to the check
oracle `G` (`ROM.Alg`, CY24 p. 20). The adversary keeps full key exposure and sees the other
oracles whole; the distinguisher is unrestricted. A randomized query-bounded adversary is a
mixture of these, not formalized. -/
structure CheckQueryBounded
    (A : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n Q) (q : ℕ) :
    Prop where
  /-- Every choice reads `G` through `q` queries. -/
  choose : ∀ j keys H h hist, ∃ alg : ROM.Alg (RingOf (PubKey p prims) N × Fin N × Fin reps)
    (CommitHashBytes p) ((pubSigner prims (Msg := Msg) N βmin reps tol enc).Choice n) q,
    ∀ G, A.choose j keys (H, G) h hist = alg.output G

omit [Fintype Msg] [DecidableEq Msg] [Inhabited prims.Hint] [Fintype prims.Hint]
  [DecidableEq prims.Hint] in
/-- **The check of a ring of defect above `s` reads `G` at the ring's points only**: the
predicate `s < ringDefect l ∧ RingCheck G l` of the label `l` is local for the labelling of the
check points `(l, j, r)` by their ring. -/
theorem localPred_highCheck (s : ℝ) :
    ROM.LocalPred (fun x : RingOf (PubKey p prims) N × Fin N × Fin reps => x.1)
      (fun l (G : CheckOrc p prims N reps) =>
        s < ringDefect prims βmin l.1 ∧ RingCheck prims βmin tol G l) := by
  intro l G G' hag
  change (_ ∧ RingCheck prims βmin tol G l) ↔ (_ ∧ RingCheck prims βmin tol G' l)
  have hf : checkFails prims βmin G l = checkFails prims βmin G' l :=
    congrArg Finset.card (Finset.filter_congr fun jr _ => by
      rw [hag (l, Fin.castLE l.2 jr.1, jr.2) rfl])
  unfold RingCheck
  rw [hf]

open Classical in
omit [Fintype Msg] [DecidableEq Msg] [Inhabited prims.Hint] [Fintype prims.Hint]
  [DecidableEq prims.Hint] in
/-- **The search for a high-defect ring that passes the check** (the search lemma at the check
oracle): for a deterministic classical algorithm making `q` queries to the check oracle and
outputting a challenge, the challenge's ring has defect above `s` and passes the check with
probability at most `(q + 1) · checkError reps tol s x`, for every `x ≥ 1`
(`ROM.expect_label_le`, `expect_ringCheck_le`). -/
theorem expect_badChoice_le {C : Type} (s : ℝ) {x : ℝ} (hx : 1 ≤ x) {q : ℕ}
    (alg : ROM.Alg (RingOf (PubKey p prims) N × Fin N × Fin reps) (CommitHashBytes p) C q)
    (ring : C → RingOf (PubKey p prims) N) :
    𝔼 G : CheckOrc p prims N reps, (if s < ringDefect prims βmin (ring (alg.output G)).1 ∧
        RingCheck prims βmin tol G (ring (alg.output G)) then 1 else 0 : ℝ) ≤
      (q + 1) * checkError reps tol s x := by
  have hε : ∀ l : RingOf (PubKey p prims) N, 𝔼 G : CheckOrc p prims N reps,
      (if s < ringDefect prims βmin l.1 ∧ RingCheck prims βmin tol G l then 1 else 0 : ℝ) ≤
        checkError reps tol s x := fun l => by
    by_cases hl : s < ringDefect prims βmin l.1
    · refine (Finset.expect_le_expect fun G _ => ?_).trans
        (expect_ringCheck_le prims βmin tol l hl.le hx)
      by_cases h : RingCheck prims βmin tol G l <;> simp [hl, h]
    · simp only [hl, false_and, if_false, Finset.expect_const_zero]
      exact checkError_nonneg reps tol s (zero_le_one.trans hx)
  have h := ROM.expect_label_le (fun x : RingOf (PubKey p prims) N × Fin N × Fin reps => x.1) alg
    (fun l (G : CheckOrc p prims N reps) =>
      s < ringDefect prims βmin l.1 ∧ RingCheck prims βmin tol G l)
    (localPred_highCheck prims s) (fun l => by convert hε l using 3) ring
  convert h using 3

open Classical in
/-- **Anonymity of the ML-DSA ring signature publishing `w₁` against adversaries with `q`
check-oracle queries** (BKM06 Definition 4, ePrint 2005/304, p. 6, one challenge, keys given at
the start as in CCLM22 Experiment 2, p. 21; the adversary receives every honest user's
key-generation coins and sees `H_µ`, `H` and the proof system's oracle whole, and its choice reads
the check oracle `G` through `q` classical queries, `CheckQueryBounded`): with the hypotheses of
`advantage_le`, the advantage is at most
`2 · anonError + wiError δ C + 2 (q + 1) · checkError reps tol s x`, at every defect budget
`s < 1`, threshold fraction `θ ∈ (0, 1)` and `x ≥ 1`. `C` bounds the challenges of the set valid
for any key vector, as in `advantage_le`; it enters `anonError` and `wiError` and not the check
term. The proof: `advantage_le_restrict_one` at `lowOk`, `advantage_restrictLow_le`, and
`expect_badChoice_le` at each value of the users' coins, `(H_µ, H)` and the proof system's
oracle. -/
theorem advantage_le_query
    (A : PubAnonAdversary (pubSigner prims (Msg := Msg) N βmin reps tol enc) M n 1) {q : ℕ}
    (hq : CheckQueryBounded prims A q)
    (hp : SigningParams p) (hβ0 : (βmin : ℝ≥0∞) ≠ 0) (hβt : (βmin : ℝ≥0∞) ≠ ⊤)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {s θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) (hs1 : s < 1) {x : ℝ} (hx : 1 ≤ x) [NeZero n]
    {E : (j : ι) → (M.comp j).Encoder}
    {V : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt →
      FullTr P τ → Bool}
    {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
    {honest : GameOrc prims Msg N reps → (pubSigner prims (Msg := Msg) N βmin reps tol enc).Wit →
      R → CausalProver P τ (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt}
    (Rv : ∀ H, M.Reveal E (Qs H)) {PubZ : Type}
    {pubZ : (pubSigner prims (Msg := Msg) N βmin reps tol enc).Stmt → PubZ}
    {sim : ∀ H, CausalJointSimulator (Rv H).MV PubZ} {δ : NNReal}
    (hz : ∀ H, CausalHVZK (Rv H).MV ((pubSigner prims (Msg := Msg) N βmin reps tol enc).rel H)
      (honest H) pubZ (sim H) δ) {C : ℕ} (hC : A.ValidCountLe C)
    (D : (Fin n → _root_.MLDSA.Bytes 32) → GameOrc prims Msg N reps →
      (Query k kN kS L → Out k e) → PubHist (BucketVec p) M.NIProof 1 → Prop) :
    A.advantage E Qs honest D ≤
      2 * anonError (A := A) hp hβ0 hβt s θ C + M.wiError δ C +
        2 * ((q + 1) * checkError reps tol s x) := by
  have h1 := A.advantage_le_restrict_one (lowOk prims βmin s) E Qs honest D
  have h2 := advantage_restrictLow_le prims A hp hβ0 hβt h_laws hv henc hs2 hθ0 hθ1 hs1 Rv hz hC D
  simp only [Nat.cast_one, one_mul, one_add_one_eq_two] at h2
  refine h1.trans (add_le_add h2 (mul_le_mul_of_nonneg_left ?_ zero_le_two))
  refine (Finset.expect_le_expect fun keys _ => ?_).trans_eq (Fintype.expect_const _)
  refine (Finset.expect_prod_eq_expect_expect (α := SchOrc p Msg) (β := CheckOrc p prims N reps)
    (hαβ := (pubSigner prims (Msg := Msg) N βmin reps tol enc).instFintypeOrc) _).trans_le ?_
  refine (Finset.expect_le_expect fun H _ => ?_).trans_eq (Fintype.expect_const _)
  rw [Finset.expect_comm]
  refine (Finset.expect_le_expect fun h _ => ?_).trans_eq (Fintype.expect_const _)
  obtain ⟨alg, halg⟩ := hq.choose 0 keys H h Fin.elim0
  refine (Finset.expect_le_expect fun G _ => ?_).trans
    (expect_badChoice_le prims (βmin := βmin) (tol := tol) s hx alg RingChoice.ring)
  rw [halg G]
  split_ifs with h' hb'
  · exact le_rfl
  · exact absurd ⟨lt_of_not_ge h'.2, h'.1.2⟩ hb'
  · norm_num
  · exact le_rfl

end Main

end GordieHowe.Ring.MLDSAW1
