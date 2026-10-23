-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.Basic
public import GordieHowe.ProofSystem.Ligero.PlacementHiding
public import GordieHowe.ProofSystem.Ligero.UntestedMaskRow
public import GordieHowe.Model.IOP.DropMessage
public import GordieHowe.Foundations.ReedSolomon.JohnsonAgreement
public import GordieHowe.ProofSystem.Ligero.SubfieldTest

@[expose] public section

/-!
# Ligero at agreement threshold `A`

Longfellow's prepared Ligero tableau as a commit-and-prove system whose low-degree test runs in the
commit phase, analysed at an agreement threshold `A` between the dimension `k` and the block length
`N`, up to the Johnson radius (the paper's Appendix D, Security of Ligero at an agreement
threshold). This file states what both maskings of the response masks share, and the system with
untested masks (`GordieHowe.Ligero.AgreementThreshold.commitProve`); `GordieHowe.Ligero.MaskTest.Pieces` is the system with masks as
tested piece rows.

**Shared by both maskings.**

* **the commit rounds** (`commitSpec`) are the low-degree challenges of the `nrep` repetitions,
  `r j : Fin R → F` for repetition `j` (the coefficients of the data rows after `ILDT_j`, whose
  coefficient is one), and the low-degree responses `w j`, each the values of a polynomial of
  degree `< k` at the first `k` response nodes;
* **the proof phase** (`proofSpec`) is the constraint challenge, the masked linear and quadratic
  responses and the column query, with round errors `proofError`;
* **the agreement threshold** (`Threshold`: `A`, a line certificate with `B` exceptional
  challenges per line) and the commit phase on the encoded rows (`Tableau.Rows`): the agreement
  set `D_j` of `w j` with `ILDT_j + Σ r_{j,i} U_i` (`agreementSet` of repetition `j`'s matrix),
  and their intersection `D*` (`commonAgreement`); the tableau rows interpolated on the first `k`
  columns of `D*` when `|D*| ≥ A`, zero otherwise (`Threshold.pinnedRows`); the commit event,
  every repetition's challenge in the exceptional set of the line certificate for its matrix
  (`Threshold.Exceptional`, `Threshold.commitEvent`), of density `(B / (|F| - 1)) ^ nrep`
  (`Threshold.commitError`, `Threshold.card_piFinset_exceptional`: the exceptional sets are
  fixed by the encoded rows and the challenges are independent);
* **the prepared tableau** (`TableauSetup`: the threshold, the placement, the row order, the rate,
  the query count `t` and the number of repetitions `nrep`), with the extracted cells (`TableauSetup.extract`, the placed cells of
  the pinned rows) and the honest prover's data (`TableauSetup.Hiding`: admissible cells, the placed
  cells, the honest witness of the tableau).

**The system with untested masks** (`commitProve`): the oracle message is the encoded rows with
the IDOT and IQUAD masks (`Tableau.Commitment`), with its columns as leaves
(`Tableau.Commitment.leaf`); the verdict is the tableau verifier `Ligero.Tableau.accept` with the
low-degree challenge and response taken from the commit rounds.

**Soundness** (`sound`). The commit event is that every low-degree challenge is exceptional.
Outside it, with `D = D*` fixed by the commit phase before the query:

* if `|D| < A`, every accepted query lies in `D` (a low-degree column check fails outside
  `D`), so at most `(A - 1).descFactorial t` queries are accepted (`card_filter_le_of_lt`);
* if `|D| ≥ A`, some repetition is not exceptional and its agreement set contains `D`, so every
  tableau row agrees on all of `D` with a polynomial of degree `< k`, which is the pinned row
  (`Threshold.pinnedRows_agree`; `ILDT_0` through repetition `0`'s check,
  `rowsAgreeOn_tableau`); if the rows hold on the extracted cells the claim
  holds, otherwise the constraints fail on the pinned rows and the arbitrary-mask list argument
  (`GordieHowe.Ligero.UntestedMaskRow.constraintBad`, `GordieHowe.Ligero.UntestedMaskRow.selected_query_count`) costs `l / |F|` at the
  constraint challenge (`testError`) and `a.descFactorial t` queries at the column query, the
  accepted queries lying in `D` where the rows equal the pinned rows.

The column query costs the sum of the two counts over `N.descFactorial t` (`columnError`).

**The honest prover** (`honest`): the placed cells, Ligero's blinding coins and the commitment
`Ligero.HVZK.commitOf`, with the low-degree response sent in the commit phase
(`honestLdtResponse`, the first component of `Ligero.HVZK.responseOf`, which reads neither the
context nor the constraint challenge) and the masked responses in the proof phase. Completeness
is `Ligero.Completeness.accept`; hiding is `Ligero.HVZK.identDistrib` at each fixed vector of
admissible cells, with the tableau simulator's low-degree responses placed in the commit rounds
of the view (`simulate`, `viewOf`): each response `w j = ILDT_j + Σ r_{j,i} U_i` is uniform
because of its own ILDT row.

The extracted cells are computable (`TableauSetup.extract`): the common agreement set is a filter
of the columns, the first `k` of its columns are found by sorting (`firstColumns`), and the cells are
Lagrange evaluations by field operations (`LigeroInterpolation.interpolateEval`).
-/

namespace GordieHowe.Ligero.AgreementThreshold
open IOP

open ProtocolSpec Polynomial
open scoped NNReal ENNReal

section

variable {F ι Q Lin : Type} [Field F] [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin]
  {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N} {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  {products : Routing.ProductLayout ι Q}

/-! ### The commit rounds -/

section CommitRounds

variable (F) (R k nrep : ℕ)

/-- **The commit rounds** after the oracle message: the low-degree challenges of the `nrep`
repetitions (`Tableau.LdtChallenge`: for repetition `j`, the coefficients of the data rows after
`ILDT_j`, whose coefficient is one), then the low-degree responses (`Tableau.LdtResponse`: for
each repetition the values of a polynomial of degree `< k` at the first `k` response nodes,
`Tableau.responseNode`). The C++ draws the `nrep · R` challenge elements in one draw and writes
the `nrep · k` response elements in one write, both repetition-major. -/
abbrev commitSpec : ProtocolSpec 2 where
  dir i := if i.val = 0 then .V_to_P else .P_to_V
  «Type» i := match i.val with
    | 0 => Tableau.LdtChallenge F R nrep
    | _ => Tableau.LdtResponse F k nrep

/-- The low-degree challenge round. -/
def ldtIdx : (commitSpec F R k nrep).ChallengeIdx := ⟨0, rfl⟩

omit [Field F] [Fintype F] in
/-- The commit rounds draw one challenge, the low-degree challenge. -/
theorem commitIdx_eq (i : (commitSpec F R k nrep).ChallengeIdx) : i = ldtIdx F R k nrep := by
  obtain ⟨⟨n, hn⟩, hi⟩ := i
  match n, hn, hi with
  | 0, _, _ => rfl
  | n + 1, _, hi => exact absurd hi (by simp)

instance (i : (commitSpec F R k nrep).ChallengeIdx) : Fintype ((commitSpec F R k nrep).Challenge i) := by
  obtain ⟨⟨n, hn⟩, hi⟩ := i
  match n, hn, hi with
  | 0, _, _ => exact inferInstanceAs (Fintype (Tableau.LdtChallenge F R nrep))
  | n + 1, _, hi => exact absurd hi (by simp)

instance [DecidableEq F] (i : (commitSpec F R k nrep).ChallengeIdx) :
    DecidableEq ((commitSpec F R k nrep).Challenge i) := by
  obtain ⟨⟨n, hn⟩, hi⟩ := i
  match n, hn, hi with
  | 0, _, _ => exact inferInstanceAs (DecidableEq (Tableau.LdtChallenge F R nrep))
  | n + 1, _, hi => exact absurd hi (by simp)

instance (i : (commitSpec F R k nrep).ChallengeIdx) : Nonempty ((commitSpec F R k nrep).Challenge i) := by
  obtain ⟨⟨n, hn⟩, hi⟩ := i
  match n, hn, hi with
  | 0, _, _ => exact inferInstanceAs (Nonempty (Tableau.LdtChallenge F R nrep))
  | n + 1, _, hi => exact absurd hi (by simp)

/-- The full transcript of the commit rounds. -/
abbrev CommitRounds : Type := (commitSpec F R k nrep).Transcript (Fin.last 2)

variable {F R k nrep}

/-- The low-degree challenges of the commit rounds. -/
def ldtChallenge (tr : CommitRounds F R k nrep) : Tableau.LdtChallenge F R nrep := tr ⟨0, by decide⟩

/-- The low-degree responses of the commit rounds. -/
def ldtResponse (tr : CommitRounds F R k nrep) : Tableau.LdtResponse F k nrep := tr ⟨1, by decide⟩

/-- **The commit rounds from their two entries**: the low-degree challenges `r` and the
low-degree responses `w`. -/
def commitTranscript (r : Tableau.LdtChallenge F R nrep) (w : Tableau.LdtResponse F k nrep) : CommitRounds F R k nrep :=
  fun i => match i with
    | ⟨0, _⟩ => r
    | ⟨1, _⟩ => w

omit [Field F] [Fintype F] in
@[simp] theorem ldtChallenge_commitTranscript (r : Tableau.LdtChallenge F R nrep) (w : Tableau.LdtResponse F k nrep) :
    ldtChallenge (commitTranscript r w) = r :=
  rfl

omit [Field F] [Fintype F] in
@[simp] theorem ldtResponse_commitTranscript (r : Tableau.LdtChallenge F R nrep) (w : Tableau.LdtResponse F k nrep) :
    ldtResponse (commitTranscript r w) = w :=
  rfl

/-- **The honest commit rounds**: the low-degree challenges, then the responses `f` to them. -/
def honestCommitRounds (f : Tableau.LdtChallenge F R nrep → Tableau.LdtResponse F k nrep) :
    CausalTranscript (commitSpec F R k nrep) where
  transcript ch := commitTranscript (ch (ldtIdx F R k nrep)) (f (ch (ldtIdx F R k nrep)))
  challenge ch i := by
    obtain rfl := commitIdx_eq F R k nrep i
    rfl
  causal i ch ch' h := by
    obtain ⟨⟨i, hi⟩, hd⟩ := i
    match i, hi, hd with
    | 0, _, h0 => exact absurd h0 (by simp)
    | 1, _, _ => exact congrArg f (h (ldtIdx F R k nrep) (Fin.mk_lt_mk.mpr Nat.zero_lt_one))

end CommitRounds

/-! ### The proof phase -/

section ProofSpec

variable (F N nL nQ) (k t : ℕ)

/-- The constraint challenge: the coefficients of the linear and of the quadratic checks. -/
abbrev ConstraintChallenge : Type := (Fin nL → F) × (Fin nQ → F)

/-- The masked responses: the values of the linear and of the quadratic response at the first
`2k − 1` response nodes (the last two components of `Tableau.Response`). -/
abbrev MaskedResponse : Type := (Fin (2 * k - 1) → F) × (Fin (2 * k - 1) → F)

/-- **The proof phase**: the constraint challenge, the masked responses and the column query; the
two-stage test `TwoStageTest.spec` without its mask round `0` (the masks are in the oracle
message or recombined from it). -/
abbrev proofSpec : ProtocolSpec 3 :=
  (TwoStageTest.spec (Tableau.Aux F N) (ConstraintChallenge F nL nQ) (MaskedResponse F k)
    (Tableau.Query N t)).dropMsg 0

omit [Field F] [Fintype F] in
/-- The mask round of the two-stage test is a prover round. -/
theorem maskRound_dir :
    (TwoStageTest.spec (Tableau.Aux F N) (ConstraintChallenge F nL nQ) (MaskedResponse F k)
      (Tableau.Query N t)).dir 0 = .P_to_V :=
  rfl

/-- The column query round. -/
def queryIdx : (proofSpec F N nL nQ k t).ChallengeIdx := ⟨2, rfl⟩

/-- The proof phase's challenge types are finite. -/
instance (i : (proofSpec F N nL nQ k t).ChallengeIdx) :
    Fintype ((proofSpec F N nL nQ k t).Challenge i) :=
  letI := Tableau.Query.fintype N t
  inferInstance

/-- The proof phase's challenge types have decidable equality. -/
instance [DecidableEq F] (i : (proofSpec F N nL nQ k t).ChallengeIdx) :
    DecidableEq ((proofSpec F N nL nQ k t).Challenge i) :=
  ProtocolSpec.dropMsg_decidableEq i

/-- The proof phase draws the column query. -/
instance : Nonempty (proofSpec F N nL nQ k t).ChallengeIdx :=
  ⟨queryIdx F N nL nQ k t⟩

variable {F N nL nQ k t}

/-- The column query of a challenge vector. -/
def chQuery (ch : (proofSpec F N nL nQ k t).Challenges) : Tableau.Query N t :=
  ch (queryIdx F N nL nQ k t)

/-- The constraint challenge of a full transcript. -/
def constraintOf (tr : (proofSpec F N nL nQ k t).Transcript (Fin.last 3)) :
    ConstraintChallenge F nL nQ :=
  tr ⟨0, Nat.zero_lt_succ _⟩

/-- The masked responses of a full transcript. -/
def maskedOf (tr : (proofSpec F N nL nQ k t).Transcript (Fin.last 3)) : MaskedResponse F k :=
  tr ⟨1, Nat.one_lt_succ_succ _⟩

/-- The column query of a full transcript. -/
def queryOf (tr : (proofSpec F N nL nQ k t).Transcript (Fin.last 3)) : Tableau.Query N t :=
  tr ⟨2, Nat.lt_succ_self _⟩

variable (k t) in
/-- The constraint challenge round. -/
def constraintIdx : (proofSpec F N nL nQ k t).ChallengeIdx := ⟨0, rfl⟩

omit [Field F] [Fintype F] in
/-- The proof phase has two challenge rounds, the constraint challenge and the column query. -/
theorem proof_challengeIdx_cases (i : (proofSpec F N nL nQ k t).ChallengeIdx) :
    i = constraintIdx k t ∨ i = queryIdx F N nL nQ k t := by
  obtain ⟨⟨i, hi⟩, hd⟩ := i
  match i, hi, hd with
  | 0, _, _ => exact .inl rfl
  | 1, _, h => cases h
  | 2, _, _ => exact .inr rfl

/-- The constraint challenge of a challenge vector. -/
def chConstraint (ch : (proofSpec F N nL nQ k t).Challenges) : ConstraintChallenge F nL nQ :=
  ch (constraintIdx k t)

/-- **A full transcript of the proof phase from its three entries**: the constraint challenge, the
masked responses and the column query. -/
def proofTranscript (rc : ConstraintChallenge F nL nQ) (p : MaskedResponse F k)
    (q : Tableau.Query N t) : (proofSpec F N nL nQ k t).Transcript (Fin.last 3) :=
  fun i => match i with
    | ⟨0, _⟩ => rc
    | ⟨1, _⟩ => p
    | ⟨2, _⟩ => q

/-- **The honest proof phase**: the constraint challenge, the masked responses `f` to it, the
column query. -/
def honestProof (f : ConstraintChallenge F nL nQ → MaskedResponse F k) :
    CausalTranscript (proofSpec F N nL nQ k t) where
  transcript ch := proofTranscript (chConstraint ch) (f (chConstraint ch)) (chQuery ch)
  challenge ch i := by
    rcases proof_challengeIdx_cases i with rfl | rfl <;> rfl
  causal i ch ch' h := by
    obtain ⟨⟨i, hi⟩, hd⟩ := i
    match i, hi, hd with
    | 0, _, h0 => cases h0
    | 1, _, _ => exact congrArg f (h (constraintIdx k t) (Fin.mk_lt_mk.mpr Nat.zero_lt_one))
    | 2, _, h2 => cases h2

/-- **The errors of the proof phase**: `test` at the constraint challenge and `column` at the
column query. -/
def proofError (test column : ℝ≥0) : (proofSpec F N nL nQ k t).ChallengeIdx → ℝ≥0 :=
  fun i => TwoStageTest.error test column (dropChallengeIdx i)

omit [Field F] [Fintype F] in
/-- Every round error of the proof phase is at most `δ` when the test and column errors are. -/
theorem proofError_le_of {test column δ : ℝ≥0} (htest : test ≤ δ) (hcol : column ≤ δ)
    (i : (proofSpec F N nL nQ k t).ChallengeIdx) : proofError test column i ≤ δ := by
  unfold proofError TwoStageTest.error
  split_ifs
  exacts [htest, hcol]

omit [Field F] [Fintype F] in
/-- The column query's round error is the column error. -/
theorem proofError_queryIdx (test column : ℝ≥0) :
    proofError (F := F) (N := N) (nL := nL) (nQ := nQ) (k := k) (t := t) test column
      (queryIdx F N nL nQ k t) = column :=
  rfl

omit [Field F] [Fintype F] in
/-- The errors of the proof phase sum to the test and column errors. -/
theorem sum_proofError (test column : ℝ≥0) :
    ∑ i, proofError (F := F) (N := N) (nL := nL) (nQ := nQ) (k := k) (t := t) test column i =
      test + column :=
  (sum_dropChIdx (maskRound_dir F N nL nQ k t) _).trans (TwoStageTest.error_sum _ _)

end ProofSpec

/-! ### The low-degree test's agreement sets and the interpolated rows -/

/-- The low-degree response polynomial: the interpolant of the response values on the first `k`
response nodes (`Tableau.Response.code` of a response with these values). -/
noncomputable def responsePoly (C : GordieHowe.RSCode F N) (w : Fin C.k → F) : F[X] :=
  LigeroInterpolation.interpolate (Tableau.responseNode C C.k) w

omit [Fintype F] in
theorem natDegree_responsePoly_lt (w : Fin C.k → F) : (responsePoly C w).natDegree < C.k :=
  LigeroInterpolation.interpolate_degree C.k_pos
    (Tableau.responseNode_injective C (Tableau.k_le_N C)) _

omit [Fintype F] in
theorem code_eq_responsePoly {nrep : ℕ} (w : Tableau.LdtResponse F C.k nrep)
    (p : MaskedResponse F C.k) (j : Fin nrep) :
    Tableau.Response.code C (w, p) j = responsePoly C (w j) :=
  rfl

/-- **The agreement set of one low-degree check**: the columns `j` at which the low-degree
response's value equals `U 0 j + Σ r_i U (i + 1) j` (`AffineCodeTest.projection`), i.e. where the
low-degree column check of the matrix `U` passes. -/
def agreementSet [DecidableEq F] (C : GordieHowe.RSCode F N) (U : RSCode.Matrix F (R + 1) N)
    (r : Fin R → F) (w : Fin C.k → F) : Finset (Fin N) :=
  Finset.univ.filter fun j => AffineCodeTest.projection U r j =
    LigeroInterpolation.interpolateEval (Tableau.responseNode C C.k) w (C.D j)

omit [Fintype F] in
theorem mem_agreementSet [DecidableEq F] {U : RSCode.Matrix F (R + 1) N} {r : Fin R → F}
    {w : Fin C.k → F} {j : Fin N} :
    j ∈ agreementSet C U r w ↔
      AffineCodeTest.projection U r j = (responsePoly C w).eval (C.D j) := by
  simp only [agreementSet, Finset.mem_filter, Finset.mem_univ, true_and, responsePoly,
    LigeroInterpolation.eval_interpolate]

/-- **The common agreement set `D*` of the `nrep` repetitions**: the columns at which the
low-degree check of every repetition passes (`mem_commonAgreement`). -/
def commonAgreement [DecidableEq F] {nrep : ℕ} (C : GordieHowe.RSCode F N)
    (O : Tableau.Rows F N R nrep) (r : Tableau.LdtChallenge F R nrep)
    (w : Tableau.LdtResponse F C.k nrep) : Finset (Fin N) :=
  Finset.univ.filter fun col => ∀ j, AffineCodeTest.projection (O.ldtMatrix j) (r j) col =
    LigeroInterpolation.interpolateEval (Tableau.responseNode C C.k) (w j) (C.D col)

omit [Fintype F] in
theorem mem_commonAgreement [DecidableEq F] {nrep : ℕ} {O : Tableau.Rows F N R nrep}
    {r : Tableau.LdtChallenge F R nrep} {w : Tableau.LdtResponse F C.k nrep} {col : Fin N} :
    col ∈ commonAgreement C O r w ↔ ∀ j, col ∈ agreementSet C (O.ldtMatrix j) (r j) (w j) := by
  simp only [commonAgreement, agreementSet, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype F] in
/-- The common agreement set lies in the agreement set of every repetition. -/
theorem commonAgreement_subset [DecidableEq F] {nrep : ℕ} (O : Tableau.Rows F N R nrep)
    (r : Tableau.LdtChallenge F R nrep) (w : Tableau.LdtResponse F C.k nrep) (j : Fin nrep) :
    commonAgreement C O r w ⊆ agreementSet C (O.ldtMatrix j) (r j) (w j) :=
  fun _ h => mem_commonAgreement.mp h j

omit [Fintype F] in
/-- **With a single repetition the common agreement set is the agreement set** of the tableau. -/
theorem commonAgreement_eq_of_subsingleton [DecidableEq F] {nrep : ℕ} [NeZero nrep]
    [Subsingleton (Fin nrep)] (O : Tableau.Rows F N R nrep) (r : Tableau.LdtChallenge F R nrep)
    (w : Tableau.LdtResponse F C.k nrep) :
    commonAgreement C O r w = agreementSet C O.tableau (r 0) (w 0) := by
  ext col
  rw [mem_commonAgreement]
  exact ⟨fun h => h 0, fun h j => Subsingleton.elim 0 j ▸ h⟩

omit [Fintype F] in
/-- **With one repetition the common agreement set is the agreement set** of the tableau. -/
theorem commonAgreement_one [DecidableEq F] (O : Tableau.Rows F N R 1)
    (r : Tableau.LdtChallenge F R 1) (w : Tableau.LdtResponse F C.k 1) :
    commonAgreement C O r w = agreementSet C O.tableau (r 0) (w 0) :=
  commonAgreement_eq_of_subsingleton O r w

omit [Fintype F] in
/-- **Accepted queries lie in the common agreement set**: the low-degree column check of some
repetition fails outside it. -/
theorem mem_commonAgreement_of_accept {nrep : ℕ} [NeZero nrep] {O : Tableau.Rows F N R nrep}
    {u : Tableau.Aux F N} {L : Tableau.LinearSystem (nL := nL) C P}
    {r : Tableau.LdtChallenge F R nrep} {rc : ConstraintChallenge F nL nQ}
    {w : Tableau.LdtResponse F C.k nrep} {p : MaskedResponse F C.k} {t : ℕ}
    {q : Tableau.Query N t} [DecidableEq F] (h : Tableau.AcceptProp C P L O u (r, rc) (w, p) q)
    (s : Fin t) : q s ∈ commonAgreement C O r w :=
  mem_commonAgreement.mpr fun j => mem_agreementSet.mpr (h.2.1 j s)

open Classical in
/-- **Queries inside a set of fewer than `A` columns**: at most `(A − 1).descFactorial t` query
tuples have all their columns in `D` when `|D| < A`. -/
theorem card_filter_le_of_lt {D : Finset (Fin N)} {A t : ℕ} (hD : D.card < A)
    {p : Tableau.Query N t → Prop} (hp : ∀ q, p q → ∀ s, q s ∈ D) :
    (Finset.univ.filter p).card ≤ (A - 1).descFactorial t :=
  le_trans (Finset.card_le_card fun q hq =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp q (Finset.mem_filter.mp hq).2⟩)
    ((Fintype.card_embedding_filter_mem D).trans_le
      (Nat.descFactorial_le (k := D.card) t (by omega)))

/-- **A count of query tuples as a fraction**: at most `a + b` of the `N.descFactorial t` query
tuples is at most `(a + b) / N.descFactorial t` of them, for `t ≤ N`. -/
theorem card_le_fraction {t : ℕ} (ht : t ≤ N) {s : Finset (Tableau.Query N t)} {a b : ℕ}
    (h : s.card ≤ a + b) :
    (s.card : ℝ≥0) ≤ ((a + b : ℝ≥0) / N.descFactorial t) * Fintype.card (Tableau.Query N t) := by
  have hcard : Fintype.card (Tableau.Query N t) = N.descFactorial t := by
    simp only [Tableau.Query, Fintype.card_embedding_eq, Fintype.card_fin]
  have hpos : (0 : ℝ≥0) < (N.descFactorial t : ℕ) := by
    exact_mod_cast Nat.descFactorial_pos.mpr ht
  rw [hcard, div_mul_cancel₀ _ (ne_of_gt hpos)]
  exact_mod_cast h

/-- **The first `k` columns of `D`** in increasing order, for `k ≤ |D|`. -/
def firstColumns (D : Finset (Fin N)) {k : ℕ} (h : k ≤ D.card) : Fin k ↪ Fin N :=
  (Fin.castLEEmb h).trans (D.orderEmbOfFin rfl).toEmbedding

theorem firstColumns_mem (D : Finset (Fin N)) {k : ℕ} (h : k ≤ D.card) (s : Fin k) :
    firstColumns D h s ∈ D :=
  D.orderEmbOfFin_mem rfl _

/-- **The rows interpolated on the columns `cols`**: row `i` is the polynomial of degree `< k`
through the values of `U i` at the `k` columns. -/
noncomputable def interpolatedRows {m : ℕ} (C : GordieHowe.RSCode F N) (U : RSCode.Matrix F m N)
    (cols : Fin C.k ↪ Fin N) : Fin m → F[X] :=
  fun i => LigeroInterpolation.interpolate (fun s => C.D (cols s)) (fun s => U i (cols s))

omit [Fintype F] in
theorem natDegree_interpolatedRows_lt {m : ℕ} (U : RSCode.Matrix F m N) (cols : Fin C.k ↪ Fin N)
    (i : Fin m) : (interpolatedRows C U cols i).natDegree < C.k :=
  LigeroInterpolation.interpolate_degree C.k_pos (C.D_injective.comp cols.injective) _

omit [Fintype F] in
/-- Rows of degree `< k` that agree with `U` on a column set containing the `k` columns `cols` are
the rows interpolated on `cols`. -/
theorem interpolatedRows_eq {m : ℕ} {U : RSCode.Matrix F m N} {D : Finset (Fin N)}
    {fs : Fin m → F[X]} (hfs : RSCode.RowsAgreeOn C U D fs)
    {cols : Fin C.k ↪ Fin N} (hcols : ∀ s, cols s ∈ D) : interpolatedRows C U cols = fs := by
  classical
  funext i
  symm
  refine Lagrange.eq_interpolate_of_eval_eq _ (C.D_injective.comp cols.injective).injOn ?_
    fun s _ => hfs.agree i _ (hcols s)
  rw [Finset.card_univ, Fintype.card_fin]
  exact degree_le_natDegree.trans_lt (by exact_mod_cast hfs.degree i)

omit [Fintype F] in
/-- **The tableau agrees with codewords on the common agreement set when one repetition does**:
if the matrix of repetition `ρ` agrees on its agreement set with polynomials `fs` of degree
`< k`, then the tableau (`Rows.tableau`: `ILDT_0` and the data rows) agrees on the common
agreement set `D*` with polynomials of degree `< k`. The data rows are those of `fs`; `ILDT_0`
agrees on `D*` with `w_0 − Σ_i r_{0,i} f_{i+1}`, by repetition `0`'s check, which passes on
`D*`. -/
theorem rowsAgreeOn_tableau [DecidableEq F] {nrep : ℕ} [NeZero nrep]
    {O : Tableau.Rows F N R nrep} {r : Tableau.LdtChallenge F R nrep}
    {w : Tableau.LdtResponse F C.k nrep} {ρ : Fin nrep} {fs : Fin (R + 1) → F[X]}
    (hfs : RSCode.RowsAgreeOn C (O.ldtMatrix ρ) (agreementSet C (O.ldtMatrix ρ)
      (r ρ) (w ρ)) fs) :
    RSCode.RowsAgreeOn C O.tableau (commonAgreement C O r w)
      (Fin.cons (responsePoly C (w 0) - ∑ i, r 0 i • fs i.succ) fun i => fs i.succ) := by
  have hdata : ∀ i, ∀ col ∈ commonAgreement C O r w, (fs i.succ).eval (C.D col) = O.data i col :=
    fun i col hcol => hfs.agree i.succ col (commonAgreement_subset O r w ρ hcol)
  refine ⟨?_, ?_⟩
  · intro row
    refine Fin.cases ?_ (fun i => hfs.degree i.succ) row
    have hb : (∑ i, r 0 i • fs i.succ).natDegree ≤ C.k - 1 :=
      natDegree_sum_le_of_forall_le _ _ fun i _ =>
        (natDegree_smul_le _ _).trans (Nat.le_sub_one_of_lt (hfs.degree i.succ))
    exact (natDegree_sub_le _ _).trans_lt
      (max_lt (natDegree_responsePoly_lt _) (hb.trans_lt (Nat.sub_lt C.k_pos one_pos)))
  · intro row col hcol
    refine Fin.cases ?_ (fun i => ?_) row
    · have h0 := mem_agreementSet.mp (commonAgreement_subset O r w 0 hcol)
      simp only [AffineCodeTest.projection, Tableau.Rows.ldtMatrix_zero,
        Tableau.Rows.ldtMatrix_succ] at h0
      simp only [Fin.cons_zero, eval_sub, eval_finsetSum, eval_smul, smul_eq_mul,
        hdata _ col hcol, ← h0, Tableau.Rows.tableau_zero]
      ring
    · simp only [Fin.cons_succ, Tableau.Rows.tableau_succ, hdata i col hcol]

/-! ### The agreement threshold and the commit phase -/

/-- **An agreement threshold for the code `C`**: a number `A` with `k ≤ A`, and a line certificate
at threshold `A` with at most `B` exceptional challenges per line
(`RSCode.LineCertificate`), a parameter fact about the code. The commit phase of
Ligero at agreement threshold `A` reads the tableau through it (`pinnedRows`, `exceptional`,
`commitEvent`). -/
structure Threshold (C : GordieHowe.RSCode F N) where
  A : ℕ
  k_le_A : C.k ≤ A
  B : ℝ≥0
  line : RSCode.LineCertificate C A B

namespace Threshold

variable (th : Threshold C) {nrep : ℕ}

/-- **The pinned rows** of the commit phase: when the common agreement set `D*` of the low-degree
test (`commonAgreement`) has at least `A` columns, every tableau row (`Rows.tableau`) interpolated
on the first `k` columns of `D*`; the zero rows otherwise. -/
noncomputable def pinnedRows [DecidableEq F] [NeZero nrep] (O : Tableau.Rows F N R nrep)
    (tr : CommitRounds F R C.k nrep) : Fin (R + 1) → F[X] :=
  if h : th.A ≤ (commonAgreement C O (ldtChallenge tr) (ldtResponse tr)).card then
    interpolatedRows C O.tableau (firstColumns _ (th.k_le_A.trans h))
  else 0

omit [Fintype F] in
theorem natDegree_pinnedRows_lt [DecidableEq F] [NeZero nrep] (O : Tableau.Rows F N R nrep)
    (tr : CommitRounds F R C.k nrep) (i : Fin (R + 1)) :
    (th.pinnedRows O tr i).natDegree < C.k := by
  unfold pinnedRows
  split_ifs
  · exact natDegree_interpolatedRows_lt _ _ i
  · simpa using C.k_pos

/-- **The exceptional challenges of a matrix**: a set of low-degree challenges outside which a
low-degree response agreeing with `U 0 + Σ r_i U (i + 1)` on at least `A` columns makes every row
agree with a polynomial of degree `< k` on all of them
(`RSCode.exists_exceptional_rowsAgreeOn`, chosen; it depends on `U` only). -/
noncomputable def exceptional (U : RSCode.Matrix F (R + 1) N) : Finset (Fin R → F) :=
  (RSCode.exists_exceptional_rowsAgreeOn C th.line th.k_le_A U).choose

/-- **Every low-degree challenge is exceptional** for its repetition's matrix: the commit phase
was bad. -/
def Exceptional (O : Tableau.Rows F N R nrep) (tr : CommitRounds F R C.k nrep) : Prop :=
  ∀ j, ldtChallenge tr j ∈ th.exceptional (O.ldtMatrix j)

theorem exceptional_iff {O : Tableau.Rows F N R nrep} {tr : CommitRounds F R C.k nrep} :
    th.Exceptional O tr ↔ ∀ j, ldtChallenge tr j ∈ th.exceptional (O.ldtMatrix j) :=
  Iff.rfl

/-- **With one repetition the commit phase is bad** exactly when its challenge is exceptional for
the tableau. -/
theorem exceptional_one_iff {O : Tableau.Rows F N R 1} {tr : CommitRounds F R C.k 1} :
    th.Exceptional O tr ↔ ldtChallenge tr 0 ∈ th.exceptional O.tableau :=
  ⟨fun h => h 0, fun h j => Subsingleton.elim j 0 ▸ h⟩

/-- **The commit error**: `(B / (|F| - 1)) ^ nrep`, the density of the challenge vectors whose
`nrep` challenges are all exceptional. -/
noncomputable def commitError (nrep : ℕ) : ℝ≥0 := (th.B / (Fintype.card F - 1)) ^ nrep

@[simp] theorem commitError_one : th.commitError 1 = th.B / (Fintype.card F - 1) :=
  pow_one _

/-- The exceptional challenges of one matrix are at most a `B / (|F| - 1)` fraction of the
challenges. -/
theorem card_exceptional (U : RSCode.Matrix F (R + 1) N) :
    ((th.exceptional U).card : ℝ≥0) ≤ th.B / (Fintype.card F - 1) * Fintype.card (Fin R → F) :=
  RSCode.card_le_density
    (RSCode.exists_exceptional_rowsAgreeOn C th.line th.k_le_A U).choose_spec.1

/-- **The challenge vectors whose challenges are all exceptional** are at most a `commitError`
fraction: the repetitions' challenges are independent and each repetition's exceptional set is
fixed by the encoded rows. -/
theorem card_piFinset_exceptional (O : Tableau.Rows F N R nrep) :
    ((Fintype.piFinset fun j => th.exceptional (O.ldtMatrix j)).card : ℝ≥0) ≤
      th.commitError nrep * Fintype.card (Tableau.LdtChallenge F R nrep) := by
  rw [Fintype.card_piFinset, Fintype.card_pi, commitError, Nat.cast_prod, Nat.cast_prod,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← mul_pow, ← Fin.prod_const]
  exact Finset.prod_le_prod' fun j _ => th.card_exceptional (O.ldtMatrix j)

/-- Outside the exceptional challenges, an agreement set of at least `A` columns makes every row
agree on all of it with a polynomial of degree `< k`. -/
theorem exists_rowsAgreeOn [DecidableEq F] {U : RSCode.Matrix F (R + 1) N} {r : Fin R → F}
    (hr : r ∉ th.exceptional U) {w : Fin C.k → F} (hD : th.A ≤ (agreementSet C U r w).card) :
    ∃ fs, RSCode.RowsAgreeOn C U (agreementSet C U r w) fs := by
  obtain ⟨fs, hfs, -⟩ :=
    (RSCode.exists_exceptional_rowsAgreeOn C th.line th.k_le_A U).choose_spec.2 r hr
      (natDegree_responsePoly_lt w) hD fun j hj => (mem_agreementSet.mp hj).symm
  exact ⟨fs, hfs⟩

/-- **Outside the commit event the pinned rows agree with the tableau on the common agreement
set**, when it has at least `A` columns. Some repetition `ρ` has a challenge that is not
exceptional for its matrix; its agreement set contains `D*`, so it has at least `A` columns and
the matrix agrees on it with codewords (`exists_rowsAgreeOn`); then the tableau agrees on `D*`
with codewords (`rowsAgreeOn_tableau`), which are the pinned rows (`interpolatedRows_eq`). -/
theorem pinnedRows_agree [DecidableEq F] [NeZero nrep] {O : Tableau.Rows F N R nrep}
    {tr : CommitRounds F R C.k nrep} (hr : ¬ th.Exceptional O tr)
    (hD : th.A ≤ (commonAgreement C O (ldtChallenge tr) (ldtResponse tr)).card) {col : Fin N}
    (hcol : col ∈ commonAgreement C O (ldtChallenge tr) (ldtResponse tr)) (i : Fin (R + 1)) :
    O.tableau i col = (th.pinnedRows O tr i).eval (C.D col) := by
  obtain ⟨ρ, hρ⟩ := not_forall.mp hr
  obtain ⟨fs, hfs⟩ := th.exists_rowsAgreeOn hρ (hD.trans (Finset.card_le_card
    (commonAgreement_subset O (ldtChallenge tr) (ldtResponse tr) ρ)))
  have hgs := rowsAgreeOn_tableau hfs
  rw [pinnedRows, dite_eq_left hD, interpolatedRows_eq hgs (firstColumns_mem _ _)]
  exact (hgs.agree i col hcol).symm

/-- **A pinned row with a value outside the subfield at a point of it**: outside the commit
event, if the pinned row `i` takes a value outside the subfield `E` at a point of `E`, then row
`i` of the tableau agrees on the common agreement set with the pinned row, a polynomial of degree
`< k` with a coefficient outside `E`. (A value outside `E` makes the pinned rows nonzero, so the
common agreement set has at least `A` columns; `Polynomial.eval_mem_of_coeff_mem` gives the
coefficient.) -/
theorem agreesWithNonSubfield_pinnedRows [DecidableEq F] [NeZero nrep] (E : Subfield F)
    {O : Tableau.Rows F N R nrep} {tr : CommitRounds F R C.k nrep}
    (hr : ¬ th.Exceptional O tr) {i : Fin (R + 1)} {x : F} (hx : x ∈ E)
    (hval : (th.pinnedRows O tr i).eval x ∉ E) :
    SubfieldTest.AgreesWithNonSubfield E C.D C.k
      (commonAgreement C O (ldtChallenge tr) (ldtResponse tr)) (O.tableau i)
        (th.pinnedRows O tr i) := by
  have hD : th.A ≤ (commonAgreement C O (ldtChallenge tr) (ldtResponse tr)).card := by
    by_contra hD
    apply hval
    rw [pinnedRows, dite_eq_right hD]
    simp
  refine ⟨th.natDegree_pinnedRows_lt O tr i, ?_, fun j hj => th.pinnedRows_agree hr hD hj i⟩
  by_contra hc
  push Not at hc
  exact hval (Polynomial.eval_mem_of_coeff_mem E hc hx)

/-- **The commit event** on oracle messages `Com` read as encoded rows by `tab`: every
low-degree challenge is exceptional for its repetition's matrix. -/
def commitEvent {Com : Type} (tab : Com → Tableau.Rows F N R nrep)
    (i : (commitSpec F R C.k nrep).ChallengeIdx) (O : Com)
    (tr : (commitSpec F R C.k nrep).Transcript i.1.succ) : Prop :=
  (tr ⟨0, Nat.succ_pos _⟩ : Tableau.LdtChallenge F R nrep) ∈
    Fintype.piFinset fun j => th.exceptional ((tab O).ldtMatrix j)

open Classical in
/-- The commit event has probability at most `commitError nrep` over the low-degree challenges
(`card_piFinset_exceptional`). -/
theorem commitEvent_bound {Com : Type} (tab : Com → Tableau.Rows F N R nrep) :
    (commitSpec F R C.k nrep).EventBound (th.commitEvent tab) fun _ => th.commitError nrep := by
  intro i O tr
  obtain rfl := commitIdx_eq F R C.k nrep i
  rw [← card_le_iff_probUniform_le]
  have he : (Finset.univ.filter fun ch : (commitSpec F R C.k nrep).Challenge (ldtIdx F R C.k nrep) =>
      th.commitEvent tab (ldtIdx F R C.k nrep) O ((commitSpec F R C.k nrep).concat tr ch)) =
        (Fintype.piFinset fun j => th.exceptional ((tab O).ldtMatrix j) :
          Finset (Tableau.LdtChallenge F R nrep)) := by
    ext ch
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact Iff.rfl
  rw [he]
  exact th.card_piFinset_exceptional (tab O)

/-- The commit phase was bad exactly when every low-degree challenge is exceptional. -/
theorem eventOccurs_iff {Com : Type} {tab : Com → Tableau.Rows F N R nrep} {O : Com}
    {tr : CommitRounds F R C.k nrep} :
    EventOccurs (th.commitEvent tab) O tr ↔ th.Exceptional (tab O) tr := by
  refine ⟨fun ⟨_, h⟩ j => Fintype.mem_piFinset.mp h j, fun h => ⟨ldtIdx F R C.k nrep, ?_⟩⟩
  exact Fintype.mem_piFinset.mpr h

end Threshold

/-! ### The prepared tableau at an agreement threshold -/

/-- **The data of a prepared Ligero tableau at agreement threshold `A`**, shared by both maskings
of the response masks, on the prepared tableau `P` of the code `C`, for cells `ι → F` with the
product layout `products` and linear rows indexed by `Lin`:

* the agreement threshold (`Threshold`: `A`, `k ≤ A`, a line certificate with at most `B`
  exceptional challenges per line);
* `placement`, `index`: where every cell and every product copy sits in the tableau, and the
  order of the prepared linear equations (the fixed layout);
* `t`, `t_le`: the number of queried columns;
* `nrep`, `nrep_pos`: the number of repetitions of the low-degree test, at least one (a parameter
  condition).

The code's decoding radius `C.e` is not used. -/
structure TableauSetup (C : GordieHowe.RSCode F N) (P : Tableau.Parameters (R := R) (nQ := nQ) C)
    (products : Routing.ProductLayout ι Q) (Lin : Type) (nL : ℕ) extends Threshold C where
  placement : Preparation.Placement C P ι Q
  index : Fin nL ≃ Routing.PreparedRow Lin Q
  t : ℕ
  t_le : t ≤ N
  /-- The number of repetitions of the low-degree test. -/
  nrep : ℕ
  /-- The low-degree test has at least one repetition. -/
  nrep_pos : 0 < nrep

namespace TableauSetup

variable (S : TableauSetup C P products Lin nL)

/-- The number of repetitions of a setup is nonzero (`nrep_pos`). -/
instance : NeZero S.nrep := ⟨S.nrep_pos.ne'⟩

/-- **The commit error of the setup**: `(B / (|F| − 1)) ^ nrep` at its number of repetitions
(`Threshold.commitError`). -/
noncomputable def commitError : ℝ≥0 := S.toThreshold.commitError S.nrep

/-- **The prepared linear system** of a family of rows: the rows' coefficients and constants, and
the copy-routing rows, at the placement (`Ligero.Preparation.formSystem`, computed from the
coefficient vectors). It is the polynomial system `Ligero.Preparation.linearSystem` of the rows'
polynomials (`linearSystem_eq`). -/
def linearSystem (rows : Lin → AffineForm F ι) : Tableau.LinearSystem (nL := nL) C P :=
  Preparation.formSystem S.placement products S.index rows

omit [Fintype F] [Fintype Lin] in
theorem linearSystem_eq (rows : Lin → AffineForm F ι) :
    S.linearSystem rows =
      Preparation.linearSystem S.placement products (fun l => (rows l).toMvPolynomial) S.index :=
  Preparation.formSystem_eq ..

omit [Fintype F] in
/-- Rows of polynomials satisfying the prepared linear system of the affine rows `rows` give
cells, read at the placement, on which `rows` and the products hold
(`Ligero.Preparation.holds_source`). -/
theorem rowsHold_of_holds (rows : Lin → AffineForm F ι) {fs : Fin (R + 1) → F[X]}
    (h : Tableau.Holds C P (S.linearSystem rows) fs) :
    RowsHold rows products (S.placement.sourceReadout fs) := by
  rw [rowsHold_iff]
  refine Preparation.holds_source S.placement products _
    (fun l => (rows l).totalDegree_toMvPolynomial_le) S.index _ ?_
  rw [← Preparation.formSystem_eq]
  exact h

/-- The proof phase's challenge types are nonempty (at most `N` queried columns). -/
instance (i : (proofSpec F N nL nQ C.k S.t).ChallengeIdx) :
    Nonempty ((proofSpec F N nL nQ C.k S.t).Challenge i) :=
  haveI : Nonempty (Tableau.Query N S.t) := Tableau.Query.nonempty_of_le S.t_le
  dropMsg_nonempty i

variable [DecidableEq F]

/-- **The cells extracted from the commit phase**: on the common agreement set `D*` of the
low-degree test (`commonAgreement`), when `|D*| ≥ A`, the value of each cell's row of the tableau
(`Rows.tableau`) interpolated on the first `k` columns of `D*` at the cell's message node; zero
otherwise. They are the placed cells of the pinned rows (`extract_eq`). No repetition is chosen.

Running time: the common agreement set is one pass over the `N` columns, each computing, for each of
the `nrep` repetitions, `ILDT_j + Σ r_{j,i} U (i + 1)` (`R` multiplications) and the response's
value by Lagrange evaluation (`LigeroInterpolation.interpolateEval`, `O(k²)` field operations); the
first `k` columns of `D*` come from sorting `D*` (`O(N log N)` comparisons); each cell is one
Lagrange evaluation on these `k` columns, `O(k²)` field operations. In total
`O(N · nrep · (R + k²) + |ι| · (N log N + k²))`. This running time is argued here, not proved in
Lean. -/
def extract (O : Tableau.Rows F N R S.nrep) (tr : CommitRounds F R C.k S.nrep) : ι → F :=
  if h : S.A ≤ (commonAgreement C O (ldtChallenge tr) (ldtResponse tr)).card then
    fun i => LigeroInterpolation.interpolateEval
      (fun s => C.D (firstColumns _ (S.k_le_A.trans h) s))
      (fun s => O.tableau (S.placement.source i).1 (firstColumns _ (S.k_le_A.trans h) s))
      (P.nodes (S.placement.source i).2)
  else 0

omit [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- The extracted cells are the placed cells of the pinned rows. -/
theorem extract_eq (O : Tableau.Rows F N R S.nrep) (tr : CommitRounds F R C.k S.nrep) :
    S.extract O tr = S.placement.sourceReadout (S.pinnedRows O tr) := by
  funext i
  unfold extract Threshold.pinnedRows
  split_ifs
  · simp only [Preparation.Placement.sourceReadout, interpolatedRows,
      LigeroInterpolation.eval_interpolate]
  · simp [Preparation.Placement.sourceReadout]

omit [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- **With one repetition the extracted cells are those of the agreement set of the tableau**:
each cell's row interpolated on the first `k` columns of `agreementSet` of the tableau, the
challenge and the response, when it has at least `A` columns. -/
theorem extract_one (hS : S.nrep = 1) (O : Tableau.Rows F N R S.nrep)
    (tr : CommitRounds F R C.k S.nrep) :
    S.extract O tr =
      if h : S.A ≤ (agreementSet C O.tableau (ldtChallenge tr 0) (ldtResponse tr 0)).card then
        fun i => LigeroInterpolation.interpolateEval
          (fun s => C.D (firstColumns _ (S.k_le_A.trans h) s))
          (fun s => O.tableau (S.placement.source i).1 (firstColumns _ (S.k_le_A.trans h) s))
          (P.nodes (S.placement.source i).2)
      else 0 := by
  have : Subsingleton (Fin S.nrep) := Fin.subsingleton_iff_le_one.mpr hS.le
  simp only [extract, commonAgreement_eq_of_subsingleton]

omit [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- An extracted cell is its pinned row's value at its message node, read through the placement's
readout. -/
theorem extract_eq_eval (O : Tableau.Rows F N R S.nrep) (tr : CommitRounds F R C.k S.nrep)
    (i : ι) : S.extract O tr i =
      (S.pinnedRows O tr (S.placement.messageReadout.row i)).eval
        (S.placement.messageReadout.point i) := by
  rw [extract_eq]
  rfl

/-! ### The honest prover shared by both maskings -/

/-- **The data of the honest prover** of a prepared tableau: the hiding layout (the rows'
blinding fields with their facts about the field and parameter conditions,
`Ligero.HVZK.HidingLayout`) and the allocation conditions of the placement (parameter conditions:
aliased coordinates hold one source variable, occupied product cells lie in a copy's column).
Completeness needs only these. -/
structure Placement (S : TableauSetup C P products Lin nL) where
  layout : HVZK.HidingLayout C P
  aliasesAgree : S.placement.AliasesAgree products
  productsCovered : S.placement.ProductsCovered

/-- **The data of the honest prover** of a prepared tableau at agreement threshold `A`: that of the
honest prover (`Placement`) and the hiding threshold `t ≤` the number of privacy positions (a
parameter condition, the paper's `nq ≤ k − ℓ`). -/
structure Hiding (S : TableauSetup C P products Lin nL) extends Placement S where
  t_le_privacy : S.t ≤ C.k - P.witness.card

variable {S} (Hd : S.Placement)

/-- **Admissible cells**: every placed value, a cell or a copy of a product operand, lies in its
row's blinding field. -/
def Placement.Admissible (x : ι → F) : Prop :=
  ∀ z (row : Fin R), (S.placement.location z).1 = row.succ →
    Routing.honestCopies products x z ∈ Hd.layout.field row

open Classical in
/-- **The committed cells**: the placement's cells of the honest copies (zero at unoccupied
cells), for admissible cells; zero otherwise. -/
noncomputable def Placement.cells (x : ι → F) : HVZK.Cells Hd.layout.toBlindingFields :=
  if h : Hd.Admissible x then S.placement.cells _ (Routing.honestCopies products x) h
  else ⟨fun _ _ => 0, fun _ _ _ => zero_mem _⟩

omit [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
theorem Placement.cells_of_admissible {x : ι → F} (h : Hd.Admissible x) :
    Hd.cells x = S.placement.cells _ (Routing.honestCopies products x) h :=
  dite_eq_left h

variable {Ctx : Type} (rows : Ctx → Lin → AffineForm F ι)

omit [DecidableEq F] in
/-- **The honest cells satisfy the tableau**: admissible cells satisfying the rows give
zero-privacy rows that satisfy the prepared linear system (`Ligero.Preparation.holds_zeroRows`). -/
noncomputable def Placement.witness {x : ι → F} (hx : Hd.Admissible x) (c : Ctx)
    (hrows : RowsHold (rows c) products x) :
    HVZK.Witness (S.linearSystem (rows c)) Hd.layout.toBlindingFields where
  toCells := Hd.cells x
  holds := by
    rw [Hd.cells_of_admissible hx, S.linearSystem_eq]
    exact Preparation.holds_zeroRows S.placement products _
      (fun l => (rows c l).totalDegree_toMvPolynomial_le) S.index _ hx Hd.aliasesAgree
      Hd.productsCovered ((rowsHold_iff _ _ _).mp hrows) (Routing.honestCopies_routing _ _)

end TableauSetup

/-! ### The honest prover's messages and the simulated leaves -/

/-- **The honest low-degree responses** for the cells `ω`, the blinding `ρ` and the low-degree
challenges `r`: for each repetition `j`, the values at the first `k` response nodes of the
interpolant of `ILDT_j`'s values plus the combination by `r j` of the data rows' values. It is the first component of
`Ligero.HVZK.responseOf` (`fst_responseOf`), which reads neither the linear system nor the
constraint challenge, so the honest prover sends it in the commit phase. -/
def honestLdtResponse {Bf : HVZK.BlindingFields C P} {hrate : 2 * C.k - 1 ≤ N} {nrep : ℕ}
    (ω : HVZK.Cells Bf) (ρ : HVZK.Coins hrate Bf nrep) (r : Tableau.LdtChallenge F R nrep) :
    Tableau.LdtResponse F C.k nrep :=
  fun j i => LigeroInterpolation.interpolateEval P.nodes
    (ρ.response.ildt j + ∑ l, r j l • HVZK.rowValues ω ρ.privacy l) (Tableau.responseNode C C.k i)

omit [Fintype F] in
theorem fst_responseOf {Bf : HVZK.BlindingFields C P} {hrate : 2 * C.k - 1 ≤ N} {nrep : ℕ}
    [NeZero nrep] (L : Tableau.LinearSystem (nL := nL) C P) (ω : HVZK.Cells Bf)
    (ρ : HVZK.Coins hrate Bf nrep) (r : Tableau.LdtChallenge F R nrep)
    (rc : ConstraintChallenge F nL nQ) :
    (HVZK.responseOf L ω ρ (r, rc)).1 = honestLdtResponse ω ρ r :=
  rfl

/-- **The leaves the verdict sees**, rebuilt from a view of the tableau (`Ligero.HVZK.View`) and
the query: the `s`-th queried column of the view, read as a leaf by `g`, at position `q s`;
nothing elsewhere. The query index is found by a search over `Fin t` (`Fin.find`). -/
def viewLeaves {L : Type} {k t nrep : ℕ} (g : Tableau.Column F R nrep × F × F → L)
    (q : Tableau.Query N t) (v : HVZK.View F R k t nrep) (j : Fin N) : Option L :=
  if h : ∃ s, q s = j then some (g (v.2 (Fin.find (fun s => q s = j) h))) else none

omit [Fintype F] in
/-- **What the verifier sees of a message is the leaves rebuilt from a view**: for a message view
querying the columns of `q`, whose table at each queried column is the leaf `g` reads off the
view's column. -/
theorem see_eq_viewLeaves {M Ch L : Type} {k t nrep : ℕ} (V : MessageView M Ch (Fin N) L)
    {ch : Ch} {q : Tableau.Query N t} (hq : V.queries ch = Finset.univ.map q)
    (g : Tableau.Column F R nrep × F × F → L) (m : M) (v : HVZK.View F R k t nrep)
    (hv : ∀ s, V.read m (q s) = g (v.2 s)) : V.see ch m = viewLeaves g q v := by
  funext j
  by_cases h : ∃ s, q s = j
  · obtain ⟨s, rfl⟩ := h
    have hs : Fin.find (fun s' => q s' = q s) ⟨s, rfl⟩ = s :=
      q.injective (Fin.find_spec (p := fun s' => q s' = q s) ⟨s, rfl⟩)
    have hmem : q s ∈ V.queries ch := hq ▸ Finset.mem_map_of_mem _ (Finset.mem_univ s)
    rw [viewLeaves, dite_eq_left ⟨s, rfl⟩, hs, MessageView.see_of_mem _ hmem m, hv]
  · have hj : j ∉ V.queries ch := by
      rw [hq]
      intro hm
      obtain ⟨s, -, hs⟩ := Finset.mem_map.mp hm
      exact h ⟨s, hs⟩
    rw [viewLeaves, dite_eq_right h]
    simp [MessageView.see, hj]

/-! ### The system with untested masks -/

/-- **The data of Ligero at agreement threshold `A` with untested masks**: the prepared tableau at
agreement threshold `A` (`TableauSetup`), and `a`, `l`, `list`: the mask agreement threshold and
list size of the arbitrary-mask list argument (`UntestedMaskRow.Parameters`; the masks are not tested
in this system). -/
structure Setup (C : GordieHowe.RSCode F N) (P : Tableau.Parameters (R := R) (nQ := nQ) C)
    (products : Routing.ProductLayout ι Q) (Lin : Type) (nL : ℕ)
    extends TableauSetup C P products Lin nL where
  /-- The mask agreement threshold. -/
  a : ℕ
  /-- The list size of the mask list. -/
  l : ℕ
  /-- The arbitrary-mask list hypotheses at `a` and `l`. -/
  list : UntestedMaskRow.Parameters C a l

/-- **The code parameters of Ligero at agreement threshold `A` with untested masks**, parameter
facts about the code `C` at the numbers `A` (the agreement threshold), `B` (the exceptional count
of the line certificate), `a` and `l` (the mask agreement threshold and list size): `k ≤ A`, a
line certificate at threshold `A` with at most `B` exceptional challenges per line
(`RSCode.LineCertificate`), and the arbitrary-mask list hypotheses
(`UntestedMaskRow.Parameters`). A configuration proves them once per tableau, the line certificate
from a weighted Johnson certificate (`RSCode.lineCertificate_of_weightedJohnson`) or,
at the unique-decoding threshold, from the unique-decoding certificate
(`RSCode.lineCertificate_uniqueDecoding`, the `A` tableau of `Falcon512.Native.ROMParams`). -/
structure Parameters (C : GordieHowe.RSCode F N) (A B a l : ℕ) : Prop where
  /-- The message length is at most the agreement threshold. -/
  k_le_A : C.k ≤ A
  /-- The line certificate at threshold `A` with at most `B` exceptional challenges per line. -/
  line : RSCode.LineCertificate C A B
  /-- The arbitrary-mask list hypotheses. -/
  list : UntestedMaskRow.Parameters C a l

omit [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- **The rate condition of the mask code**, `2k − 1 ≤ N`, from the Johnson hypotheses of the
arbitrary-mask list (`UntestedMaskRow.Parameters.rate_le`). -/
theorem Setup.rate_le (S : Setup C P products Lin nL) : 2 * C.k - 1 ≤ N :=
  S.list.rate_le

variable (S : Setup C P products Lin nL) {Ctx : Type} (rows : Ctx → Lin → AffineForm F ι)
  [DecidableEq F]

/-- The input of the proof phase: the context, the oracle message and the commit rounds. -/
abbrev Input (Ctx : Type) (F : Type) (N R k nrep : ℕ) : Type :=
  FieldProof.CommitProve.Input Ctx (Tableau.Commitment F N R nrep) (CommitRounds F R k nrep)

/-- **The verdict**: the tableau verifier on the linear system of the context's rows, the
committed tableau and masks, the low-degree challenge and response of the commit rounds, and the
constraint challenge, masked responses and query of the proof phase. -/
def verdict (c : Input Ctx F N R C.k S.nrep)
    (tr : (proofSpec F N nL nQ C.k S.t).Transcript (Fin.last 3)) : Bool :=
  Tableau.accept C P (S.linearSystem (rows c.ctx)) c.com.rows c.com.masks
    (ldtChallenge c.rounds, constraintOf tr) (ldtResponse c.rounds, maskedOf tr) (queryOf tr)

/-- **Ligero at agreement threshold `A` with untested masks as a commit-and-prove system** for the
rows `rows` and the products `products` on the setup `S`: the tableau and the masks as the oracle
message, with its columns as leaves (`Tableau.Commitment.leaf`); the low-degree challenge and
response as the commit rounds (`commitSpec`); the cells read from the rows pinned by the
low-degree test as the extracted cells (`TableauSetup.extract`); the constraint challenge, masked
responses and column query as the proof phase (`proofSpec`), with the tableau verifier as verdict
(`verdict`). -/
def commitProve : FieldProof.CommitProve F ι products Ctx rows where
  Com := Tableau.Commitment F N R S.nrep
  nLeaves := N
  Leaf := Tableau.Leaf F R S.nrep
  leaf := Tableau.Commitment.leaf
  leaf_injective := Tableau.Commitment.leaf_injective
  ofLeaves := Tableau.Commitment.ofLeaves
  leaf_ofLeaves := Tableau.Commitment.leaf_ofLeaves
  leafDefault := ⟨⟨0, 0⟩, 0, 0⟩
  nc := 2
  commitRounds := commitSpec F R C.k S.nrep
  extract O tr := S.extract O.rows tr
  n := 3
  spec := proofSpec F N nL nQ C.k S.t
  V := verdict S rows
  queries ch := Finset.univ.map (chQuery ch)
  reads c ch O O' r tr htr h := by
    have hq : queryOf tr = chQuery ch := htr (queryIdx F N nL nQ C.k S.t)
    have hl : ∀ s, O.leaf (queryOf tr s) = O'.leaf (queryOf tr s) := fun s => by
      rw [hq]
      exact h _ (Finset.mem_map_of_mem _ (Finset.mem_univ s))
    exact Tableau.accept_congr C P _
      (fun s => congrArg Tableau.Leaf.column (hl s))
      (fun s => congrArg Tableau.Leaf.dotMask (hl s))
      (fun s => congrArg Tableau.Leaf.quadMask (hl s))

/-- **The verifier queries `t` leaves** at every challenge vector: the `t` distinct queried
columns. -/
theorem card_queries (ch : (proofSpec F N nL nQ C.k S.t).Challenges) :
    ((commitProve S rows).queries ch).card = S.t := by
  simp [commitProve]

/-! ### Soundness -/

/-- **The test error**: the list cost `l / |F|` at the constraint challenge. -/
noncomputable def testError : ℝ≥0 := S.l / Fintype.card F

/-- **The column error**: `(A − 1).descFactorial t` accepted queries when the agreement set is
small, `a.descFactorial t` from the mask list otherwise, over the `N.descFactorial t` queries. -/
noncomputable def columnError : ℝ≥0 :=
  ((S.A - 1).descFactorial S.t + S.a.descFactorial S.t : ℝ≥0) / N.descFactorial S.t

/-- **The errors of the proof phase**: `testError` at the constraint challenge and `columnError`
at the column query (`proofError`). -/
noncomputable def error : (proofSpec F N nL nQ C.k S.t).ChallengeIdx → ℝ≥0 :=
  proofError (testError S) (columnError S)

omit [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
/-- Every round error of the proof phase is at most `δ` when the test and column errors are. -/
theorem error_le_of {δ : ℝ≥0} (htest : testError S ≤ δ) (hcol : columnError S ≤ δ)
    (i : (proofSpec F N nL nQ C.k S.t).ChallengeIdx) : error S i ≤ δ :=
  proofError_le_of htest hcol i

omit [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
/-- The errors of the proof phase sum to the test and column errors. -/
theorem error_sum : ∑ i, error S i = testError S + columnError S :=
  sum_proofError _ _

/-- **The round errors of Ligero at agreement threshold `A`** as numbers: the commit error at the
low-degree challenge, the test error at the constraint challenge and the column error at the
column query. -/
structure Bounds where
  /-- The commit error. -/
  commit : ℝ≥0
  /-- The test error. -/
  test : ℝ≥0
  /-- The column error. -/
  column : ℝ≥0

/-- **The round errors of Ligero at agreement threshold `A` with untested masks** on a field `F`,
at block length `N`, agreement threshold `A`, exceptional count `B`, `t` queried columns and mask
parameters `a`, `l`: those of `Threshold.commitError`, `testError` and `columnError` at a setup
with these numbers. -/
noncomputable def bounds (F : Type) [Fintype F] (N A B nrep t a l : ℕ) : Bounds :=
  ⟨((B : ℝ≥0) / (Fintype.card F - 1)) ^ nrep, (l : ℝ≥0) / Fintype.card F,
    ((A - 1).descFactorial t + a.descFactorial t : ℝ≥0) / N.descFactorial t⟩

/-- **With one repetition the commit error** is `B / (|F| − 1)`. -/
@[simp] theorem bounds_commit_one (F : Type) [Fintype F] (N A B t a l : ℕ) :
    (bounds F N A B 1 t a l).commit = (B : ℝ≥0) / (Fintype.card F - 1) :=
  pow_one _

/-- **The claim of the proof phase**: every low-degree challenge was exceptional (the commit
phase was bad, `Threshold.eventOccurs_iff`), or the rows hold on the extracted cells. -/
def Claim (c : Input Ctx F N R C.k S.nrep) : Prop :=
  S.Exceptional c.com.rows c.rounds ∨
    RowsHold (rows c.ctx) products (S.extract c.com.rows c.rounds)

/-- **The bad constraint challenges**: the selected list event (`UntestedMaskRow.constraintBad`) on
the pinned rows and the masks. -/
def Bad (c : Input Ctx F N R C.k S.nrep) (u : Tableau.Aux F N) (rc : ConstraintChallenge F nL nQ) :
    Prop :=
  UntestedMaskRow.constraintBad C P (S.linearSystem (rows c.ctx)) S.rate_le S.a
    (S.pinnedRows c.com.rows c.rounds) u rc

/-- The verdict of the two-stage test on the input, the masks, the constraint challenge, the
masked responses and the query. -/
def testAccept (c : Input Ctx F N R C.k S.nrep) (u : Tableau.Aux F N) (rc : ConstraintChallenge F nL nQ)
    (p : MaskedResponse F C.k) (q : Tableau.Query N S.t) : Bool :=
  Tableau.accept C P (S.linearSystem (rows c.ctx)) c.com.rows u (ldtChallenge c.rounds, rc)
    (ldtResponse c.rounds, p) q

omit [Fintype Lin] in
open Classical in
/-- The bad constraint challenges are at most a `testError` fraction. -/
theorem test_count (c : Input Ctx F N R C.k S.nrep) (u : Tableau.Aux F N) :
    ((Finset.univ.filter fun rc => Bad S rows c u rc).card : ℝ≥0) ≤
      testError S * Fintype.card (ConstraintChallenge F nL nQ) := by
  have h := UntestedMaskRow.constraint_bad_count C P (S.linearSystem (rows c.ctx)) S.a
    S.list (S.pinnedRows c.com.rows c.rounds) u
  unfold testError
  rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F))]
  exact_mod_cast h

open Classical in
/-- **The column count**: when the claim is false and the constraint challenge is not bad, at
most `(A − 1).descFactorial t + a.descFactorial t` queries are accepted, whatever the masked
responses. -/
theorem query_count_nat (c : Input Ctx F N R C.k S.nrep) (hc : ¬ Claim S rows c) (u : Tableau.Aux F N)
    (rc : ConstraintChallenge F nL nQ) (hbad : ¬ Bad S rows c u rc) (p : MaskedResponse F C.k) :
    (Finset.univ.filter fun q : Tableau.Query N S.t =>
      Tableau.AcceptProp C P (S.linearSystem (rows c.ctx)) c.com.rows u
        (ldtChallenge c.rounds, rc) (ldtResponse c.rounds, p) q).card ≤
      (S.A - 1).descFactorial S.t + S.a.descFactorial S.t := by
  set D := commonAgreement C c.com.rows (ldtChallenge c.rounds) (ldtResponse c.rounds)
  set L := S.linearSystem (rows c.ctx)
  have hnot : ¬ S.Exceptional c.com.rows c.rounds := fun h => hc (.inl h)
  by_cases hD : S.A ≤ D.card
  · refine le_trans ?_ (Nat.le_add_left _ _)
    by_cases hp : Tableau.Valid C P L (ldtChallenge c.rounds, rc) (ldtResponse c.rounds, p)
    · have hfalse : ¬ Tableau.Holds C P L (S.pinnedRows c.com.rows c.rounds) := by
        intro hh
        apply hc
        right
        rw [TableauSetup.extract_eq]
        exact S.rowsHold_of_holds (rows c.ctx) hh
      refine le_trans (Finset.card_le_card fun q hq => ?_)
        (UntestedMaskRow.selected_query_count C P L S.a S.list
          (S.pinnedRows c.com.rows c.rounds) (S.natDegree_pinnedRows_lt _ _) u hfalse
          (ldtChallenge c.rounds, rc) hbad _ hp S.t)
      have ha := (Finset.mem_filter.mp hq).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        Tableau.selectedAccept_of_agree C P L _ _ u _ _ q
          (fun s i => S.pinnedRows_agree hnot hD (mem_commonAgreement_of_accept ha s) i)
          ha.2.2.1 ha.2.2.2⟩
    · have he : (Finset.univ.filter fun q : Tableau.Query N S.t =>
          Tableau.AcceptProp C P L c.com.rows u (ldtChallenge c.rounds, rc)
            (ldtResponse c.rounds, p) q) = ∅ :=
        Finset.filter_eq_empty_iff.mpr fun q _ hq => hp hq.1
      rw [he]
      exact Nat.zero_le _
  · exact le_trans (card_filter_le_of_lt (not_le.mp hD) fun q hq => mem_commonAgreement_of_accept hq)
      (Nat.le_add_right _ _)

open Classical in
/-- The column count as a fraction: at most `columnError` of the queries are accepted. -/
theorem query_count (c : Input Ctx F N R C.k S.nrep) (hc : ¬ Claim S rows c) (u : Tableau.Aux F N)
    (rc : ConstraintChallenge F nL nQ) (hbad : ¬ Bad S rows c u rc) (p : MaskedResponse F C.k) :
    ((Finset.univ.filter fun q : Tableau.Query N S.t =>
      testAccept S rows c u rc p q = true).card : ℝ≥0) ≤
      columnError S * Fintype.card (Tableau.Query N S.t) := by
  have h := query_count_nat S rows c hc u rc hbad p
  rw [← Finset.filter_congr fun q _ => Tableau.accept_eq_true_iff C P _ _ u _ _ q] at h
  exact card_le_fraction S.t_le h

/-- **The two-stage test of the proof phase**, round-by-round sound relative to `Claim`: the
constraint challenge costs `testError` (`test_count`), the column query `columnError`
(`query_count`). -/
noncomputable def testProof :
    ClaimProof (TwoStageTest.spec (Tableau.Aux F N) (ConstraintChallenge F nL nQ)
      (MaskedResponse F C.k) (Tableau.Query N S.t)) (Input Ctx F N R C.k S.nrep)
      (TwoStageTest.error (testError S) (columnError S)) :=
  TwoStageTest.proof (Claim S rows) (Bad S rows) (testAccept S rows) (testError S) (columnError S)
    (fun c u _ => test_count S rows c u)
    (fun c u rc p hc hb => query_count S rows c hc u rc hb p)

/-- **Soundness of Ligero at agreement threshold `A` with untested masks** (the paper's Appendix
D.6, Security of Ligero without the mask test, with the low-degree test in the commit phase): the
commit event is that every one of the `nrep` low-degree challenges is exceptional
(`Threshold.commitEvent`), of probability at most
`TableauSetup.commitError = (B / (|F| − 1)) ^ nrep`; the proof phase is the two-stage test
(`testProof`) with the masks read from the oracle message (`ClaimProof.dropMsg`), round-by-round
sound relative to "the commit phase was bad or the rows hold on the extracted cells", with the
errors `error`: `l / |F|` at the constraint challenge and
`((A − 1).descFactorial t + a.descFactorial t) / N.descFactorial t` at the column query. -/
noncomputable def sound :
    (commitProve S rows).Sound (fun _ => S.commitError) (error S) where
  commitEvent := S.commitEvent Tableau.Commitment.rows
  commitEvent_bound := S.commitEvent_bound Tableau.Commitment.rows
  proof := ((testProof S rows).dropMsg (maskRound_dir F N nL nQ C.k S.t) id
    fun c => c.com.masks).ofFintype _ _
  V_eq _ _ := rfl
  claim_iff _ := or_congr_left S.eventOccurs_iff.symm

/-! ### The honest prover -/

variable {S} (Hd : S.Hiding)

variable (S) in
/-- **The view from a tableau view** at the low-degree challenge `r`, the constraint challenge
`rc` and the query `q`: the queried columns of the tableau view as leaves (`viewLeaves`), the
low-degree challenge and the low-degree response as the commit rounds, the constraint challenge,
the masked responses and the query as the proof-phase transcript. -/
def viewOf (r : Tableau.LdtChallenge F R S.nrep) (rc : ConstraintChallenge F nL nQ)
    (q : Tableau.Query N S.t) (v : HVZK.View F R C.k S.t S.nrep) : (commitProve S rows).View :=
  ⟨viewLeaves (fun x => ⟨x.1, x.2.1, x.2.2⟩) q v, commitTranscript r v.1.1,
    proofTranscript rc v.1.2 q⟩

/-- **The simulator** of Ligero at agreement threshold `A` with untested masks: on the context
`c`, the low-degree challenge (in `chc`) and the proof-phase challenges, the tableau simulator
`Ligero.HVZK.simulate` on the linear system of the context's rows at the low-degree and
constraint challenges and the query; its low-degree response goes into the commit rounds, its
masked responses into the proof-phase transcript and its queried columns into the leaves
(`viewOf`).

Running time: one run of `Ligero.HVZK.simulate` (polynomial in the tableau sizes, its
docstring), the verifier's computation of the prepared linear system from the rows (one pass over
the placement per row), and the assembly of the leaves, a search over the `t` queried columns for
each of the `N` positions. This running time is argued here, not proved in Lean. -/
def simulate (c : Ctx) (chc : (commitSpec F R C.k S.nrep).Challenges)
    (ch : (proofSpec F N nL nQ C.k S.t).Challenges)
    (s : HVZK.SimCoins S.rate_le Hd.layout S.t S.nrep) :
    (commitProve S rows).View :=
  viewOf S rows (chc (ldtIdx F R C.k S.nrep)) (chConstraint ch) (chQuery ch)
    (HVZK.simulate (S.linearSystem (rows c)) S.rate_le Hd.layout
      (chc (ldtIdx F R C.k S.nrep), chConstraint ch) (chQuery ch) s)

namespace TableauSetup.Placement

variable (Pl : S.Placement)

/-- **The honest prover's coins**: the blinding coins of the layout's blinding fields. -/
abbrev Coins : Type := HVZK.Coins S.rate_le Pl.layout.toBlindingFields S.nrep

/-- **The honest oracle message**: the commitment `Ligero.HVZK.commitOf` of the placed cells with
the blinding coins. -/
noncomputable def commit (x : ι → F) (ρ : Pl.Coins) : (commitProve S rows).Com :=
  HVZK.commitOf (Pl.cells x) ρ

/-- **The honest commit rounds**: the low-degree challenge and the honest low-degree response
(`honestLdtResponse`). -/
noncomputable def commitRounds (x : ι → F) (ρ : Pl.Coins) :
    CausalTranscript (commitProve S rows).commitRounds :=
  honestCommitRounds (honestLdtResponse (Pl.cells x) ρ)

/-- **The honest proof**: the masked responses of `Ligero.HVZK.responseOf` at the low-degree
challenge of the commit rounds and the constraint challenge. -/
noncomputable def prove (c : Ctx) (x : ι → F) (ρ : Pl.Coins)
    (r : (commitProve S rows).Rounds) : CausalTranscript (commitProve S rows).spec :=
  honestProof fun rc =>
    (HVZK.responseOf (S.linearSystem (rows c)) (Pl.cells x) ρ (ldtChallenge r, rc)).2

/-- **Completeness of the honest prover** (`Ligero.Completeness.accept` at the zero-privacy rows
the placement fills): on admissible cells satisfying the rows, the verifier accepts at every coins
and every challenge. No query bound is needed. -/
theorem complete (c : Ctx) (x : ι → F)
    (hx : FieldProof.CommitProve.Admits Pl.Admissible (rows c) products x) (ρ : Pl.Coins)
    (chc : (commitProve S rows).commitRounds.Challenges)
    (ch : (commitProve S rows).spec.Challenges) :
    (commitProve S rows).V ⟨c, Pl.commit rows x ρ, (Pl.commitRounds rows x ρ).transcript chc⟩
      ((Pl.prove rows c x ρ ((Pl.commitRounds rows x ρ).transcript chc)).transcript ch) =
        true := by
  have hacc := Completeness.accept (HVZK.honest Pl.layout.products_ne_zero
    (Pl.witness rows hx.admissible c hx.rowsHold) ρ) (chc (ldtIdx F R C.k S.nrep), chConstraint ch)
    (chQuery ch)
  have ht : (HVZK.commitOf (Pl.witness rows hx.admissible c hx.rowsHold).toCells ρ).rows =
      Completeness.encode (HVZK.honest Pl.layout.products_ne_zero
        (Pl.witness rows hx.admissible c hx.rowsHold) ρ) :=
    congrArg Tableau.Commitment.rows (HVZK.commitOf_eq Pl.layout.products_ne_zero _ _)
  rw [← HVZK.responseOf_eq Pl.layout.products_ne_zero, ← ht] at hacc
  exact hacc

end TableauSetup.Placement

/-- **The simulator of Ligero at agreement threshold `A` with untested masks**: `simulate` at the
hiding data `Hd`, on its coins (`HVZK.SimCoins`).

Running time: that of `simulate` (its docstring). This running time is argued here, not proved in
Lean. -/
def honestSim : (commitProve S rows).Sim where
  SimCoins := HVZK.SimCoins S.rate_le Hd.layout S.t S.nrep
  sim c chc ch s := simulate rows Hd c chc ch s

/-- **The honest prover of Ligero at agreement threshold `A` with untested masks**: the honest prover
of the placement (`TableauSetup.Placement.commit`, `commitRounds`, `prove`), complete by
`TableauSetup.Placement.complete`; hiding is `Ligero.HVZK.identDistrib` at each fixed vector of
admissible cells, the low-degree response `w = u0 + Σ r_i U_i` uniform from the ILDT row `u0`, with
the simulator `honestSim` (`simulate`), under the query bound `t ≤ k − |witness|` of `Hd`. -/
noncomputable def honest : (commitProve S rows).Honest (honestSim rows Hd) where
  Coins := Hd.Coins
  commit := Hd.commit rows
  commitRounds := Hd.commitRounds rows
  prove := Hd.prove rows
  Admissible := Hd.Admissible
  complete := Hd.complete rows
  hides c x hx chc ch := by
    have key := (HVZK.identDistrib (hrate := S.rate_le)
      (Hd.witness rows hx.admissible c hx.rowsHold) (chc (ldtIdx F R C.k S.nrep), chConstraint ch)
      (chQuery ch) Hd.t_le_privacy).comp
        (viewOf S rows (chc (ldtIdx F R C.k S.nrep)) (chConstraint ch) (chQuery ch))
    refine IdentDistrib.trans (IdentDistrib.of_equiv (Equiv.refl _) fun ρ => ?_) key
    exact congrArg (fun l => FieldProof.CommitProve.View.mk l _ _)
      (see_eq_viewLeaves (commitProve S rows).comView rfl _ _ _ fun _ => rfl)

end

end GordieHowe.Ligero.AgreementThreshold
