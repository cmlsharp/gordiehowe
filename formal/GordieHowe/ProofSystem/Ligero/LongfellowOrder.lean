-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.InterleavedAgreementList
public import GordieHowe.ProofSystem.Ligero.TwoStageKnowledge
public import GordieHowe.Headline

@[expose] public section

/-!
# Ligero in Longfellow's order of challenges

Longfellow's prepared Ligero tableau with the low-degree challenges sent in one verifier message
together with the constraint challenge (AHIV22 §4.7 step 1; LF draft-03 §4.4.4), and untested
masks: there is no mask test. The protocol (`spec`) is the two-stage test
(`TwoStageTest.spec`):

* round 0, the prover's oracle message: the encoded rows and the IDOT and IQUAD mask rows
  (`Tableau.Commitment`);
* round 1, the **joint challenge**: the `nrep` low-degree challenges and the constraint challenge
  (`Tableau.Challenge`);
* round 2, the response: the low-degree responses and the masked linear and quadratic responses
  (`Tableau.Response`);
* round 3, the column query (`Tableau.Query`).

The verdict is the tableau verifier `Tableau.accept` on these messages (`verifier`).

**The analysis at agreement threshold `A`** (`Setup`: Ligero at agreement threshold `A` with
untested masks, `AgreementThreshold.Setup`, and the list size `L` of the interleaved code at `A`,
`GordieHowe.Ligero.InterleavedAgreementList.Parameters`). Nothing is pinned before the joint challenge, so the state after it
quantifies over the agreement list `List(T, A)` of the tableau `T` (`GordieHowe.Ligero.InterleavedAgreementList.list`): the
joint challenge is bad (`JointBad`) when every low-degree challenge is exceptional for its
repetition's matrix, or the constraint challenge is in the list event
`GordieHowe.Ligero.UntestedMaskRow.constraintBad` of some member of `List(T, A)`. The exceptional sets depend on the
encoded rows only, and each member's list event depends on that member and the masks only, so
the joint round costs `(B / (|F| − 1)) ^ nrep + L · l / |F|` (`jointError`, `joint_count`).

At the column query the low-degree response is fixed, and the extractor reads it (`extractor`):
the cells of the rows pinned by the low-degree response, `GordieHowe.Ligero.AgreementThreshold.TableauSetup.extract`. If the
extractor fails and the joint challenge was not bad, the column count of Ligero with the
low-degree test in the commit phase applies (`column_count`): when the common agreement set has
at least `A` columns, the pinned rows agree with the tableau on it, so they are a member of
`List(T, A)` and their list event did not occur (`GordieHowe.Ligero.AgreementThreshold.query_count`); otherwise every
accepted query lies in the common agreement set. The column round costs
`((A − 1).descFactorial t + a.descFactorial t) / N.descFactorial t`
(`GordieHowe.Ligero.AgreementThreshold.columnError`), with no list factor.

Round-by-round knowledge soundness (`rbr_knowledge_soundness`) then follows from the two counts
(`TwoStageTest.rbrKnowledgeSoundness_of_counts`), at the state function `stateFn`
(`TwoStageTest.knowledgeState` of `JointBad`) and the named extractor `extractor`.
-/

namespace GordieHowe.Ligero.LongfellowOrder
open IOP

open ProtocolSpec Polynomial
open scoped NNReal

section

variable {F ι Q Lin : Type} [Field F] [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin]
  {N R nL nQ : ℕ} {C : GordieHowe.RSCode F N} {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  {products : Routing.ProductLayout ι Q}

variable (F N R nL nQ) (k t nrep : ℕ) in
/-- **Ligero in Longfellow's order of challenges**: the oracle message (the encoded rows and the
masks), the joint challenge (the low-degree and constraint challenges), the response (the
low-degree and masked responses) and the column query; the two-stage test
`TwoStageTest.spec`. -/
abbrev spec : ProtocolSpec 4 :=
  TwoStageTest.spec (Tableau.Commitment F N R nrep) (Tableau.Challenge F R nL nQ nrep)
    (Tableau.Response F k nrep) (Tableau.Query N t)

/-- **The data of Ligero in Longfellow's order of challenges at agreement threshold `A`**, with
untested masks: Ligero at agreement threshold `A` with untested masks (`AgreementThreshold.Setup`: the
threshold `A` with its line certificate of `B` exceptional challenges per line, the placement, the
row order, the rate, the query count `t`, the repetitions `nrep`, and the mask list parameters
`a`, `l`), and `L`, `interleaved`: the list size of the interleaved code at `A` with its Johnson
hypotheses (`InterleavedAgreementList.Parameters`, parameter facts). -/
structure Setup (C : GordieHowe.RSCode F N) (P : Tableau.Parameters (R := R) (nQ := nQ) C)
    (products : Routing.ProductLayout ι Q) (Lin : Type) (nL : ℕ)
    extends AgreementThreshold.Setup C P products Lin nL where
  /-- The list size of the interleaved code at the agreement threshold. -/
  L : ℕ
  /-- The Johnson hypotheses of the interleaved code at `A` with list size `L`. -/
  interleaved : InterleavedAgreementList.Parameters N (C.k - 1) A L

/-- **The code parameters of Ligero in Longfellow's order of challenges**, parameter facts about
the code `C` at the numbers `A`, `B` (the agreement threshold and the exceptional count of the line
certificate), `a`, `l` (the mask agreement threshold and list size) and `L` (the list size of the
interleaved code at `A`): those of Ligero at agreement threshold `A` with untested masks
(`AgreementThreshold.Parameters`) and the Johnson hypotheses of the interleaved code
(`InterleavedAgreementList.Parameters`). A configuration proves them once per tableau. -/
structure Parameters (C : GordieHowe.RSCode F N) (A B a l L : ℕ) : Prop
    extends AgreementThreshold.Parameters C A B a l where
  /-- The Johnson hypotheses of the interleaved code at `A` with list size `L`. -/
  interleaved : InterleavedAgreementList.Parameters N (C.k - 1) A L

variable (S : Setup C P products Lin nL)

/-- The challenge types of the protocol are nonempty (at most `N` queried columns). -/
instance (i : (spec F N R nL nQ C.k S.t S.nrep).ChallengeIdx) :
    Nonempty ((spec F N R nL nQ C.k S.t S.nrep).Challenge i) :=
  haveI : Nonempty (Tableau.Query N S.t) := Tableau.Query.nonempty_of_le S.t_le
  inferInstance

variable {Ctx : Type} (rows : Ctx → Lin → AffineForm F ι)

/-- **The relation**: the rows of the context hold on the cells, with the products. -/
def relation (rows : Ctx → Lin → AffineForm F ι) (products : Routing.ProductLayout ι Q) :
    Set (Ctx × (ι → F)) :=
  {p | RowsHold (rows p.1) products p.2}

omit [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin] in
theorem mem_relation {c : Ctx} {x : ι → F} :
    (c, x) ∈ relation rows products ↔ RowsHold (rows c) products x :=
  Iff.rfl

variable [DecidableEq F]

/-- **The verdict on the messages**: the tableau verifier on the linear system of the context's
rows, the encoded rows and the masks of the oracle message, the joint challenge, the response and
the query. -/
def accept (c : Ctx) (O : Tableau.Commitment F N R S.nrep)
    (ch : Tableau.Challenge F R nL nQ S.nrep) (p : Tableau.Response F C.k S.nrep)
    (q : Tableau.Query N S.t) : Bool :=
  Tableau.accept C P (S.linearSystem (rows c)) O.rows O.masks ch p q

/-- **The verifier of Ligero in Longfellow's order of challenges**: `accept` on the four
messages. -/
def verifier : Verifier (spec F N R nL nQ C.k S.t S.nrep) Ctx :=
  TwoStageTest.verifier (accept S rows)

/-- **The joint challenge is bad** for the oracle message `O`: every low-degree challenge is
exceptional for its repetition's matrix (`Threshold.exceptional`), or the constraint challenge is
in the list event `UntestedMaskRow.constraintBad` of some member of the agreement list of the tableau
at `A` (`InterleavedAgreementList.list`). Both depend on `O` and the joint challenge only. -/
def JointBad (c : Ctx) (O : Tableau.Commitment F N R S.nrep)
    (ch : Tableau.Challenge F R nL nQ S.nrep) : Prop :=
  ch.1 ∈ Fintype.piFinset (fun j => S.exceptional (O.rows.ldtMatrix j)) ∨
    ∃ fs ∈ InterleavedAgreementList.list C O.rows.tableau S.A,
      UntestedMaskRow.constraintBad C P (S.linearSystem (rows c)) S.rate_le S.a fs O.masks ch.2

/-- **The state function** of Ligero in Longfellow's order of challenges: false before the joint
challenge, `JointBad` after it, and `JointBad` or acceptance on the full transcript
(`TwoStageTest.knowledgeState`). Not required to be efficient: it quantifies over the agreement
list. -/
def stateFn : KnowledgeStateFunction (verifier S rows) :=
  TwoStageTest.knowledgeState (JointBad S rows) (accept S rows)

/-- **The extractor** of Ligero in Longfellow's order of challenges: once the response is sent
(prefixes of length at least `3`), the cells extracted from the low-degree challenges of the joint
challenge and the low-degree responses of the response (`AgreementThreshold.TableauSetup.extract`: the
cells of the tableau rows interpolated on the first `k` columns of the common agreement set, when
it has at least `A` columns); zero before.

Running time: one run of `AgreementThreshold.TableauSetup.extract`, `O(N · nrep · (R + k²) + |ι| ·
(N log N + k²))` field operations and comparisons (its docstring): polynomial in the tableau
sizes. This running time is argued here, not proved in Lean. -/
def extractor : Extractor (spec F N R nL nQ C.k S.t S.nrep) Ctx (ι → F) where
  extract m _ tr :=
    if h : 3 ≤ (m : ℕ) then
      S.extract (tr ⟨0, by omega⟩ : Tableau.Commitment F N R S.nrep).rows
        (AgreementThreshold.commitTranscript (tr ⟨1, by omega⟩ : Tableau.Challenge F R nL nQ S.nrep).1
          (tr ⟨2, by omega⟩ : Tableau.Response F C.k S.nrep).1)
    else 0

omit [Fintype F] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- After the response the extractor reads the low-degree challenges and responses. -/
theorem extractor_three (c : Ctx) (tr : (spec F N R nL nQ C.k S.t S.nrep).Transcript ⟨3, by decide⟩) :
    extractor S ⟨3, by decide⟩ c tr =
      S.extract (tr ⟨0, by decide⟩ : Tableau.Commitment F N R S.nrep).rows
        (AgreementThreshold.commitTranscript (tr ⟨1, by decide⟩ : Tableau.Challenge F R nL nQ S.nrep).1
          (tr ⟨2, by decide⟩ : Tableau.Response F C.k S.nrep).1) :=
  rfl

/-! ### The errors -/

/-- **The joint error**: the commit error `(B / (|F| − 1)) ^ nrep` and `L` times the mask list
cost `l / |F|` (`AgreementThreshold.testError`). -/
noncomputable def jointError : ℝ≥0 := S.commitError + S.L * AgreementThreshold.testError S.toSetup

/-- **The round errors**: `jointError` at the joint challenge and the column error
`((A − 1).descFactorial t + a.descFactorial t) / N.descFactorial t` (`AgreementThreshold.columnError`)
at the column query. -/
noncomputable def error : (spec F N R nL nQ C.k S.t S.nrep).ChallengeIdx → ℝ≥0 :=
  TwoStageTest.error (jointError S) (AgreementThreshold.columnError S.toSetup)

omit [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
/-- Every round error is at most `δ` when the joint and column errors are. -/
theorem error_le_of {δ : ℝ≥0} (hjoint : jointError S ≤ δ)
    (hcol : AgreementThreshold.columnError S.toSetup ≤ δ) (i : (spec F N R nL nQ C.k S.t S.nrep).ChallengeIdx) :
    error S i ≤ δ := by
  unfold error TwoStageTest.error
  split_ifs
  exacts [hjoint, hcol]

omit [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
/-- **The joint error as numbers**: at exceptional count `B`, the commit error plus `L` times the
test error of `AgreementThreshold.bounds` at the setup's numbers. -/
theorem jointError_eq_bounds {B : ℕ} (hB : S.B = B) :
    jointError S = (AgreementThreshold.bounds F N S.A B S.nrep S.t S.a S.l).commit +
      S.L * (AgreementThreshold.bounds F N S.A B S.nrep S.t S.a S.l).test := by
  simp only [jointError, AgreementThreshold.TableauSetup.commitError, AgreementThreshold.Threshold.commitError,
    AgreementThreshold.testError, AgreementThreshold.bounds, hB]

omit [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
/-- **The column error as numbers**: the column error of `AgreementThreshold.bounds` at the setup's
numbers. -/
theorem columnError_eq_bounds (B : ℕ) :
    AgreementThreshold.columnError S.toSetup = (AgreementThreshold.bounds F N S.A B S.nrep S.t S.a S.l).column :=
  rfl

/-- **A setup at given numbers**: its agreement threshold `A`, exceptional count `B`, repetitions
`nrep`, query count `t`, mask agreement threshold `a`, mask list size `l` and interleaved list
size `L`. -/
structure Setup.Numbers (A B nrep t a l L : ℕ) : Prop where
  /-- The agreement threshold. -/
  A_eq : S.A = A
  /-- The exceptional count of the line certificate. -/
  B_eq : S.B = B
  /-- The number of low-degree repetitions. -/
  nrep_eq : S.nrep = nrep
  /-- The number of queried columns. -/
  t_eq : S.t = t
  /-- The mask agreement threshold. -/
  a_eq : S.a = a
  /-- The mask list size. -/
  l_eq : S.l = l
  /-- The list size of the interleaved code. -/
  L_eq : S.L = L

omit [Fintype ι] [Fintype Q] [Fintype Lin] [DecidableEq F] in
/-- **The round errors of a setup at given numbers** are at most `δ` when the numbers' joint
error `(B / (|F| − 1)) ^ nrep + L · l / |F|` and column error are (`AgreementThreshold.bounds`). -/
theorem error_le_of_numbers {A B nrep t a l L : ℕ} (h : S.Numbers A B nrep t a l L) {δ : ℝ≥0}
    (hjoint : (AgreementThreshold.bounds F N A B nrep t a l).commit +
      L * (AgreementThreshold.bounds F N A B nrep t a l).test ≤ δ)
    (hcol : (AgreementThreshold.bounds F N A B nrep t a l).column ≤ δ)
    (i : (spec F N R nL nQ C.k S.t S.nrep).ChallengeIdx) : error S i ≤ δ := by
  refine error_le_of S ?_ ?_ i
  · rw [jointError_eq_bounds S h.B_eq, h.A_eq, h.nrep_eq, h.t_eq, h.a_eq, h.l_eq, h.L_eq]
    exact hjoint
  · rw [columnError_eq_bounds S B, h.A_eq, h.nrep_eq, h.t_eq, h.a_eq, h.l_eq]
    exact hcol

/-! ### Soundness -/

omit [Fintype Lin] in
open Classical in
/-- **The joint round count**: for every context and oracle message, at most a `jointError`
fraction of the joint challenges is bad. The exceptional low-degree challenges are at most a
`commitError` fraction (`Threshold.card_piFinset_exceptional`); each member of the agreement list,
of which there are at most `L` (`InterleavedAgreementList.card_list_le_of_parameters`), has at most an
`l / |F|` fraction of bad constraint challenges (`UntestedMaskRow.constraint_bad_count`). -/
theorem joint_count (c : Ctx) (O : Tableau.Commitment F N R S.nrep) :
    ((Finset.univ.filter fun ch => JointBad S rows c O ch).card : ℝ≥0) ≤
      jointError S * Fintype.card (Tableau.Challenge F R nL nQ S.nrep) := by
  set E := Fintype.piFinset fun j => S.exceptional (O.rows.ldtMatrix j)
  set Ls := InterleavedAgreementList.list C O.rows.tableau S.A
  set L' := S.linearSystem (rows c)
  have hsub : (Finset.univ.filter fun ch => JointBad S rows c O ch) ⊆
      (Finset.univ.filter fun ch : Tableau.Challenge F R nL nQ S.nrep => ch.1 ∈ E) ∪
        Ls.biUnion fun fs => Finset.univ.filter fun ch : Tableau.Challenge F R nL nQ S.nrep =>
          UntestedMaskRow.constraintBad C P L' S.rate_le S.a fs O.masks ch.2 := by
    intro ch hch
    rcases (Finset.mem_filter.mp hch).2 with h | ⟨fs, hfs, hb⟩
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩)
    · exact Finset.mem_union_right _
        (Finset.mem_biUnion.mpr ⟨fs, hfs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩)
  have hcard := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
    (Nat.add_le_add_left Finset.card_biUnion_le _))
  have hleft : (Finset.univ.filter fun ch : Tableau.Challenge F R nL nQ S.nrep => ch.1 ∈ E).card =
      (Finset.univ.filter fun r => r ∈ E).card * Fintype.card ((Fin nL → F) × (Fin nQ → F)) :=
    by convert UntestedMaskRow.count_left (fun r => r ∈ E)
  have hright : ∀ fs, (Finset.univ.filter fun ch : Tableau.Challenge F R nL nQ S.nrep =>
      UntestedMaskRow.constraintBad C P L' S.rate_le S.a fs O.masks ch.2).card =
        Fintype.card (Tableau.LdtChallenge F R S.nrep) * (Finset.univ.filter fun rc =>
          UntestedMaskRow.constraintBad C P L' S.rate_le S.a fs O.masks rc).card := fun fs => by
    convert UntestedMaskRow.count_right
      (fun rc => UntestedMaskRow.constraintBad C P L' S.rate_le S.a fs O.masks rc)
  rw [hleft, Finset.sum_congr rfl fun fs _ => hright fs] at hcard
  have hE : ((Finset.univ.filter fun r => r ∈ E).card : ℝ≥0) ≤
      S.commitError * Fintype.card (Tableau.LdtChallenge F R S.nrep) := by
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    exact S.card_piFinset_exceptional O.rows
  have hl : ∀ fs, ((Finset.univ.filter fun rc =>
      UntestedMaskRow.constraintBad C P L' S.rate_le S.a fs O.masks rc).card : ℝ≥0) ≤
        AgreementThreshold.testError S.toSetup * Fintype.card ((Fin nL → F) × (Fin nQ → F)) := by
    intro fs
    have h := UntestedMaskRow.constraint_bad_count C P L' S.a S.list fs O.masks
    unfold AgreementThreshold.testError
    rw [div_mul_eq_mul_div, le_div_iff₀ (by exact_mod_cast Fintype.card_pos (α := F))]
    exact_mod_cast h
  have hLs : (Ls.card : ℝ≥0) ≤ S.L := by
    exact_mod_cast InterleavedAgreementList.card_list_le_of_parameters O.rows.tableau S.interleaved
  have hsum : (∑ fs ∈ Ls, (Fintype.card (Tableau.LdtChallenge F R S.nrep) *
      (Finset.univ.filter fun rc =>
        UntestedMaskRow.constraintBad C P L' S.rate_le S.a fs O.masks rc).card : ℕ) : ℝ≥0) ≤
        S.L * (Fintype.card (Tableau.LdtChallenge F R S.nrep) *
          (AgreementThreshold.testError S.toSetup * Fintype.card ((Fin nL → F) × (Fin nQ → F)))) := by
    push_cast
    refine (Finset.sum_le_sum fun fs _ => mul_le_mul_of_nonneg_left (hl fs) (by positivity)).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right hLs (by positivity)
  calc ((Finset.univ.filter fun ch => JointBad S rows c O ch).card : ℝ≥0)
      ≤ ((Finset.univ.filter fun r => r ∈ E).card *
          Fintype.card ((Fin nL → F) × (Fin nQ → F)) : ℕ) +
        ((∑ fs ∈ Ls, (Fintype.card (Tableau.LdtChallenge F R S.nrep) *
          (Finset.univ.filter fun rc =>
            UntestedMaskRow.constraintBad C P L' S.rate_le S.a fs O.masks rc).card : ℕ)) : ℝ≥0) := by
        exact_mod_cast hcard
    _ ≤ S.commitError * Fintype.card (Tableau.LdtChallenge F R S.nrep) *
          Fintype.card ((Fin nL → F) × (Fin nQ → F)) +
        S.L * (Fintype.card (Tableau.LdtChallenge F R S.nrep) *
          (AgreementThreshold.testError S.toSetup * Fintype.card ((Fin nL → F) × (Fin nQ → F)))) := by
        push_cast
        exact add_le_add (mul_le_mul_of_nonneg_right hE (by positivity)) (by exact_mod_cast hsum)
    _ = jointError S * Fintype.card (Tableau.Challenge F R nL nQ S.nrep) := by
        rw [Fintype.card_prod (Tableau.LdtChallenge F R S.nrep), jointError]
        push_cast
        ring

open Classical in
/-- **The column round count**: at an oracle message, a joint challenge and a response where the
extracted cells do not satisfy the rows and the joint challenge was not bad, at most a
`columnError` fraction of the queries is accepted. The low-degree challenges are not all
exceptional. If the common agreement set has at least `A` columns, the pinned rows agree with the
tableau on it (`Threshold.pinnedRows_agree`), so they are a member of the agreement list
(`InterleavedAgreementList.mem_list_of_rowsAgreeOn`) whose list event did not occur, and the column count of
Ligero with the low-degree test in the commit phase applies (`AgreementThreshold.query_count`). Otherwise
every accepted query lies in the common agreement set (`AgreementThreshold.card_filter_le_of_lt`). -/
theorem column_count (c : Ctx) (O : Tableau.Commitment F N R S.nrep)
    (ch : Tableau.Challenge F R nL nQ S.nrep) (p : Tableau.Response F C.k S.nrep)
    (hE : ¬ RowsHold (rows c) products (S.extract O.rows (AgreementThreshold.commitTranscript ch.1 p.1)))
    (hb : ¬ JointBad S rows c O ch) :
    ((Finset.univ.filter fun q => accept S rows c O ch p q = true).card : ℝ≥0) ≤
      AgreementThreshold.columnError S.toSetup * Fintype.card (Tableau.Query N S.t) := by
  let inp : AgreementThreshold.Input Ctx F N R C.k S.nrep := ⟨c, O, AgreementThreshold.commitTranscript ch.1 p.1⟩
  have hnotExc : ¬ S.Exceptional O.rows inp.rounds := fun h =>
    hb (.inl (Fintype.mem_piFinset.mpr fun j => h j))
  have hc : ¬ AgreementThreshold.Claim S.toSetup rows inp := fun h => h.elim hnotExc hE
  by_cases hD : S.A ≤ (AgreementThreshold.commonAgreement C O.rows ch.1 p.1).card
  · have hrows : RSCode.RowsAgreeOn C O.rows.tableau
        (AgreementThreshold.commonAgreement C O.rows ch.1 p.1) (S.pinnedRows O.rows inp.rounds) :=
      ⟨S.natDegree_pinnedRows_lt O.rows inp.rounds,
        fun i _ hj => (S.pinnedRows_agree hnotExc hD hj i).symm⟩
    have hmem := InterleavedAgreementList.mem_list_of_rowsAgreeOn S.k_le_A hrows hD
    have hbad : ¬ AgreementThreshold.Bad S.toSetup rows inp O.masks ch.2 := fun h =>
      hb (.inr ⟨_, hmem, h⟩)
    exact AgreementThreshold.query_count S.toSetup rows inp hc O.masks ch.2 hbad p.2
  · have h := AgreementThreshold.card_filter_le_of_lt (not_le.mp hD)
      (p := fun q => accept S rows c O ch p q = true) fun q hq =>
        AgreementThreshold.mem_commonAgreement_of_accept
          ((Tableau.accept_eq_true_iff C P _ O.rows O.masks ch p q).mp hq)
    have h' : (Finset.univ.filter fun q => accept S rows c O ch p q = true).card ≤
        (S.A - 1).descFactorial S.t + S.a.descFactorial S.t := by
      convert h.trans (Nat.le_add_right _ (S.a.descFactorial S.t))
    exact AgreementThreshold.card_le_fraction S.t_le h'

/-- **Round-by-round knowledge soundness of Ligero in Longfellow's order of challenges**
(Appendix B, Ligero in LF's order of challenges): with the low-degree challenges sent together
with the constraint challenge (AHIV22 §4.7 step 1; LF draft-03 §4.4.4) and untested masks, at
agreement threshold `A`, the verifier `verifier` is round-by-round knowledge sound for the
relation "the rows hold on the cells" (`relation`) at the named extractor `extractor` (the cells
of the rows pinned by the low-degree response) and the state function `stateFn`, with the round
errors `error`:

* at the joint challenge, `(B / (|F| − 1)) ^ nrep + L · l / |F|` (`jointError`), where `B` is the
  exceptional count of the line certificate at `A`, `L` the list size of the interleaved code at
  `A` (`InterleavedAgreementList.card_le`, the Johnson bound, or one above the unique-decoding radius,
  `InterleavedAgreementList.card_le_one`) and `l` the list size of an untested mask
  (`UntestedMaskRow.Parameters`);
* at the column query, `((A − 1).descFactorial t + a.descFactorial t) / N.descFactorial t`
  (`AgreementThreshold.columnError`), with `a` the mask agreement threshold, and no list factor. -/
@[headline]
theorem rbr_knowledge_soundness :
    rbrKnowledgeSoundness (relation rows products) (verifier S rows) (extractor S)
      (stateFn S rows) (error S) :=
  haveI : Nonempty (Tableau.Query N S.t) := Tableau.Query.nonempty_of_le S.t_le
  TwoStageTest.rbrKnowledgeSoundness_of_counts (JointBad S rows) (accept S rows)
    (relation rows products) (extractor S) (jointError S) (AgreementThreshold.columnError S.toSetup)
    (fun c O => joint_count S rows c O)
    (fun c tr hE hb => column_count S rows c _ _ _
      (fun h => hE (by rw [mem_relation, extractor_three]; exact h)) hb)

/-! ### Part (1) on the data rows -/

section DataRows

variable {nrep : ℕ} [NeZero nrep] (O : Tableau.Rows F N R nrep) {A : ℕ}

omit [Fintype F] [DecidableEq F] [NeZero nrep] in
/-- **Paper `lem:ligero-lf-order` (1), the Johnson bound on the data rows**: for every tableau and
a threshold `A ≤ N` within the Johnson radius (`A² > N (k − 1)`), the interleaved agreement list of
the data rows `u_0, …, u_{m−1}` (`InterleavedAgreementList.list` of `O.data`) has at most
`L(A) = N (A − k + 1) / (A² − N (k − 1))` members (`InterleavedAgreementList.card_le`). -/
@[headline]
theorem card_dataList_le (hAN : A ≤ N) (hJ : N * (C.k - 1) < A ^ 2) :
    (InterleavedAgreementList.list C O.data A).card ≤ InterleavedAgreementList.bound N (C.k - 1) A :=
  InterleavedAgreementList.card_le O.data hAN hJ

omit [Fintype F] [DecidableEq F] [NeZero nrep] in
/-- **Paper `lem:ligero-lf-order` (1), above the unique-decoding radius on the data rows**: when
`2A > N + k − 1`, the interleaved agreement list of the data rows has at most one member
(`InterleavedAgreementList.card_le_one`). -/
@[headline]
theorem card_dataList_le_one (hA : N + (C.k - 1) < 2 * A) :
    (InterleavedAgreementList.list C O.data A).card ≤ 1 :=
  InterleavedAgreementList.card_le_one O.data hA

omit [Fintype F] [DecidableEq F] in
/-- **The list of the joint challenge's state projects onto the data rows' list**: at a threshold
`A ≥ k`, a member of the agreement list of the tableau `O.tableau` (the low-degree mask row of
repetition `0` and the data rows, the list `JointBad` ranges over) restricted to the data rows is a
member of the data rows' list (`InterleavedAgreementList.succ_mem_list`). -/
theorem succ_mem_dataList (hkA : C.k ≤ A) {fs : Fin (R + 1) → F[X]}
    (h : fs ∈ InterleavedAgreementList.list C O.tableau A) :
    (fun i => fs i.succ) ∈ InterleavedAgreementList.list C O.data A := by
  have hs := InterleavedAgreementList.succ_mem_list hkA h
  rwa [show (fun i => O.tableau i.succ) = O.data from funext O.tableau_succ] at hs

end DataRows

end

end GordieHowe.Ligero.LongfellowOrder
