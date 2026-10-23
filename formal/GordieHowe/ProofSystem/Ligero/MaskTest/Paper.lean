-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.MaskTest
public import GordieHowe.ProofSystem.Ligero.UntestedMask
public import GordieHowe.Headline

@[expose] public section

/-!
# Ligero with the mask test, in the form of the paper's lemma

The paper's lemma on Ligero with the mask test (`lem:ligero`, errors `def:ligero-errors`) states:
(1) soundness, a commit event of density at most `(B/(|K| − 1))^nrep` at the low-degree challenges,
then a round-by-round sound proof phase for "the claims hold at the extracted values", with error
`1/|K|` at the constraint challenge and `((A − 1)_t + (2k − 1)_t + (k − 1)_t)/(N)_t` at the column
query; (2) completeness; (3) honest-verifier zero knowledge with error `0`.

The Lean proves it as Ligero at agreement threshold `A` with the mask test and the prefix-row
subfield test (`GordieHowe.Ligero.MaskTest`, a `CommitProve` system): soundness `sound` (a
`CommitProve.SoundOn` record), the errors `error` (`error_sum`), the honest prover `honest`. This file
restates the three parts as theorems: `GordieHowe.Ligero.MaskTest.sound`, `GordieHowe.Ligero.MaskTest.complete`,
`GordieHowe.Ligero.MaskTest.hvzk`.

The paper's corollary on Ligero without the mask test (`cor:untested-ligero`) is the same with
untested masks (`GordieHowe.Ligero.UntestedMask`): error `l/|K|` at the constraint challenge, `l` the list
bound of `lem:untested-masks` (`GordieHowe.Ligero.UntestedMaskRow.Parameters`), and `((A − 1)_t + a_t)/(N)_t` at the
column query, `a` the mask agreement threshold. It is restated as
`GordieHowe.Ligero.UntestedMask.sound`, `GordieHowe.Ligero.UntestedMask.complete`, `GordieHowe.Ligero.UntestedMask.hvzk`.
-/

namespace GordieHowe.Ligero.MaskTest
open IOP

open scoped NNReal

variable {K ι Q Lin : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [Fintype Q]
  [Fintype Lin] {N R nQ nL np : ℕ} {C : GordieHowe.RSCode K N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C} {products : Routing.ProductLayout ι Q}
  (S : Setup C P products Lin nL np) {Ctx : Type} (rows : Ctx → Lin → AffineForm K ι)

/-- **The guarantees of part (1) of the paper's lemma `lem:ligero`** for the soundness record
`sound` of Ligero with the mask test and the prefix-row test: the commit error is
`(B/(|K| − 1))^nrep` (`commitError_eq`), the commit events of the low-degree challenges have at
most that probability at every oracle message (`commit_bound`), the proof phase is round-by-round
sound with the system's verifier (`V_eq`) for "the commit phase was bad, or the rows hold on the
extracted cells and every prefix cell lies in `E`" (`claim_iff`), and its errors sum to `1/|K|`
plus `((A − 1)_t + (2k − 1)_t)/(N)_t`, plus `(k − 1)_t/(N)_t` when there is a prefix cell
(`sum_error`). -/
structure LigeroSound : Prop where
  /-- The commit error. -/
  commitError_eq : S.commitError = (S.B / (Fintype.card K - 1)) ^ S.nrep
  /-- The commit events have probability at most the commit error. -/
  commit_bound :
    (commitProve S rows).commitRounds.EventBound (soundIP S rows).commitEvent fun _ => S.commitError
  /-- The proof phase's verifier is the system's. -/
  V_eq : ∀ c tr, (soundIP S rows).proof.V c tr = (commitProve S rows).V c tr
  /-- The proof phase's claim. -/
  claim_iff : ∀ c, (soundIP S rows).proof.claim c ↔
    (commitProve S rows).CommitBad (soundIP S rows).commitEvent c.com c.rounds ∨
      (RowsHold (rows c.ctx) products ((commitProve S rows).extract c.com c.rounds) ∧
        S.pre.In ((commitProve S rows).extract c.com c.rounds))
  /-- The proof-phase errors sum to the constraint and column errors. -/
  sum_error : ∑ i, error S i = 1 / Fintype.card K +
    ((S.A - 1).descFactorial S.t + (2 * C.k - 1).descFactorial S.t : ℝ≥0) / N.descFactorial S.t +
      if np = 0 then 0 else ((C.k - 1).descFactorial S.t : ℝ≥0) / N.descFactorial S.t

/-- **Paper `lem:ligero`, part (1)**: soundness of Ligero with the mask test and the prefix-row
subfield test. The low-degree challenges are exceptional with probability at most
`(B/(|K| − 1))^nrep`; otherwise the proof phase, with the system's verifier, is round-by-round sound
for "the rows hold on the extracted cells and every prefix cell lies in `E`", with errors summing to
`1/|K| + ((A − 1)_t + (2k − 1)_t)/(N)_t`, plus `(k − 1)_t/(N)_t` with a prefix cell. -/
@[headline]
theorem sound : LigeroSound S rows where
  commitError_eq := rfl
  commit_bound := (soundIP S rows).commitEvent_bound
  V_eq := (soundIP S rows).V_eq
  claim_iff := (soundIP S rows).claim_iff
  sum_error := error_sum S

variable {S} in
/-- **Paper `lem:ligero`, part (2)**: completeness of Ligero with the mask test and the prefix-row
test, with no query bound: the honest prover needs only the placement data `Pl` (the hiding layout,
the allocation conditions, free piece rows, prefix rows' blinding fields inside `E`). On cells
admissible for the honest prover (every placed value in its row's blinding field) that satisfy the
rows, the verifier accepts the honest proof at every coins and every challenge. -/
@[headline]
theorem complete (Pl : Placement S) (c : Ctx) {x : ι → K}
    (hx : FieldProof.CommitProve.Admits Pl.inner.Admissible (rows c) products x)
    (ρ : Pl.Coins) (chc : (commitProve S rows).commitRounds.Challenges)
    (ch : (commitProve S rows).spec.Challenges) :
    (commitProve S rows).V ⟨c, Pl.commit rows x ρ, (Pl.commitRounds rows x ρ).transcript chc⟩
      ((Pl.prove rows c x ρ ((Pl.commitRounds rows x ρ).transcript chc)).transcript ch) = true :=
  Pl.complete rows c x hx ρ chc ch

variable {S} (Hd : Hiding S)

/-- **Paper `lem:ligero`, part (3)**: honest-verifier zero knowledge of Ligero with the mask test
with error `0`. At every admissible cells satisfying the rows and every challenges, the verifier's
view of the honest proof under uniform coins has the law of the simulator of `honest`
(`MaskTest.Pieces.simulate`), which reads only the context and the challenges. The query bounds
`2t ≤ k` and the blinding layout are fields of `Hd`. -/
@[headline]
theorem hvzk (c : Ctx) {x : ι → K}
    (hx : FieldProof.CommitProve.Admits Hd.inner.Admissible (rows c) products x)
    (chc : (commitProve S rows).commitRounds.Challenges)
    (ch : (commitProve S rows).spec.Challenges) :
    (fun ρ => (commitProve S rows).view ch ((honest rows Hd).commit x ρ)
      (((honest rows Hd).commitRounds x ρ).transcript chc)
      (((honest rows Hd).prove c x ρ
        (((honest rows Hd).commitRounds x ρ).transcript chc)).transcript ch)) =ᵈ
      (honestSim rows Hd).sim c chc ch :=
  (honest rows Hd).hides c x hx chc ch

end GordieHowe.Ligero.MaskTest

namespace GordieHowe.Ligero.UntestedMask
open IOP

open scoped NNReal

variable {K ι Q Lin : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [Fintype Q]
  [Fintype Lin] {N R nQ nL np : ℕ} {C : GordieHowe.RSCode K N}
  {P : Tableau.Parameters (R := R) (nQ := nQ) C} {products : Routing.ProductLayout ι Q}
  (S : Setup C P products Lin nL np) {Ctx : Type} (rows : Ctx → Lin → AffineForm K ι)

/-- **The guarantees of the paper's corollary `cor:untested-ligero`, part (1)** for the soundness
record `sound` of Ligero without the mask test and with the prefix-row test: the commit error is
`(B/(|K| − 1))^nrep` (`commitError_eq`), the commit events have at most that probability
(`commit_bound`), the proof phase is round-by-round sound with the system's verifier (`V_eq`) for
"the commit phase was bad, or the rows hold on the extracted cells and every prefix cell lies in
`E`" (`claim_iff`), and its errors sum to `l/|K|` plus `((A − 1)_t + a_t)/(N)_t`, plus
`(k − 1)_t/(N)_t` when there is a prefix cell (`sum_error`). -/
structure UntestedSound : Prop where
  /-- The commit error. -/
  commitError_eq : S.commitError = (S.B / (Fintype.card K - 1)) ^ S.nrep
  /-- The commit events have probability at most the commit error. -/
  commit_bound :
    (commitProve S rows).commitRounds.EventBound (soundIP S rows).commitEvent fun _ => S.commitError
  /-- The proof phase's verifier is the system's. -/
  V_eq : ∀ c tr, (soundIP S rows).proof.V c tr = (commitProve S rows).V c tr
  /-- The proof phase's claim. -/
  claim_iff : ∀ c, (soundIP S rows).proof.claim c ↔
    (commitProve S rows).CommitBad (soundIP S rows).commitEvent c.com c.rounds ∨
      (RowsHold (rows c.ctx) products ((commitProve S rows).extract c.com c.rounds) ∧
        S.pre.In ((commitProve S rows).extract c.com c.rounds))
  /-- The proof-phase errors sum to the constraint and column errors. -/
  sum_error : ∑ i, error S i = S.l / Fintype.card K +
    ((S.A - 1).descFactorial S.t + S.a.descFactorial S.t : ℝ≥0) / N.descFactorial S.t +
      if np = 0 then 0 else ((C.k - 1).descFactorial S.t : ℝ≥0) / N.descFactorial S.t

/-- **Paper `cor:untested-ligero`, part (1)**: soundness of Ligero without the mask test, with the
prefix-row subfield test. The low-degree challenges are exceptional with probability at most
`(B/(|K| − 1))^nrep`; otherwise the proof phase, with the system's verifier, is round-by-round sound
for "the rows hold on the extracted cells and every prefix cell lies in `E`", with errors summing to
`l/|K| + ((A − 1)_t + a_t)/(N)_t`, plus `(k − 1)_t/(N)_t` with a prefix cell. -/
@[headline]
theorem sound : UntestedSound S rows where
  commitError_eq := rfl
  commit_bound := (soundIP S rows).commitEvent_bound
  V_eq := (soundIP S rows).V_eq
  claim_iff := (soundIP S rows).claim_iff
  sum_error := error_sum S

variable {S} in
/-- **Paper `cor:untested-ligero`, part (2)**: completeness of Ligero without the mask test, with no
query bound: the honest prover needs only the placement data `Pl` (the hiding layout, the
allocation conditions, prefix rows' blinding fields inside `E`). On cells admissible for the honest
prover (every placed value in its row's blinding field) that satisfy the rows, the verifier accepts
the honest proof at every coins and every challenge. -/
@[headline]
theorem complete (Pl : Placement S) (c : Ctx) {x : ι → K}
    (hx : FieldProof.CommitProve.Admits Pl.inner.Admissible (rows c) products x)
    (ρ : Pl.Coins) (chc : (commitProve S rows).commitRounds.Challenges)
    (ch : (commitProve S rows).spec.Challenges) :
    (commitProve S rows).V ⟨c, Pl.commit rows x ρ, (Pl.commitRounds rows x ρ).transcript chc⟩
      ((Pl.prove rows c x ρ ((Pl.commitRounds rows x ρ).transcript chc)).transcript ch) = true :=
  Pl.complete rows c x hx ρ chc ch

variable {S} (Hd : Hiding S)

/-- **Paper `cor:untested-ligero`, part (3)**: honest-verifier zero knowledge of Ligero without the
mask test with error `0`. At every admissible cells satisfying the rows and every challenges, the
verifier's view of the honest proof under uniform coins has the law of the simulator of `honest`
(`Ligero.AgreementThreshold.simulate`), which reads only the context and the challenges. -/
@[headline]
theorem hvzk (c : Ctx) {x : ι → K}
    (hx : FieldProof.CommitProve.Admits Hd.inner.Admissible (rows c) products x)
    (chc : (commitProve S rows).commitRounds.Challenges)
    (ch : (commitProve S rows).spec.Challenges) :
    (fun ρ => (commitProve S rows).view ch ((honest rows Hd).commit x ρ)
      (((honest rows Hd).commitRounds x ρ).transcript chc)
      (((honest rows Hd).prove c x ρ
        (((honest rows Hd).commitRounds x ρ).transcript chc)).transcript ch)) =ᵈ
      (honestSim rows Hd).sim c chc ch :=
  (honest rows Hd).hides c x hx chc ch

end GordieHowe.Ligero.UntestedMask
