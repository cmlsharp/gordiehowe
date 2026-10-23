-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Ligero.UntestedMask
public import GordieHowe.ProofSystem.Ligero.MaskTest

@[expose] public section

/-!
# Ligero with the prefix-row test, with either masking

A packing tree's commitment (`tree_zk.h`) is plain Ligero at agreement threshold `A` with the
prefix-row subfield test, with one of the two maskings of the response masks: untested masks
(`GordieHowe.Ligero.UntestedMask`) or the mask test (`GordieHowe.Ligero.MaskTest`). `Setup` is a setup of
either, and this module states once, by cases, what a domain proof consumes: the commit-and-prove
system (`Setup.commitProve`), its soundness on the prefix condition (`Setup.sound`,
`CommitProve.SoundOn` with `PrefixCells.In`), the errors (`Setup.error_sum`), the honest prover
(`Setup.Hiding`, `Setup.honest`), and the system with its extracted cells confined to the prefix
condition (`Setup.confined`, `Setup.soundConfined`, `Setup.honestConfined`,
`Setup.in_extract_confined`), which a circuit proof reads its witness from (`CommitProve.confine`).
-/

namespace GordieHowe.Ligero.MaskRow
open IOP

open scoped NNReal

section

variable {K ι Q Lin : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype ι] [Fintype Q]
  [Fintype Lin] {N R nQ nL np : ℕ}

/-- **A setup of Ligero with the prefix-row test** on the code `C` and the tableau `P`, for cells
`ι → K` with the product layout `products` and affine rows indexed by `Lin`, with `np` prefix
cells: untested masks (`listRadius`) or the mask test (`split`). -/
inductive Setup (C : GordieHowe.RSCode K N) (P : Tableau.Parameters (R := R) (nQ := nQ) C)
    (products : Routing.ProductLayout ι Q) (Lin : Type) (nL np : ℕ) where
  /-- Untested masks (`GordieHowe.Ligero.UntestedMask`). -/
  | listRadius (S : UntestedMask.Setup C P products Lin nL np)
  /-- Masks as tested piece rows (`GordieHowe.Ligero.MaskTest`). -/
  | split (S : MaskTest.Setup C P products Lin nL np)

variable {C : GordieHowe.RSCode K N} {P : Tableau.Parameters (R := R) (nQ := nQ) C}
  {products : Routing.ProductLayout ι Q}

namespace Setup

/-- The prefix cells. -/
def pre : Setup C P products Lin nL np → PrefixCells K ι np
  | .listRadius S => S.pre
  | .split S => S.pre

/-- **Every prefix cell lies in the setup's subfield.** -/
abbrev PrefixIn (S : Setup C P products Lin nL np) (x : ι → K) : Prop := S.pre.In x

/-- The number of queried columns. -/
def t : Setup C P products Lin nL np → ℕ
  | .listRadius S => S.t
  | .split S => S.t

/-- The number of repetitions of the low-degree test. -/
def nrep : Setup C P products Lin nL np → ℕ
  | .listRadius S => S.nrep
  | .split S => S.nrep

/-- At least one repetition. -/
theorem nrep_pos : (S : Setup C P products Lin nL np) → 0 < S.nrep
  | .listRadius S => S.nrep_pos
  | .split S => S.nrep_pos

variable {Ctx : Type}

/-- **The commit-and-prove system of the setup** for the rows `rows`. -/
def commitProve (S : Setup C P products Lin nL np) (rows : Ctx → Lin → AffineForm K ι) :
    FieldProof.CommitProve K ι products Ctx rows :=
  match S with
  | .listRadius S => UntestedMask.commitProve S rows
  | .split S => MaskTest.commitProve S rows

variable (rows : Ctx → Lin → AffineForm K ι)

/-- **The commit error**: every low-degree challenge exceptional, `(B/(|K| − 1)) ^ nrep`. -/
noncomputable def commitError : Setup C P products Lin nL np → ℝ≥0
  | .listRadius S => S.commitError
  | .split S => S.commitError

/-- **The errors of the proof phase**: the test and column errors of the masking, and, when the
prefix is nonempty, the joint subfield term at the column query. -/
noncomputable def error (S : Setup C P products Lin nL np) :
    (S.commitProve rows).spec.ChallengeIdx → ℝ≥0 :=
  match S with
  | .listRadius S => UntestedMask.error S
  | .split S => MaskTest.error S

/-- **The round bounds of the setup's tableau**: the commit, test and column errors of
`Ligero.AgreementThreshold` or of `MaskTest.Pieces`. -/
noncomputable def bounds : Setup C P products Lin nL np → Ligero.AgreementThreshold.Bounds
  | .listRadius S => ⟨S.commitError, Ligero.AgreementThreshold.testError S.toSetup,
      Ligero.AgreementThreshold.columnError S.toSetup⟩
  | .split S => ⟨S.commitError, MaskTest.Pieces.testError K,
      MaskTest.Pieces.columnError S.toSetup⟩

/-- **Soundness on the prefix condition** (`GordieHowe.Ligero.UntestedMask.soundIP`,
`GordieHowe.Ligero.MaskTest.soundIP`): the commit event has probability at most `commitError`, and the
proof phase is round-by-round sound relative to "the commit phase was bad, or the rows hold on the
extracted cells and every prefix cell lies in `E`". -/
noncomputable def sound (S : Setup C P products Lin nL np) :
    (S.commitProve rows).SoundOn S.PrefixIn (fun _ => S.commitError) (S.error rows) :=
  match S with
  | .listRadius S => UntestedMask.soundIP S rows
  | .split S => MaskTest.soundIP S rows

variable {rows} in
/-- **The proof-phase errors sum** to the test and column bounds and, when the prefix is
nonempty, the joint subfield term `(k − 1)_t / (N)_t`. -/
theorem error_sum (S : Setup C P products Lin nL np) :
    ∑ i, S.error rows i = S.bounds.test + S.bounds.column +
      if np = 0 then 0 else SubfieldTest.jointSubfieldError C.k N S.t := by
  cases S with
  | listRadius S => exact UntestedMask.error_sum S
  | split S => exact MaskTest.error_sum S

variable {rows} in
/-- **Every proof-phase round error is at most `δ`** when the test bound is and the column bound
with, when the prefix is nonempty, the joint subfield term `(k − 1)_t / (N)_t` is. -/
theorem error_le_of (S : Setup C P products Lin nL np) {δ : ℝ≥0} (htest : S.bounds.test ≤ δ)
    (hcol : S.bounds.column +
      (if np = 0 then 0 else SubfieldTest.jointSubfieldError C.k N S.t) ≤ δ)
    (i : (S.commitProve rows).spec.ChallengeIdx) : S.error rows i ≤ δ := by
  cases S with
  | listRadius S => exact UntestedMask.error_le_of S htest hcol i
  | split S => exact MaskTest.error_le_of S htest hcol i

omit [DecidableEq K] [Fintype ι] [Fintype Q] [Fintype Lin] in
/-- The commit error is the commit bound. -/
theorem commitError_eq (S : Setup C P products Lin nL np) : S.commitError = S.bounds.commit := by
  cases S <;> rfl

variable {rows} in
/-- **The commit phase draws one challenge**, the low-degree challenge. -/
theorem exists_commitIdx_unique (S : Setup C P products Lin nL np) :
    ∃ j : (S.commitProve rows).commitRounds.ChallengeIdx, ∀ j', j' = j := by
  cases S with
  | listRadius S => exact ⟨_, Ligero.AgreementThreshold.commitIdx_eq K R C.k S.nrep⟩
  | split S => exact ⟨_, Ligero.AgreementThreshold.commitIdx_eq K R C.k S.nrep⟩

variable {rows} in
/-- **The commit phase has one challenge index** (`exists_commitIdx_unique`). -/
theorem card_commitIdx (S : Setup C P products Lin nL np) :
    Fintype.card (S.commitProve rows).commitRounds.ChallengeIdx = 1 :=
  Fintype.card_eq_one_iff.mpr S.exists_commitIdx_unique

/-! ### The honest prover -/

/-- **The data of the honest prover** of the setup's system. -/
def Hiding : Setup C P products Lin nL np → Type
  | .listRadius S => UntestedMask.Hiding S
  | .split S => MaskTest.Hiding S

/-- **The simulator of the setup's system** (`GordieHowe.Ligero.UntestedMask.honestSim`,
`GordieHowe.Ligero.MaskTest.honestSim`) at the hiding data `Hd`.

Running time: one run of the masking's simulator (polynomial in the tableau sizes, its
docstring). This running time is argued here, not proved in Lean. -/
def sim : (S : Setup C P products Lin nL np) → S.Hiding → (S.commitProve rows).Sim
  | .listRadius _, Hd => UntestedMask.honestSim rows Hd
  | .split _, Hd => MaskTest.honestSim rows Hd

/-- **The honest prover of the setup's system** (`GordieHowe.Ligero.UntestedMask.honest`,
`GordieHowe.Ligero.MaskTest.honest`), simulated by `sim`: completeness, with the prefix-row test
accepting, and hiding. -/
noncomputable def honest (S : Setup C P products Lin nL np) (Hd : S.Hiding) :
    (S.commitProve rows).Honest (S.sim rows Hd) :=
  match S, Hd with
  | .listRadius _, Hd => UntestedMask.honest rows Hd
  | .split _, Hd => MaskTest.honest rows Hd

/-- **The admissible cells of the honest prover**: every placed value in its row's blinding
field. -/
def Admissible : (S : Setup C P products Lin nL np) → S.Hiding → (ι → K) → Prop
  | .listRadius _, Hd => Hd.inner.Admissible
  | .split _, Hd => Hd.inner.Admissible

theorem admissible_honest (S : Setup C P products Lin nL np) (Hd : S.Hiding) (x : ι → K) :
    (S.honest rows Hd).Admissible x ↔ S.Admissible Hd x := by
  cases S <;> rfl

/-! ### The extracted cells confined to the prefix condition -/

/-- **The system with its extracted cells confined to the prefix condition**: every extracted
prefix cell outside `E` replaced by `0` (`PrefixCells.confineMap`). -/
def confined [DecidableEq ι] (S : Setup C P products Lin nL np) :
    FieldProof.CommitProve K ι products Ctx rows :=
  (S.commitProve rows).confine S.pre.confineMap

/-- **The confined extracted cells satisfy the prefix condition.** -/
theorem in_extract_confined [DecidableEq ι] (S : Setup C P products Lin nL np)
    (O : (S.confined rows).Com) (r : (S.confined rows).Rounds) :
    S.PrefixIn ((S.confined rows).extract O r) :=
  S.pre.confines.good _

/-- **Soundness of the confined system** (`CommitProve.SoundOn.confine`): the commit event, and
the proof phase round-by-round sound relative to "the commit phase was bad or the rows hold on the
confined extracted cells", with the errors of `sound`. -/
noncomputable def soundConfined [DecidableEq ι] (S : Setup C P products Lin nL np) :
    (S.confined rows).Sound (fun _ => S.commitError) (S.error rows) :=
  (S.sound rows).confine S.pre.confines

/-- **The simulator of the setup's system** (`Ligero.AgreementThreshold.simulate`,
`MaskTest.Pieces.simulate`, read as views of the system with the prefix-row test).

Running time: one run of the masking's simulator (polynomial in the tableau sizes, its
docstring). This running time is argued here, not proved in Lean. -/
def simulate : (S : Setup C P products Lin nL np) → (Hd : S.Hiding) → Ctx →
    (S.commitProve rows).commitRounds.Challenges → (S.commitProve rows).spec.Challenges →
    (S.sim rows Hd).SimCoins → (S.commitProve rows).View
  | .listRadius S, Hd => fun c chc ch s =>
    UntestedMask.viewOfInner S rows (Ligero.AgreementThreshold.simulate rows Hd.inner c chc ch s)
  | .split S, Hd => fun c chc ch s =>
    MaskTest.viewOfInner S rows (MaskTest.Pieces.simulate Hd.inner rows c chc ch s)

/-- The simulator of the setup's system is `simulate`. -/
theorem sim_sim (S : Setup C P products Lin nL np) (Hd : S.Hiding) :
    (S.sim rows Hd).sim = S.simulate rows Hd := by
  cases S <;> rfl

/-- **The simulator of the confined system**: `simulate`, its views confined.

Running time: one run of `simulate`. This running time is argued here, not proved in Lean. -/
def simConfined [DecidableEq ι] (S : Setup C P products Lin nL np) (Hd : S.Hiding) :
    (S.confined rows).Sim where
  SimCoins := (S.sim rows Hd).SimCoins
  sim c chc ch s :=
    (S.commitProve rows).viewConfine S.pre.confineMap (S.simulate rows Hd c chc ch s)

/-- **The honest prover of the confined system**: that of the setup's system, simulated by
`simConfined`. -/
noncomputable def honestConfined [DecidableEq ι] (S : Setup C P products Lin nL np)
    (Hd : S.Hiding) : (S.confined rows).Honest (S.simConfined rows Hd) where
  Coins := (S.honest rows Hd).Coins
  commit := (S.honest rows Hd).commit
  commitRounds := (S.honest rows Hd).commitRounds
  prove := (S.honest rows Hd).prove
  Admissible := (S.honest rows Hd).Admissible
  complete := (S.honest rows Hd).complete
  hides c x hx chc ch := by
    have h := ((S.honest rows Hd).hides c x hx chc ch).comp
      ((S.commitProve rows).viewConfine S.pre.confineMap)
    rw [sim_sim] at h
    exact h

end Setup

end

end GordieHowe.Ligero.MaskRow
