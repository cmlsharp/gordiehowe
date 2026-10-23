-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Realize

@[expose] public section

/-!
# GordieHowe: the realization step, the honest obligations

The obligations of the honest prover the realization step's honest domains read
(`GordieHowe.RealizedProgram.realizedAt_of_honest_derivs`): every group's histograms count its
needles (`GordieHowe.RealizedProgram.HistogramsCount`, static and late together, `Range.combined`;
the counts `honestCounts`, a range's its needles' histogram), and the H half of every MAC holds
(`GordieHowe.RealizedProgram.MacsHonest`).

**The histograms and the digits are part of the honest source assignment.** A needle may read
statement values (`enc.high` of Falcon ring native reads a public value), so the honest source
assignment carries the histograms and the digits, as the honest prover computes them from the
honest input. `HistogramsCount` is a property of honest assignments, stated on the honest prover
only.

**The MACs' honest values** (`GordieHowe.RealizedProgram.MacsHonest`) are obligations of the honest prover as well: the
tag `U = Σ_c β^(c+1) · chunk_c(X_H)` and the blind, the polynomial-basis bits of the tag's pad,
which the C++ MAC generator computes (compiler/mac.h) and which have no Lean statement.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP ProofSystem.PhaseLayout
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp}

variable (ir) in
/-- **The honest counts of group `g` of table `t`**, reading values by `rd`, in `α`'s field
(`lem:logup`): for a range, the histogram of the group's needles (`Range.histogram`); for any
other table, the needle count of each row at its first occurrence (`Range.rowHistogram`). -/
-- spec-side
def honestCounts (rd : ir.Valuation I) (t g : ℕ) :
    Fin (ir.tableSize t) → (I (ir.chalField (ir.alphaOf t))).K :=
  match (ir.table t).rows with
  | .range _ => histogram (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g)
  | .columns _ => rowHistogram (ir.tableRow rd (ir.chalField (ir.alphaOf t)) t)
      (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g)
  | .expr _ => rowHistogram (ir.tableRow rd (ir.chalField (ir.alphaOf t)) t)
      (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g)

/-- **The honest counts of a range** are the histogram of the needles. -/
theorem honestCounts_of_isRange {t : ℕ} (hr : ir.IsRange t) (rd : ir.Valuation I) (g : ℕ) :
    ir.honestCounts rd t g = histogram (ir.groupNeedles rd (ir.chalField (ir.alphaOf t)) t g) := by
  unfold honestCounts
  split
  · rfl
  · rename_i cols h
    rw [IsRange, h] at hr
    cases hr
  · rename_i e' h
    rw [IsRange, h] at hr
    cases hr

/-- **Every group's histograms count its needles** in the environment `e`: the static histogram
plus the late histogram (`Range.combined`) is the group's honest counts (`honestCounts`), read in
`α`'s field. A property of honest assignments. -/
def HistogramsCount (e : ir.Env I) : Prop :=
  ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t,
    combined (ir.staticHist (ir.reader e) (ir.chalField (ir.alphaOf t)) t g)
        (ir.lateHist (ir.reader e) (ir.chalField (ir.alphaOf t)) t g) =
      ir.honestCounts (ir.reader e) t g

/-- **The MACs' honest values** in the environment `e` (compiler/mac.h; obligations of the honest
prover): for every cross-field `equal` whose H half the compiler states by its own circuit, the tag is
the honest tag at the key (`MacTagAt`: `U = Σ_c β^(c+1) · chunk_c(X_H)` where `x`'s domain hosts the
MAC, `U = Σ_c β^(c+1) · chunk_c(X_A)` where no domain does); for every cross-field `equal`, each
blind is the polynomial-basis bits of the tag's pad (`padCopy pad polynomialBits`): its coordinate
`i` is `1` when bit `i` of the pad's integer reading is set, `0` otherwise. A hosted tag gives the
realized program's H half; the blinds make the MAC's tails hold with the
tag, which the honest strategy states among the program's predicates (`HonestStrategy.sat`). -/
structure MacsHonest (e : ir.Env I) : Prop where
  /-- The tag of every MAC is its honest tag at its key. -/
  tag : ∀ p ∈ ir.predicates, ∀ dx x dy y k real, p.body = .cross dx x dy y k real →
    real.hPredicate = none → ir.MacTagAt (ir.reader e) dx x real (castElt (e.chal real.key 0))
  /-- The blinds of every MAC are the polynomial-basis bits of its tag's pad. -/
  blind : ∀ p ∈ ir.predicates, ∀ dx x dy y k real, p.body = .cross dx x dy y k real →
    ∀ b ∈ real.blind.toList ++ real.blindX.toList, ∀ i < real.width,
      ir.reader e b i =
        if ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit i then 1 else 0

variable {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

end

end GordieHowe.RealizedProgram
