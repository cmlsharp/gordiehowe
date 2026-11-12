-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.PublicW1.MLDSAPublicW1
public import GordieHowe.Applications.Ring.PublicW1.Restrict
public import GordieHowe.Applications.Ring.PublicW1.CheckSearch

@[expose] public section

/-!
# Two facts about averages and the ring check

- `Finset.expect_prod_eq_expect_expect`: an average over pairs is the iterated average, for any
  `Fintype` instance on the pairs.
- `localPred_highCheck`: the ring check of a ring of shortfall above its level reads the check
  oracle `G` at the ring's points only (`RingCheck.admits_congr`).
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


section Main

variable {N : ℕ} {βmin : ℚ≥0} {reps tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {n Q : ℕ}


omit [Fintype Msg] [DecidableEq Msg] [Inhabited prims.Hint] [Fintype prims.Hint]
  [DecidableEq prims.Hint] in
/-- **The ring check of a ring of shortfall above its level reads `G` at the ring's points only**:
the predicate `chk.s < ringDefectOf l ∧ chk.Admits G l` of the label `l` is local for the
labelling of the check points `(l, j, r)` by their ring (`RingCheck.admits_congr`). -/
theorem localPred_highCheck {cutOf : CutoffFamily prims} (chk : RingCheck prims cutOf N reps) :
    ROM.LocalPred (fun x : RingOf (PubKey p prims) N × Fin N × Fin reps => x.1)
      (fun l (G : CheckOrc p prims N reps) =>
        chk.s < ringDefectOf prims cutOf l.1 ∧ chk.Admits prims G l) := by
  intro l G G' hag
  exact and_congr_right fun _ => chk.admits_congr prims fun j r => hag (l, j, r) rfl


end Main

end GordieHowe.Ring.MLDSAW1
