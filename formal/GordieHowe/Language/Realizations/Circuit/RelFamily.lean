-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelTable
public import GordieHowe.Language.RealizedProgram.RealizationValid
public import GordieHoweNative.Language.Realizations.Circuit.RelFamily

@[expose] public section

/-!
# GordieHowe: the family records of a GKR circuit's realization and alignment entries

A realization entry's raw-call results have no printed form; its family record
(`GKR.Rel.FamCert`) holds their wires and points at the table nodes and the input block the
realization reads. This file builds, from the record and the printed program, the cuts and the one
assertion item the relational check (`GKR.Rel.relOk`) compares, and the record's guards:

* **Fraction trees** (`GKR.Rel.FracTree.okB`, `GKR.Rel.FracTree.cuts`): the certificate gives the
  tree; the check reads each inner node's kids below it and their spans of leaves adjacent, the
  root spanning every leaf (`fracLo`, `fracHi`). An inner node's numerator is `n_l·d_r + n_r·d_l`
  and its denominator `d_l·d_r`, a leaf's numerator one.
* **A range LogUp** (`GordieHowe.RealizedProgram.logupCuts`,
  `GordieHowe.RealizedProgram.logupGuardE`): each leaf's denominator is `α − needle`, the needles
  the group's members' coordinates read by the nodes the record names (their prints are the members'
  needle expressions); the tree; the sum `S` of the histograms times the weights, the inputs of the
  weights block; the item `N − D·S`.
* **A MAC H half** (`GordieHowe.RealizedProgram.macHCuts`, `GordieHowe.RealizedProgram.macHGuardE`):
  each chunk is `Σ_i g^i · X[c w + i]`, `g` the code `2` and its powers computed with the field's
  arithmetic; the item `U − Σ_c chunk_c · r_c`.
* **An alignment entry** (`GordieHowe.RealizedProgram.fillerGuardB`): its pairs read the inputs of
  the filler block the record names, in order.

Every guard compares a pointer with the printed program; nothing is searched. Each checker is its
failure-reporting twin's success.

The definitions are in `GordieHoweNative/Language/Realizations/Circuit/RelFamily.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert Frac FracTree LogupCert MacHCert FamCert relOkE)

/-! ## Reading the record -/

/-- **The trie reads the node's wires.** -/
theorem wireAtT_wiresT (E : ETable) (k i : ℕ) : wireAtT (wiresT E k) i = wireAt E k i := by
  unfold wireAtT wiresT wireAt
  cases h : Nat.blt i (E.get k).wires.length
  · have h' : ¬ i < (E.get k).wires.length := fun hl => by simp [Nat.blt_eq.mpr hl] at h
    simp only [Bool.cond_false]
    exact (List.getD_eq_default _ _ (Nat.not_lt.mp h')).symm
  · simp only [Nat.blt_eq] at h
    simp only [Bool.cond_true]
    exact Trie.get_ofList _ h


theorem needleWires_eq (E : ETable) (ms : List Member) (ys : List ℕ) :
    needleWires E ms ys = (needleCoords ms ys).map fun q => wireAt E q.1 q.2 := by
  unfold needleWires needleCoords
  simp only [List.map_flatMap, List.map_map, Function.comp_def, wireAtT_wiresT]

section

variable (ir : RealizedProgram)

/-- **Every challenge's value lies in the challenge's field** (a sweep of the values). -/
def chalFieldsB : Bool :=
  (List.range ir.values.length).all fun v =>
    match (ir.value v).kind with
    | .challenge j => Nat.beq (ir.valueField v) (ir.chalField j)
    | _ => true

variable (c : ℕ) (ar : CodeArith) (cd : CircuitData)

/-! ## The range LogUp -/

/-- **A range LogUp entry checks.** -/
def logupB (k t g : ℕ) (lc : LogupCert) (as : List Assert) : Bool :=
  okB (ir.logupE c ar cd k t g lc as)

/-! ## The MAC H half -/

/-- **The cuts of a MAC H entry** (cross-field `equal` `p`): per chunk `c`, its wire against
`Σ_{i < w} g^i · X[c w + i]`, `g` the code `2`, its powers by the field's arithmetic. -/
def macHCuts (p : ℕ) (mc : MacHCert) : List (Wire × TE) :=
  match (ir.predicate p).body with
  | .cross _ _ _ _ _ real =>
    let w := real.width
    let G := Trie.ofList (powList ar 2 w 1)
    mc.chunks.zipIdx.map fun q =>
      (q.1, TE.sumL ((List.range w).map fun i =>
        TE.scale (G.get i) (teW (wireAt cd.table mc.bits (q.2 * w + i)))))
  | _ => []

/-- **A MAC H entry checks**, as its twin: its guards, its cuts, its item. -/
def macHE (k p : ℕ) (mc : MacHCert) (as : List Assert) : Except CertFailure Unit :=
  seqE (ir.macHGuardE c ar cd k p mc as)
    (seqE (mapE (fun r => ⟨k, 0, .rel r⟩)
      (relOkE cd.w cd.dag cd.consts ar (ir.macHCuts ar cd p mc) []))
      (mapE (fun r => ⟨k, 0, .rel r⟩) (relOkE cd.w cd.dag cd.consts ar [] [macHItem cd mc as])))

/-- **A MAC H entry checks.** -/
def macHB (k p : ℕ) (mc : MacHCert) (as : List Assert) : Bool := okB (ir.macHE c ar cd k p mc as)

/-! ## Reading wires by key -/

theorem logupCutsT_eq (t g : ℕ) (lc : LogupCert) :
    ir.logupCutsT c cd t g lc = ir.logupCuts c cd t g lc := by
  unfold logupCutsT logupCuts
  dsimp only
  rw [needleWires_eq]
  simp only [wireAtT_wiresT, List.zip_map_right, List.map_map]
  rfl

theorem macHCutsT_eq (p : ℕ) (mc : MacHCert) :
    ir.macHCutsT ar cd p mc = ir.macHCuts ar cd p mc := by
  unfold macHCutsT macHCuts
  cases (ir.predicate p).body <;> simp only [wireAtT_wiresT]

end

end GordieHowe.RealizedProgram
