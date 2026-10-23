-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Basic

@[expose] public section

/-!
# GordieHowe: completeness certificates, the honest environment

The honest late values of a completeness certificate (`GordieHowe.RealizedProgram.genLateOf`: the
source program's at its own late values, the late generators' at every other) and how the honest
environment reads them: the source late values as the execution's, the generated ones as their
generators' (`honestEnvC_late_eq`), so a value reading no generated late value reads at the honest
environment as at the source environment with the source late values
(`reader_honestEnvC_srcEnvL_of_noGen`). These are `honestEnv_late_eq` and its companions with the
generators read off the certificate.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP

section

variable {ir : RealizedProgram} {I : Interp}

variable (ir I) in
/-- **The facts the late generators' values need**: a tag's pad space is the whole field, every pad
space of a late value contains the naturals, and every late value has a pad cell in its domain at
each coordinate (`GenFacts` with the tags read off `G`). -/
structure CGenFacts (G : Gens) : Prop where
  /-- A tag's pad space is the whole field. -/
  tagFull : ∀ v < ir.values.length, ∀ p, G.at v = .tag p → (ir.value v).padSpace = .full
  /-- Every pad space of a late value contains the naturals. -/
  natCast : ∀ l : ir.Late, ∀ n : ℕ,
    (n : (I (ir.valueField l.1)).K) ∈ (I (ir.valueField l.1)).space (ir.value l.1).padSpace
  /-- Every late value's domain is a domain of the program. -/
  domain : ∀ l : ir.Late, (ir.value l.1).domain < ir.domains.length
  /-- Every late value has a pad cell in its domain at each coordinate. -/
  padCells : ∀ l : ir.Late, ∀ i < (ir.value l.1).size,
    CellKey.pad l.1 i ∈ ir.cellKeys (ir.value l.1).domain

/-- **A late generator's value lies in its pad space**: a tag's pad space is the whole field, every
other generated value is a natural. -/
theorem genValOf_mem {G : Gens} (hG : ir.CGenFacts I G) (e : ir.Env I) (l : ir.Late) (i : ℕ) :
    ir.genValOf G e l.1 i ∈ (I (ir.valueField l.1)).space (ir.value l.1).padSpace := by
  by_cases ht : ∃ p, G.at l.1 = .tag p
  · obtain ⟨p, hp⟩ := ht
    rw [hG.tagFull l.1 l.1.2 p hp]
    exact AddSubgroup.mem_top _
  · push Not at ht
    obtain ⟨n, hn⟩ := genValOf_natCast G e ht i
    rw [hn]
    exact hG.natCast l n

variable (I) in
/-- **The honest late values of a certificate** for the honest inputs `y` (statement `stmtOf y`,
committed values `val y`, the source program's late values `SL`) at the challenges `c` and the pads
`π`: the source program's late values at its own late values, the late generators' values
(`genValOf`) at the source environment with those late values (`srcEnvL`) at every other. -/
def genLateOf {Inp : Type} {G : Gens} (hG : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I)
    (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)
    (l : (ir.layout I).Late) : (ir.layout I).Mask l := fun i =>
  if h : ir.IsSourceValue l.1 then ⟨SL.late y c l.1 i, SL.mem y c l h i⟩
  else ⟨ir.genValOf G (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) l.1 i,
    genValOf_mem hG _ l i⟩

/-- **The honest environment reads the honest late values** at the late values' coordinates: the
message minus the pad. -/
theorem honestEnv_late_genLateOf {Inp : Type} {G : Gens} (hG : ir.CGenFacts I G)
    (stmtOf val : Inp → ir.Valuation I) (SL : ir.SrcLate I Inp) (x : ir.Valuation I) (y : Inp)
    (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) (l : ir.Late) {i : ℕ}
    (hi : i < (ir.value l.1).size) :
    (ir.honestEnv I x (val y) (ir.genLateOf I hG stmtOf val SL y) c π).late l.1 i =
      (ir.genLateOf I hG stmtOf val SL y c π l ⟨i, hi⟩).1 := by
  have hcond : (l.1 : ℕ) < ir.values.length ∧ ir.IsLate l.1 ∧ i < (ir.value l.1).size :=
    ⟨l.1.2, l.2, hi⟩
  simp only [honestEnv, layoutEnv, hcond, and_self, ite_true, msgRead, bindAsg,
    honestAsg_pad (hG.domain l) (hG.padCells l i hi), padsOf, ProofSystem.PhaseLayout.honestRun]
  change (((ir.genLateOf I hG stmtOf val SL y c π l ⟨i, hi⟩).1 : (I (ir.valueField l.1)).K) + _) -
    _ = _
  simp

section HonestEnv

variable {Inp : Type} {G : Gens} (hG : ir.CGenFacts I G) (stmtOf val : Inp → ir.Valuation I)
  (SL : ir.SrcLate I Inp) (y : Inp) (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The honest environment of the honest inputs `y` at the statement `x`. -/
local notation "HEx" => ir.honestEnv I x (val y) (ir.genLateOf I hG stmtOf val SL y) c π

set_option hygiene false in
/-- The honest environment of the honest inputs `y`. -/
local notation "HE" => ir.honestEnv I (stmtOf y) (val y) (ir.genLateOf I hG stmtOf val SL y) c π

/-- **The honest environment's late values are the generated values** at every generated late
value, `0` past the coordinates on both sides. -/
theorem honestEnvC_late_eq (x : ir.Valuation I) {u : ℕ} (hu : u < ir.values.length)
    (hl : ir.IsLate u) (hns : ¬ ir.IsSourceValue u) :
    (HEx).late u = ir.genValOf G (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) u := by
  funext i
  by_cases hi : i < (ir.value u).size
  · rw [honestEnv_late_genLateOf hG stmtOf val SL x y c π ⟨⟨u, hu⟩, hl⟩ hi]
    simp only [genLateOf, dif_neg hns]
  · rw [honestEnv_late_zero fun h => hi h.2.2, genValOf, if_neg hi]

/-- **The honest environment's late values are the source program's** at its own late values. -/
theorem honestEnvC_late_eq_src (x : ir.Valuation I) {u : ℕ} (hu : u < ir.values.length)
    (hl : ir.IsLate u) (hs : ir.IsSourceValue u) :
    (HEx).late u = ir.srcLateOf I (SL.late y c) u := by
  funext i
  by_cases hi : i < (ir.value u).size
  · rw [honestEnv_late_genLateOf hG stmtOf val SL x y c π ⟨⟨u, hu⟩, hl⟩ hi]
    simp only [genLateOf, hs, dite_true, srcLateOf, hl, hi, and_self, ite_true]
  · rw [honestEnv_late_zero fun h => hi h.2.2]
    simp only [srcLateOf, hi, and_false, ite_false]

/-- **A late value read but not a late value of the program reads `0`.** -/
theorem honestEnvC_late_of_not (x : ir.Valuation I) {u : ℕ}
    (hl : ¬ (u < ir.values.length ∧ ir.IsLate u)) : (HEx).late u = 0 :=
  funext fun _ => honestEnv_late_zero fun h => hl ⟨h.1, h.2.1⟩

/-- **The honest environment reads like the source environment with the source late values** at a
value reading no generated late value. -/
theorem reader_honestEnvC_srcEnvL_of_noGen {v : ℕ} (hv : ir.NoGenRead v) :
    ir.reader HE v = ir.reader (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) v := by
  refine reader_eq_of_late (e := HE)
    (e' := ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π) rfl rfl rfl fun u hu => ?_
  by_cases hl : u < ir.values.length ∧ ir.IsLate u
  · rw [honestEnvC_late_eq_src hG stmtOf val SL y c π _ hl.1 hl.2 (hv u hu hl.1 hl.2)]
    rfl
  · rw [honestEnvC_late_of_not hG stmtOf val SL y c π _ hl]
    funext i
    simp only [srcEnvL, srcLateOf]
    rw [if_neg (fun h => hl ⟨lt_of_isLate h.2.1, h.2.1⟩)]
    rfl

/-- **A predicate reading no generated late value holds at the honest environment** where it holds
at the source environment with the source late values. -/
theorem holds_honestC_of_src {b : PredBody} (hb : ir.NoGenPred b)
    (h : ir.HoldsWith (ir.reader (ir.srcEnvL I (stmtOf y) (val y) (SL.late y c) c π)) b) :
    ir.HoldsWith (ir.reader HE) b :=
  (holdsWith_congr fun w hw =>
    reader_honestEnvC_srcEnvL_of_noGen hG stmtOf val SL y c π (hb w hw)).2 h

end HonestEnv

end

end GordieHowe.RealizedProgram
