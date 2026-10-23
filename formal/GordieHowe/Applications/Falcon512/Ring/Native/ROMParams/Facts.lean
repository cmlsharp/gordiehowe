-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Native.ROMParams.ProofSystem
public import GordieHowe.Applications.Falcon512.Ring.Frontend.Basic

@[expose] public section

/-!
# GordieHowe frontend: the program facts of `Falcon512.Ring.Native.ROMParams`

The native Falcon ring frontend's program facts (`GordieHowe.Falcon512.Ring.FalconRingPowers`,
`GordieHowe.Falcon512.Ring.FalconRingSelect`, `GordieHowe.Falcon512.Ring.FalconRingBase`) and the generic norm's
(`GordieHowe.Falcon512.Norm.FalconNorm`) for `GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Program.program` (export
`b65a4929`), by `decide` and `rfl` (generated data: reading predicates several entries deep raises
`maxRecDepth` for the `rfl` facts), and domain `A`'s field `F_q^9` (`GordieHowe.Falcon512.AField`).
-/

namespace GordieHowe.Falcon512.Ring.Native.ROMParams

open Generated.Falcon512.Ring.Native.ROMParams.Program
open Norm Ring

instance : AField (interpROM 0) := inferInstanceAs (AField RealizedProgram.fq9)

set_option maxRecDepth 4096 in
instance : FalconRingPowers program where
  one := 0
  gamma := 8
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  exprs_length := by decide +kernel
  expr0 := rfl
  expr1 := rfl
  exprEven m hm := by
    simp only [List.mem_range'_1] at hm
    obtain ⟨h1, h2⟩ := hm
    interval_cases m <;> rfl
  exprOdd m hm := by
    simp only [List.mem_range'_1] at hm
    obtain ⟨h1, h2⟩ := hm
    interval_cases m <;> rfl
  expr15 := rfl
  size0 := by decide +kernel

set_option maxRecDepth 4096 in
instance : FalconRingSelect program where
  idx := 7
  dig := 21
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  exprs_length := by decide +kernel
  expr16 := rfl
  exprSel t ht := by
    simp only [List.mem_range'_1] at ht
    obtain ⟨h1, h2⟩ := ht
    interval_cases t <;> rfl

set_option maxRecDepth 4096 in
theorem ring_member : ∃ t, (program.predicate 0).body = .equal 0 (.add (.apply (.sum 512)
    (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf 6))) (.reindex [(0, 1, 512)] (.leaf 20))))
    (.scale (.const 12288) (.mux (.reindex [(5, 0, 1)] (.leaf 7)) (.reindex [(1, 0, 1)] (.ref 20))
      (.reindex [(0, 0, 1)] (.ref 20))))) (.leaf 1) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
theorem ring_sig : ∃ t, (program.predicate 1).body = .equal 0 (.add (.apply (.ntt 512 10302 .natural)
    (.add (.leaf 5) (.scale (.const 12288) (.leaf 10)))) (.scale (.const 12288)
      (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf 6)))
        (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.apply (.ntt 512 10302 .natural)
          (.leaf 9))))))) (.leaf 2) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
theorem ring_idxBool :
    ∃ t, (program.predicate 14).body = .equal 0 (.mul (.leaf 7) (.leaf 7)) (.leaf 7) t :=
  ⟨_, rfl⟩

set_option maxRecDepth 4096 in
/-- The membership's facts: the ring `4`, the spectrum `6`, the powers `20`, the zero constant `1`,
`ψ = 10302`, `−1 = 12288`, the index bits' check `14`. -/
instance : FalconRingMember program where
  ring := 4
  spec := 6
  pow := 20
  zero := 1
  psi := 10302
  mOne := 12288
  idxPred := 14
  chal := 5
  s2 := 9
  domainField0 := by decide +kernel
  member := ring_member
  idxBool := ring_idxBool
  inSource := by decide +kernel
  powersKind := rfl
  digestsKind := rfl
  consts := by decide +kernel
  gammaKind := rfl
  ringKind := rfl
  chalKind := rfl
  chal_ne_ring := by decide
  fields := by decide +kernel
  sizes := by decide +kernel
  chal0 := by decide +kernel
  isSourceChal_iff := fun j => by
    constructor
    · intro h
      have hj : j < 2 := h.1
      have key : ∀ j < 2, program.IsSourceChal j → j = 0 := by decide +kernel
      exact key j hj h
    · rintro rfl
      decide +kernel
  values_length := by decide +kernel
  privKinds := ⟨rfl, rfl, rfl⟩

set_option maxRecDepth 4096 in
/-- The native ring's facts outside the membership. -/
instance : FalconRingBase program where
  ids := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  sig := ring_sig
  inSource1 := by decide +kernel
  const2 := by decide +kernel
  chalKind := rfl
  fields := by decide +kernel
  sizes := by decide +kernel
  values_length := by decide +kernel
  primeVals := by decide +kernel
  privKinds := ⟨rfl, rfl⟩

set_option maxRecDepth 4096 in
theorem norm_center : ∃ t, (program.predicate 2).body = .equal 0 (.add (.mul (.ref 21) (.ref 21))
    (.scale (.const 12288) (.mul (.add (.add (.ref 22) (.scale (.const 64) (.ref 23)))
      (.scale (.const 4096) (.ref 24))) (.add (.add (.ref 22) (.scale (.const 64) (.ref 23)))
        (.scale (.const 4096) (.ref 24)))))) (.leaf 3) t := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_top : ∃ t, (program.predicate 3).body = .equal 0 (.ref 25) (.leaf 1) t :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_col0 : ∃ real, (program.predicate 4).body = .mod 0 0 (.mul (.ref 26) (.ref 26))
    (.add (.ref 27) (.scale (.const 64) (.ref 28))) real := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_col1 : ∃ real, (program.predicate 5).body = .mod 0 0
    (.add (.scale (.const 2) (.mul (.ref 26) (.ref 29))) (.ref 30))
    (.add (.ref 31) (.scale (.const 64) (.ref 32))) real := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_col2 : ∃ real, (program.predicate 6).body = .mod 0 0
    (.add (.add (.scale (.const 2) (.mul (.ref 26) (.ref 33))) (.mul (.ref 29) (.ref 29)))
      (.ref 34)) (.add (.ref 35) (.scale (.const 64) (.ref 36))) real := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_col3 : ∃ real, (program.predicate 7).body = .mod 0 0
    (.add (.scale (.const 2) (.mul (.ref 29) (.ref 33))) (.ref 37))
    (.add (.ref 38) (.scale (.const 64) (.ref 39))) real := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_col4 : ∃ real, (program.predicate 8).body = .mod 0 0
    (.add (.mul (.ref 33) (.ref 33)) (.ref 40)) (.add (.ref 41) (.scale (.const 64) (.ref 42)))
    real := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_col5 : ∃ real, (program.predicate 9).body = .mod 0 0 (.ref 43) (.ref 44) real :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_normalize : ∃ real, (program.predicate 10).body = .mod 0 0
    (.add (.add (.ref 45) (.apply (.batched 102 (.sum 63)) (.ref 46))) (.ref 47))
    (.add (.leaf 14) (.scale (.const 64) (.ref 48))) real := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_complement : ∃ real, (program.predicate 11).body = .mod 0 0
    (.add (.add (.ref 49) (.leaf 16)) (.ref 50)) (.add (.leaf 18) (.scale (.const 64) (.leaf 17)))
    real := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_dcBool : ∃ t, (program.predicate 15).body =
    .equal 0 (.mul (.leaf 17) (.leaf 17)) (.leaf 17) t := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_encB : ∃ t, (program.predicate 16).body =
    .equal 0 (.mul (.ref 54) (.ref 54)) (.ref 54) t := ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_rangeA : ∃ real, (program.predicate 17).body = .mem 0 [.leaf 11] (.range 64) real :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_rangeSq : ∃ real, (program.predicate 18).body = .mem 0 [.leaf 12] (.range 64) real :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_rangeCc : ∃ real, (program.predicate 19).body = .mem 0 [.leaf 13] (.range 189) real :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_rangeNd : ∃ real, (program.predicate 20).body = .mem 0 [.leaf 14] (.range 64) real :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_rangeNc : ∃ real, (program.predicate 21).body = .mem 0 [.leaf 15] (.range 64) real :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_rangeD : ∃ real, (program.predicate 22).body = .mem 0 [.leaf 16] (.range 64) real :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_high : ∃ real, (program.predicate 23).body = .mem 0 [.ref 51] (.range 16) real :=
  ⟨_, rfl⟩
set_option maxRecDepth 4096 in
theorem norm_slack : ∃ real, (program.predicate 24).body =
    .mem 0 [.add (.scale (.const 12288) (.apply (.sum 512) (.ref 51))) (.leaf 19)] (.range 393)
      real := ⟨_, rfl⟩

/-- The norm's index maps of the batches (`6426` entries, decided coordinate by coordinate). -/
theorem norm_i70_entry : ∀ b < 17, ∀ m < 6, ∀ s < 63, idx50.entry ((6 * b + m) * 63 + s) =
    if 63 * b + s < 1024 then 6 * (63 * b + s) + m else 6144 := by
  decide +kernel

set_option maxRecDepth 4096 in
/-- **The generic norm's identifiers and facts** at the ring's one domain. -/
noncomputable instance : FalconNorm program where
  dA := 0
  fA := 0
  domainField := by decide +kernel
  s2 := 9
  s1 := 10
  a := 11
  sq := 12
  cc := 13
  nd := 14
  nc := 15
  D := 16
  Dc := 17
  tgt := 18
  off := 19
  z1 := 1
  z := 3
  e0 := 21
  p0 := 2
  eMax := 54
  pDc := 15
  pEncB := 16
  pRange := 17
  pHigh := 23
  pSlack := 24
  eHigh := 51
  eMid := 53
  eB := 54
  iHigh := idx55
  iMid := idx56
  i52 := idx33
  i53 := idx34
  i54 := idx35
  i55 := idx36
  i56 := idx37
  i57 := idx17
  i58 := idx38
  i59 := idx39
  i60 := idx40
  i61 := idx41
  i62 := idx42
  i63 := idx43
  i64 := idx44
  i65 := idx45
  i66 := idx46
  i67 := idx47
  i68 := idx48
  i69 := idx49
  i70 := idx50
  i71 := idx51
  i72 := idx52
  i73 := idx53
  i74 := idx54
  refsOrdered := (RealizedProgram.refsOrderedB_iff program).1 (by decide +kernel)
  inSource_A := by decide +kernel
  center := norm_center
  top := norm_top
  col0 := norm_col0
  col1 := norm_col1
  col2 := norm_col2
  col3 := norm_col3
  col4 := norm_col4
  col5 := norm_col5
  normalize := norm_normalize
  complement := norm_complement
  dcBool := norm_dcBool
  encB := norm_encB
  rangeA := norm_rangeA
  rangeSq := norm_rangeSq
  rangeCc := norm_rangeCc
  rangeNd := norm_rangeNd
  rangeNc := norm_rangeNc
  rangeD := norm_rangeD
  high := norm_high
  slack := norm_slack
  exprs_norm := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  exprs_enc := ⟨rfl, rfl, rfl⟩
  norm_le := by decide
  enc_le := by decide
  idx_enc := by decide +kernel
  exprs_length := by decide +kernel
  sizes_A := by decide +kernel
  primeA_all := by decide +kernel
  fields_A := by decide +kernel
  noBound := by decide +kernel
  consts_A := by decide +kernel
  const41 := ⟨[0], rfl, rfl⟩
  const555 := ⟨by decide +kernel, [38, 16, 53, 1, 2, 0], rfl, by decide⟩
  i52_entry := by decide +kernel
  i53_entry := by decide +kernel
  i54_entry := by decide +kernel
  i55_entry := by decide +kernel
  i56_entry := by decide +kernel
  i58_entry := by decide +kernel
  i59_entry := by decide +kernel
  i60_entry := by decide +kernel
  i61_entry := by decide +kernel
  i62_entry := by decide +kernel
  i63_entry := by decide +kernel
  i64_entry := by decide +kernel
  i65_entry := by decide +kernel
  i66_entry := by decide +kernel
  i67_entry := by decide +kernel
  i68_entry := by decide +kernel
  i52_size := by decide +kernel
  i54_size := by decide +kernel
  i55_size := by decide +kernel
  i56_size := by decide +kernel
  i67_size := by decide +kernel
  i69_entry := by decide +kernel
  i71_entry := by decide +kernel
  i72_entry := by decide +kernel
  i73_entry := by decide +kernel
  i74_entry := by decide +kernel
  i57_entry := by decide +kernel
  i70_entry := norm_i70_entry
  idx_sizes := by decide +kernel

end GordieHowe.Falcon512.Ring.Native.ROMParams

