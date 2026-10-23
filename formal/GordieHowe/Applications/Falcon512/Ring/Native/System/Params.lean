-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.System.Params
public import GordieHowe.Foundations.Probability.RangeGroups
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative20
public import GordieHowe.Applications.Falcon512.Native.Fields.FalconNative9

@[expose] public section

/-!
# Falcon ring, native arm: the parameters

The parameters of the Falcon-512 ring signature's native arm as the C++ compiles it
(`lib/gordiehowe/examples/rings/falcon_ring.h`, `falcon_ring_native`, and the
ring's profile constants): the membership table's transform root
(`psi`), and the Ligero codes of domain A at the ROM parameters at two low-degree repetitions, one for
`Falcon512.Native.ROMParams` (`GordieHowe.Falcon512.Ring.Native.Params.aNativeROMShape`) and one for `Falcon512.Ring.Native.ROMParams`
(`GordieHowe.Falcon512.Ring.Native.Params.aRingROMShape`), with their line certificates (`GordieHowe.Falcon512.Ring.Native.Params.aNativeROMMaskTest`, `GordieHowe.Falcon512.Ring.Native.Params.aRingROMMaskTest`) and their
round bounds (`GordieHowe.Falcon512.Ring.Native.Params.aNativeROMCommit_le`, `GordieHowe.Falcon512.Ring.Native.Params.aRingROMCommit_le`, …). The notes below
record the C++'s range plan, phase layout, domain A and its packing tree, which the generated
plan data carries (`GordieHowe/Generated/Falcon512/Ring/Native/QROMParams/Plan.lean`,
`GordieHowe/Generated/Falcon512/Ring/Native/ROMParams/Plan.lean`). The system has one domain, `A`, and no MAC: the
salt and the message are public, so `c = HashToPoint(r ‖ m)` is a statement value and the relation
is proved in `A` alone. Names are the C++'s scoped node names (`member.ring.gamma`, `norm.a`,
`enc.high`, `alpha:A`, …), as in the generated plan data. Citations are `file:line` at
`f4d7f5db`, relative to `lib/gordiehowe/` unless they name another directory.

The C++ compiles two field profiles: one at the QROM parameters (`F_q^20`, the tower `u^4 = 11`, `v^5 = u + 2`,
`FalconNativeField20`) and one at the ROM parameters (`F_q^9 = F_q[x]/(x^9 - 2)`, `FalconNativeField9`). The ring
profile does not raise the packing tree's largest edge degree (`DomainProfile::d_max`, default `16`;
Falcon native sets it to the field's degree, `examples/falcon/falcon_native.h`), so the tree at the QROM
parameters has the intermediate node `GF(p^4)`: `GF(p) < GF(p^4) < F_q^20`. The tree at the ROM parameters is `GF(p) < F_q^9`.
-/

namespace GordieHowe.Falcon512.Ring.Native.Params

open scoped NNReal
open Emulated.Params (q n betaSq)

/-! ## The ring and its membership table

`public_table(s, A, "ring", keys, RowMap::negacyclic(A.field(), kN, psi, NttOrder::kNatural))`
and `select_row(s, table, "signer", spectrum)` (`examples/rings/falcon_ring.h`,
`membership`; `table.h:501-724`): the ring's keys are the table's rows, a row's record is the
negacyclic transform of the key at the root `ψ` in natural order (cell `k` is `h(ψ^(2k + 1))`),
one challenge `γ` compresses a record into its digest `Σ_k rec[k] γ^k`, and the committed
spectrum's digest equals the selected row's digest, the fold of the public digests over the
committed index bits. -/

/-- **The transform root** `ψ = 10302` of order `2n = 1024` in `F_q`
(`examples/rings/falcon_ring.h`, `kNativePsi`; plan data, `leaf0.psi` and the spectral gadget's
`root`). -/
abbrev psi : ℕ := 10302

/-! ## The range plan

The requests of domain A in declaration order (`examples/rings/falcon_ring.h`: the native norm,
then the encoding): `norm.a`, `norm.sq`, `norm.cc` (`norm.h:271`, `:306-307`), `norm.nd`,
`norm.nc` (`norm.h:358-359`), `norm.D` (`norm.h:410`), `enc.high`, `enc.slack_hi`, `enc.slack_lo`
(`norm.h:488,501-502`). Every request is realized direct (static) at the table size, honest bound
and maximum `T = 64`. There is one table `[0, 64)`, split into groups of at most `4096` needles
(`examples/rings/falcon_ring.h`, `native_compile_profile`; `falcon_ring_profile.h`,
`kNativeRangeGroup`), so each group's fraction tree stays as shallow as the existing ring's. -/

/-! ## The phase layout

The C++ draws both challenges in its phase `1`, the Lean's phase `0`: the membership challenge
`member.ring.gamma` (`table.h:569`) and the lookup point `alpha:A`. No value is late (plan
data, `messages = []`). -/

/-! ## Domain A

The coordinates of domain A in allocation order (plan data, `coords`): the public inputs (the
constant one, `c`, the table's `powers` and `digests`, the encoding's offsets, `alpha:A`
and the weights), then the committed cells (`key.spectrum`, the index bits, `s2`, `signature.s1`,
the native norm's witness, `enc.slack_hi`, and the five groups' histograms). -/

/-! ## Domain A's packing tree and extended Fiat–Shamir points

At the QROM parameters: `GF(p) < GF(p^4) < F_q^20`, two subfield-mask edges of degrees `4` and `5`; the input row and
the affine rows read the prime-field cells, so they are routed to the inner stage `GF(p) < GF(p^4)`
(`110` rows), which draws one weight per row slot (its GKR layers, the input row and the affine
rows); the root draws one more per measurement of the inner stage, and Ligero's linear test one per
root measurement and its combined row (`TreePlan::stream_rows`). At the ROM parameters: `GF(p) < F_q^9`, one edge
of degree `9`, as in Falcon native. -/

/-! ## The Ligero codes of domain A

Ligero at an agreement threshold, with the mask test, at the tableaus of the plan data (domain
A's `ligero` entry: rate, `block_enc`, `N`, `k`, the opened columns `t` and the blinding width
`r = t`). The code is `k = (block_enc + 1) / (2 + rate)`, `N = block_enc − (2k − 1)`
(`../ligero/ligero_param.h`, `LigeroParam`). The code at the QROM parameters, its agreement
threshold and its line certificate are `Tableau.fq20K271Shape` and `Tableau.fq20K271Line`. -/

/-! ### The codes at the ROM parameters at two low-degree repetitions

The compiler's choices for domain A over `F_q^9`, the mask test, two low-degree repetitions, with
the compiler's agreement thresholds and exceptional counts (`lib/gordiehowe/compiler/ligero_choice.h`,
`best_line_exhaustive`): `Falcon512.Native.ROMParams` `(rate, t, block_enc) = (5, 90, 2369)` at
`A = 758`; `Falcon512.Ring.Native.ROMParams` `(5, 89, 2105)` at `A = 673`. -/

/-! ### The code at the ROM parameters of `Falcon512.Native.ROMParams`'s domain A, `(N, k) = (1694, 338)`, `t = 90`, two low-degree repetitions -/

/-- The rate of the tableau: `5`. -/
abbrev aNativeROMRate : ℕ := 5

/-- `block_enc` of the tableau: `2369`. -/
abbrev aNativeROMBlockEnc : ℕ := 2369

/-- The opened columns of the tableau: `t = 90`. -/
abbrev aNativeROMT : ℕ := 90

/-- The low-degree repetitions of the tableau: `2`. -/
abbrev aNativeROMReps : ℕ := 2

/-- The message length of the code: `k = 338`. -/
abbrev aNativeROMK : ℕ := (aNativeROMBlockEnc + 1) / (2 + aNativeROMRate)

/-- The block length of the code: `N = 1694`. -/
abbrev aNativeROMN : ℕ := aNativeROMBlockEnc - (2 * aNativeROMK - 1)

/-- The agreement threshold of the line certificate: `A = 758`. -/
abbrev aNativeROMAgree : ℕ := 758

/-- The exceptional count of the line certificate: `B = 34023420758` (`2^34.99`). -/
abbrev aNativeROMExceptions : ℕ := 34023420758

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (5, 90, 2369)` at two
low-degree repetitions. -/
def aNativeROMShape : Ligero.Relative.Shape :=
  ⟨aNativeROMRate, aNativeROMT, aNativeROMBlockEnc, aNativeROMReps, aNativeROMT⟩

/-- The message length is `338`. -/
theorem aNativeROMK_eq : aNativeROMK = 338 := rfl

/-- The block length is `1694`. -/
theorem aNativeROMN_eq : aNativeROMN = 1694 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 758`: the weighted
Johnson certificate `(m, B, H) = (111, 249, 31543)` for degree `337` on `1694` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem aNativeROMLine {F : Type} [Field F] (C : GordieHowe.RSCode F aNativeROMN)
    (hk : C.k = aNativeROMK) :
    RSCode.LineCertificate C aNativeROMAgree (aNativeROMExceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 337) (m := 111) (B := 249)
    (H := 31543) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test**. -/
theorem aNativeROMMaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F aNativeROMN)
    (hk : C.k = aNativeROMK) :
    Ligero.MaskTest.Pieces.Parameters C aNativeROMAgree aNativeROMExceptions :=
  ⟨by rw [hk]; decide, aNativeROMLine C hk⟩

/-- The round bounds of the tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev aNativeROMBounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds FalconNativeField9 aNativeROMN aNativeROMAgree aNativeROMExceptions
    aNativeROMReps aNativeROMK aNativeROMT

/-- The commit round of the tableau: `(34023420758/(|F| − 1))^2`, `2^-174.56`. -/
theorem aNativeROMCommit_le : aNativeROMBounds.commit ≤ (1 : ℝ≥0) / 2 ^ 140 := by
  show (((34023420758 : ℕ) : ℝ≥0) / (Fintype.card FalconNativeField9 - 1)) ^ 2 ≤ _
  rw [falconNativeField_card]
  have h := ratio_pred_pow_le_dyadic (num := 34023420758) (q := 12289 ^ 9) (c := 1) (e := 140)
    (nrep := 2) (by decide +kernel)
  rwa [Nat.cast_one] at h

/-- The test round of the tableau with the mask test: `1/|F|`, `2^-122.266`. -/
theorem aNativeROMTest_le : aNativeROMBounds.test ≤ (218048 : ℝ≥0) / 2 ^ 140 := by
  show (1 : ℝ≥0) / (Fintype.card FalconNativeField9 : ℝ≥0) ≤ _
  rw [falconNativeField_card]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 218048) (by decide +kernel) (by decide +kernel)

/-- The column round of the tableau with the mask test at `t = 90`, with the joint subfield
term: `((758 − 1)_90 + (2 · 338 − 1)_90)/(1694)_90 + (338 − 1)_90/(1694)_90`, `2^-109.066`. -/
theorem aNativeROMColumn_le : aNativeROMBounds.column +
    Ligero.SubfieldTest.jointSubfieldError aNativeROMK aNativeROMN aNativeROMT ≤
      (2051026752 : ℝ≥0) / 2 ^ 140 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

/-! ### The code at the ROM parameters of `Falcon512.Ring.Native.ROMParams`'s domain A, `(N, k) = (1506, 300)`, `t = 89`, two low-degree repetitions -/

/-- The rate of the tableau: `5`. -/
abbrev aRingROMRate : ℕ := 5

/-- `block_enc` of the tableau: `2105`. -/
abbrev aRingROMBlockEnc : ℕ := 2105

/-- The opened columns of the tableau: `t = 89`. -/
abbrev aRingROMT : ℕ := 89

/-- The low-degree repetitions of the tableau: `2`. -/
abbrev aRingROMReps : ℕ := 2

/-- The message length of the code: `k = 300`. -/
abbrev aRingROMK : ℕ := (aRingROMBlockEnc + 1) / (2 + aRingROMRate)

/-- The block length of the code: `N = 1506`. -/
abbrev aRingROMN : ℕ := aRingROMBlockEnc - (2 * aRingROMK - 1)

/-- The agreement threshold of the line certificate: `A = 673`. -/
abbrev aRingROMAgree : ℕ := 673

/-- The exceptional count of the line certificate: `B = 51456804230` (`2^35.58`). -/
abbrev aRingROMExceptions : ℕ := 51456804230

/-- **The Ligero numbers of the tableau**: `(rate, t, block_enc) = (5, 89, 2105)` at two
low-degree repetitions. -/
def aRingROMShape : Ligero.Relative.Shape :=
  ⟨aRingROMRate, aRingROMT, aRingROMBlockEnc, aRingROMReps, aRingROMT⟩

/-- The message length is `300`. -/
theorem aRingROMK_eq : aRingROMK = 300 := rfl

/-- The block length is `1506`. -/
theorem aRingROMN_eq : aRingROMN = 1506 := rfl

/-- **The line certificate of the code**, at agreement threshold `A = 673`: the weighted
Johnson certificate `(m, B, H) = (111, 249, 53709)` for degree `299` on `1506` points
(`lib/gordiehowe/compiler/ligero_choice.h`, `best_line_exhaustive`). -/
theorem aRingROMLine {F : Type} [Field F] (C : GordieHowe.RSCode F aRingROMN)
    (hk : C.k = aRingROMK) :
    RSCode.LineCertificate C aRingROMAgree (aRingROMExceptions : ℕ) :=
  RSCode.lineCertificate_of_weightedJohnson C (D := 299) (m := 111) (B := 249)
    (H := 53709) (by unfold ReedSolomon.HiddenDerivative.IsJohnsonWeightedCertificate; decide +kernel)
    hk (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [ReedSolomon.HiddenDerivative.johnsonWeightedRefinedExceptionCount])

/-- **The code parameters of the tableau with the mask test**. -/
theorem aRingROMMaskTest {F : Type} [Field F] (C : GordieHowe.RSCode F aRingROMN)
    (hk : C.k = aRingROMK) :
    Ligero.MaskTest.Pieces.Parameters C aRingROMAgree aRingROMExceptions :=
  ⟨by rw [hk]; decide, aRingROMLine C hk⟩

/-- The round bounds of the tableau (`Ligero.MaskTest.Pieces.bounds`). -/
noncomputable abbrev aRingROMBounds : Ligero.AgreementThreshold.Bounds :=
  Ligero.MaskTest.Pieces.bounds FalconNativeField9 aRingROMN aRingROMAgree aRingROMExceptions
    aRingROMReps aRingROMK aRingROMT

/-- The commit round of the tableau: `(51456804230/(|F| − 1))^2`, `2^-173.37`. -/
theorem aRingROMCommit_le : aRingROMBounds.commit ≤ (1 : ℝ≥0) / 2 ^ 140 := by
  show (((51456804230 : ℕ) : ℝ≥0) / (Fintype.card FalconNativeField9 - 1)) ^ 2 ≤ _
  rw [falconNativeField_card]
  have h := ratio_pred_pow_le_dyadic (num := 51456804230) (q := 12289 ^ 9) (c := 1) (e := 140)
    (nrep := 2) (by decide +kernel)
  rwa [Nat.cast_one] at h

/-- The test round of the tableau with the mask test: `1/|F|`, `2^-122.266`. -/
theorem aRingROMTest_le : aRingROMBounds.test ≤ (218048 : ℝ≥0) / 2 ^ 140 := by
  show (1 : ℝ≥0) / (Fintype.card FalconNativeField9 : ℝ≥0) ≤ _
  rw [falconNativeField_card]
  exact_mod_cast ratio_le_dyadic (num := 1) (c := 218048) (by decide +kernel) (by decide +kernel)

/-- The column round of the tableau with the mask test at `t = 89`, with the joint subfield
term: `((673 − 1)_89 + (2 · 300 − 1)_89)/(1506)_89 + (300 − 1)_89/(1506)_89`, `2^-108.588`. -/
theorem aRingROMColumn_le : aRingROMBounds.column +
    Ligero.SubfieldTest.jointSubfieldError aRingROMK aRingROMN aRingROMT ≤
      (2856780266 : ℝ≥0) / 2 ^ 140 :=
  column_le_dyadic (by decide +kernel) (by decide +kernel)

end GordieHowe.Falcon512.Ring.Native.Params
