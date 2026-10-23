-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Shared.MACProfiles
public import GordieHowe.Applications.Params
public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Foundations.Algebra.IntLift
public import GordieHowe.ProofSystem.Ligero.MaskTest.Pieces
public import GordieHowe.ProofSystem.Ligero.RelativeLayout
public import GordieHowe.ProofSystem.Ligero.SubfieldTest
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Foundations.Fields.GoldilocksQuartic
public import GordieHowe.Foundations.Fields.GF2_256
public import GordieHowe.Foundations.Fields.GF2_128
public import LatticeCrypto.MLDSA.Params

@[expose] public section

/-!
# ML-DSA: the parameters both configurations use

The parameters of the ML-DSA-44 proofs of possession (`lib/gordiehowe/examples/mldsa/mldsa_native.h`,
`examples/mldsa/mldsa_emulated.h`, the shared gadgets in `examples/mldsa/mldsa_gadgets.h`, the hashes of domain
H in `examples/mldsa/mldsa_hash.h` and SampleInBall in `examples/mldsa/sample_in_ball.h`; `msgLen = 32`, an
empty context) that ML-DSA native and ML-DSA emulated share: ML-DSA-44's constants (read from
`mldsa44`), the range table and the sizes of `w` and the norm, the MAC field profiles (`Profile`,
`GordieHowe.MLDSA44.Native.Params.Profile.qrom`, `GordieHowe.MLDSA44.Native.Params.Profile.rom`, with the width, taps and chunk count `nch` derived from them), and
the stream length of the rising-threshold selection (`nSamples`). The section comments record the
plans' challenge points with extended stream budgets and the Ligero tableaus at both profiles. ML-DSA emulated's own
parameters are in `GordieHowe/Applications/MLDSA44/Emulated/System/Params.lean`.
-/

namespace GordieHowe.MLDSA44.Native.Params

open scoped NNReal

/-! ## ML-DSA-44's constants -/

/-- ML-DSA's modulus `q = 8380417` (`examples/mldsa/mldsa_gadgets.h`, `kQ`). -/
abbrev q : ℕ := mldsa44.q

/-- The ring degree `N = 256` (`examples/mldsa/mldsa_hash.h`, `kN`; the vendored
`MLDSA.ringDegree`). -/
abbrev N : ℕ := _root_.MLDSA.ringDegree

/-- The rows `K = 4` of `A` (`examples/mldsa/mldsa_hash.h`, `kK`; the vendored `mldsa44.k`). -/
abbrev nRows : ℕ := _root_.MLDSA.mldsa44.k

/-- The columns `L = 4` of `A` (`examples/mldsa/mldsa_gadgets.h`, `kL`; the vendored `mldsa44.l`). -/
abbrev nCols : ℕ := _root_.MLDSA.mldsa44.l

/-- The challenge weight `τ = 39` (`examples/mldsa/mldsa_hash.h`, `kTau`). -/
abbrev τ : ℕ := mldsa44.τ

/-- The dropped bits `d = 13` (`examples/mldsa/mldsa_gadgets.h`, `kD`). -/
abbrev dBits : ℕ := mldsa44.d

/-- The low-order rounding range `γ₂ = (q - 1) / 88 = 95232` (`examples/mldsa/mldsa_gadgets.h`). -/
abbrev γ₂ : ℕ := mldsa44.γ₂

/-- The bits of a high part `6` (`examples/mldsa/mldsa_hash.h`, `kR1Bits`). -/
abbrev r1Bits : ℕ := mldsa44.r1_bits

/-- The norm bound `γ₁ - β = 130994` (`examples/mldsa/mldsa_gadgets.h`, `kBound`). -/
abbrev normBound : ℕ := mldsa44.normBound

/-- The bits of the crossing, `w1Encode(w1)` then the challenge's `(support, sign)` pairs:
`K N r1 + 2 N = 6656` (`examples/mldsa/mldsa_gadgets.h`, `crossing`). -/
abbrev crossBits : ℕ := nRows * N * r1Bits + 2 * N

/-! ## The range table and requests

One table `[0, 512)` (`examples/mldsa/mldsa_native.h`, `kT`; `:135-148`, `compile_profile`). The
requests of domain A in declaration order (`examples/mldsa/mldsa_native.h`): `norm.z`
(`mldsa_gadgets.h:354`: `z + (γ₁ - β - 1)` below `2 (γ₁ - β) - 1`), `hint.offset`, `hint.slack` and
`hint.nowrap` (`mldsa_gadgets.h:430-434`), `hint_weight.weight` (`mldsa_gadgets.h:443`:
`Σ h` below `ω + 1`), then the MAC's `mac.low`, `mac.high` and `mac.nowrap` (`mod.h:483-501`). The
planner realizes `norm.z` two-sided with two digits and binds `z` to them (`z` has no cell),
`hint.offset` and `hint.slack` as two digits each, bound to them, `hint.nowrap` and `mac.nowrap`
implied, `hint_weight.weight` as one complement needle (`range.h:536-559`), and the MAC's limbs
direct late. -/

/-- The range table size `T = 512` (`examples/mldsa/mldsa_native.h`; `NativeArm`'s `B₁`). -/
abbrev T : ℕ := 512

/-- The coordinates of `w'`, `h`, `hint.offset` and `hint.slack`, `K N = 1024`. -/
abbrev wDim : ℕ := nRows * N

/-- `norm.z`'s offset `γ₁ - β - 1 = 130993` (`mldsa_gadgets.h:354`). -/
abbrev normOffset : ℕ := normBound - 1

/-- `norm.z`'s honest bound and maximum `2 (γ₁ - β) - 1 = 261987`. -/
abbrev normHonest : ℕ := 2 * normBound - 1

/-! ## The MAC field profiles

The MAC's field `GF(2^w)` with its reduction taps (`GordieHowe.MACProfile`,
`../params/param_sets.h`) and the native arm `MLDSANativeArm mldsa44 w taps`
(`GordieHowe/Applications/Params.lean`): the table size `B₁ = 512` and the base `B₂` of the MAC quotient's two digits,
which the C++'s radix search picks (`mod.h:346-366`: the least `max(B, ⌊Qmax / B⌋ + 1)`; `116` at the QROM
parameters, `115` at the ROM parameters), with the arm's parameter facts. -/

/-- **A field profile of ML-DSA native**: the MAC field (`mac`) and the native arm
`NativeArm` at its width and taps (`arm`), with `B₁ = T`. -/
structure Profile where
  /-- The MAC field: width, taps, `convMax`. -/
  mac : GordieHowe.MACProfile
  /-- The native arm `NativeArm` at the MAC's width and taps. -/
  arm : NativeArm mldsa44 mac.macWidth mac.macTaps
  /-- The arm's table is the range table. -/
  arm_B₁ : arm.B₁ = T
  /-- The width divides the crossing (`Params.MACWidth`). -/
  macWidth_dvd : mac.macWidth ∣ crossBits
  /-- `mac.high`'s honest bound `acc_max / (2 B) + 1` lies in the table. -/
  high_le : (mldsa44.chunks mac.macWidth * mac.convMax + 1) / (2 * arm.B₂) + 1 ≤ T
  /-- The limbs' maximum `Dmax` admits the table bound. -/
  dmax_ge : T ≤ (q - 2) / (2 * (1 + arm.B₂)) + 1
  /-- `mac.nowrap`'s honest bound `acc_max + 1` is at most its implied bound. -/
  acc_le : mldsa44.chunks mac.macWidth * mac.convMax + 1 ≤ 2 * (T - 1) + 2 * arm.B₂ * (T - 1)
  /-- `mac.nowrap`'s implied bound is at most its maximum `p - 1` (`mac.digits`, `mod.h:479-482`). -/
  nowrap_lt : 2 * (T - 1) + 2 * arm.B₂ * (T - 1) + 1 ≤ q - 1

namespace Profile

variable (P : Profile)

/-- The MAC's width `w`. -/
abbrev macWidth : ℕ := P.mac.macWidth

/-- The MAC's reduction taps. -/
abbrev macTaps : Finset ℕ := P.mac.macTaps

/-- The MAC's chunk count `nch = 6656 / w` (`26` at the QROM parameters, `52` at the ROM parameters;
`mldsa44.chunks`). -/
abbrev nch : ℕ := mldsa44.chunks P.macWidth

/-- **The QROM parameters**: `GF(2^256)`, `B₂ = 116` (`mldsa44NativeQROM`). -/
def qrom : Profile where
  mac := GordieHowe.MACProfile.qrom
  arm := mldsa44NativeQROM
  arm_B₁ := rfl
  macWidth_dvd := by decide
  high_le := by decide
  dmax_ge := by decide
  acc_le := by decide
  nowrap_lt := by decide

/-- **The ROM parameters**: `GF(2^128)`, `B₂ = 115` (`mldsa44NativeROM`). -/
def rom : Profile where
  mac := GordieHowe.MACProfile.rom
  arm := mldsa44NativeROM
  arm_B₁ := rfl
  macWidth_dvd := by decide
  high_le := by decide
  dmax_ge := by decide
  acc_le := by decide
  nowrap_lt := by decide

end Profile

/-! ## The rising-threshold selection and SampleInBall

`h2c.sample.select` (`examples/mldsa/sample_in_ball.h`): `S = 264` stream bytes (`SHAKE256` bytes
`8..271` of `c̃'`, `kSibBytes = 272`, `examples/mldsa/mldsa_hash.h`), `τ = 39` outputs of `8` bits, the
threshold's low `bit_width(τ) = 6` bits committed. `h2c.sample.mem` (`sample_in_ball.h:275-390`):
the memory check over `N = 256` cells, records of arity `3`, `τ + N = 295` reads and
`(N - τ) + 2 τ = 295` writes, of which the `N - τ` initial writes are constant. -/

/-- The stream bytes `S = 264`. -/
abbrev nSamples : ℕ := 264

/-! ## The phase layout

Lean phase `0` is C++ phase `1`: the challenges `h2c.sample.select.delta`, `h2c.sample.mem.delta`
and `mac.beta`, and the messages `mac.value`, `mac.acc`, `mac.low` and `range.dynamic:A.512`;
Lean phase `1` is C++ phase `2`: `alpha:A`. -/

/-! ## The domains

The circuit sizes of the plan data. Domain H's committed inputs include the bit views of the Keccak
outputs, the alignment inputs, the run's zero bits and the batch pads, which are not coordinates. -/

/-! ## The challenge points with extended stream budgets

The C++ lets three challenge points of each domain read `k + e + 4 · n · F::kBytes` stream bytes
instead of the default `k + e` (`BasicTranscript::extend_point_budget_for`), `n` the rows the point
draws one weight for (`TreePlan::stream_rows`): domain H's packing stage's combination (the row
slots before it: one per GKR layer, the input row, the affine rows and two reduction rows per
batch), each domain's root combination (the slots after every stage) and Ligero's linear test (the
root's measurements and its combined row). Domain A has no inner stage. The counts follow the plan
data's circuit sizes; the exported points are `Domain.streamPoints`, and `Domain.FollowsStreamRule`
states the rule. -/

/-! ## The Ligero tableaus

Ligero at an agreement threshold, with the mask test, at the tableaus of the plan data (each
domain's `ligero` entry: rate, `block_enc`, `N`, `k`, the opened columns `t` and the blinding width
`r = t`). The agreement thresholds, exceptional counts and line certificates are those of
`MLDSA44.Native.QROMParams.AlgebraField.aLine` and `MLDSA44.Native.ROMParams.AlgebraField.aLine`
(domain A) and of `Tableau.gf256K339R2Line` and `Tableau.gf128K282R2Line` (domain H). -/

end GordieHowe.MLDSA44.Native.Params
