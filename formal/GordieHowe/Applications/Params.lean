-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import GordieHowe.Foundations.Algebra.ConvMatrix

@[expose] public section

/-!
# Scheme and arm parameters

The scheme constants and, per algebra arm, the radices, table sizes and MAC group structure, with
the integer bounds every gadget relies on, each of the form "this value stays below that modulus".
This file states both as structures and discharges the bounds for ML-DSA-44 and Falcon-512 by
computation, so an arm whose parameters violate a bound fails to compile.

Everything here is a natural number. Field sizes for probability bounds are kept separate (they are
real numbers and belong to the round-by-round layer).

The `Conv(r)` coordinate bound is a property of an explicit integer matrix: `Conv.convMax w T` for
chunk width `w` and reduction taps `T`, defined in `GordieHowe/Foundations/Algebra/ConvMatrix.lean`.

Every arm structure takes the MAC shape `(w, T)` as parameters: the chunk width and the reduction
taps of `GF(2^w)`.
-/

namespace GordieHowe

/-- The 128-bit MAC chunk width at the ROM parameters (`256` at the QROM parameters). -/
abbrev macChunkBits : ℕ := 128

/-- The `Conv(r)` coordinate bound at the 128-bit shape. -/
theorem convMax_128 : Conv.convMax macChunkBits Conv.gf2_128Taps = 504 :=
  Conv.convMax_gf2_128

/-- Width of a raw Falcon HashToPoint candidate, before rejection sampling. -/
abbrev falconSampleBits : ℕ := 16

/-- The Goldilocks prime `2^64 − 2^32 + 1`, the characteristic of the emulated arms' field
`F_{p²}` (`GordieHowe/Foundations/Fields/Goldilocks.lean`). -/
def pGold : ℕ := 2 ^ 64 - 2 ^ 32 + 1

theorem pGold_eq : pGold = 18446744069414584321 := by
  unfold pGold; norm_num

/-! ## ML-DSA -/

/-- ML-DSA scheme constants (FIPS 204). -/
structure MLDSA44.Params where
  q : ℕ
  N : ℕ
  K : ℕ
  L : ℕ
  d : ℕ
  γ₁ : ℕ
  γ₂ : ℕ
  β : ℕ
  τ : ℕ
  ω : ℕ
  q_hi : ℕ
  r1_bits : ℕ
  q_prime : Nat.Prime q
  q_hi_def : q_hi = (q - 1) / (2 * γ₂)
  q_decomp : 2 * γ₂ * q_hi = q - 1
  τ_pos : 0 < τ
  τ_le : τ ≤ 128

namespace MLDSA44.Params

/-- The infinity-norm bound `γ₁ - β`. -/
def normBound (P : Params) : ℕ := P.γ₁ - P.β

/-- Chunks of shared witness: `w1` bits plus the ternary `c`, in `w`-bit chunks. -/
def chunks (P : Params) (w : ℕ) : ℕ := (P.K * P.N * P.r1_bits + 2 * P.N) / w

/-- A MAC width whose `P.chunks w` chunks of `w` bits cover the crossing (the `K·N·r1_bits`
bits of `w1_tilde`, then the `2·N` challenge bits) exactly, so that equal chunks give equal
`w1_tilde` and challenge bits. The analogue of `Falcon512.Params.macChunkBits_dvd`; discharged by `decide` at
each configuration. -/
class MACWidth (P : Params) (w : ℕ) : Prop where
  cover : w * P.chunks w = P.K * P.N * P.r1_bits + 2 * P.N

end MLDSA44.Params

def mldsa44 : MLDSA44.Params where
  q := 8380417
  N := 256
  K := 4
  L := 4
  d := 13
  γ₁ := 131072
  γ₂ := 95232
  β := 78
  τ := 39
  ω := 80
  q_hi := 44
  r1_bits := 6
  q_prime := by norm_num
  q_hi_def := by norm_num
  q_decomp := by norm_num
  τ_pos := by norm_num
  τ_le := by norm_num

/-- ML-DSA's modulus `q = 8380417` is prime (`mldsa44.q_prime`), the one instance the ML-DSA fields
use. -/
instance instFactPrimeMlDsaQ : Fact (Nat.Prime 8380417) := ⟨mldsa44.q_prime⟩

example : mldsa44.chunks 128 = 52 := by decide
example : mldsa44.chunks 256 = 26 := by decide
example : mldsa44.normBound = 130994 := by decide

/-- An ML-DSA algebra arm: the field characteristic, the lookup radix and table size `B₁ = T`, the
MAC quotient radix `B₂ = S_dyn`, and the integer bounds this arm's gadgets rely on, at the MAC shape
`(w, taps)`. -/
structure MLDSA44.Arm (P : Params) (w : ℕ) (taps : Finset ℕ) where
  /-- characteristic of the algebra field: `q` natively, `p` emulated -/
  char : ℕ
  B₁ : ℕ
  B₂ : ℕ
  /-- two-sided range reconstruction: `2(B₁² - 1) < char` -/
  twoSided : 2 * (B₁ ^ 2 - 1) < char
  /-- single-group MAC accumulator: `chunks · convMax + 1 < char` -/
  macAcc : P.chunks w * Conv.convMax w taps + 1 < char
  /-- MAC tail reconstruction `M̃ + 2ℓ + 2B₂u` with `ℓ, u < B₁`: below `char` -/
  macTail : 1 + 2 * (B₁ - 1) + 2 * B₂ * (B₁ - 1) < char
  /-- honest MAC quotient fits two base-`B₂` digits: completeness -/
  honestQuot : (P.chunks w * Conv.convMax w taps + 1) / 2 < B₂ ^ 2
  /-- hint-weight lookup: `ω < B₁` and `char > K·N + B₁` -/
  hintWeight₁ : P.ω < B₁
  hintWeight₂ : P.K * P.N + B₁ < char

/-- An ML-DSA native arm: an `Arm` whose algebra field has characteristic `q`, with the facts
the native circuit reads besides `Arm`'s: the dynamic histogram prefix fits the table, the
norm's two limbs cover `[0, 2·(γ₁ − β) − 1)`, and the lookup requests (UseHint and norm `4` per
coefficient of `K` resp. `L` polynomials, the hint-weight complement, and `2` per MAC bit) number
fewer than the characteristic, so a single lookup group is sound (`logup_range_check`'s caller
obligation). The emulated arms stay on `Arm`. -/
structure MLDSA44.NativeArm (P : Params) (w : ℕ) (taps : Finset ℕ)
    extends Arm P w taps where
  char_eq : char = P.q
  dyn_le : B₂ ≤ B₁
  normRadix : 2 * P.normBound - 1 ≤ B₁ ^ 2
  needles_lt : P.K * P.N * 4 + 1 + P.L * P.N * 4 + 2 * w < char

/-- The ML-DSA-44 native arm at the 128-bit MAC shape. -/
def mldsa44NativeROM : MLDSA44.NativeArm mldsa44 macChunkBits Conv.gf2_128Taps where
  char := 8380417
  B₁ := 512
  B₂ := 115
  twoSided := by decide
  macAcc := by rw [convMax_128]; decide
  macTail := by decide
  honestQuot := by rw [convMax_128]; decide
  hintWeight₁ := by decide
  hintWeight₂ := by decide
  char_eq := rfl
  dyn_le := by decide
  normRadix := by decide
  needles_lt := by decide

/-- The ML-DSA-44 native arm at the 256-bit MAC shape: 26 chunks and `B₂ = 116` (`kMLDSANative` of
the `MLDSA44.Native.QROMParams` profile, `lib/params/param_sets.h`; `(26·1017 + 1)/2 < 116²`). -/
def mldsa44NativeQROM : MLDSA44.NativeArm mldsa44 256 Conv.gf2_256Taps where
  char := 8380417
  B₁ := 512
  B₂ := 116
  twoSided := by decide
  macAcc := by rw [Conv.convMax_gf2_256]; decide
  macTail := by decide
  honestQuot := by rw [Conv.convMax_gf2_256]; decide
  hintWeight₁ := by decide
  hintWeight₂ := by decide
  char_eq := rfl
  dyn_le := by decide
  normRadix := by decide
  needles_lt := by decide

example : mldsa44.chunks 256 * Conv.convMax 256 Conv.gf2_256Taps + 1 = 26443 := by
  rw [Conv.convMax_gf2_256]; decide
example : 1 + 2 * (512 - 1) + 2 * 116 * (512 - 1) = 119575 := by decide
example : (mldsa44.chunks 256 * Conv.convMax 256 Conv.gf2_256Taps + 1) / 2 = 13221 ∧
    116 ^ 2 = 13456 := by rw [Conv.convMax_gf2_256]; decide

/-- Table rows for ML-DSA native, as the document prints them. -/
example : 2 * (mldsa44NativeROM.B₁ ^ 2 - 1) = 524286 := by decide
example : mldsa44.chunks macChunkBits * Conv.convMax macChunkBits Conv.gf2_128Taps + 1 = 26209 := by rw [convMax_128]; decide
example : 1 + 2 * (512 - 1) + 2 * 115 * (512 - 1) = 118553 := by decide
example : (mldsa44.chunks macChunkBits * Conv.convMax macChunkBits Conv.gf2_128Taps + 1) / 2 = 13104 ∧ 115 ^ 2 = 13225 := by rw [convMax_128]; decide

example : 1 + 2 * (4096 - 1) + 2 * 115 * (4096 - 1) = 950041 := by decide

example : 1 + 2 * (4096 - 1) + 2 * 116 * (4096 - 1) = 958231 := by decide

/-! ## Falcon -/

/-! The selected Falcon codec uses one sign bit, seven low magnitude bits,
and a unary high part with a terminating bit. These are format constants,
not tuning parameters of an arithmetic arm. -/
namespace Falcon512.Codec

def lowBits : ℕ := 7
def magnitudeBits : ℕ := 11
def lowRadix : ℕ := 2 ^ lowBits
def magnitudeBound : ℕ := 2 ^ magnitudeBits
def baseCoefficientBits : ℕ := 1 + lowBits + 1

theorem lowRadix_eq : lowRadix = 128 := by decide
theorem magnitudeBound_eq : magnitudeBound = 2048 := by decide
theorem baseCoefficientBits_eq : baseCoefficientBits = 9 := by decide

end Falcon512.Codec

/-- Falcon scheme constants. -/
structure Falcon512.Params where
  q : ℕ
  n : ℕ
  /-- squared-norm acceptance bound -/
  βSq : ℕ
  /-- hash samples drawn by the fixed-length sampler -/
  S : ℕ
  /-- salt (nonce) length in bytes -/
  saltBytes : ℕ
  /-- Compressed signature polynomial payload, excluding header and nonce. -/
  sigPayloadBytes : ℕ
  /-- Each coefficient needs a sign, seven low bits, and a unary terminator. -/
  encodingFits : Codec.baseCoefficientBits * n ≤ 8 * sigPayloadBytes
  q_prime : Nat.Prime q
  n_pos : 0 < n
  /-- every codec magnitude is a residue: `2047 < q` -/
  magnitudeBound_le_q : Codec.magnitudeBound ≤ q
  /-- the norm bound is below `q²`, so the norm gadget's centering is unique -/
  βSq_lt : βSq < q ^ 2
  n_le_S : n ≤ S
  /-- raw samples are 16 bits and the rejection bound is `5q < 2^16` -/
  bound_lt : 5 * q < 2 ^ 16
  /-- the `n` 16-bit samples split into 128-bit chunks, the MAC width at the ROM parameters (the
  256-bit width has its own `MACWidth` instance) -/
  macChunkBits_dvd : macChunkBits ∣ falconSampleBits * n

namespace Falcon512.Params

/-- `HashToPoint` rejection bound. -/
def bound (P : Params) : ℕ := 5 * P.q

/-- Total unary zero bits available after the fixed per-coefficient overhead. -/
def encodingHighBudget (P : Params) : ℕ := 8 * P.sigPayloadBytes - Codec.baseCoefficientBits * P.n

end Falcon512.Params

def falcon512 : Falcon512.Params where
  q := 12289
  n := 512
  βSq := 34034726
  S := 512 + 127
  saltBytes := 40
  sigPayloadBytes := 625
  encodingFits := by norm_num [Falcon512.Codec.baseCoefficientBits, Falcon512.Codec.lowBits]
  q_prime := by norm_num
  n_pos := by norm_num
  magnitudeBound_le_q := by decide
  βSq_lt := by norm_num
  n_le_S := by norm_num
  bound_lt := by norm_num
  macChunkBits_dvd := by norm_num

example : falcon512.bound = 61445 := by decide
example : falcon512.encodingHighBudget = 392 := by decide

end GordieHowe
