-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Range
public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Applications.MLDSA44.Gadgets.InfinityNorm
public import GordieHowe.Applications.MLDSA44.Spec.Rounding
public import GordieHowe.Foundations.Algebra.IntLift

@[expose] public section

/-!
# The ML-DSA UseHint relation

Per coefficient, the UseHint output `y` (the shared `w1` bits), the hint `h`, the committed
`nonpositive` bit `s` and the offset and slack limbs force `y = UseHint(h, w)`
(`GordieHowe.MLDSA44.useHintCoeff_of_relation`, `GordieHowe/Applications/MLDSA44/Spec/Rounding.lean`).

The relation is the one `use_hint` asserts in the C++
(`lib/gordiehowe/examples/mldsa/mldsa_gadgets.h`). This file states it in two arms:

* the relation (`relationResult`): `down = h·s`, `up = h − down`,
  `raw_high = y − up + down + M·(up·[y=0] − down·[y=M−1])`,
  `endpoint = (s − down)·[y=0] + down·[y=M−1]`, `lower = 1 − γ₂·s − endpoint`, the assertion
  `offset + slack = (γ₂ − 1) + endpoint`, and the result `2γ₂·raw_high + (lower + offset)`.
* the output reading: `y = Σ_b 2^b·bits[b]`, `[y=0]` and `[y=M−1]` by equality tests on the bits.
  The Lean uses `Bits.eqConst` (the product of the bits or their complements); the equality tree
  of `Logic::eq_reduce` (`lib/circuits/logic/logic.h`) has the same value on Boolean bits
  (`Bits.eqConst_eq`).
* the native arm (`native`): `assert1(leq(bits, M − 1))` (the Lean comparator is `Bits.leConst`,
  equal on Boolean bits by `Bits.leConst_eq`), `assert_is_bit(h)` as `h − h·h = 0`,
  `offset = Σ_l lo[l]·512^l`, `slack = Σ_l hi[l]·512^l`, needles `lo[0], hi[0], lo[1], hi[1]`, and
  `assert_eq(w, result)`. The sign `s` is a `BitW` input and the bits are `w1_tilde` bytes
  (`vinput<8>`); both are asserted Boolean where they are read in (`Logic::input`,
  `lib/circuits/logic/logic.h`), so `relation_sound` takes the hint and sign as `Bool` values and
  the bits' Booleanity as a hypothesis (`hbits`), all supplied by `Logic::input`.
* the emulated arm (`emulated`, base `B1 = 4096`, two limbs): `b·(b − 1) = 0` for `h`, `s`,
  `corner` and each output bit, the same needles, `assert1(vleq(bits, M − 1))`, and
  `assert_eq(result + q·corner, w)`.

A loop over the `K·N` coefficients applies these per coefficient (`native`, `emulated`); the hint
sum it accumulates is `HintWeight`'s input. The Lean takes each coefficient's output bits per
coefficient.
-/

namespace GordieHowe.MLDSA44.UseHint

open _root_.MLDSA _root_.MLDSA.Concrete GordieHowe.MLDSA44

variable {K : Type*} [Field K] [DecidableEq K]

/-- `M = (q − 1)/(2γ₂)`, the number of high parts (`Params::M`). -/
def hiCount (γ₂ : ℕ) : ℕ := (modulus - 1) / (2 * γ₂)

/-- The three values the relation reads about its output. -/
structure Output (K : Type*) where
  value : K
  atZero : K
  atLast : K

/-- `use_hint_output_from_bits`: the value and the two equality indicators. -/
def outputFromBits (M : ℕ) {r : ℕ} (bits : BitWires K r) : Output K :=
  ⟨∑ b : Fin r, (2 : K) ^ (b : ℕ) * bits b, Bits.eqConst bits 0, Bits.eqConst bits (M - 1)⟩

/-- `endpoint = (s − h·s)·[y=0] + h·s·[y=M−1]`. -/
def endpoint (h s : K) (y : Output K) : K := (s - h * s) * y.atZero + h * s * y.atLast

/-- `raw_high = y − up + down + M·(up·[y=0] − down·[y=M−1])`, `down = h·s`, `up = h − down`. -/
def rawHigh (M : ℕ) (h s : K) (y : Output K) : K :=
  y.value - (h - h * s) + h * s + (M : K) * ((h - h * s) * y.atZero - h * s * y.atLast)

/-- `lower = 1 − γ₂·s − endpoint`. -/
def lower (γ₂ : ℕ) (h s : K) (y : Output K) : K := 1 - (γ₂ : K) * s - endpoint h s y

/-- The relation's interval assertion `offset + slack = (γ₂ − 1) + endpoint`. -/
def IntervalEq (γ₂ : ℕ) (h s offset slack : K) (y : Output K) : Prop :=
  offset + slack = ((γ₂ - 1 : ℕ) : K) + endpoint h s y

/-- The relation's result `2γ₂·raw_high + (lower + offset)`. -/
def relationResult (γ₂ M : ℕ) (h s offset : K) (y : Output K) : K :=
  ((2 * γ₂ : ℕ) : K) * rawHigh M h s y + (lower γ₂ h s y + offset)

/-- **The native gadget** (`assert_use_hint_single`, bit form). -/
def native (γ₂ B k : ℕ) {r : ℕ} (h w s : K) (lo hi : Fin k → K) (bits : BitWires K r) :
    Check K :=
  let M := hiCount γ₂
  let y := outputFromBits M bits
  let offset := Range.reconstruct B (List.ofFn lo)
  let slack := Range.reconstruct B (List.ofFn hi)
  (Check.assert (decide (Bits.leConst bits (M - 1) = 1) && decide (h - h * h = 0) &&
      decide (offset + slack = ((γ₂ - 1 : ℕ) : K) + endpoint h s y) &&
      decide (w = relationResult γ₂ M h s offset y))).and
    ⟨true, List.interleavePairs (List.ofFn lo) (List.ofFn hi)⟩

/-- **The emulated gadget** (the loop body of `ml_dsa_fp::assert_use_hint`). -/
def emulated (γ₂ B k : ℕ) {r : ℕ} (h w s corner : K) (lo hi : Fin k → K)
    (bits : BitWires K r) : Check K :=
  let M := hiCount γ₂
  let y := outputFromBits M bits
  let offset := Range.reconstruct B (List.ofFn lo)
  let slack := Range.reconstruct B (List.ofFn hi)
  (Check.assert (decide (h * (h - 1) = 0) && decide (s * (s - 1) = 0) &&
      decide (corner * (corner - 1) = 0) &&
      (List.finRange r).all (fun b => decide (bits b * (bits b - 1) = 0)) &&
      decide (Bits.leConst bits (M - 1) = 1) &&
      decide (offset + slack = ((γ₂ - 1 : ℕ) : K) + endpoint h s y) &&
      decide (relationResult γ₂ M h s offset y + (modulus : K) * corner = w))).and
    ⟨true, List.interleavePairs (List.ofFn lo) (List.ofFn hi)⟩

theorem native_ok_iff {γ₂ B k r : ℕ} {h w s : K} {lo hi : Fin k → K} {bits : BitWires K r} :
    (native γ₂ B k h w s lo hi bits).ok = true ↔
      Bits.leConst bits (hiCount γ₂ - 1) = 1 ∧ h - h * h = 0 ∧
        IntervalEq γ₂ h s (Range.reconstruct B (List.ofFn lo))
          (Range.reconstruct B (List.ofFn hi)) (outputFromBits (hiCount γ₂) bits) ∧
        w = relationResult γ₂ (hiCount γ₂) h s (Range.reconstruct B (List.ofFn lo))
          (outputFromBits (hiCount γ₂) bits) := by
  simp [native, IntervalEq, and_assoc]

theorem emulated_ok_iff {γ₂ B k r : ℕ} {h w s corner : K} {lo hi : Fin k → K}
    {bits : BitWires K r} :
    (emulated γ₂ B k h w s corner lo hi bits).ok = true ↔
      h * (h - 1) = 0 ∧ s * (s - 1) = 0 ∧ corner * (corner - 1) = 0 ∧
        (∀ b, bits b * (bits b - 1) = 0) ∧ Bits.leConst bits (hiCount γ₂ - 1) = 1 ∧
        IntervalEq γ₂ h s (Range.reconstruct B (List.ofFn lo))
          (Range.reconstruct B (List.ofFn hi)) (outputFromBits (hiCount γ₂) bits) ∧
        relationResult γ₂ (hiCount γ₂) h s (Range.reconstruct B (List.ofFn lo))
          (outputFromBits (hiCount γ₂) bits) + (modulus : K) * corner = w := by
  simp [emulated, IntervalEq, and_assoc]

@[simp] theorem native_needles (γ₂ B k : ℕ) {r : ℕ} (h w s : K) (lo hi : Fin k → K)
    (bits : BitWires K r) :
    (native γ₂ B k h w s lo hi bits).needles =
      List.interleavePairs (List.ofFn lo) (List.ofFn hi) := by
  simp [native]

@[simp] theorem emulated_needles (γ₂ B k : ℕ) {r : ℕ} (h w s corner : K) (lo hi : Fin k → K)
    (bits : BitWires K r) :
    (emulated γ₂ B k h w s corner lo hi bits).needles =
      List.interleavePairs (List.ofFn lo) (List.ofFn hi) := by
  simp [emulated]

/-! ### Semantics of the derived wires on Boolean inputs -/

omit [DecidableEq K] in
theorem bit_of_mul_sub {x : K} (h : x * (x - 1) = 0) : x = 0 ∨ x = 1 := by
  rcases mul_eq_zero.mp h with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

omit [DecidableEq K] in
theorem exists_bool_of_bit {x : K} (h : x = 0 ∨ x = 1) : ∃ b : Bool, x = (b.toNat : K) := by
  rcases h with rfl | rfl
  · exact ⟨false, by simp⟩
  · exact ⟨true, by simp⟩

theorem decide_toNat_eq_one (b : Bool) : decide (((b.toNat : ℕ) : K) = 1) = b := by
  cases b <;> simp

/-- On Boolean bits encoding `y < 2^r` with `M − 1 < 2^r`, the output triple is `y`, `[y = 0]`,
`[y = M − 1]`. -/
theorem outputFromBits_eq {M r : ℕ} {bits : BitWires K r} (hbits : Bits.AllBool bits)
    (hM : M - 1 < 2 ^ r) :
    outputFromBits M bits =
      ⟨(Bits.natOfBits bits : K), ((decide (Bits.natOfBits bits = 0)).toNat : K),
        ((decide (Bits.natOfBits bits = M - 1)).toNat : K)⟩ := by
  have h0 : (0 : ℕ) % 2 ^ r = 0 := Nat.zero_mod _
  have hL : (M - 1) % 2 ^ r = M - 1 := Nat.mod_eq_of_lt hM
  have hind : ∀ P : Prop, [Decidable P] → (if P then (1 : K) else 0) = ((decide P).toNat : K) := by
    intro P _
    by_cases hP : P <;> simp [hP]
  simp only [outputFromBits, Bits.eqConst_eq hbits, h0, hL, hind, Output.mk.injEq, and_true]
  simp only [Bits.natOfBits, Nat.cast_sum, Nat.cast_ite, Nat.cast_pow, Nat.cast_ofNat,
    Nat.cast_zero]
  refine Finset.sum_congr rfl fun b _ => ?_
  rcases hbits b with h | h <;> simp [h]

omit [DecidableEq K] in
/-- `endpoint` on Boolean inputs is the spec's `useHintEndpoint`. -/
theorem endpoint_cast (M : ℕ) (hb sb : Bool) (y : ℕ) :
    endpoint ((hb.toNat : ℕ) : K) (sb.toNat : ℕ)
        ⟨(y : K), ((decide (y = 0)).toNat : K), ((decide (y = M - 1)).toNat : K)⟩ =
      (useHintEndpoint M hb sb y : K) := by
  unfold endpoint useHintEndpoint
  generalize decide (y = 0) = z0
  generalize decide (y = M - 1) = z1
  cases hb <;> cases sb <;> cases z0 <;> cases z1 <;> simp

omit [DecidableEq K] in
/-- `raw_high` on Boolean inputs is the spec's `useHintRawHigh`. -/
theorem rawHigh_cast (M : ℕ) (hb sb : Bool) (y : ℕ) :
    rawHigh M ((hb.toNat : ℕ) : K) (sb.toNat : ℕ)
        ⟨(y : K), ((decide (y = 0)).toNat : K), ((decide (y = M - 1)).toNat : K)⟩ =
      ((useHintRawHigh M hb sb y : ℤ) : K) := by
  unfold rawHigh useHintRawHigh
  generalize decide (y = 0) = z0
  generalize decide (y = M - 1) = z1
  cases hb <;> cases sb <;> cases z0 <;> cases z1 <;> simp

omit [DecidableEq K] in
/-- `lower + offset` on Boolean inputs is the spec's `useHintLow`. -/
theorem lower_add_cast (γ₂ M : ℕ) (hb sb : Bool) (y offset : ℕ) :
    lower γ₂ ((hb.toNat : ℕ) : K) (sb.toNat : ℕ)
        ⟨(y : K), ((decide (y = 0)).toNat : K), ((decide (y = M - 1)).toNat : K)⟩ + (offset : K) =
      ((useHintLow γ₂ M hb sb y offset : ℤ) : K) := by
  unfold lower useHintLow
  rw [endpoint_cast]
  push_cast
  ring

omit [DecidableEq K] in
/-- The relation's result on Boolean inputs is the spec's integer `2γ₂·raw_high + low`. -/
theorem relationResult_cast (γ₂ M : ℕ) (hb sb : Bool) (y offset : ℕ) :
    relationResult γ₂ M ((hb.toNat : ℕ) : K) (sb.toNat : ℕ) (offset : K)
        ⟨(y : K), ((decide (y = 0)).toNat : K), ((decide (y = M - 1)).toNat : K)⟩ =
      ((2 * γ₂ * useHintRawHigh M hb sb y + useHintLow γ₂ M hb sb y offset : ℤ) : K) := by
  unfold relationResult
  rw [rawHigh_cast, lower_add_cast]
  push_cast
  ring

/-! ### The shared relation -/

/-- What the relation establishes on Boolean inputs with in-table limbs: the output bound, and
naturals `offset`, `slack` satisfying the spec's interval equation with the relation's result
equal to the spec's integer. -/
structure RelationFacts (γ₂ : ℕ) (hb sb : Bool) (y : ℕ) (res : K) : Prop where
  output_lt : y < hiCount γ₂
  exists_offset : ∃ offset slack : ℕ,
    offset + slack = γ₂ - 1 + useHintEndpoint (hiCount γ₂) hb sb y ∧
      res = ((2 * γ₂ * useHintRawHigh (hiCount γ₂) hb sb y +
        useHintLow γ₂ (hiCount γ₂) hb sb y offset : ℤ) : K)

/-- **The relation's soundness core.** `hchar`, `hγp` and `hr` are parameter conditions; `hbits` is
Booleanity of the output bits; `hle` and `hint` are the gadget's comparator and interval
assertions; `hlo`, `hhi` the limb lookups. -/
theorem relation_sound {p : ℕ} [CharP K p] {γ₂ B k r : ℕ} (hγ : 0 < γ₂)
    (hchar : 2 * (B ^ k - 1) < p) (hγp : γ₂ < p) (hr : hiCount γ₂ < 2 ^ r) (hM : 0 < hiCount γ₂) (hb sb : Bool)
    {lo hi : Fin k → K} {bits : BitWires K r} (hbits : Bits.AllBool bits)
    (hle : Bits.leConst bits (hiCount γ₂ - 1) = 1)
    (hlo : ∀ l, Range.IsNatBelow B (lo l)) (hhi : ∀ l, Range.IsNatBelow B (hi l))
    (hint : IntervalEq γ₂ ((hb.toNat : ℕ) : K) (sb.toNat : ℕ)
      (Range.reconstruct B (List.ofFn lo)) (Range.reconstruct B (List.ofFn hi))
      (outputFromBits (hiCount γ₂) bits)) :
    RelationFacts γ₂ hb sb (Bits.natOfBits bits)
      (relationResult γ₂ (hiCount γ₂) ((hb.toNat : ℕ) : K) (sb.toNat : ℕ)
        (Range.reconstruct B (List.ofFn lo)) (outputFromBits (hiCount γ₂) bits)) := by
  set M := hiCount γ₂
  set y := Bits.natOfBits bits
  have hy : y < M := by
    rw [Bits.leConst_eq hbits _] at hle
    by_contra hge
    rw [if_neg (by omega)] at hle
    exact zero_ne_one hle
  have hout := outputFromBits_eq (M := M) hbits (by omega)
  obtain ⟨a, ha, hacast⟩ := Range.reconstruct_isNatBelow (List.length_ofFn (f := lo))
    (fun v hv => by obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hv; exact hlo l)
  obtain ⟨b, hbB, hbcast⟩ := Range.reconstruct_isNatBelow (List.length_ofFn (f := hi))
    (fun v hv => by obtain ⟨l, rfl⟩ := List.mem_ofFn.mp hv; exact hhi l)
  rw [hout, ← hacast, ← hbcast] at hint
  rw [hout, ← hacast]
  unfold IntervalEq at hint
  rw [endpoint_cast] at hint
  have hE := useHintEndpoint_le_one M hb sb y
  have hab : a + b < p := by omega
  have hc : γ₂ - 1 + useHintEndpoint M hb sb y < p := by omega
  have hsum : a + b = γ₂ - 1 + useHintEndpoint M hb sb y :=
    IntLift.add_eq_of_natCast (K := K) hab hc
      (by rw [hint]; push_cast [Nat.cast_add]; ring)
  exact ⟨hy, a, b, hsum, relationResult_cast γ₂ M hb sb y a⟩

/-! ### Native soundness and completeness -/

/-- The native conclusion: the hint is a bit, the output is below `M`, `w` is the image of an
integer, and every integer representative of `w` has UseHint `y` modulo `q`. -/
structure NativeHolds (γ₂ : ℕ) (h w : K) (y : ℕ) : Prop where
  hint_bool : h = 0 ∨ h = 1
  output_lt : y < hiCount γ₂
  exists_int : ∃ n : ℤ, (n : K) = w
  useHint : ∀ n : ℤ, (n : K) = w → useHintCoeff (decide (h = 1)) (n : Coeff) γ₂ = y

/-! ### Emulated soundness -/

/-- The emulated conclusion: the hint is a bit, the output is below `M`, and every natural
representative of `w` below `W` has UseHint `y` modulo `q`. -/
structure EmulatedHolds (γ₂ W : ℕ) (h w : K) (y : ℕ) : Prop where
  hint_bool : h = 0 ∨ h = 1
  output_lt : y < hiCount γ₂
  useHint : ∀ n < W, (n : K) = w → useHintCoeff (decide (h = 1)) (n : Coeff) γ₂ = y

/-- **Emulated soundness.** Over a field of characteristic `p`: if the gadget accepts and its
limbs lie in `[0, B)`, every natural `n < W` that `w` is the cast of has UseHint `y`. `hγ`,
`hdvd`, `hchar`, `hr` and `hWp` are parameter conditions (`W` is the range of the caller's `w`
representative, `W + 2q ≤ p`). -/
theorem emulated_sound {p : ℕ} [CharP K p] {γ₂ B k r W : ℕ} (hγ : 0 < γ₂)
    (hdvd : 2 * γ₂ ∣ modulus - 1) (hchar : 2 * (B ^ k - 1) < p) (hr : hiCount γ₂ < 2 ^ r)
    (hWp : W + 2 * modulus ≤ p) {h w s corner : K} {lo hi : Fin k → K} {bits : BitWires K r}
    (hok : (emulated γ₂ B k h w s corner lo hi bits).ok = true)
    (hn : ∀ v ∈ (emulated γ₂ B k h w s corner lo hi bits).needles, Range.IsNatBelow B v) :
    EmulatedHolds γ₂ W h w (Bits.natOfBits bits) := by
  obtain ⟨hbit, hsbit, hcbit, hbitsb, hle, hint, hres⟩ := emulated_ok_iff.mp hok
  have hh := bit_of_mul_sub hbit
  have hbits : Bits.AllBool bits := fun b => bit_of_mul_sub (hbitsb b)
  have hM : 0 < hiCount γ₂ := Nat.zero_lt_of_lt (useHintCoeff_lt hγ hdvd false 0)
  have hγq : γ₂ < modulus := by
    have := Nat.le_of_dvd (by decide) hdvd
    omega
  have hmem : ∀ v, v ∈ List.interleavePairs (List.ofFn lo) (List.ofFn hi) → Range.IsNatBelow B v :=
    fun v hv => hn v (by simpa using hv)
  have hlo : ∀ l, Range.IsNatBelow B (lo l) := fun l => hmem _
    ((List.interleavePairs_perm_append _ _).mem_iff.mpr
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨l, rfl⟩)))
  have hhi : ∀ l, Range.IsNatBelow B (hi l) := fun l => hmem _
    ((List.interleavePairs_perm_append _ _).mem_iff.mpr
      (List.mem_append_right _ (List.mem_ofFn.mpr ⟨l, rfl⟩)))
  obtain ⟨hb, rfl⟩ := exists_bool_of_bit hh
  obtain ⟨sb, rfl⟩ := exists_bool_of_bit (bit_of_mul_sub hsbit)
  obtain ⟨cb, rfl⟩ := exists_bool_of_bit (bit_of_mul_sub hcbit)
  obtain ⟨hy, off, sl, hsum, hreseq⟩ :=
    relation_sound hγ hchar (by omega) hr hM hb sb hbits hle hlo hhi hint
  rw [hreseq] at hres
  refine ⟨Or.imp id id hh, hy, fun n hnW hn' => ?_⟩
  rw [decide_toNat_eq_one]
  set R := 2 * γ₂ * useHintRawHigh (hiCount γ₂) hb sb (Bits.natOfBits bits) +
    useHintLow γ₂ (hiCount γ₂) hb sb (Bits.natOfBits bits) off with hR
  obtain ⟨hR0, hR1⟩ := useHintRelation_bounds hγ hdvd hy hsum
  have hR0' : -(γ₂ : ℤ) ≤ R := hR0
  have hR1' : R < modulus := hR1
  have hcq : (0 : ℤ) ≤ (cb.toNat : ℤ) * modulus ∧ (cb.toNat : ℤ) * modulus ≤ modulus := by
    cases cb <;> simp
  have hfield : ((n : ℤ) : K) = ((R + (cb.toNat : ℤ) * modulus : ℤ) : K) := by
    rw [Int.cast_natCast, hn', ← hres]
    push_cast
    ring
  have hlt : ((n : ℤ) - (R + (cb.toNat : ℤ) * modulus)).natAbs < p := by
    have : (((n : ℤ) - (R + (cb.toNat : ℤ) * modulus)).natAbs : ℤ) < p := by
      rw [Int.natCast_natAbs, abs_lt]
      have hWpZ : (W : ℤ) + 2 * modulus ≤ p := by exact_mod_cast hWp
      have hnWZ : (n : ℤ) < W := by exact_mod_cast hnW
      have hγqZ : (γ₂ : ℤ) < modulus := by exact_mod_cast hγq
      have hn0 : (0 : ℤ) ≤ n := by positivity
      constructor <;> linarith [hcq.1, hcq.2]
    exact_mod_cast this
  have heq := IntLift.intCast_inj_of_natAbs_sub_lt (K := K) hlt hfield
  have := useHintCoeff_of_relation_int (wInt := (n : ℤ)) (corner := (cb.toNat : ℤ)) hγ hdvd hy hsum
    (by rw [heq]; rfl)
  rwa [Int.cast_natCast] at this

/-! ### Completeness -/

/-- One coefficient's honest advice: the sign, the offset and slack limbs, the output bits. -/
structure Advice (K : Type*) (k r : ℕ) where
  s : K
  lo : Fin k → K
  hi : Fin k → K
  bits : BitWires K r

/-- The honest advice for hint `hb` and coefficient `wc`: `useHintSign`, the base-`B` limbs of
`useHintOffset` and of the complementary slack, and the bits of `useHintCoeff hb wc γ₂`. -/
-- spec-side
def honest (γ₂ B k r : ℕ) (hb : Bool) (wc : Coeff) : Advice K k r :=
  let y := useHintCoeff hb wc γ₂
  let sb := useHintSign γ₂ wc
  let off := useHintOffset γ₂ hb wc
  let sl := γ₂ - 1 + useHintEndpoint (hiCount γ₂) hb sb y - off
  ⟨(sb.toNat : K), fun l => (off / B ^ (l : ℕ) % B : ℕ), fun l => (sl / B ^ (l : ℕ) % B : ℕ),
    fun i => Bits.constBit y i⟩

/-- The emulated arm's honest wrap bit: `1` exactly when the relation's integer result is the
canonical representative minus `q`. -/
-- spec-side
def honestCorner (γ₂ : ℕ) (wc : Coeff) : Bool :=
  !decide ((wc.val : ℤ) = 2 * γ₂ * (decomposeCoeff wc γ₂).1 + (decomposeCoeff wc γ₂).2)

/-- The facts about the honest advice shared by both arms. -/
theorem honest_spec {γ₂ B k r : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (hr : hiCount γ₂ < 2 ^ r) (hγB : γ₂ < B ^ k) (hb : Bool) (wc : Coeff) :
    Bits.AllBool (honest (K := K) γ₂ B k r hb wc).bits ∧
      Bits.natOfBits (honest (K := K) γ₂ B k r hb wc).bits = useHintCoeff hb wc γ₂ ∧
      Bits.leConst (honest (K := K) γ₂ B k r hb wc).bits (hiCount γ₂ - 1) = 1 ∧
      IntervalEq γ₂ ((hb.toNat : ℕ) : K) (honest (K := K) γ₂ B k r hb wc).s
        (Range.reconstruct B (List.ofFn (honest (K := K) γ₂ B k r hb wc).lo))
        (Range.reconstruct B (List.ofFn (honest (K := K) γ₂ B k r hb wc).hi))
        (outputFromBits (hiCount γ₂) (honest (K := K) γ₂ B k r hb wc).bits) ∧
      relationResult γ₂ (hiCount γ₂) ((hb.toNat : ℕ) : K) (honest (K := K) γ₂ B k r hb wc).s
          (Range.reconstruct B (List.ofFn (honest (K := K) γ₂ B k r hb wc).lo))
          (outputFromBits (hiCount γ₂) (honest (K := K) γ₂ B k r hb wc).bits) =
        ((2 * γ₂ * (decomposeCoeff wc γ₂).1 + (decomposeCoeff wc γ₂).2 : ℤ) : K) ∧
      ∀ v ∈ List.interleavePairs (List.ofFn (honest (K := K) γ₂ B k r hb wc).lo)
        (List.ofFn (honest (K := K) γ₂ B k r hb wc).hi), Range.IsNatBelow B v := by
  dsimp only [honest]
  set M := hiCount γ₂
  set y := useHintCoeff hb wc γ₂
  set sb := useHintSign γ₂ wc
  set off := useHintOffset γ₂ hb wc
  set E := useHintEndpoint M hb sb y
  have hy : y < M := useHintCoeff_lt hγ hdvd hb wc
  obtain ⟨hoff0, hrel0⟩ := useHintRelation_honest hγ hdvd hb wc
  have hoff : off ≤ γ₂ - 1 + E := hoff0
  have hrel : 2 * (γ₂ : ℤ) * useHintRawHigh M hb sb y + useHintLow γ₂ M hb sb y off =
      2 * γ₂ * (decomposeCoeff wc γ₂).1 + (decomposeCoeff wc γ₂).2 := hrel0
  have hE := useHintEndpoint_le_one M hb sb y
  have hallb : Bits.AllBool (fun i : Fin r => (Bits.constBit y i : K)) :=
    fun i => Bits.constBit_bool y i
  have hnat : Bits.natOfBits (fun i : Fin r => (Bits.constBit y i : K)) = y := by
    rw [Bits.natOfBits_constBit, Nat.mod_eq_of_lt (by omega)]
  have hout : outputFromBits M (fun i : Fin r => (Bits.constBit y i : K)) =
      ⟨(y : K), ((decide (y = 0)).toNat : K), ((decide (y = M - 1)).toNat : K)⟩ := by
    rw [outputFromBits_eq hallb (by omega), hnat]
  obtain ⟨hlo, hlo'⟩ := InfinityNorm.radix_spec (K := K) (B := B) (k := k) (a := off) (by omega)
  obtain ⟨hhi, hhi'⟩ := InfinityNorm.radix_spec (K := K) (B := B) (k := k)
    (a := γ₂ - 1 + E - off) (by omega)
  refine ⟨hallb, hnat, ?_, ?_, ?_, fun v hv => ?_⟩
  · rw [Bits.leConst_eq hallb _, hnat, if_pos (by omega)]
  · show IntervalEq γ₂ _ _ (Range.reconstruct B (List.ofFn fun l : Fin k =>
      ((off / B ^ (l : ℕ) % B : ℕ) : K))) (Range.reconstruct B (List.ofFn fun l : Fin k =>
      (((γ₂ - 1 + E - off) / B ^ (l : ℕ) % B : ℕ) : K))) _
    rw [hlo, hhi, hout]
    unfold IntervalEq
    rw [endpoint_cast, ← Nat.cast_add, ← Nat.cast_add]
    congr 1
    omega
  · show relationResult γ₂ M _ _ (Range.reconstruct B (List.ofFn fun l : Fin k =>
      ((off / B ^ (l : ℕ) % B : ℕ) : K))) _ = _
    rw [hlo, hout, relationResult_cast, hrel]
  · rcases (List.interleavePairs_perm_append _ _).mem_iff.mp hv |> List.mem_append.mp with h | h
    · exact hlo' v h
    · exact hhi' v h

/-- **Native completeness.** In characteristic `q`, the honest advice passes for any hint `hb`
and coefficient `wc`, with `w` the canonical representative. `hγ`, `hdvd`, `hr` and `hγB` are
parameter conditions. -/
theorem native_complete [CharP K modulus] {γ₂ B k r : ℕ} (hγ : 0 < γ₂)
    (hdvd : 2 * γ₂ ∣ modulus - 1) (hr : hiCount γ₂ < 2 ^ r) (hγB : γ₂ < B ^ k) (hb : Bool)
    (wc : Coeff) :
    let a := honest (K := K) γ₂ B k r hb wc
    (native γ₂ B k ((hb.toNat : ℕ) : K) (wc.val : K) a.s a.lo a.hi a.bits).ok = true ∧
      ∀ v ∈ (native γ₂ B k ((hb.toNat : ℕ) : K) (wc.val : K) a.s a.lo a.hi a.bits).needles,
        Range.IsNatBelow B v := by
  intro a
  obtain ⟨_, _, hle, hint, hres, hneed⟩ := honest_spec (K := K) hγ hdvd hr hγB hb wc
  refine ⟨native_ok_iff.mpr ⟨hle, by cases hb <;> simp, hint, ?_⟩, fun v hv => hneed v
    (by simpa using hv)⟩
  rw [hres]
  have hq : ((modulus : ℤ) : K) = 0 := by
    rw [Int.cast_natCast]; exact CharP.cast_eq_zero K modulus
  rcases (decomposeCoeff_repr hγ hdvd wc).val_eq with h | h
  · rw [← Int.cast_natCast, h]
  · rw [← Int.cast_natCast, h]
    push_cast
    rw [CharP.cast_eq_zero K modulus, add_zero]

/-- **Emulated completeness.** The honest advice with the honest wrap bit passes for any hint
`hb` and coefficient `wc`, with `w` the canonical representative. -/
theorem emulated_complete {γ₂ B k r : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    (hr : hiCount γ₂ < 2 ^ r) (hγB : γ₂ < B ^ k) (hb : Bool) (wc : Coeff) :
    let a := honest (K := K) γ₂ B k r hb wc
    let c : K := ((honestCorner γ₂ wc).toNat : ℕ)
    (emulated γ₂ B k ((hb.toNat : ℕ) : K) (wc.val : K) a.s c a.lo a.hi a.bits).ok = true ∧
      ∀ v ∈ (emulated γ₂ B k ((hb.toNat : ℕ) : K) (wc.val : K) a.s c a.lo a.hi a.bits).needles,
        Range.IsNatBelow B v := by
  intro a c
  obtain ⟨hallb, _, hle, hint, hres, hneed⟩ := honest_spec (K := K) hγ hdvd hr hγB hb wc
  have hbit : ∀ b : Bool, ((b.toNat : ℕ) : K) * (((b.toNat : ℕ) : K) - 1) = 0 := by
    intro b; cases b <;> simp
  refine ⟨emulated_ok_iff.mpr ⟨hbit hb, hbit _, hbit _, fun b => ?_, hle, hint, ?_⟩,
    fun v hv => hneed v (by simpa using hv)⟩
  · rcases hallb b with h | h <;> rw [h] <;> ring
  · rw [hres]
    unfold c honestCorner
    rcases (decomposeCoeff_repr hγ hdvd wc).val_eq with h | h
    · rw [← Int.cast_natCast (R := K) wc.val, h]
      simp
    · have hne : ¬ (wc.val : ℤ) = 2 * γ₂ * (decomposeCoeff wc γ₂).1 + (decomposeCoeff wc γ₂).2 := by
        rw [h]; have : (0 : ℤ) < modulus := by decide
        omega
      rw [decide_eq_false hne, ← Int.cast_natCast (R := K) wc.val, h]
      simp

end GordieHowe.MLDSA44.UseHint
