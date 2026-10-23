-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Spec.Rq
public import LatticeCrypto.MLDSA.ConcretePrimitives
import all LatticeCrypto.MLDSA.Concrete.Rounding

@[expose] public section

/-!
# ML-DSA rounding: `Decompose` and `UseHint`

Facts about the vendored `MLDSA.Concrete.decomposeCoeff` (FIPS 204 Algorithm 36) and
`MLDSA.Concrete.useHintCoeff` (Algorithm 40) that the A circuit's UseHint relation targets
(`use_hint` in `lib/gordiehowe/examples/mldsa/mldsa_gadgets.h`).

`decomposeCoeff_of_repr` characterizes `Decompose` by its representation: writing `α = 2γ₂` and
`M = (q - 1) / α`, every residue has exactly one representation `α · r1 + r0` with `r1 < M` and
`-γ₂ < r0 ≤ γ₂`, or `r1 = 0` and `r0 = -γ₂`, and `decomposeCoeff` returns it (a tiling of
`[-γ₂, q - 1 - γ₂]`). `useHintCoeff_of_relation` states that the integer constraints of the UseHint
relation force its output to be `UseHint(h, w)`.
-/

namespace GordieHowe.MLDSA44

open _root_.MLDSA _root_.MLDSA.Concrete

/-- `decomposeCoeff` read off a quotient-remainder split `r.val = 2γ₂ · qq + t`, `t < 2γ₂`. -/
theorem decomposeCoeff_of_val {r : Coeff} {γ₂ qq t : ℕ} (hval : r.val = 2 * γ₂ * qq + t)
    (ht : t < 2 * γ₂) :
    decomposeCoeff r γ₂ =
      if t ≤ γ₂ then
        (if 2 * γ₂ * qq = modulus - 1 then (0, (t : ℤ) - 1) else (qq, t))
      else
        (if 2 * γ₂ * (qq + 1) = modulus - 1 then (0, (t : ℤ) - 2 * γ₂ - 1)
          else (qq + 1, (t : ℤ) - 2 * γ₂)) := by
  have hγ : 0 < 2 * γ₂ := by omega
  have hmod : r.val % (2 * γ₂) = t := by
    rw [hval, Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
  have hdiv : r.val / (2 * γ₂) = qq := by
    rw [hval, Nat.add_comm, Nat.add_mul_div_left _ _ hγ, Nat.div_eq_of_lt ht, Nat.zero_add]
  have hhalf : 2 * γ₂ / 2 = γ₂ := by omega
  unfold decomposeCoeff
  simp only [hmod, hdiv, hhalf]
  split_ifs <;> simp_all

/-- **`Decompose` by representation.** Let `α = 2γ₂` divide `q - 1` and `M = (q - 1) / α`.
If `r1 < M` and either `-γ₂ < r0 ≤ γ₂`, or `r1 = 0` and `r0 = -γ₂`, then
`decomposeCoeff (α · r1 + r0) γ₂ = (r1, r0)`. `hγ` and `hdvd` are `param`s. -/
theorem decomposeCoeff_of_repr {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1) {r1 : ℕ}
    {r0 : ℤ} (hr1 : r1 < (modulus - 1) / (2 * γ₂))
    (hr0 : (-(γ₂ : ℤ) < r0 ∧ r0 ≤ γ₂) ∨ (r1 = 0 ∧ r0 = -(γ₂ : ℤ))) :
    decomposeCoeff (((2 * γ₂ * r1 : ℕ) : ℤ) + r0 : ℤ) γ₂ = (r1, r0) := by
  obtain ⟨M, hM⟩ := hdvd
  have hq : modulus = 2 * γ₂ * M + 1 := by
    have : 1 ≤ modulus := by decide
    omega
  have hMdef : (modulus - 1) / (2 * γ₂) = M := by
    rw [hM, Nat.mul_div_cancel_left _ (by omega)]
  rw [hMdef] at hr1
  have hMpos : 0 < M := by omega
  have hαr1 : 2 * γ₂ * r1 + 2 * γ₂ ≤ 2 * γ₂ * M := by
    have := Nat.mul_le_mul_left (2 * γ₂) (Nat.succ_le_of_lt hr1)
    rwa [Nat.mul_succ] at this
  have hαM : 2 * γ₂ ≤ 2 * γ₂ * M := Nat.le_mul_of_pos_right _ hMpos
  have hsplitM : 2 * γ₂ * (M - 1) + 2 * γ₂ = 2 * γ₂ * M := by
    rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hMpos]
  have hwrap : ∀ x, x < M → 2 * γ₂ * x ≠ modulus - 1 := by
    intro x hx
    have := Nat.mul_lt_mul_of_pos_left hx (show 0 < 2 * γ₂ by omega)
    omega
  rcases le_or_gt 0 r0 with hpos | hneg
  · -- `0 ≤ r0 ≤ γ₂`: the first branch, no wrap.
    have hr0le : r0 ≤ γ₂ := by rcases hr0 with h | h <;> omega
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hpos
    have hlt : 2 * γ₂ * r1 + n < modulus := by omega
    have hval : ((((2 * γ₂ * r1 : ℕ) : ℤ) + (n : ℤ) : ℤ) : Coeff).val = 2 * γ₂ * r1 + n := by
      rw [show (((2 * γ₂ * r1 : ℕ) : ℤ) + (n : ℤ) : ℤ) = ((2 * γ₂ * r1 + n : ℕ) : ℤ) by push_cast; ring,
        Int.cast_natCast, ZMod.val_natCast_of_lt hlt]
    rw [decomposeCoeff_of_val hval (by omega), if_pos (by omega), if_neg (hwrap r1 hr1)]
  · rcases Nat.eq_zero_or_pos r1 with hr1z | hr1pos
    · -- `r1 = 0`, `-γ₂ ≤ r0 < 0`: the value is `q + r0`, which decomposes with a wrap.
      subst hr1z
      have hr0ge : -(γ₂ : ℤ) ≤ r0 := by rcases hr0 with h | h <;> omega
      obtain ⟨n, hn⟩ : ∃ n : ℕ, r0 = -(n : ℤ) := ⟨r0.natAbs, by omega⟩
      subst hn
      have hn1 : 1 ≤ n := by omega
      have hnγ : n ≤ γ₂ := by omega
      have hval : ((((2 * γ₂ * 0 : ℕ) : ℤ) + -(n : ℤ) : ℤ) : Coeff).val = modulus - n := by
        have hcast : ((((2 * γ₂ * 0 : ℕ) : ℤ) + -(n : ℤ) : ℤ) : Coeff) = ((modulus - n : ℕ) : Coeff) := by
          rw [Nat.cast_sub (by omega), ZMod.natCast_self]
          push_cast
          ring
        rw [hcast, ZMod.val_natCast_of_lt (by omega)]
      by_cases hn1' : n = 1
      · subst hn1'
        rw [decomposeCoeff_of_val (qq := M) (t := 0) (by rw [hval]; omega) (by omega),
          if_pos (by omega), if_pos (by omega)]
        simp
      · rw [decomposeCoeff_of_val (qq := M - 1) (t := 2 * γ₂ + 1 - n) (by rw [hval]; omega)
            (by omega),
          if_neg (by omega), if_pos (by rw [Nat.sub_add_cancel hMpos]; omega)]
        simp only [Prod.mk.injEq, true_and]
        push_cast [show n ≤ 2 * γ₂ + 1 by omega]
        ring
    · -- `r1 ≥ 1`, `-γ₂ < r0 < 0`: the second branch at quotient `r1 - 1`, no wrap.
      have hr0gt : -(γ₂ : ℤ) < r0 := by rcases hr0 with h | h <;> omega
      obtain ⟨n, hn⟩ : ∃ n : ℕ, r0 = -(n : ℤ) := ⟨r0.natAbs, by omega⟩
      subst hn
      have hαle : 2 * γ₂ ≤ 2 * γ₂ * r1 := Nat.le_mul_of_pos_right _ hr1pos
      have hsplit : 2 * γ₂ * r1 = 2 * γ₂ * (r1 - 1) + 2 * γ₂ := by
        rw [← Nat.mul_succ, Nat.succ_eq_add_one, Nat.sub_add_cancel hr1pos]
      have hval : ((((2 * γ₂ * r1 : ℕ) : ℤ) + -(n : ℤ) : ℤ) : Coeff).val =
          2 * γ₂ * (r1 - 1) + (2 * γ₂ - n) := by
        have hcast : ((((2 * γ₂ * r1 : ℕ) : ℤ) + -(n : ℤ) : ℤ) : Coeff) =
            ((2 * γ₂ * r1 - n : ℕ) : Coeff) := by
          rw [Nat.cast_sub (by omega)]
          push_cast
          ring
        rw [hcast, ZMod.val_natCast_of_lt (by omega)]
        omega
      rw [decomposeCoeff_of_val hval (by omega), if_neg (by omega),
        Nat.sub_add_cancel hr1pos, if_neg (hwrap r1 hr1)]
      simp only [Prod.mk.injEq, true_and]
      push_cast [show n ≤ 2 * γ₂ by omega]
      ring

/-- `useHintCoeff` read off the decomposition of its input. -/
theorem useHintCoeff_of_decompose {r : Coeff} {γ₂ r1 : ℕ} {r0 : ℤ}
    (hdec : decomposeCoeff r γ₂ = (r1, r0)) (h : Bool) :
    useHintCoeff h r γ₂ =
      if h then
        (if r0 > 0 then (r1 + 1) % ((modulus - 1) / (2 * γ₂))
          else (r1 + (modulus - 1) / (2 * γ₂) - 1) % ((modulus - 1) / (2 * γ₂)))
      else r1 := by
  unfold useHintCoeff
  rw [hdec]

theorem coeff_apply (f : Rq) (k : Fin ringDegree) : coeff f k = f.get k := rfl

/-- Coefficient `k` of `UseHint(h, w)` is `useHintCoeff` on coefficient `k`. -/
theorem coeff_useHint_eq (p : MLDSA.Params) (h : Hint) (w : Rq) (k : Fin ringDegree) :
    coeff (useHint p h w) k = ((useHintCoeff (h.get k) (w.get k) p.gamma2 : ℕ) : Coeff) := by
  rw [coeff_apply]
  exact Vector.get_ofFn _ k

/-- The coefficientwise characterization of `UseHint` (FIPS 204 Algorithm 40), phrased against
the vendored `decomposeCoeff`: coefficient `k` of `UseHint(h, w)` is the high part of
`Decompose(coeff w k)`, adjusted by one step modulo `m = (q-1)/(2γ₂)` in the direction the low
part's sign picks out when `h k` is set. -/
theorem coeff_useHint (p : MLDSA.Params) (h : Hint) (w : Rq) (k : Fin ringDegree) :
    coeff (useHint p h w) k =
      (let m := (modulus - 1) / (2 * p.gamma2)
       let r1 := (decomposeCoeff (coeff w k) p.gamma2).1
       let r0 := (decomposeCoeff (coeff w k) p.gamma2).2
       if h.get k then (if r0 > 0 then (r1 + 1) % m else (r1 + m - 1) % m) else r1 : ℕ) := by
  rw [coeff_useHint_eq, useHintCoeff_of_decompose (Prod.eta _).symm, coeff_apply]

/-! ### The UseHint relation -/

/-- `raw_high` of `use_hint`, over the integers: the output `y` with the hint's `±1` adjustment
undone, wrapping modulo `M` at `y = 0` (upward hint) and `y = M - 1` (downward hint). `h` is the
hint bit and `s` the committed `nonpositive` bit. -/
-- spec-side
def useHintRawHigh (M : ℕ) (h s : Bool) (y : ℕ) : ℤ :=
  (y : ℤ) - (h && !s).toNat + (h && s).toNat +
    M * (((h && !s) && decide (y = 0)).toNat - ((h && s) && decide (y = M - 1)).toNat : ℤ)

/-- `endpoint` of `use_hint`: `1` exactly when the low part may take the exceptional value `-γ₂`,
i.e. `s` is set and `raw_high = 0`. -/
-- spec-side
def useHintEndpoint (M : ℕ) (h s : Bool) (y : ℕ) : ℕ :=
  ((s && !h) && decide (y = 0)).toNat + ((h && s) && decide (y = M - 1)).toNat

/-- `low = lower + offset` of `use_hint`, with `lower = 1 - s·γ₂ - endpoint`. -/
-- spec-side
def useHintLow (γ₂ M : ℕ) (h s : Bool) (y offset : ℕ) : ℤ :=
  1 - (s.toNat * γ₂ : ℕ) - useHintEndpoint M h s y + offset

/-- **UseHint relation soundness**. Let `M = (q - 1)/(2γ₂)`. Suppose the output `y` is below `M`
(`gadget:OutputFromBits`), `offset` and `slack` are naturals (the range lookups) satisfying the
relation's interval equation `offset + slack = γ₂ - 1 + endpoint` (an integer equation, since both
sides are far below the field characteristic), and the coefficient `w` is congruent modulo `q` to
`2γ₂ · raw_high + low`, the relation's result (the caller's assertion; the emulated caller adds
`corner · q`). Then `y = UseHint(h, w)`. `hγ` and `hdvd` are `param`s. -/
theorem useHintCoeff_of_relation {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {h s : Bool} {y offset slack : ℕ} {w : Coeff}
    (hy : y < (modulus - 1) / (2 * γ₂))
    (hsum : offset + slack = γ₂ - 1 + useHintEndpoint ((modulus - 1) / (2 * γ₂)) h s y)
    (hw : w = ((2 * γ₂ * useHintRawHigh ((modulus - 1) / (2 * γ₂)) h s y +
      useHintLow γ₂ ((modulus - 1) / (2 * γ₂)) h s y offset : ℤ) : Coeff)) :
    useHintCoeff h w γ₂ = y := by
  set M := (modulus - 1) / (2 * γ₂) with hMdef
  have hMpos : 0 < M := by
    obtain ⟨c, hc⟩ := hdvd
    rw [hMdef, hc, Nat.mul_div_cancel_left _ (by omega)]
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp at hc; exact absurd hc (by decide)
    · exact h0
  -- The decomposition the relation binds `w` to.
  have hrepr : ∀ {r1 : ℕ} {r0 : ℤ}, r1 < M →
      ((-(γ₂ : ℤ) < r0 ∧ r0 ≤ γ₂) ∨ (r1 = 0 ∧ r0 = -(γ₂ : ℤ))) →
      useHintRawHigh M h s y = r1 → useHintLow γ₂ M h s y offset = r0 →
      decomposeCoeff w γ₂ = (r1, r0) := by
    intro r1 r0 hr1 hr0 hraw hlow
    rw [hw, hraw, hlow, show (2 * (γ₂ : ℤ) * (r1 : ℤ)) = ((2 * γ₂ * r1 : ℕ) : ℤ) by push_cast; ring]
    exact decomposeCoeff_of_repr hγ hdvd hr1 hr0
  have hM1 : ((M - 1 : ℕ) : ℤ) = (M : ℤ) - 1 := by push_cast [show 1 ≤ M by omega]; ring
  cases h <;> cases s
  · -- no hint, positive low part: `raw_high = y`, `low = 1 + offset ∈ [1, γ₂]`.
    have he : useHintEndpoint M false false y = 0 := by simp [useHintEndpoint]
    rw [he] at hsum
    have hdec := hrepr (r1 := y) (r0 := 1 + offset) hy (Or.inl ⟨by omega, by omega⟩)
      (by simp [useHintRawHigh]) (by simp [useHintLow, he])
    rw [useHintCoeff_of_decompose hdec]
    rfl
  · -- no hint, nonpositive low part: `raw_high = y`, `low ∈ [1 - γ₂ - [y = 0], 0]`.
    by_cases hy0 : y = 0
    · have he : useHintEndpoint M false true y = 1 := by simp [useHintEndpoint, hy0]
      rw [he] at hsum
      have hdec := hrepr (r1 := 0) (r0 := -(γ₂ : ℤ) + offset) hMpos
        (by by_cases hoff : offset = 0
            · right; subst hoff; simp
            · left; constructor <;> omega)
        (by simp [useHintRawHigh, hy0]) (by simp [useHintLow, he])
      rw [useHintCoeff_of_decompose hdec, hy0]
      rfl
    · have he : useHintEndpoint M false true y = 0 := by simp [useHintEndpoint, hy0]
      rw [he] at hsum
      have hdec := hrepr (r1 := y) (r0 := 1 - γ₂ + offset) hy
        (Or.inl ⟨by omega, by omega⟩) (by simp [useHintRawHigh]) (by simp [useHintLow, he])
      rw [useHintCoeff_of_decompose hdec]
      rfl
  · -- hint, positive low part: `y = (raw_high + 1) mod M`, `low = 1 + offset ∈ [1, γ₂]`.
    have he : useHintEndpoint M true false y = 0 := by simp [useHintEndpoint]
    rw [he] at hsum
    have hlow : useHintLow γ₂ M true false y offset = 1 + offset := by simp [useHintLow, he]
    by_cases hy0 : y = 0
    · have hdec := hrepr (r1 := M - 1) (r0 := 1 + offset) (by omega)
        (Or.inl ⟨by omega, by omega⟩) (by simp [useHintRawHigh, hy0, hM1]; ring) hlow
      rw [useHintCoeff_of_decompose hdec, hy0]
      simp only [ite_true, show (1 + (offset : ℤ)) > 0 by omega]
      rw [Nat.sub_add_cancel hMpos, Nat.mod_self]
    · have hdec := hrepr (r1 := y - 1) (r0 := 1 + offset) (by omega)
        (Or.inl ⟨by omega, by omega⟩)
        (by simp [useHintRawHigh, hy0]; push_cast [show 1 ≤ y by omega]; ring) hlow
      rw [useHintCoeff_of_decompose hdec]
      simp only [ite_true, show (1 + (offset : ℤ)) > 0 by omega]
      rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt hy]
  · -- hint, nonpositive low part: `y = (raw_high - 1) mod M`, `low ∈ [1 - γ₂ - [y = M-1], 0]`.
    by_cases hyl : y = M - 1
    · have he : useHintEndpoint M true true y = 1 := by simp [useHintEndpoint, hyl]
      rw [he] at hsum
      have hdec := hrepr (r1 := 0) (r0 := -(γ₂ : ℤ) + offset) hMpos
        (by by_cases hoff : offset = 0
            · right; subst hoff; simp
            · left; constructor <;> omega)
        (by simp [useHintRawHigh, hyl, hM1]) (by simp [useHintLow, he])
      rw [useHintCoeff_of_decompose hdec, hyl]
      simp only [ite_true, show ¬ (-(γ₂ : ℤ) + offset > 0) by omega, ite_false, Nat.zero_add]
      exact Nat.mod_eq_of_lt (by omega)
    · have he : useHintEndpoint M true true y = 0 := by simp [useHintEndpoint, hyl]
      rw [he] at hsum
      have hdec := hrepr (r1 := y + 1) (r0 := 1 - γ₂ + offset) (by omega)
        (Or.inl ⟨by omega, by omega⟩) (by simp [useHintRawHigh, hyl]) (by simp [useHintLow, he])
      rw [useHintCoeff_of_decompose hdec]
      simp only [ite_true, show ¬ (1 - (γ₂ : ℤ) + offset > 0) by omega, ite_false]
      rw [show y + 1 + M - 1 = y + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt hy]

/-- The emulated caller's form: the relation's integer result plus a multiple of `q` (the
`corner` bit) is an integer representative of `w`. -/
theorem useHintCoeff_of_relation_int {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {h s : Bool} {y offset slack : ℕ} {wInt corner : ℤ}
    (hy : y < (modulus - 1) / (2 * γ₂))
    (hsum : offset + slack = γ₂ - 1 + useHintEndpoint ((modulus - 1) / (2 * γ₂)) h s y)
    (hw : wInt = 2 * γ₂ * useHintRawHigh ((modulus - 1) / (2 * γ₂)) h s y +
      useHintLow γ₂ ((modulus - 1) / (2 * γ₂)) h s y offset + corner * modulus) :
    useHintCoeff h (wInt : Coeff) γ₂ = y :=
  useHintCoeff_of_relation hγ hdvd hy hsum (by rw [hw]; push_cast; simp)

/-- The polynomial form: if coefficient `k` of `w` satisfies the UseHint relation with output
`y`, coefficient `k` of `UseHint(h, w)` is `y`. -/
theorem coeff_useHint_of_relation (p : MLDSA.Params) (hγ : 0 < p.gamma2)
    (hdvd : 2 * p.gamma2 ∣ modulus - 1) {h : Hint} {w : Rq} {k : Fin ringDegree} {s : Bool}
    {y offset slack : ℕ}
    (hy : y < (modulus - 1) / (2 * p.gamma2))
    (hsum : offset + slack =
      p.gamma2 - 1 + useHintEndpoint ((modulus - 1) / (2 * p.gamma2)) (h.get k) s y)
    (hw : coeff w k = ((2 * p.gamma2 * useHintRawHigh ((modulus - 1) / (2 * p.gamma2)) (h.get k) s y +
      useHintLow p.gamma2 ((modulus - 1) / (2 * p.gamma2)) (h.get k) s y offset : ℤ) : Coeff)) :
    coeff (useHint p h w) k = y := by
  rw [coeff_useHint_eq, useHintCoeff_of_relation hγ hdvd hy hsum (by rw [← coeff_apply]; exact hw)]

/-! ### The forward direction: `Decompose`'s output and the honest relation witness -/

/-- The properties of a `Decompose` output `(r1, r0)` of `r`: the high part is below
`M = (q - 1)/(2γ₂)`, the low part lies in `(-γ₂, γ₂]` or is the exceptional `-γ₂` at high part zero,
and `2γ₂ · r1 + r0` is the canonical representative of `r`, or that minus `q` (the wrap interval).
-/
structure DecomposeRepr (γ₂ : ℕ) (r : Coeff) (r1 : ℕ) (r0 : ℤ) : Prop where
  high_lt : r1 < (modulus - 1) / (2 * γ₂)
  low_mem : (-(γ₂ : ℤ) < r0 ∧ r0 ≤ γ₂) ∨ (r1 = 0 ∧ r0 = -(γ₂ : ℤ))
  val_eq : (r.val : ℤ) = 2 * γ₂ * r1 + r0 ∨ (r.val : ℤ) = 2 * γ₂ * r1 + r0 + modulus

/-- `decomposeCoeff` returns a representation with the properties of `DecomposeRepr`.
`hγ` and `hdvd` are `param`s. -/
theorem decomposeCoeff_repr {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1) (r : Coeff) :
    DecomposeRepr γ₂ r (decomposeCoeff r γ₂).1 (decomposeCoeff r γ₂).2 := by
  obtain ⟨M, hM⟩ := hdvd
  have hq1 : 1 ≤ modulus := by decide
  have hq : modulus = 2 * γ₂ * M + 1 := by omega
  have hMdef : (modulus - 1) / (2 * γ₂) = M := by
    rw [hM, Nat.mul_div_cancel_left _ (by omega)]
  have hA : 0 < 2 * γ₂ := by omega
  have hMpos : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · rw [h0, mul_zero] at hq; exact absurd hq (by decide)
    · exact h0
  have hrlt : r.val < 2 * γ₂ * M + 1 := hq ▸ ZMod.val_lt r
  obtain ⟨qq, t, hval, htlt⟩ : ∃ qq t, r.val = 2 * γ₂ * qq + t ∧ t < 2 * γ₂ :=
    ⟨_, _, (Nat.div_add_mod _ _).symm, Nat.mod_lt _ hA⟩
  have hqqM : qq ≤ M := Nat.le_of_mul_le_mul_left (by omega) hA
  have hvalZ : (r.val : ℤ) = 2 * γ₂ * qq + t := by rw [hval]; push_cast; ring
  have hqZ : (modulus : ℤ) = 2 * γ₂ * M + 1 := by rw [hq]; push_cast; ring
  rw [decomposeCoeff_of_val hval htlt]
  split_ifs with h1 h2 h3 <;> dsimp only
  · -- `t ≤ γ₂` at the top: `r = q - 1`, output `(0, -1)`.
    have ht0 : t = 0 := by omega
    subst ht0
    have h2Z : 2 * (γ₂ : ℤ) * qq + 1 = modulus := by
      have : 2 * γ₂ * qq + 1 = modulus := by omega
      exact_mod_cast this
    refine ⟨by rw [hMdef]; exact hMpos, by push_cast; simp only [true_and]; omega, Or.inr ?_⟩
    push_cast
    linarith
  · refine ⟨?_, Or.inl ⟨by omega, by omega⟩, Or.inl (by linarith)⟩
    rw [hMdef]
    rcases Nat.lt_or_ge qq M with hlt | hge
    · exact hlt
    · have hqM : qq = M := le_antisymm hqqM hge
      rw [hqM] at h2
      omega
  · -- `t > γ₂` and the next high part is the top: output `(0, t - 2γ₂ - 1)`.
    have h3Z : 2 * (γ₂ : ℤ) * (qq + 1) + 1 = modulus := by
      have : 2 * γ₂ * (qq + 1) + 1 = modulus := by omega
      exact_mod_cast this
    refine ⟨by rw [hMdef]; exact hMpos, by push_cast; simp only [true_and]; omega, Or.inr ?_⟩
    push_cast
    linarith
  · have hlt : qq < M := Nat.lt_of_mul_lt_mul_left (a := 2 * γ₂) (by omega)
    refine ⟨?_, Or.inl ⟨by omega, by omega⟩, Or.inl (by push_cast; linarith)⟩
    rw [hMdef]
    rcases Nat.lt_or_ge (qq + 1) M with h | h
    · exact h
    · have hqM : qq + 1 = M := by omega
      rw [hqM] at h3
      omega

/-- UseHint's output is below `M = (q - 1)/(2γ₂)`. -/
theorem useHintCoeff_lt {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1) (h : Bool)
    (r : Coeff) : useHintCoeff h r γ₂ < (modulus - 1) / (2 * γ₂) := by
  have hrep := decomposeCoeff_repr hγ hdvd r
  have hMpos : 0 < (modulus - 1) / (2 * γ₂) := by have := hrep.high_lt; omega
  rw [useHintCoeff_of_decompose (Prod.eta _).symm]
  cases h
  · exact hrep.high_lt
  · simp only [ite_true]
    split_ifs
    · exact Nat.mod_lt _ hMpos
    · exact Nat.mod_lt _ hMpos

/-- The honest `nonpositive` bit of the UseHint relation: the sign of the low part. -/
-- spec-side
def useHintSign (γ₂ : ℕ) (r : Coeff) : Bool := decide ((decomposeCoeff r γ₂).2 ≤ 0)

/-- The honest offset of the UseHint relation: the low part minus `lower`. -/
-- spec-side
def useHintOffset (γ₂ : ℕ) (h : Bool) (r : Coeff) : ℕ :=
  ((decomposeCoeff r γ₂).2 - (1 - (((useHintSign γ₂ r).toNat * γ₂ : ℕ) : ℤ) -
    useHintEndpoint ((modulus - 1) / (2 * γ₂)) h (useHintSign γ₂ r) (useHintCoeff h r γ₂))).toNat

/-- On the honest witness the relation's `raw_high` is `Decompose`'s high part and its endpoint
is `1` exactly for a nonpositive low part at high part zero. -/
theorem useHintRawHigh_honest {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1) (h : Bool)
    (r : Coeff) :
    useHintRawHigh ((modulus - 1) / (2 * γ₂)) h (useHintSign γ₂ r) (useHintCoeff h r γ₂) =
        (decomposeCoeff r γ₂).1 ∧
      useHintEndpoint ((modulus - 1) / (2 * γ₂)) h (useHintSign γ₂ r) (useHintCoeff h r γ₂) =
        if useHintSign γ₂ r = true ∧ (decomposeCoeff r γ₂).1 = 0 then 1 else 0 := by
  have hrep := decomposeCoeff_repr hγ hdvd r
  set M := (modulus - 1) / (2 * γ₂) with hMdef
  set r1 := (decomposeCoeff r γ₂).1 with hr1
  set r0 := (decomposeCoeff r γ₂).2 with hr0
  have hlt : r1 < M := hrep.high_lt
  have hy : useHintCoeff h r γ₂ =
      if h then (if r0 > 0 then (r1 + 1) % M else (r1 + M - 1) % M) else r1 :=
    useHintCoeff_of_decompose (Prod.eta _).symm h
  unfold useHintSign
  rw [← hr0, hy]
  cases h <;> by_cases hs : r0 ≤ 0
  · by_cases hr : r1 = 0 <;> simp [useHintRawHigh, useHintEndpoint, hs, hr]
  · simp [useHintRawHigh, useHintEndpoint, hs]
  · -- hint, nonpositive: `y = (r1 - 1) mod M`
    have hnot : ¬ r0 > 0 := by omega
    by_cases hr10 : r1 = 0
    · have hyv : (r1 + M - 1) % M = M - 1 := by rw [hr10, zero_add, Nat.mod_eq_of_lt (by omega)]
      rw [hr10] at hyv
      simp only [hnot, ite_false, ite_true, hs, hr10, hyv]
      simp [useHintRawHigh, useHintEndpoint]
      push_cast [show 1 ≤ M by omega]
      ring
    · have hyv : (r1 + M - 1) % M = r1 - 1 := by
        rw [show r1 + M - 1 = r1 - 1 + M by omega, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      have hne : r1 - 1 ≠ M - 1 := by omega
      simp only [hnot, ite_false, ite_true, hs, hr10]
      rw [hyv]
      simp [useHintRawHigh, useHintEndpoint, hne]
      push_cast [show 1 ≤ r1 by omega]
      ring
  · -- hint, positive: `y = (r1 + 1) mod M`
    have hpos : r0 > 0 := by omega
    by_cases hr1M : r1 + 1 = M
    · have hyv : (r1 + 1) % M = 0 := by rw [hr1M, Nat.mod_self]
      simp only [hpos, ite_true, hyv, hs]
      simp [useHintRawHigh, useHintEndpoint]
      omega
    · have hyv : (r1 + 1) % M = r1 + 1 := Nat.mod_eq_of_lt (by omega)
      simp only [hpos, ite_true, hyv, hs]
      simp [useHintRawHigh, useHintEndpoint]

/-- **The honest UseHint witness satisfies the relation** (completeness): with the honest sign and
offset, the offset fits its interval, the relation's `raw_high` and `low` are `Decompose`'s high and
low parts, so its result `2γ₂ · raw_high + low` is the representative of `r` given by
`DecomposeRepr.val_eq`. `hγ` and `hdvd` are `param`s. -/
theorem useHintRelation_honest {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1) (h : Bool)
    (r : Coeff) :
    useHintOffset γ₂ h r ≤ γ₂ - 1 +
        useHintEndpoint ((modulus - 1) / (2 * γ₂)) h (useHintSign γ₂ r) (useHintCoeff h r γ₂) ∧
      2 * γ₂ * useHintRawHigh ((modulus - 1) / (2 * γ₂)) h (useHintSign γ₂ r)
          (useHintCoeff h r γ₂) +
        useHintLow γ₂ ((modulus - 1) / (2 * γ₂)) h (useHintSign γ₂ r) (useHintCoeff h r γ₂)
          (useHintOffset γ₂ h r) =
        2 * γ₂ * (decomposeCoeff r γ₂).1 + (decomposeCoeff r γ₂).2 := by
  have hrep := decomposeCoeff_repr hγ hdvd r
  obtain ⟨hraw, hend⟩ := useHintRawHigh_honest hγ hdvd h r
  set E := useHintEndpoint ((modulus - 1) / (2 * γ₂)) h (useHintSign γ₂ r) (useHintCoeff h r γ₂)
  set r1 := (decomposeCoeff r γ₂).1
  set r0 := (decomposeCoeff r γ₂).2
  set s := useHintSign γ₂ r with hsdef
  have hsr : s = decide (r0 ≤ 0) := rfl
  -- the low part lies in `[lower, upper]`
  have hbounds : 1 - ((s.toNat * γ₂ : ℕ) : ℤ) - E ≤ r0 ∧
      r0 - (1 - ((s.toNat * γ₂ : ℕ) : ℤ) - E) ≤ γ₂ - 1 + E := by
    have hmem := hrep.low_mem
    cases hs : s <;> rw [hs] at hend <;> simp only [Bool.false_eq_true, false_and, ite_false,
      true_and, Bool.toNat_false, Bool.toNat_true, zero_mul, one_mul] at hend ⊢ <;> rw [hsr] at hs
    · have : ¬ r0 ≤ 0 := by simpa using hs
      rw [hend]; push_cast; omega
    · have : r0 ≤ 0 := by simpa using hs
      split_ifs at hend with hr10 <;> rw [hend] <;> push_cast <;> omega
  have hoff : ((useHintOffset γ₂ h r : ℕ) : ℤ) = r0 - (1 - ((s.toNat * γ₂ : ℕ) : ℤ) - E) := by
    unfold useHintOffset
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hbounds.1)
  refine ⟨by have := hbounds.2; omega, ?_⟩
  rw [hraw]
  unfold useHintLow
  rw [hoff]
  ring

/-- `raw_high` of an output below `M` lies in `[0, M)`. -/
theorem useHintRawHigh_mem {M : ℕ} {h s : Bool} {y : ℕ} (hy : y < M) :
    0 ≤ useHintRawHigh M h s y ∧ useHintRawHigh M h s y < M := by
  unfold useHintRawHigh
  cases hz : decide (y = 0) <;> cases hl : decide (y = M - 1) <;>
    simp only [decide_eq_true_eq, decide_eq_false_iff_not] at hz hl <;>
    cases h <;> cases s <;> simp <;> omega

/-- The endpoint indicator is at most `1`. -/
theorem useHintEndpoint_le_one (M : ℕ) (h s : Bool) (y : ℕ) : useHintEndpoint M h s y ≤ 1 := by
  unfold useHintEndpoint
  cases decide (y = 0) <;> cases decide (y = M - 1) <;> cases h <;> cases s <;> simp

/-- A low part whose offset satisfies the interval equation lies in `[-γ₂, γ₂]`. -/
theorem useHintLow_mem {γ₂ M : ℕ} (hγ : 0 < γ₂) {h s : Bool} {y offset slack : ℕ}
    (hsum : offset + slack = γ₂ - 1 + useHintEndpoint M h s y) :
    -(γ₂ : ℤ) ≤ useHintLow γ₂ M h s y offset ∧ useHintLow γ₂ M h s y offset ≤ γ₂ := by
  have hE := useHintEndpoint_le_one M h s y
  unfold useHintLow
  cases s
  · have hE0 : useHintEndpoint M h false y = 0 := by cases h <;> simp [useHintEndpoint]
    rw [hE0] at hsum ⊢
    simp only [Bool.toNat_false, zero_mul]
    push_cast
    constructor <;> omega
  · simp only [Bool.toNat_true, one_mul]
    constructor <;> omega

/-- The relation's result `2γ₂ · raw_high + low` lies in `[-γ₂, q)`. `hγ` and `hdvd` are
`param`s; `hy` and `hsum` are the relation's output bound and interval equation. -/
theorem useHintRelation_bounds {γ₂ : ℕ} (hγ : 0 < γ₂) (hdvd : 2 * γ₂ ∣ modulus - 1)
    {h s : Bool} {y offset slack : ℕ} (hy : y < (modulus - 1) / (2 * γ₂))
    (hsum : offset + slack = γ₂ - 1 + useHintEndpoint ((modulus - 1) / (2 * γ₂)) h s y) :
    -(γ₂ : ℤ) ≤ 2 * γ₂ * useHintRawHigh ((modulus - 1) / (2 * γ₂)) h s y +
        useHintLow γ₂ ((modulus - 1) / (2 * γ₂)) h s y offset ∧
      2 * γ₂ * useHintRawHigh ((modulus - 1) / (2 * γ₂)) h s y +
        useHintLow γ₂ ((modulus - 1) / (2 * γ₂)) h s y offset < modulus := by
  obtain ⟨M, hM⟩ := hdvd
  have hq1 : 1 ≤ modulus := by decide
  have hMdef : (modulus - 1) / (2 * γ₂) = M := by
    rw [hM, Nat.mul_div_cancel_left _ (by omega)]
  rw [hMdef] at hy hsum ⊢
  have hqZ : (modulus : ℤ) = 2 * γ₂ * M + 1 := by
    have : modulus = 2 * γ₂ * M + 1 := by omega
    rw [this]; push_cast; ring
  obtain ⟨hr0, hr1⟩ := useHintRawHigh_mem (h := h) (s := s) hy
  obtain ⟨hl0, hl1⟩ := useHintLow_mem hγ hsum
  have hγZ : (0 : ℤ) < γ₂ := by exact_mod_cast hγ
  constructor
  · nlinarith
  · have : useHintRawHigh M h s y ≤ M - 1 := by omega
    nlinarith

end GordieHowe.MLDSA44
