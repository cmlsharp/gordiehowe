-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHowe.Applications.Falcon512.System.Algebra

@[expose] public section

/-!
# GordieHowe frontend: cross-field equalities of bits

A cross-field `equal(x, y)` of width `1` (`PredBody.cross`) holds in the compiler's contract
(`GordieHowe.RealizedProgram.HoldsWith`): `y`'s readings are below `2`, and where `x`'s are, the readings agree. When
`x` is a bit view (a bit by construction, `GordieHowe.RealizedProgram.reader_bool_of_bits`) the contract's premise
holds outright; with `y` Boolean by its own check (`v · v = v`, `PredBody.boolCheck?`), `x` and `y`
are `1` at the same coordinates (`GordieHowe.RealizedProgram.one_iff_of_cross`), so their words denote the same
naturals (`GordieHowe.RealizedProgram.natOfBits_wordAt_eq_of_cross`).

The native Falcon programs' crossing (`GordieHowe.Falcon512.Native.ROMParams.natOfBits_raw_eq`) is in
`GordieHowe/Applications/Falcon512/Native/ROMParams/Frontend/Basic.lean`.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Matchers -/

/-- **The leaves of a cross-field `equal` of width `1`**: `x` in domain `dx`, `y` in domain `dy`. -/
structure CrossLeaves where
  /-- The domain of `x`. -/
  dx : ℕ
  /-- The value `x`. -/
  x : ℕ
  /-- The domain of `y`. -/
  dy : ℕ
  /-- The value `y`. -/
  y : ℕ
  deriving DecidableEq, Repr

/-- **A cross-field `equal` of two leaves, of width `1`**, read off a predicate body. -/
def PredBody.crossLeaves? : PredBody → Option CrossLeaves
  | .cross dx (.leaf x) dy (.leaf y) k _ => if k.width = 1 then some ⟨dx, x, dy, y⟩ else none
  | _ => none

/-- **The body of a matched cross-field `equal`.** -/
theorem PredBody.eq_of_crossLeaves? {b : PredBody} {s : CrossLeaves} (h : b.crossLeaves? = some s) :
    ∃ real, b = .cross s.dx (.leaf s.x) s.dy (.leaf s.y) {} real := by
  unfold crossLeaves? at h
  split at h
  · rename_i dx x dy y k real
    split_ifs at h with hk
    cases h
    obtain ⟨w⟩ := k
    subst hk
    exact ⟨real, rfl⟩
  · cases h

/-- **The Boolean check `v · v = v`** of value `v` in domain `d`. -/
structure BoolCheck where
  /-- The domain. -/
  d : ℕ
  /-- The value. -/
  v : ℕ
  deriving DecidableEq, Repr

/-- **A Boolean check `v · v = v`**, read off a predicate body. -/
def PredBody.boolCheck? : PredBody → Option BoolCheck
  | .equal d (.mul (.leaf u) (.leaf u')) (.leaf u'') _ =>
    if u' = u ∧ u'' = u then some ⟨d, u⟩ else none
  | _ => none

/-- **The body of a matched Boolean check.** -/
theorem PredBody.eq_of_boolCheck? {b : PredBody} {s : BoolCheck} (h : b.boolCheck? = some s) :
    ∃ t, b = .equal s.d (.mul (.leaf s.v) (.leaf s.v)) (.leaf s.v) t := by
  unfold boolCheck? at h
  split at h
  · rename_i d u u' u'' t
    split_ifs at h with hu
    cases h
    obtain ⟨rfl, rfl⟩ := hu
    exact ⟨t, rfl⟩
  · cases h

section

variable {ir : RealizedProgram} {I : Interp}

/-! ## Words of bits -/

variable (ir) in
/-- **Word `j` of `w` bits of value `v`**, read in field `f`: coordinates `j w, …, j w + w − 1`. -/
def wordAt (rd : ir.Valuation I) (f v w j : ℕ) : BitWires (I f).K w :=
  fun b => ir.evalE rd f (.leaf v) (j * w + b)

/-- **A Boolean check holds where its value is `0` or `1`.** -/
theorem bool_of_boolCheck {b : PredBody} {s : BoolCheck} (hs : b.boolCheck? = some s)
    {rd : ir.Valuation I} (h : ir.HoldsWith rd b) {i : ℕ} (hi : i < (ir.value s.v).size) :
    ir.evalE rd (ir.domainField s.d) (.leaf s.v) i = 0 ∨
      ir.evalE rd (ir.domainField s.d) (.leaf s.v) i = 1 := by
  obtain ⟨t, rfl⟩ := PredBody.eq_of_boolCheck? hs
  exact eq_zero_or_one_of_sq_eq_self ((sq _).trans (h i hi))

/-- **A cross-field `equal` of width `1` between bits** makes them `1` at the same coordinates:
the contract's premise holds as `x` is `0` or `1` (`hx`), so the integer readings agree, and
those of `0` and `1` are `0` and `1` in both fields. -/
theorem one_iff_of_cross {b : PredBody} {s : CrossLeaves} (hs : b.crossLeaves? = some s)
    {rd : ir.Valuation I} (h : ir.HoldsWith rd b)
    (hx0 : (I (ir.domainField s.dx)).toNat 0 = 0) (hx1 : (I (ir.domainField s.dx)).toNat 1 = 1)
    (hy0 : (I (ir.domainField s.dy)).toNat 0 = 0) (hy1 : (I (ir.domainField s.dy)).toNat 1 = 1)
    (hx : ∀ i < (ir.value s.x).size, ir.evalE rd (ir.domainField s.dx) (.leaf s.x) i = 0 ∨
      ir.evalE rd (ir.domainField s.dx) (.leaf s.x) i = 1)
    (hy : ∀ i < (ir.value s.x).size, ir.evalE rd (ir.domainField s.dy) (.leaf s.y) i = 0 ∨
      ir.evalE rd (ir.domainField s.dy) (.leaf s.y) i = 1)
    {i : ℕ} (hi : i < (ir.value s.x).size) :
    ir.evalE rd (ir.domainField s.dx) (.leaf s.x) i = 1 ↔
      ir.evalE rd (ir.domainField s.dy) (.leaf s.y) i = 1 := by
  obtain ⟨real, rfl⟩ := PredBody.eq_of_crossLeaves? hs
  have heq := h.2 (fun i hi => by
    rcases hx i hi with h0 | h1
    · change (I _).toNat (ir.evalE rd _ _ i) < 2
      rw [h0, hx0]
      omega
    · change (I _).toNat (ir.evalE rd _ _ i) < 2
      rw [h1, hx1]
      omega) i hi
  change (I _).toNat (ir.evalE rd _ _ i) = (I _).toNat (ir.evalE rd _ _ i) at heq
  rcases hx i hi with h0 | h1 <;> rcases hy i hi with h0' | h1'
  · simp [h0, h0']
  · rw [h0, h1', hx0, hy1] at heq
    omega
  · rw [h1, h0', hx1, hy0] at heq
    omega
  · simp [h1, h1']

/-- **Words of bits equal across fields**: at a cross-field `equal` of width `1` between bits, word
`j` of `w` bits of `x` and of `y` denote the same natural (`one_iff_of_cross`). -/
theorem natOfBits_wordAt_eq_of_cross
    {b : PredBody} {s : CrossLeaves} (hs : b.crossLeaves? = some s)
    {rd : ir.Valuation I} (h : ir.HoldsWith rd b)
    (hx0 : (I (ir.domainField s.dx)).toNat 0 = 0) (hx1 : (I (ir.domainField s.dx)).toNat 1 = 1)
    (hy0 : (I (ir.domainField s.dy)).toNat 0 = 0) (hy1 : (I (ir.domainField s.dy)).toNat 1 = 1)
    (hx : ∀ i < (ir.value s.x).size, ir.evalE rd (ir.domainField s.dx) (.leaf s.x) i = 0 ∨
      ir.evalE rd (ir.domainField s.dx) (.leaf s.x) i = 1)
    (hy : ∀ i < (ir.value s.x).size, ir.evalE rd (ir.domainField s.dy) (.leaf s.y) i = 0 ∨
      ir.evalE rd (ir.domainField s.dy) (.leaf s.y) i = 1)
    {w j : ℕ} (hj : j * w + w ≤ (ir.value s.x).size) :
    Bits.natOfBits (ir.wordAt rd (ir.domainField s.dx) s.x w j) =
      Bits.natOfBits (ir.wordAt rd (ir.domainField s.dy) s.y w j) :=
  Bits.natOfBits_eq_of_one_iff fun b =>
    one_iff_of_cross hs h hx0 hx1 hy0 hy1 hx hy (by have := b.isLt; omega)

end

end GordieHowe.RealizedProgram
