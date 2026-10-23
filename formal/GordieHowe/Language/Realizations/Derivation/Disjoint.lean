-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Basic

@[expose] public section

/-!
# GordieHowe: the interval of a sum of disjoint supports, for derivations

The rule `ivlDisjoint a b` of a derivation: from the intervals `[lo, hi]` of `x` (premise `a`) and
`[lo', hi']` of `y` (premise `b`), where `x` and `y` are sums of masked views of disjoint supports
(`RealizedProgram.maskSupp`: at each coordinate one of them reads a zero constant), the sum `x + y`
has the interval `[min lo lo', max hi hi']`: at each coordinate it is one of the two. This is how the joined operand of a
cross-field `equal`, the sum of the `Bit` views of its two halves, reads within `[0, 1]`, where the
interval walk's sum rule would give `[0, 2]`.
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The coordinates where a sum of masked views may be nonzero**: a masked view
`reindex m (concat A (leaf z))`, `z` a constant holding `0` and `A` any expression of length `n`
at the lengths `rl`, is nonzero only where its entry reads `A` (`mapNz n`); a sum of two such sums
only on the union of theirs, when the two are disjoint (`disjointNz`). As `maskedNz`, with any
first operand of the concatenation. -/
def maskSupp (rl : ℕ → ℕ) : Expr → Option (List (ℕ × ℕ))
  | .reindex m (.concat A (.leaf z)) =>
    if ir.zeroConstB z then some (mapNz (Expr.len ir rl A) 0 m) else none
  | .add e e' =>
    match maskSupp rl e, maskSupp rl e' with
    | some L, some L' => if disjointNz L L' then some (L ++ L') else none
    | _, _ => none
  | _ => none

/-- **`ivlDisjoint a b`** in domain `d`: from `ivl d x lo hi` (`a`) and `ivl d y lo' hi'` (`b`), `x`
and `y` of one length and well-formed shape, masked views of disjoint supports: `ivl d (x + y)
(min lo lo') (max hi hi')`. -/
def ivlDisjointFact (fs : List Fact) (d a b : ℕ) : Option Fact :=
  match fs[a]?, fs[b]? with
  | some (.ivl d₁ x lo hi), some (.ivl d₂ y lo' hi') =>
    if d₁ = d ∧ d₂ = d ∧ ir.exprLen x = ir.exprLen y ∧ ir.exprShapeOk x = true ∧
        ir.exprShapeOk y = true ∧ (ir.maskSupp (ir.refLen ir.exprs.length) (.add x y)).isSome = true
    then some (.ivl d (.add x y) (min lo lo') (max hi hi'))
    else none
  | _, _ => none

end

variable {ir : RealizedProgram} {I : Interp}

/-- **A sum of masked views is `0` off its nonzero coordinates** (`maskSupp`), where the integer
readings of the zero constants are `0` (`evalInt_eq_zero_of_maskedNz` with any first operand). -/
theorem evalInt_eq_zero_of_maskSupp {f : ℕ} {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    (hzero : ∀ z, ir.zeroConstB z = true → ∀ i, il z i = 0) {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ} :
    ∀ (e : Expr) {L : List (ℕ × ℕ)}, ir.maskSupp rl e = some L → ir.shapeOkWith rl e = true →
      ∀ {i : ℕ}, i < Expr.len ir rl e → (∀ iv ∈ L, ¬ (iv.1 ≤ i ∧ i < iv.2)) →
        Expr.evalInt ir f leaf il iref rl e i = 0
  | .reindex m e, L, h, _, i, hi, hL => by
    unfold maskSupp at h
    split at h
    · rename_i _ m' A z heq
      cases heq
      split_ifs at h with hz
      cases h
      simp only [Expr.len] at hi
      simp only [Expr.evalInt]
      by_cases ha : m.entry i < Expr.len ir rl A
      · obtain ⟨iv, hiv, h1, h2⟩ := mem_mapNz m 0 hi ha
        exact absurd ⟨by simpa using h1, by simpa using h2⟩ (hL iv hiv)
      · simp only [ha, ↓reduceIte]
        exact hzero z hz _
    · rename_i heq
      cases heq
    · cases h
  | .add e e', L, h, hs, i, hi, hL => by
    simp only [maskSupp] at h
    cases h₁ : ir.maskSupp rl e with
    | none => simp [h₁] at h
    | some L₁ =>
      cases h₂ : ir.maskSupp rl e' with
      | none => simp [h₁, h₂] at h
      | some L₂ =>
        simp only [h₁, h₂] at h
        split_ifs at h with hd
        cases h
        simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
        simp only [Expr.len] at hi
        simp only [Expr.evalInt]
        rw [evalInt_eq_zero_of_maskSupp hzero e h₁ hs.1.1 hi
            fun iv hiv => hL iv (List.mem_append_left _ hiv),
          evalInt_eq_zero_of_maskSupp hzero e' h₂ hs.1.2 (hs.2 ▸ hi)
            fun iv hiv => hL iv (List.mem_append_right _ hiv)]
        rfl
  | .leaf _, _, h, _, _, _, _ | .sub _ _, _, h, _, _, _, _ | .scale _ _, _, h, _, _, _, _
  | .mul _ _, _, h, _, _, _, _ | .concat _ _, _, h, _, _, _, _ | .linear _ _, _, h, _, _, _, _
  | .prod _ _, _, h, _, _, _, _ | .mux _ _ _, _, h, _, _, _, _ | .apply _ _, _, h, _, _, _, _
  | .ref _, _, h, _, _, _, _ | .logic _ _ _, _, h, _, _, _, _ => by
    simp [maskSupp] at h

/-- **One of two summands is `0`** at each coordinate below the length, where their sum has a
support (`maskSupp`) and the integer readings of the zero constants are `0`. -/
theorem evalInt_maskSupp_zero {f : ℕ} {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    (hzero : ∀ z, ir.zeroConstB z = true → ∀ i, il z i = 0) {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ}
    {e e' : Expr} (hm : (ir.maskSupp rl (.add e e')).isSome = true)
    (hs : ir.shapeOkWith rl e = true) (hs' : ir.shapeOkWith rl e' = true)
    (hlen : Expr.len ir rl e = Expr.len ir rl e') {i : ℕ} (hi : i < Expr.len ir rl e) :
    Expr.evalInt ir f leaf il iref rl e i = 0 ∨ Expr.evalInt ir f leaf il iref rl e' i = 0 := by
  obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 hm
  simp only [maskSupp] at hL
  cases h₁ : ir.maskSupp rl e with
  | none => simp [h₁] at hL
  | some L₁ =>
    cases h₂ : ir.maskSupp rl e' with
    | none => simp [h₁, h₂] at hL
    | some L₂ =>
      simp only [h₁, h₂] at hL
      split_ifs at hL with hd
      by_cases hin : ∃ iv ∈ L₁, iv.1 ≤ i ∧ i < iv.2
      · obtain ⟨iv, hiv, hiv'⟩ := hin
        exact .inr (evalInt_eq_zero_of_maskSupp hzero e' h₂ hs' (hlen ▸ hi)
          fun iv' hiv'' => not_mem_of_disjointNz hd hiv hiv'' hiv')
      · push Not at hin
        exact .inl (evalInt_eq_zero_of_maskSupp hzero e h₁ hs hi
          fun iv hiv h => absurd h.2 (not_lt.2 (hin iv hiv h.1)))

/-- **`ivlDisjointFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlDisjointFact_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d a b : ℕ} {f : Fact}
    (hf : ir.ivlDisjointFact fs d a b = some f) : f.HoldsWith ir rd := by
  unfold ivlDisjointFact at hf
  split at hf
  · rename_i d₁ x lo hi d₂ y lo' hi' ha hb
    split_ifs at hf with hc
    cases hf
    obtain ⟨h1, h2, hlen, hsx, hsy, hm⟩ := hc
    subst h1
    subst h2
    have hx : Fact.HoldsWith ir rd (.ivl d₂ x lo hi) := hfs _ (List.mem_of_getElem? ha)
    have hy : Fact.HoldsWith ir rd (.ivl d₂ y lo' hi') := hfs _ (List.mem_of_getElem? hb)
    intro i hi'
    change i < ir.exprLen x at hi'
    have hiy : i < ir.exprLen y := hlen ▸ hi'
    obtain ⟨hxlo, hxhi, hxc⟩ := hx i hi'
    obtain ⟨hylo, hyhi, hyc⟩ := hy i hiy
    have hz := evalInt_maskSupp_zero (ir := ir) (f := ir.domainField d₂) (leaf := rd)
      (iref := ir.refInt rd (ir.domainField d₂) ir.exprs.length)
      (fun z hz i => intOf_of_zeroConstB rd hz i) hm
      (by rw [← exprShapeOk_eq]; exact hsx) (by rw [← exprShapeOk_eq]; exact hsy) hlen hi'
    have hsum : ir.evalIntWith rd d₂ (.add x y) i =
        ir.evalIntWith rd d₂ x i + ir.evalIntWith rd d₂ y i := rfl
    refine ⟨?_, ?_, ?_⟩
    · rw [hsum]
      rcases hz with h0 | h0
      · change ir.evalIntWith rd d₂ x i = 0 at h0
        rw [h0]
        omega
      · change ir.evalIntWith rd d₂ y i = 0 at h0
        rw [h0]
        omega
    · rw [hsum]
      rcases hz with h0 | h0
      · change ir.evalIntWith rd d₂ x i = 0 at h0
        rw [h0]
        omega
      · change ir.evalIntWith rd d₂ y i = 0 at h0
        rw [h0]
        omega
    · rw [hsum, Int.cast_add, hxc, hyc]
      rfl
  · cases hf

end GordieHowe.RealizedProgram
