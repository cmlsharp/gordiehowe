-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Basic

@[expose] public section

/-!
# GordieHowe: the field form of `mod_p`, for derivations

The rule `fieldDvd k a b` of a derivation: from the field equation `x = y` (premise `k`) in domain
`d` of characteristic `p` and the intervals of `x` (premise `a`) and `y` (premise `b`), whose integer
readings cast to their values, the integer readings of `x` and `y` agree modulo `p`:
`dvd d (x − y) p`. With `congr` this concludes a `mod_q` with `q = p` whose field equation is a
predicate of the program (compiler/mod.h, `m = p`: `assert_zero(lhs − rhs)`). It needs no bound
on the intervals: two integers casting to equal elements of a field of characteristic `p` differ by
a multiple of `p`.
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **`fieldDvd k a b`** in domain `d`: from `eq d x y` (`k`), `ivl d x lo hi` (`a`) and
`ivl d y lo' hi'` (`b`), `x` and `y` of one length: `dvd d (x − y) p`, `p` the characteristic of
`d`'s field. -/
def fieldDvdFact (fs : List Fact) (d k a b : ℕ) : Option Fact :=
  match fs[k]?, fs[a]?, fs[b]? with
  | some (.eq d₀ x y), some (.ivl d₁ x' _ _), some (.ivl d₂ y' _ _) =>
    if d₀ = d ∧ d₁ = d ∧ d₂ = d ∧ x'.beq x = true ∧ y'.beq y = true ∧
        ir.exprLen x = ir.exprLen y ∧ d < ir.domains.length then
      some (.dvd d (.sub x y) (ir.charOf (ir.domainField d)))
    else none
  | _, _, _ => none

end

variable {ir : RealizedProgram} {I : Interp}

/-- **`fieldDvdFact_sound`**: the rule is sound: its fact holds where its premises do, in a field
of the program's characteristic. -/
theorem fieldDvdFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) {rd : ir.Valuation I}
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d k a b : ℕ} {f : Fact}
    (hf : ir.fieldDvdFact fs d k a b = some f) : f.HoldsWith ir rd := by
  unfold fieldDvdFact at hf
  split at hf
  · rename_i d₀ x y d₁ x' lo hi d₂ y' lo' hi' hk ha hb
    split_ifs at hf with hc
    cases hf
    obtain ⟨h0, h1, h2, hx, hy, hlen, hdd⟩ := hc
    subst h0
    subst h1
    subst h2
    have hx' := Expr.eq_of_beq hx
    have hy' := Expr.eq_of_beq hy
    subst hx'
    subst hy'
    have he : Fact.HoldsWith ir rd (.eq d₂ x' y') := hfs _ (List.mem_of_getElem? hk)
    have hix : Fact.HoldsWith ir rd (.ivl d₂ x' lo hi) := hfs _ (List.mem_of_getElem? ha)
    have hiy : Fact.HoldsWith ir rd (.ivl d₂ y' lo' hi') := hfs _ (List.mem_of_getElem? hb)
    have hd := domainField_lt hwf hdd
    have hchar : CharP (I (ir.domainField d₂)).K (ir.charOf (ir.domainField d₂)) := by
      have h := ringChar.charP (I (ir.domainField d₂)).K
      rwa [hI.ringChar _ hd, hI.characteristic _ hd] at h
    intro i hi'
    change i < ir.exprLen x' at hi'
    have hcx := (hix i hi').2.2
    have hcy := (hiy i (hlen ▸ hi')).2.2
    have hsub : ir.evalIntWith rd d₂ (.sub x' y') i =
        ir.evalIntWith rd d₂ x' i - ir.evalIntWith rd d₂ y' i := rfl
    rw [hsub, ← CharP.intCast_eq_zero_iff (I (ir.domainField d₂)).K, Int.cast_sub, hcx, hcy,
      he i hi', sub_self]
  · cases hf

end GordieHowe.RealizedProgram
