-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Rules

@[expose] public section

/-!
# GordieHowe: solving an integer equation for one atom's interval, for derivations

The rule `ivlSolve k ks a j lo hi` of a derivation: from the integer equation `e₁ = e₂` (premise
`k`, `intEq`), the integer linear form of `e₁ − e₂` (`ilin`: sums, differences and constant
multiples read centred, every other node an atom) is `c + s · a + Σ_t c_t · t` with `a`'s
coefficients summing to `s = ±1`; the other atoms' intervals are the `ivl` premises `ks`, consumed
in the form's order (`solveIvl`). Then `a = −s (c + Σ_t c_t · t)` lies in the interval arithmetic
of that sum, within `[lo, hi]`. The premise `j`, an `ivl` fact of `a`, supplies the cast of `a`'s
integer reading to its value, which an integer equation does not give.
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-- **The integer linear form of an expression** at the characteristic `p`: its constant and its
terms, sums, differences and constant multiples (read centred) expanded, any other node a term of
coefficient `1`. -/
def ilin (p : ℕ) : Expr → ℤ × List (ℤ × Expr)
  | .add a b =>
    let x := ilin p a
    let y := ilin p b
    (x.1 + y.1, x.2 ++ y.2)
  | .sub a b =>
    let x := ilin p a
    let y := ilin p b
    (x.1 - y.1, x.2 ++ y.2.map fun t => (-t.1, t.2))
  | .scale (.const c) a =>
    let x := ilin p a
    (centeredZ p c * x.1, x.2.map fun t => (centeredZ p c * t.1, t.2))
  | e => (0, [(1, e)])

/-- **The premises of `ivlSolve`**: the `ivl` facts of domain `d` at `ks`, each of an expression
at least `n` long. -/
def solvePrem (fs : List Fact) (d n : ℕ) : List ℕ → Option (List (Expr × Ivl))
  | [] => some []
  | k :: ks =>
    match fs[k]? with
    | some (.ivl d' x a b) =>
      if d' = d ∧ n ≤ ir.exprLen x then (solvePrem fs d n ks).map ((x, ⟨a, b⟩) :: ·) else none
    | _ => none

end

/-- **The coefficient of `a` and the interval of the other terms** of a linear form, the other
terms' intervals the premises `ps` consumed in order. -/
def solveIvl (a : Expr) : List (ℤ × Expr) → List (Expr × Ivl) → Option (ℤ × Ivl)
  | [], [] => some (0, ⟨0, 0⟩)
  | [], _ :: _ => none
  | (c, t) :: ts, ps =>
    if t.beq a = true then (solveIvl a ts ps).map fun r => (r.1 + c, r.2)
    else
      match ps with
      | (x, K) :: ps' =>
        if x.beq t = true then (solveIvl a ts ps').map fun r => (r.1, r.2.add (K.smul c))
        else none
      | [] => none

section

variable (ir : RealizedProgram)

/-- **`ivlSolve k ks a j lo hi`** in domain `d`: from `intEq d e₁ e₂` (`k`), the `ivl` facts `ks`
of the other atoms of `e₁ − e₂` and an `ivl` fact of `a` (`j`): `ivl d a lo hi`. -/
def ivlSolveFact (fs : List Fact) (d k : ℕ) (ks : List ℕ) (a : Expr) (j : ℕ) (lo hi : ℤ) :
    Option Fact :=
  match fs[k]?, fs[j]? with
  | some (.intEq d₀ e₁ e₂), some (.ivl d₁ a' _ _) =>
    if d₀ = d ∧ d₁ = d ∧ d < ir.domains.length ∧ a'.beq a = true ∧
        ir.exprLen a ≤ ir.exprLen e₁ then
      match solvePrem ir fs d (ir.exprLen a) ks with
      | some ps =>
        match solveIvl a (ilin (ir.charOf (ir.domainField d)) (.sub e₁ e₂)).2 ps with
        | some (s, J) =>
          let c := (ilin (ir.charOf (ir.domainField d)) (.sub e₁ e₂)).1
          if s = 1 ∧ lo ≤ -(c + J.hi) ∧ -(c + J.lo) ≤ hi ∨
              s = -1 ∧ lo ≤ c + J.lo ∧ c + J.hi ≤ hi then
            some (.ivl d a lo hi)
          else none
        | none => none
      | none => none
    else none
  | _, _ => none

end

variable {ir : RealizedProgram} {I : Interp}

theorem list_sum_map_neg' {α : Type*} (g : α → ℤ) :
    ∀ l : List α, (l.map fun x => -(g x)).sum = -(l.map g).sum
  | [] => by simp
  | x :: l => by simp only [List.map_cons, List.sum_cons, list_sum_map_neg' g l]; ring

/-- **The integer linear form reads as the expression** (`ilin`), constants read centred. -/
theorem ilin_sound {rd : ir.Valuation I} {d : ℕ}
    (hcen : ∀ c, (I (ir.domainField d)).centered c = centeredZ (ir.charOf (ir.domainField d)) c)
    (i : ℕ) : ∀ e : Expr,
      ir.evalIntWith rd d e i = (ilin (ir.charOf (ir.domainField d)) e).1 +
        ((ilin (ir.charOf (ir.domainField d)) e).2.map fun t => t.1 * ir.evalIntWith rd d t.2 i).sum
  | .add a b => by
    simp only [ilin, evalIntWith_add, ilin_sound hcen i a, ilin_sound hcen i b, List.map_append,
      List.sum_append]
    ring
  | .sub a b => by
    simp only [ilin, evalIntWith_sub, ilin_sound hcen i a, ilin_sound hcen i b, List.map_append,
      List.sum_append, List.map_map, Function.comp_def, neg_mul,
      list_sum_map_neg' (fun (t : ℤ × Expr) => t.1 * ir.evalIntWith rd d t.2 i)]
    ring
  | .scale (.const c) a => by
    simp only [ilin, evalIntWith_scale_const, hcen, ilin_sound hcen i a, List.map_map,
      Function.comp_def, mul_assoc, List.sum_map_mul_left]
    ring
  | .leaf _ => by simp [ilin]
  | .scale (.node _ _) _ => by simp [ilin]
  | .mul _ _ => by simp [ilin]
  | .reindex _ _ => by simp [ilin]
  | .concat _ _ => by simp [ilin]
  | .linear _ _ => by simp [ilin]
  | .prod _ _ => by simp [ilin]
  | .mux _ _ _ => by simp [ilin]
  | .apply _ _ => by simp [ilin]
  | .ref _ => by simp [ilin]
  | .logic _ _ _ => by simp [ilin]

/-- **`solveIvl_sound`**: the terms read as `s · a` plus a sum in the interval, where each
premise's expression reads within its interval. -/
theorem solveIvl_sound {a : Expr} (v : Expr → ℤ) :
    ∀ {ts : List (ℤ × Expr)} {ps : List (Expr × Ivl)} {s : ℤ} {J : Ivl},
      solveIvl a ts ps = some (s, J) → (∀ x ∈ ps, v x.1 ∈ x.2) →
        ∃ R ∈ J, (ts.map fun t => t.1 * v t.2).sum = s * v a + R
  | [], [], s, J, h, _ => by
    simp only [solveIvl, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨0, by simp, by simp⟩
  | [], _ :: _, _, _, h, _ => by simp [solveIvl] at h
  | (c, t) :: ts, ps, s, J, h, hps => by
    simp only [solveIvl] at h
    split_ifs at h with ht
    · obtain ⟨⟨s', J'⟩, h', he⟩ := Option.map_eq_some_iff.1 h
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      obtain ⟨R, hR, hsum⟩ := solveIvl_sound v h' hps
      obtain rfl := Expr.eq_of_beq ht
      refine ⟨R, hR, ?_⟩
      simp only [List.map_cons, List.sum_cons, hsum]
      ring
    · split at h
      · rename_i x K ps'
        split_ifs at h with hx
        obtain ⟨⟨s', J'⟩, h', he⟩ := Option.map_eq_some_iff.1 h
        simp only [Prod.mk.injEq] at he
        obtain ⟨rfl, rfl⟩ := he
        obtain ⟨R, hR, hsum⟩ := solveIvl_sound v h' fun y hy => hps y (List.mem_cons_of_mem _ hy)
        obtain rfl := Expr.eq_of_beq hx
        have hK : v x ∈ K := hps _ List.mem_cons_self
        refine ⟨R + c * v x, Ivl.add_mem hR (Ivl.smul_mem c hK), ?_⟩
        simp only [List.map_cons, List.sum_cons, hsum]
        ring
      · cases h

/-- **The premises of `ivlSolve` hold** at every coordinate below `n`. -/
theorem solvePrem_sound {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd)
    {d n : ℕ} : ∀ {ks : List ℕ} {ps : List (Expr × Ivl)}, solvePrem ir fs d n ks = some ps →
      ∀ i < n, ∀ x ∈ ps, ir.evalIntWith rd d x.1 i ∈ x.2
  | [], ps, h, i, _, x, hm => by
    simp only [solvePrem, Option.some.injEq] at h
    subst h
    cases hm
  | k :: ks, ps, h, i, hi, x, hm => by
    simp only [solvePrem] at h
    split at h
    · rename_i d' y lo hi' hk
      split_ifs at h with hc
      obtain ⟨ps', h', rfl⟩ := Option.map_eq_some_iff.1 h
      obtain ⟨rfl, hn⟩ := hc
      rcases List.mem_cons.1 hm with rfl | hm
      · have hy : Fact.HoldsWith ir rd (.ivl d' y lo hi') := hfs _ (List.mem_of_getElem? hk)
        obtain ⟨h1, h2, -⟩ := hy i (by omega)
        exact ⟨h1, h2⟩
      · exact solvePrem_sound hfs h' i hi x hm
    · cases h

/-- **`ivlSolveFact_sound`**: the rule is sound: its fact holds where its premises do. -/
theorem ivlSolveFact_sound (hI : I.Registered ir) (hwf : ir.WellFormed) {rd : ir.Valuation I}
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d k : ℕ} {ks : List ℕ} {a : Expr}
    {j : ℕ} {lo hi : ℤ} {f : Fact} (hf : ir.ivlSolveFact fs d k ks a j lo hi = some f) :
    f.HoldsWith ir rd := by
  unfold ivlSolveFact at hf
  split at hf
  · rename_i d₀ e₁ e₂ d₁ a' lo' hi' hk hj
    split_ifs at hf with hc
    obtain ⟨h0, h1, hd, ha, hlen⟩ := hc
    subst h0
    subst h1
    obtain rfl := Expr.eq_of_beq ha
    have hf' := domainField_lt hwf hd
    have hcen : ∀ c, (I (ir.domainField d₁)).centered c =
        centeredZ (ir.charOf (ir.domainField d₁)) c := fun c => by
      rw [FieldInterp.centered_eq, hI.characteristic _ hf']
    have he : Fact.HoldsWith ir rd (.intEq d₁ e₁ e₂) := hfs _ (List.mem_of_getElem? hk)
    have hca : Fact.HoldsWith ir rd (.ivl d₁ a' lo' hi') := hfs _ (List.mem_of_getElem? hj)
    split at hf
    · rename_i ps hps
      split at hf
      · rename_i s J hs
        dsimp only at hf
        split_ifs at hf with hsJ
        cases hf
        intro i hi
        obtain ⟨R, hR, hsum⟩ := solveIvl_sound (fun x => ir.evalIntWith rd d₁ x i) hs
          (solvePrem_sound hfs hps i hi)
        have h0 := ilin_sound (rd := rd) hcen i (.sub e₁ e₂)
        rw [evalIntWith_sub, he i (by omega), sub_self, hsum] at h0
        refine ⟨?_, ?_, (hca i hi).2.2⟩ <;>
        · rcases hsJ with ⟨rfl, h1, h2⟩ | ⟨rfl, h1, h2⟩ <;>
          · obtain ⟨hR1, hR2⟩ := hR
            linarith
      · cases hf
    · cases hf
  · cases hf

end GordieHowe.RealizedProgram
