-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Core.Circuit

@[expose] public section

/-!
# Circuits whose query intervals differ by a permutation at their start

Two circuits of the core (`Quantum.Circuit`) with queries at the same places, whose `k`-th query
intervals are related by a permutation `σs k` read at the interval's start (`Circuit.SegPerm`):
the interval of the first is that of the second read after `σs k`. The relation is built gate by
gate from the end, a gate `K'` of the first read after the permutation `σs 0` of the rest being the
gate `K` of the second read after a permutation `τ` (a Kraus map read after a permutation at its
input, or a permutation moved past the permutation of the rest).

- `Circuit.SegPerm`, `Circuit.SegPerm.head_apply`, `Circuit.SegPerm.tail`,
  `Circuit.SegPerm.seg_apply`, `Circuit.SegPerm.queries_eq`.
- `Circuit.PermTail`, `Circuit.prefixPerms`, `Circuit.SegPerm.append_same`: a common prefix whose
  gates after its last query are basis permutations, composing to `g`, moves the permutation of
  the rest's first interval back to the start of that interval, conjugated by `g`.
-/

open Matrix

namespace GordieHowe.Quantum

namespace Circuit

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- **The query intervals of `c'` are those of `c` read after the permutations `σs`** (built
gate by gate from the end): the empty circuits with the identities; at a query, the identity for
the interval it ends; at a Kraus map `K'` of `c'` and `K` of `c`, the permutation `τ` at its input
when `K'` followed by the permutation `σs 0` of the rest is `K` read after `τ` (`hK`). -/
inductive SegPerm : (ℕ → Equiv.Perm ι) → Circuit ι → Circuit ι → Prop
  | nil : SegPerm (fun _ => 1) nil nil
  | query {σs : ℕ → Equiv.Perm ι} {c' c : Circuit ι} (h : SegPerm σs c' c) :
      SegPerm (fun i => if i = 0 then 1 else σs (i - 1)) (query c') (query c)
  | kraus {R R' : Type} [Fintype R] [Fintype R'] {σs : ℕ → Equiv.Perm ι} {c' c : Circuit ι}
      (K' : KrausMap R' ι ι) (K : KrausMap R ι ι) (τ : Equiv.Perm ι) (h : SegPerm σs c' c)
      (hK : ∀ ρ, (K' ρ).submatrix (σs 0).symm (σs 0).symm = K (ρ.submatrix τ.symm τ.symm)) :
      SegPerm (fun i => if i = 0 then τ else σs i) (kraus K' c') (kraus K c)

namespace SegPerm

/-- **The intervals before the first query** are related by `σs 0`. -/
theorem head_apply {σs : ℕ → Equiv.Perm ι} {c' c : Circuit ι} (h : SegPerm σs c' c) :
    ∀ ρ, (head c').K ρ = (head c).K (ρ.submatrix (σs 0).symm (σs 0).symm) := by
  induction h with
  | nil =>
    intro ρ
    rfl
  | query _ _ =>
    intro ρ
    rfl
  | kraus K' K τ _ hK ih =>
    intro ρ
    change ((head _).K.comp K') ρ = ((head _).K.comp K) (ρ.submatrix τ.symm τ.symm)
    rw [KrausMap.comp_apply, KrausMap.comp_apply, ih, hK]

/-- **After the first query** the circuits are related by the shifted permutations. -/
theorem tail {σs : ℕ → Equiv.Perm ι} {c' c : Circuit ι} (h : SegPerm σs c' c) :
    SegPerm (fun i => σs (i + 1)) (Circuit.tail c') (Circuit.tail c) := by
  induction h with
  | nil => exact SegPerm.nil
  | @query σs c' c h _ =>
    have e : (fun i => (fun i => if i = 0 then (1 : Equiv.Perm ι) else σs (i - 1)) (i + 1)) =
        σs := funext fun i => by simp
    rw [e]
    exact h
  | @kraus R R' _ _ σs c' c K' K τ h hK ih =>
    have e : (fun i => (fun i => if i = 0 then τ else σs i) (i + 1)) = fun i => σs (i + 1) :=
      funext fun i => by simp
    rw [e]
    exact ih

/-- **The query intervals are related by the permutations `σs`.** -/
theorem seg_apply : ∀ (k : ℕ) {σs : ℕ → Equiv.Perm ι} {c' c : Circuit ι}, SegPerm σs c' c →
    ∀ ρ, (seg c' k).K ρ = (seg c k).K (ρ.submatrix (σs k).symm (σs k).symm)
  | 0, _, _, _, h, ρ => h.head_apply ρ
  | k + 1, _, _, _, h, ρ => seg_apply k h.tail ρ

/-- **The circuits have the same number of queries.** -/
theorem queries_eq {σs : ℕ → Equiv.Perm ι} {c' c : Circuit ι} (h : SegPerm σs c' c) :
    c'.queries = c.queries := by
  induction h with
  | nil => rfl
  | query _ ih => simp [queries, ih]
  | kraus _ _ _ _ _ ih => exact ih

end SegPerm

/-- **The gates after the last query are basis permutations composing to `g`**: a gate `K` there
acts as the permutation `k` (`hK`), applied before the later ones. -/
inductive PermTail : Circuit ι → Equiv.Perm ι → Prop
  | nil : PermTail nil 1
  | query {c : Circuit ι} {g : Equiv.Perm ι} (h : PermTail c g) : PermTail (query c) g
  | krausQ {R : Type} [Fintype R] (K : KrausMap R ι ι) {c : Circuit ι} {g : Equiv.Perm ι}
      (h : PermTail c g) (hq : 0 < c.queries) : PermTail (kraus K c) g
  | krausP {R : Type} [Fintype R] (K : KrausMap R ι ι) (k : Equiv.Perm ι) {c : Circuit ι}
      {g : Equiv.Perm ι} (h : PermTail c g) (hq : c.queries = 0)
      (hK : ∀ ρ, K ρ = ρ.submatrix k.symm k.symm) : PermTail (kraus K c) (g * k)

/-- **The interval permutations of a common prefix `c` with tail `g` before the rest's `σs`**:
the identity on the intervals of `c` before its last query, `σs 0` conjugated by `g` on the
interval across the junction, and `σs` shifted after it. -/
def prefixPerms (n : ℕ) (g : Equiv.Perm ι) (σs : ℕ → Equiv.Perm ι) (i : ℕ) : Equiv.Perm ι :=
  if i < n then 1 else if i = n then g⁻¹ * σs 0 * g else σs (i - n)

omit [Fintype ι] [DecidableEq ι] in
theorem submatrix_perm_mul (ρ : Matrix ι ι ℂ) (a b : Equiv.Perm ι) :
    (ρ.submatrix b.symm b.symm).submatrix a.symm a.symm =
      ρ.submatrix (a * b).symm (a * b).symm := by
  ext x y
  simp [Equiv.Perm.mul_def]

/-- **A common prefix with a permutation tail** (module docstring). -/
theorem SegPerm.append_same {c : Circuit ι} {g : Equiv.Perm ι} (hc : PermTail c g)
    {σs : ℕ → Equiv.Perm ι} {d' d : Circuit ι} (h : SegPerm σs d' d) :
    SegPerm (prefixPerms c.queries g σs) (c ++ d') (c ++ d) := by
  induction hc with
  | nil =>
    have e : prefixPerms (Circuit.nil : Circuit ι).queries 1 σs = σs := funext fun i => by
      unfold prefixPerms
      rcases i with _ | i <;> simp [Circuit.queries]
    rw [e]
    exact h
  | @query c g hc ih =>
    have e : prefixPerms (Circuit.query c).queries g σs =
        fun i => if i = 0 then 1 else prefixPerms c.queries g σs (i - 1) := funext fun i => by
      unfold prefixPerms
      simp only [Circuit.queries]
      rcases i with _ | i
      · simp
      · simp only [Nat.add_sub_cancel, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
          add_lt_add_iff_right, Nat.add_right_cancel_iff]
        split_ifs <;> simp_all [Nat.add_sub_add_right]
    rw [e]
    exact SegPerm.query ih
  | @krausQ R _ K c g hc hq ih =>
    have e : prefixPerms (Circuit.kraus K c).queries g σs =
        fun i => if i = 0 then 1 else prefixPerms c.queries g σs i := funext fun i => by
      show prefixPerms c.queries g σs i = _
      rcases i with _ | i
      · simp [prefixPerms, hq]
      · simp only [Nat.add_one_ne_zero, ↓reduceIte]
    rw [e]
    refine SegPerm.kraus K K 1 ih fun ρ => ?_
    have h0 : prefixPerms c.queries g σs 0 = 1 := by simp [prefixPerms, hq]
    rw [h0]
    rfl
  | @krausP R _ K k c g hc hq hK ih =>
    have e : prefixPerms (Circuit.kraus K c).queries (g * k) σs =
        fun i => if i = 0 then k⁻¹ * prefixPerms c.queries g σs 0 * k else
          prefixPerms c.queries g σs i := funext fun i => by
      unfold prefixPerms
      simp only [Circuit.queries, hq]
      rcases i with _ | i
      · simp [mul_assoc]
      · simp
    rw [e]
    refine SegPerm.kraus K K _ ih fun ρ => ?_
    rw [hK, hK, submatrix_perm_mul, submatrix_perm_mul]
    congr 2 <;> group

end Circuit

end GordieHowe.Quantum
