-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Order.Group.Nat
public import Mathlib.Data.List.Range
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# GordieHowe: sequences of naturals as arithmetic runs, for kernel reduction

`RunVec` is a sequence `ℕ → ℕ` written as arithmetic runs `(count, first value, step)` followed by
a constant tail (`RunVec.get`). The degree checker of the plan's program
(`GordieHowe/Language/RealizedProgram/Check.lean`) keeps the per-coordinate degrees of each expression in a
challenge in this form: most coordinates have the degree of their neighbours, and the powers
`γ^0, …, γ^(n-1)` of a challenge have degrees `0, …, n − 1`, one run. Lists of thousands of runs
would make the kernel recurse thousands deep and hold them in memory.

Each operation the checker uses is a function on runs with a lemma giving `get` of its result
pointwise: `zip` (the coordinatewise sum `segAdd` or maximum `segMax` of aligned runs, the maximum
split where the runs cross), `shift` and `scale` (adding or multiplying a constant), `concat` (the
first `n` coordinates of one sequence, then another), `reindex` (a view by an index map's runs),
`ofList` (one coordinate per element of a list), `chunks` (each block of `C` coordinates
aggregated by `max` or `+`, in one pass), and `maxUpTo` (the largest of the first `n`
coordinates). Runs that continue one another are merged (`merge`). Recursions on two lists or on a
count use fuel or structural recursion, never well-founded recursion, so the kernel reduces them.
-/

namespace GordieHowe.RealizedProgram

/-- **The largest of `g t` for `t < n`** (`0` for `n = 0`). -/
def maxBelow (n : ℕ) (g : ℕ → ℕ) : ℕ := ((List.range n).map g).foldr max 0

theorem maxBelow_zero (g : ℕ → ℕ) : maxBelow 0 g = 0 := rfl

theorem maxBelow_succ (n : ℕ) (g : ℕ → ℕ) : maxBelow (n + 1) g = max (maxBelow n g) (g n) := by
  simp only [maxBelow, List.range_succ, List.map_append, List.foldr_append, List.map_cons,
    List.map_nil, List.foldr_cons, List.foldr_nil, Nat.max_zero]
  generalize g n = x
  induction (List.range n).map g with
  | nil => simp
  | cons a l ih => simp only [List.foldr_cons, ih]; omega

theorem maxBelow_congr {n : ℕ} {g g' : ℕ → ℕ} (h : ∀ t < n, g t = g' t) :
    maxBelow n g = maxBelow n g' := by
  simp only [maxBelow]
  congr 1
  exact List.map_congr_left fun t ht => h t (List.mem_range.1 ht)

theorem maxBelow_add (a b : ℕ) (g : ℕ → ℕ) :
    maxBelow (a + b) g = max (maxBelow a g) (maxBelow b fun t => g (a + t)) := by
  induction b with
  | zero => simp [maxBelow_zero]
  | succ b ih => rw [← Nat.add_assoc, maxBelow_succ, ih, maxBelow_succ]; omega

/-- **A sequence of naturals as arithmetic runs**: each run `(c, a, s)` gives its `c` coordinates
the values `a, a + s, …, a + (c − 1)s`; coordinate `i` past the runs is `tail`
(`RunVec.get`). -/
structure RunVec where
  /-- The runs `(count, first value, step)`. -/
  runs : List (ℕ × ℕ × ℕ)
  /-- The value past the runs. -/
  tail : ℕ
  deriving Inhabited

namespace RunVec

/-- **Coordinate `i` of runs**, `t` past them. -/
def runsGet (t : ℕ) : List (ℕ × ℕ × ℕ) → ℕ → ℕ
  | [], _ => t
  | (c, a, s) :: rs, i => if i < c then a + s * i else runsGet t rs (i - c)

/-- **The number of coordinates the runs cover.** -/
def runsLen : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | (c, _, _) :: rs => c + runsLen rs

/-- **Coordinate `i` of the sequence.** -/
def get (x : RunVec) (i : ℕ) : ℕ := runsGet x.tail x.runs i

/-- **The number of coordinates the runs cover.** -/
def len (x : RunVec) : ℕ := runsLen x.runs

theorem runsGet_of_le (t : ℕ) :
    ∀ (rs : List (ℕ × ℕ × ℕ)) {i : ℕ}, runsLen rs ≤ i → runsGet t rs i = t
  | [], _, _ => rfl
  | (c, a, s) :: rs, i, h => by
    simp only [runsLen] at h
    simp only [runsGet, show ¬ i < c by omega, if_false]
    exact runsGet_of_le t rs (by omega)

theorem get_of_le (x : RunVec) {i : ℕ} (h : x.len ≤ i) : x.get i = x.tail :=
  runsGet_of_le x.tail x.runs h

theorem runsGet_append (t : ℕ) :
    ∀ (rs rs' : List (ℕ × ℕ × ℕ)) (i : ℕ), runsGet t (rs ++ rs') i =
      if i < runsLen rs then runsGet t rs i else runsGet t rs' (i - runsLen rs)
  | [], rs', i => by simp [runsGet, runsLen]
  | (c, a, s) :: rs, rs', i => by
    simp only [List.cons_append, runsGet, runsLen, runsGet_append t rs rs' (i - c)]
    by_cases hc : i < c
    · simp [hc, show i < c + runsLen rs by omega]
    · simp only [hc, if_false]
      by_cases h : i - c < runsLen rs
      · simp [h, show i < c + runsLen rs by omega]
      · simp [h, show ¬ i < c + runsLen rs by omega, Nat.sub_sub]

/-- A run's tail past `n` of its coordinates: coordinate `i` is the run's coordinate `n + i`. -/
theorem run_shift (a s n i : ℕ) : a + s * n + s * i = a + s * (n + i) := by ring

/-! ## Merging runs -/

/-- **Two runs as one**: `(c₁, a₁, s₁)` then `(c₂, a₂, s₂)` continue one arithmetic run when the
second starts where the first's step leads (a single coordinate taking the step that reaches the
next run) and has that step (or one coordinate). -/
def mergeStep (c₁ a₁ s₁ c₂ a₂ s₂ : ℕ) : Option ℕ :=
  if c₁ = 1 then
    if a₁ ≤ a₂ ∧ (c₂ = 1 ∨ s₂ = a₂ - a₁) then some (a₂ - a₁) else none
  else if a₂ = a₁ + s₁ * c₁ ∧ (c₂ = 1 ∨ s₂ = s₁) then some s₁ else none

theorem mergeStep_spec {c₁ a₁ s₁ c₂ a₂ s₂ s : ℕ} (h : mergeStep c₁ a₁ s₁ c₂ a₂ s₂ = some s)
    (hc : 0 < c₁) : ∀ i, i < c₁ + c₂ →
      a₁ + s * i = if i < c₁ then a₁ + s₁ * i else a₂ + s₂ * (i - c₁) := by
  intro i hi
  unfold mergeStep at h
  by_cases h1 : c₁ = 1
  · rw [if_pos h1] at h
    split_ifs at h with h2
    cases h
    subst h1
    obtain ⟨h21, h22⟩ := h2
    obtain ⟨D, rfl⟩ : ∃ D, a₂ = a₁ + D := ⟨a₂ - a₁, by omega⟩
    simp only [Nat.add_sub_cancel_left] at h22 ⊢
    by_cases hi1 : i < 1
    · have : i = 0 := by omega
      subst this
      simp
    · rw [if_neg hi1]
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      rcases h22 with h22 | h22
      · have : j = 0 := by omega
        subst this h22
        simp
      · subst h22
        simp only [Nat.add_sub_cancel]
        ring
  · rw [if_neg h1] at h
    split_ifs at h with h3
    cases h
    obtain ⟨h31, h32⟩ := h3
    split_ifs with hi1
    · rfl
    · subst h31
      rcases h32 with h32 | h32
      · have : i = c₁ := by omega
        subst this
        simp
      · subst h32
        rw [show i = c₁ + (i - c₁) by omega, Nat.mul_add, Nat.add_sub_cancel_left, Nat.add_assoc]

/-- **Runs with adjacent continuing runs merged** (`mergeStep`) and empty runs dropped, starting
from the current run `cur`. -/
def mergeAux : ℕ × ℕ × ℕ → List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ)
  | cur, [] => [cur]
  | (c₁, a₁, s₁), (c₂, a₂, s₂) :: rs =>
    if c₁ = 0 then mergeAux (c₂, a₂, s₂) rs
    else if c₂ = 0 then mergeAux (c₁, a₁, s₁) rs
    else match mergeStep c₁ a₁ s₁ c₂ a₂ s₂ with
      | some s => mergeAux (c₁ + c₂, a₁, s) rs
      | none => (c₁, a₁, s₁) :: mergeAux (c₂, a₂, s₂) rs

theorem runsGet_mergeAux (t : ℕ) :
    ∀ (r : ℕ × ℕ × ℕ) (rs : List (ℕ × ℕ × ℕ)) (i : ℕ),
      runsGet t (mergeAux r rs) i = runsGet t (r :: rs) i
  | _, [], _ => rfl
  | (c₁, a₁, s₁), (c₂, a₂, s₂) :: rs, i => by
    simp only [mergeAux]
    split_ifs with h1 h2
    · rw [runsGet_mergeAux]
      simp [runsGet, h1]
    · rw [runsGet_mergeAux]
      simp only [runsGet, h2]
      split_ifs <;> first | rfl | omega
    · split
      · rename_i s hs
        rw [runsGet_mergeAux]
        simp only [runsGet]
        by_cases hi : i < c₁ + c₂
        · rw [if_pos hi, mergeStep_spec hs (by omega) i hi]
          split_ifs <;> first | rfl | omega
        · rw [if_neg hi, if_neg (by omega), if_neg (by omega), Nat.sub_sub]
      · show (if i < c₁ then a₁ + s₁ * i else runsGet t (mergeAux (c₂, a₂, s₂) rs) (i - c₁)) =
          (if i < c₁ then a₁ + s₁ * i else runsGet t ((c₂, a₂, s₂) :: rs) (i - c₁))
        rw [runsGet_mergeAux]

/-- **Runs with continuing runs merged.** -/
def merge : List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ)
  | [] => []
  | r :: rs => mergeAux r rs

theorem runsGet_merge (t : ℕ) (rs : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    runsGet t (merge rs) i = runsGet t rs i := by
  cases rs with
  | nil => rfl
  | cons r rs => exact runsGet_mergeAux t r rs i

/-! ## Constants and coordinatewise operations -/

/-- **The constant sequence `d`.** -/
def const (d : ℕ) : RunVec := ⟨[], d⟩

@[simp] theorem get_const (d i : ℕ) : (const d).get i = d := rfl

/-- **`k` added at each coordinate.** -/
def shift (k : ℕ) (x : RunVec) : RunVec := ⟨x.runs.map fun r => (r.1, k + r.2.1, r.2.2), k + x.tail⟩

@[simp] theorem get_shift (k : ℕ) (x : RunVec) (i : ℕ) : (x.shift k).get i = k + x.get i := by
  obtain ⟨rs, t⟩ := x
  simp only [shift, get]
  induction rs generalizing i with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨c, a, s⟩ := r
    simp only [List.map_cons, runsGet]
    split_ifs
    · omega
    · exact ih _

/-- **Each coordinate multiplied by `m`.** -/
def scale (m : ℕ) (x : RunVec) : RunVec :=
  ⟨x.runs.map fun r => (r.1, m * r.2.1, m * r.2.2), m * x.tail⟩

@[simp] theorem get_scale (m : ℕ) (x : RunVec) (i : ℕ) : (x.scale m).get i = m * x.get i := by
  obtain ⟨rs, t⟩ := x
  simp only [scale, get]
  induction rs generalizing i with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨c, a, s⟩ := r
    simp only [List.map_cons, runsGet]
    split_ifs
    · ring
    · exact ih _

/-- **A coordinatewise operation on two aligned runs of `c` coordinates**, as runs: `seg c (a, s)
(a', s')` covers `c` coordinates, coordinate `i` being `f (a + s i) (a' + s' i)`. -/
structure Seg (f : ℕ → ℕ → ℕ) where
  /-- The runs. -/
  seg : ℕ → ℕ × ℕ → ℕ × ℕ → List (ℕ × ℕ × ℕ)
  /-- They cover `c` coordinates. -/
  len : ∀ c p q, runsLen (seg c p q) = c
  /-- Coordinate `i` is `f` of the runs' coordinates. -/
  get : ∀ c p q t i, i < c → runsGet t (seg c p q) i = f (p.1 + p.2 * i) (q.1 + q.2 * i)

/-- **`f` at each coordinate of two runs**, `ta` and `tb` past them, with `n` steps of fuel. -/
def zipRuns {f : ℕ → ℕ → ℕ} (S : Seg f) (ta tb : ℕ) :
    ℕ → List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ)
  | 0, _, _ => []
  | _ + 1, [], [] => []
  | n + 1, [], (c, a, s) :: bs => S.seg c (ta, 0) (a, s) ++ zipRuns S ta tb n [] bs
  | n + 1, (c, a, s) :: as, [] => S.seg c (a, s) (tb, 0) ++ zipRuns S ta tb n as []
  | n + 1, (c, a, s) :: as, (c', a', s') :: bs =>
    if c < c' then S.seg c (a, s) (a', s') ++ zipRuns S ta tb n as ((c' - c, a' + s' * c, s') :: bs)
    else if c' < c then
      S.seg c' (a, s) (a', s') ++ zipRuns S ta tb n ((c - c', a + s * c', s) :: as) bs
    else S.seg c (a, s) (a', s') ++ zipRuns S ta tb n as bs

theorem runsGet_seg_append {f : ℕ → ℕ → ℕ} (S : Seg f) (t c : ℕ) (p q : ℕ × ℕ)
    (rs : List (ℕ × ℕ × ℕ)) (i : ℕ) :
    runsGet t (S.seg c p q ++ rs) i =
      if i < c then f (p.1 + p.2 * i) (q.1 + q.2 * i) else runsGet t rs (i - c) := by
  rw [runsGet_append, S.len]
  split_ifs with h
  · exact S.get c p q t i h
  · rfl

theorem runsGet_zipRuns {f : ℕ → ℕ → ℕ} (S : Seg f) (ta tb : ℕ) :
    ∀ (n : ℕ) (as bs : List (ℕ × ℕ × ℕ)), as.length + bs.length ≤ n → ∀ i,
      runsGet (f ta tb) (zipRuns S ta tb n as bs) i = f (runsGet ta as i) (runsGet tb bs i)
  | 0, [], [], _, i => rfl
  | 0, _ :: _, _, h, _ => by simp at h
  | 0, [], _ :: _, h, _ => by simp at h
  | n + 1, [], [], _, i => rfl
  | n + 1, [], (c, a, s) :: bs, h, i => by
    simp only [zipRuns, runsGet_seg_append, runsGet]
    split_ifs
    · simp
    · exact runsGet_zipRuns S ta tb n [] bs (by simp at h ⊢; omega) _
  | n + 1, (c, a, s) :: as, [], h, i => by
    simp only [zipRuns, runsGet_seg_append, runsGet]
    split_ifs
    · simp
    · exact runsGet_zipRuns S ta tb n as [] (by simp at h ⊢; omega) _
  | n + 1, (c, a, s) :: as, (c', a', s') :: bs, h, i => by
    simp only [List.length_cons] at h
    simp only [zipRuns]
    by_cases h1 : c < c'
    · simp only [if_pos h1, runsGet_seg_append]
      rw [runsGet_zipRuns S ta tb n as ((c' - c, a' + s' * c, s') :: bs) (by simp; omega)]
      simp only [runsGet]
      by_cases hi : i < c
      · simp [hi, show i < c' by omega]
      · simp only [hi, if_false]
        by_cases hi' : i < c'
        · simp only [show i - c < c' - c by omega, if_true, hi']
          rw [run_shift, Nat.add_sub_cancel' (by omega)]
        · simp [hi', show ¬ i - c < c' - c by omega, Nat.sub_sub, Nat.add_sub_cancel' h1.le]
    · by_cases h2 : c' < c
      · simp only [if_neg h1, if_pos h2, runsGet_seg_append]
        rw [runsGet_zipRuns S ta tb n ((c - c', a + s * c', s) :: as) bs (by simp; omega)]
        simp only [runsGet]
        by_cases hi : i < c'
        · simp [hi, show i < c by omega]
        · simp only [hi, if_false]
          by_cases hi' : i < c
          · simp only [show i - c' < c - c' by omega, if_true, hi']
            rw [run_shift, Nat.add_sub_cancel' (by omega)]
          · simp [hi', show ¬ i - c' < c - c' by omega, Nat.sub_sub, Nat.add_sub_cancel' h2.le]
      · have hcc : c = c' := by omega
        subst hcc
        simp only [lt_irrefl, if_false, runsGet_seg_append, runsGet]
        by_cases hi : i < c
        · simp [hi]
        · simp only [hi, if_false]
          exact runsGet_zipRuns S ta tb n as bs (by omega) _

/-- **`f` at each coordinate of two sequences**, continuing runs merged. -/
def zip {f : ℕ → ℕ → ℕ} (S : Seg f) (x y : RunVec) : RunVec :=
  ⟨merge (zipRuns S x.tail y.tail (x.runs.length + y.runs.length) x.runs y.runs), f x.tail y.tail⟩

theorem get_zip {f : ℕ → ℕ → ℕ} (S : Seg f) (x y : RunVec) (i : ℕ) :
    (zip S x y).get i = f (x.get i) (y.get i) := by
  simp only [zip, get, runsGet_merge]
  exact runsGet_zipRuns S x.tail y.tail _ x.runs y.runs le_rfl i

/-- **The sum on aligned runs**: one run, of the summed first values and steps. -/
def segAdd : Seg (· + ·) where
  seg c p q := [(c, p.1 + q.1, p.2 + q.2)]
  len c p q := by simp [runsLen]
  get c p q t i hi := by simp only [runsGet, if_pos hi]; ring

/-- **The step past which the run `(a, s)` is at least `(a', s')`**, for `s > s'`: the least `i`
with `a + s i ≥ a' + s' i`. -/
def cross (a s a' s' : ℕ) : ℕ := if a' ≤ a then 0 else (a' - a + (s - s') - 1) / (s - s')

theorem lt_cross_iff {a s a' s' : ℕ} (h : s' < s) (i : ℕ) :
    i < cross a s a' s' ↔ a + s * i < a' + s' * i := by
  unfold cross
  have hD : 0 < s - s' := by omega
  have hs : s * i = s' * i + (s - s') * i := by
    rw [← Nat.add_mul, Nat.add_sub_cancel' h.le]
  have e : i * (s - s') = (s - s') * i := Nat.mul_comm _ _
  split_ifs with ha
  · constructor
    · intro h; omega
    · intro h'; omega
  · rw [Nat.lt_div_iff_mul_lt hD]
    omega

/-- **The larger of two runs over `c` coordinates, the run `(a, s)` of the larger step**: the
other run up to `cross`, then this one. -/
def maxCross (c a s a' s' : ℕ) : List (ℕ × ℕ × ℕ) :=
  if c ≤ cross a s a' s' then [(c, a', s')]
  else [(cross a s a' s', a', s'), (c - cross a s a' s', a + s * cross a s a' s', s)]

theorem runsLen_maxCross (c a s a' s' : ℕ) : runsLen (maxCross c a s a' s') = c := by
  unfold maxCross
  split_ifs <;> simp [runsLen] <;> omega

theorem runsGet_maxCross {a s a' s' : ℕ} (h : s' < s) (c t' i : ℕ) (hi : i < c) :
    runsGet t' (maxCross c a s a' s') i = max (a + s * i) (a' + s' * i) := by
  unfold maxCross
  have hx := lt_cross_iff (a := a) (a' := a') h i
  split_ifs with hc
  · simp only [runsGet, if_pos hi]
    have := hx.1 (by omega)
    omega
  · simp only [runsGet]
    split_ifs with h1 h2
    · have := hx.1 h1
      omega
    · rw [run_shift, Nat.add_sub_cancel' (by omega)]
      have := mt hx.2 h1
      omega
    · omega

/-- **The maximum on aligned runs**: the run of the larger first value for one step, else the run
of the smaller step up to the crossing and then the other. -/
def segMax : Seg max where
  seg c p q :=
    if p.2 = q.2 then [(c, max p.1 q.1, p.2)]
    else if q.2 < p.2 then maxCross c p.1 p.2 q.1 q.2
    else maxCross c q.1 q.2 p.1 p.2
  len c p q := by
    split_ifs
    · simp [runsLen]
    · exact runsLen_maxCross ..
    · exact runsLen_maxCross ..
  get c p q t i hi := by
    split_ifs with h1 h2
    · simp only [runsGet, if_pos hi, h1]
      omega
    · exact runsGet_maxCross h2 c t i hi
    · rw [runsGet_maxCross (by omega) c t i hi, max_comm]

/-! ## Views -/

/-- **The runs past the first `n` coordinates.** -/
def dropRuns : ℕ → List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ)
  | _, [] => []
  | n, (c, a, s) :: rs => if n < c then (c - n, a + s * n, s) :: rs else dropRuns (n - c) rs

theorem runsGet_dropRuns (t : ℕ) :
    ∀ (n : ℕ) (rs : List (ℕ × ℕ × ℕ)) (i : ℕ), runsGet t (dropRuns n rs) i = runsGet t rs (n + i)
  | _, [], _ => rfl
  | n, (c, a, s) :: rs, i => by
    simp only [dropRuns]
    by_cases h : n < c
    · simp only [if_pos h, runsGet]
      by_cases hi : i < c - n
      · simp [hi, show n + i < c by omega, run_shift]
      · simp [hi, show ¬ n + i < c by omega, show i - (c - n) = n + i - c by omega]
    · simp only [if_neg h, runsGet, if_neg (show ¬ n + i < c by omega)]
      rw [runsGet_dropRuns t (n - c) rs i, show n - c + i = n + i - c by omega]

/-- **The first `n` coordinates of runs**, `t` past them. -/
def takeRuns (t : ℕ) : ℕ → List (ℕ × ℕ × ℕ) → List (ℕ × ℕ × ℕ)
  | n, [] => if n = 0 then [] else [(n, t, 0)]
  | n, (c, a, s) :: rs => if n ≤ c then [(n, a, s)] else (c, a, s) :: takeRuns t (n - c) rs

theorem runsLen_takeRuns (t : ℕ) :
    ∀ (n : ℕ) (rs : List (ℕ × ℕ × ℕ)), runsLen (takeRuns t n rs) = n
  | n, [] => by unfold takeRuns; split_ifs with h <;> simp [runsLen, h]
  | n, (c, a, s) :: rs => by
    simp only [takeRuns]
    split_ifs with h
    · simp [runsLen]
    · simp only [runsLen, runsLen_takeRuns t (n - c) rs]; omega

theorem runsGet_takeRuns {t t' : ℕ} :
    ∀ (n : ℕ) (rs : List (ℕ × ℕ × ℕ)) {i : ℕ}, i < n →
      runsGet t' (takeRuns t n rs) i = runsGet t rs i
  | n, [], i, hi => by simp [takeRuns, show n ≠ 0 by omega, runsGet, hi]
  | n, (c, a, s) :: rs, i, hi => by
    simp only [takeRuns]
    split_ifs with h
    · simp [runsGet, hi, show i < c by omega]
    · simp only [runsGet]
      split_ifs with hc
      · rfl
      · exact runsGet_takeRuns (n - c) rs (by omega)

/-- **The first `n` coordinates of `x`, then `y`.** -/
def concat (n : ℕ) (x y : RunVec) : RunVec :=
  if x.runs.isEmpty && y.runs.isEmpty && x.tail == y.tail then y
  else ⟨merge (takeRuns x.tail n x.runs ++ y.runs), y.tail⟩

theorem get_concat (n : ℕ) (x y : RunVec) (i : ℕ) :
    (concat n x y).get i = if i < n then x.get i else y.get (i - n) := by
  unfold concat
  split_ifs with h hi hi
  · obtain ⟨xs, xt⟩ := x
    obtain ⟨ys, yt⟩ := y
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  · obtain ⟨xs, xt⟩ := x
    obtain ⟨ys, yt⟩ := y
    simp only [Bool.and_eq_true, List.isEmpty_iff, beq_iff_eq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl
  · simp only [get, runsGet_merge, runsGet_append, runsLen_takeRuns, if_pos hi]
    exact runsGet_takeRuns _ _ hi
  · simp only [get, runsGet_merge, runsGet_append, runsLen_takeRuns, if_neg hi]

theorem runsLen_map_one {α : Type} (g : α → ℕ) :
    ∀ l : List α, runsLen (l.map fun t => (1, g t, 0)) = l.length
  | [] => rfl
  | a :: l => by simp only [List.map_cons, runsLen, runsLen_map_one g l, List.length_cons]; omega

theorem runsGet_map_one {α : Type} (g : α → ℕ) (t' : ℕ) (d : α) :
    ∀ (l : List α) (i : ℕ), runsGet t' (l.map fun x => (1, g x, 0)) i =
      if i < l.length then g (l.getD i d) else t'
  | [], i => by simp [runsGet]
  | x :: l, i => by
    simp only [List.map_cons, runsGet, runsGet_map_one g t' d l, List.length_cons]
    by_cases hi : i < 1
    · simp [show i = 0 by omega]
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      simp

/-- **`g x` at coordinate `i` for the `i`-th element `x` of a list**, continuing runs merged, `t'`
past them. -/
def ofList {α : Type} (l : List α) (g : α → ℕ) (t' : ℕ) : RunVec :=
  ⟨merge (l.map fun x => (1, g x, 0)), t'⟩

theorem get_ofList {α : Type} (l : List α) (g : α → ℕ) (t' : ℕ) (d : α) (i : ℕ) :
    (ofList l g t').get i = if i < l.length then g (l.getD i d) else t' := by
  simp only [ofList, get, runsGet_merge, runsGet_map_one g t' d]

/-- **A run's entries as a view**: the run `(s, d, c)` of an index map (entries `s + d·t`, `t < c`)
read from `x`: one constant run for `d = 0`, the slice `[s, s + c)` for `d = 1`, one coordinate per
entry otherwise. -/
def reindexRun (x : RunVec) : ℕ × ℤ × ℕ → List (ℕ × ℕ × ℕ)
  | (s, d, c) =>
    if d = 0 then [(c, x.get s, 0)]
    else if d = 1 then takeRuns x.tail c (dropRuns s x.runs)
    else (List.range c).map fun t : ℕ => (1, x.get ((s : ℤ) + d * (t : ℤ)).toNat, 0)

theorem runsLen_reindexRun (x : RunVec) (r : ℕ × ℤ × ℕ) : runsLen (reindexRun x r) = r.2.2 := by
  obtain ⟨s, d, c⟩ := r
  simp only [reindexRun]
  split_ifs
  · simp [runsLen]
  · exact runsLen_takeRuns _ _ _
  · rw [runsLen_map_one, List.length_range]

theorem runsGet_reindexRun (x : RunVec) (t' : ℕ) (r : ℕ × ℤ × ℕ) {i : ℕ} (hi : i < r.2.2) :
    runsGet t' (reindexRun x r) i = x.get ((r.1 + r.2.1 * i : ℤ).toNat) := by
  obtain ⟨s, d, c⟩ := r
  simp only at hi ⊢
  simp only [reindexRun]
  split_ifs with h0 h1
  · simp [runsGet, hi, h0]
  · subst h1
    rw [runsGet_takeRuns _ _ hi, runsGet_dropRuns]
    simp only [get]
    congr 1
    omega
  · rw [runsGet_map_one _ _ 0, List.length_range, if_pos hi, List.getD_eq_getElem?_getD,
      List.getElem?_range hi, Option.getD_some]

/-- **Entry `i` of an index map's runs** (`IndexMap.entry`, restated over the run type). -/
def entryOf : List (ℕ × ℤ × ℕ) → ℕ → ℕ
  | [], _ => 0
  | (s, d, c) :: rest, i => if i < c then ((s : ℤ) + d * i).toNat else entryOf rest (i - c)

theorem runsGet_flatMap_reindexRun (x : RunVec) (t' : ℕ) :
    ∀ (m : List (ℕ × ℤ × ℕ)) (i : ℕ), runsGet t' (m.flatMap (reindexRun x)) i =
        if i < (m.map (·.2.2)).sum then x.get (entryOf m i) else t'
  | [], i => by simp [runsGet]
  | (s, d, c) :: rest, i => by
    simp only [List.flatMap_cons, runsGet_append, runsLen_reindexRun, entryOf, List.map_cons,
      List.sum_cons]
    by_cases hi : i < c
    · simp only [if_pos hi, if_pos (show i < c + (rest.map (·.2.2)).sum by omega)]
      exact runsGet_reindexRun x t' (s, d, c) hi
    · simp only [if_neg hi, runsGet_flatMap_reindexRun x t' rest (i - c)]
      by_cases h : i - c < (rest.map (·.2.2)).sum
      · simp [h, show i < c + (rest.map (·.2.2)).sum by omega]
      · simp [h, show ¬ i < c + (rest.map (·.2.2)).sum by omega]

theorem entryOf_of_le :
    ∀ (m : List (ℕ × ℤ × ℕ)) {i : ℕ}, (m.map (·.2.2)).sum ≤ i → entryOf m i = 0
  | [], _, _ => rfl
  | (s, d, c) :: rest, i, h => by
    simp only [List.map_cons, List.sum_cons] at h
    simp only [entryOf, if_neg (show ¬ i < c by omega)]
    exact entryOf_of_le rest (by omega)

/-- **The view of `x` by an index map**: coordinate `i` reads `x` at entry `i` (entry `0` past
the map), continuing runs merged. -/
def reindex (m : List (ℕ × ℤ × ℕ)) (x : RunVec) : RunVec :=
  if x.runs.isEmpty then x else ⟨merge (m.flatMap (reindexRun x)), x.get 0⟩

theorem get_reindex (m : List (ℕ × ℤ × ℕ)) (x : RunVec) (i : ℕ) :
    (reindex m x).get i = x.get (entryOf m i) := by
  unfold reindex
  split_ifs with hx
  · obtain ⟨xs, t⟩ := x
    simp only [List.isEmpty_iff] at hx
    subst hx
    rfl
  · change runsGet (x.get 0) (merge (m.flatMap (reindexRun x))) i = _
    rw [runsGet_merge, runsGet_flatMap_reindexRun x _ m i]
    split_ifs with h
    · rfl
    · rw [entryOf_of_le m (by omega)]

/-! ## Blocks -/

/-- **An aggregation of arithmetic runs**: an operation `op` with neutral `0`, and `ap k a s` its
fold over `a, a + s, …, a + (k − 1)s`. -/
structure Agg where
  /-- The operation. -/
  op : ℕ → ℕ → ℕ
  /-- The fold over an arithmetic run. -/
  ap : ℕ → ℕ → ℕ → ℕ
  /-- `op` is associative. -/
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  /-- `0` is neutral on the left. -/
  zero_op : ∀ a, op 0 a = a
  /-- `0` is neutral on the right. -/
  op_zero : ∀ a, op a 0 = a
  /-- `ap k a s` is the fold over the run. -/
  ap_eq : ∀ k a s, ap k a s = ((List.range k).map fun t => a + s * t).foldr op 0

namespace Agg

variable (A : Agg)

/-- **The aggregate of `g t` for `t < n`.** -/
def below (n : ℕ) (g : ℕ → ℕ) : ℕ := ((List.range n).map g).foldr A.op 0

theorem foldr_op (a : ℕ) : ∀ l : List ℕ, l.foldr A.op a = A.op (l.foldr A.op 0) a
  | [] => by simp [A.zero_op]
  | x :: l => by simp only [List.foldr_cons, foldr_op a l, A.assoc]

theorem below_add (a b : ℕ) (g : ℕ → ℕ) :
    A.below (a + b) g = A.op (A.below a g) (A.below b fun t => g (a + t)) := by
  simp only [below, List.range_add, List.map_append, List.foldr_append, List.map_map]
  rw [foldr_op]
  rfl

theorem below_congr {n : ℕ} {g g' : ℕ → ℕ} (h : ∀ t < n, g t = g' t) :
    A.below n g = A.below n g' := by
  simp only [below]
  congr 1
  exact List.map_congr_left fun t ht => h t (List.mem_range.1 ht)

theorem below_ap (n a s : ℕ) : A.below n (fun t => a + s * t) = A.ap n a s := (A.ap_eq n a s).symm

theorem below_const (n d : ℕ) : A.below n (fun _ => d) = A.ap n d 0 := by
  rw [← below_ap]
  simp

/-- **`max`, its fold over a nondecreasing run being the last value** (`0` for an empty run). -/
def max : Agg where
  op := Max.max
  ap k a s := if k = 0 then 0 else a + s * (k - 1)
  assoc a b c := Nat.max_assoc a b c
  zero_op a := Nat.zero_max a
  op_zero a := Nat.max_zero a
  ap_eq k a s := by
    change _ = maxBelow k _
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [maxBelow_succ, ← ih]
      simp only [Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel]
      by_cases hk : k = 0
      · subst hk
        simp
      · rw [if_neg hk]
        have : s * (k - 1) ≤ s * k := Nat.mul_le_mul_left _ (by omega)
        omega

/-- The sum of `0, …, k − 1`, `k (k − 1) / 2`. -/
theorem sum_range_id (k : ℕ) : ((List.range k).map fun t => t).sum = k * (k - 1) / 2 := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
      Nat.add_sub_cancel]
    rcases k with _ | k
    · rfl
    · rw [show (k + 1 + 1) * (k + 1) = (k + 1) * k + 2 * (k + 1) by ring,
        Nat.add_mul_div_left _ _ (by omega)]
      simp only [Nat.add_sub_cancel]

/-- **`+`, its fold over a run being `k a + s k (k − 1) / 2`.** -/
def add : Agg where
  op := (· + ·)
  ap k a s := k * a + s * (k * (k - 1) / 2)
  assoc := Nat.add_assoc
  zero_op := Nat.zero_add
  op_zero := Nat.add_zero
  ap_eq k a s := by
    rw [← List.sum_eq_foldr, ← sum_range_id]
    induction k with
    | zero => simp
    | succ k ih =>
      simp only [List.range_succ, List.map_append, List.sum_append, List.map_cons, List.map_nil,
        List.sum_cons, List.sum_nil, Nat.add_zero]
      rw [← ih]
      ring

theorem max_below (n : ℕ) (g : ℕ → ℕ) : Agg.max.below n g = maxBelow n g := rfl

theorem add_below (n : ℕ) (g : ℕ → ℕ) : Agg.add.below n g = ((List.range n).map g).sum := by
  simp only [below, add, List.sum_eq_foldr]

end Agg

/-- **The aggregate of the first `n` coordinates of runs, and the runs past them** (`t` past the
runs). -/
def chunk (A : Agg) (t : ℕ) : ℕ → List (ℕ × ℕ × ℕ) → ℕ × List (ℕ × ℕ × ℕ)
  | 0, rs => (0, rs)
  | n + 1, [] => (A.ap (n + 1) t 0, [])
  | n + 1, (c, a, s) :: rs =>
    if n + 1 ≤ c then (A.ap (n + 1) a s, (c - (n + 1), a + s * (n + 1), s) :: rs)
    else
      let r := chunk A t (n + 1 - c) rs
      (A.op (A.ap c a s) r.1, r.2)

theorem chunk_spec (A : Agg) (t : ℕ) :
    ∀ (n : ℕ) (rs : List (ℕ × ℕ × ℕ)),
      (chunk A t n rs).1 = A.below n (runsGet t rs) ∧
        ∀ i, runsGet t (chunk A t n rs).2 i = runsGet t rs (n + i)
  | 0, rs => by cases rs <;> exact ⟨rfl, fun i => by simp [chunk]⟩
  | n + 1, [] => ⟨by simp only [chunk, runsGet]; exact (A.below_const _ _).symm, fun i => rfl⟩
  | n + 1, (c, a, s) :: rs => by
    simp only [chunk]
    split_ifs with h
    · refine ⟨?_, fun i => ?_⟩
      · rw [← A.below_ap]
        exact A.below_congr fun s' hs => by simp [runsGet, show s' < c by omega]
      · simp only [runsGet]
        by_cases hi : i < c - (n + 1)
        · simp [hi, show n + 1 + i < c by omega, run_shift]
        · simp [hi, show ¬ n + 1 + i < c by omega,
            show i - (c - (n + 1)) = n + 1 + i - c by omega]
    · obtain ⟨h1, h2⟩ := chunk_spec A t (n + 1 - c) rs
      refine ⟨?_, fun i => ?_⟩
      · change A.op (A.ap c a s) (chunk A t (n + 1 - c) rs).1 = _
        rw [h1]
        conv_rhs => rw [show n + 1 = c + (n + 1 - c) by omega]
        rw [A.below_add, ← A.below_ap]
        congr 1
        · exact A.below_congr fun s' hs => by simp [runsGet, hs]
        · refine A.below_congr fun s' _ => ?_
          simp [runsGet, show ¬ c + s' < c by omega]
      · rw [h2, runsGet, if_neg (by omega), show n + 1 - c + i = n + 1 + i - c by omega]

/-- **The aggregates of `m` consecutive blocks of `C` coordinates of runs.** -/
def chunksAux (A : Agg) (t C : ℕ) : ℕ → List (ℕ × ℕ × ℕ) → List ℕ
  | 0, _ => []
  | m + 1, rs =>
    let r := chunk A t C rs
    r.1 :: chunksAux A t C m r.2

theorem length_chunksAux (A : Agg) (t C : ℕ) :
    ∀ (m : ℕ) (rs : List (ℕ × ℕ × ℕ)), (chunksAux A t C m rs).length = m
  | 0, _ => rfl
  | m + 1, rs => by simp [chunksAux, length_chunksAux A t C m]

theorem getD_chunksAux (A : Agg) (t C : ℕ) :
    ∀ (m : ℕ) (rs : List (ℕ × ℕ × ℕ)) {b : ℕ}, b < m →
      (chunksAux A t C m rs).getD b 0 = A.below C fun s => runsGet t rs (b * C + s)
  | 0, _, _, h => absurd h (Nat.not_lt_zero _)
  | m + 1, rs, b, h => by
    obtain ⟨h1, h2⟩ := chunk_spec A t C rs
    cases b with
    | zero => simp [chunksAux, h1]
    | succ b =>
      simp only [chunksAux, List.getD_cons_succ]
      rw [getD_chunksAux A t C m _ (by omega)]
      exact A.below_congr fun s _ => by rw [h2]; congr 1; ring

/-- **Uniform runs of `R` coordinates**, run `b` of value `g b`. -/
theorem runsGet_map_rows (t' R : ℕ) (hR : 0 < R) (g : ℕ → ℕ) :
    ∀ (l : List ℕ) (i : ℕ), runsGet t' (l.map fun x => (R, g x, 0)) i =
      if i < l.length * R then g (l.getD (i / R) 0) else t'
  | [], i => by simp [runsGet]
  | x :: l, i => by
    simp only [List.map_cons, runsGet, List.length_cons]
    by_cases hi : i < R
    · simp [hi, show i < (l.length + 1) * R by nlinarith, Nat.div_eq_of_lt hi]
    · simp only [hi, if_false, runsGet_map_rows t' R hR g l (i - R)]
      have hd : i / R = (i - R) / R + 1 := by
        rw [show i = (i - R) + R by omega, Nat.add_div_right _ hR, Nat.add_sub_cancel]
      by_cases h : i - R < l.length * R
      · simp [h, show i < (l.length + 1) * R by rw [Nat.succ_mul]; omega, hd]
      · simp [h, show ¬ i < (l.length + 1) * R by rw [Nat.succ_mul]; omega]

/-- **Blocks of `C` coordinates of `x`, each aggregated by `A`, spread over `R ≥ 1` coordinates
and shifted by `a`**: coordinate `i` is `a` plus the aggregate of block `i / R`, continuing runs
merged. With `R = 0` every coordinate reads block `0` (the operators' `i / R` is `0`). -/
def chunks (A : Agg) (C R a : ℕ) (x : RunVec) : RunVec :=
  if R = 0 then const (a + A.below C fun s => x.get s)
  else if (x.runs.isEmpty || C == 0) = true then const (a + A.ap C x.tail 0)
  else
    ⟨merge ((chunksAux A x.tail C ((x.len + C - 1) / C) x.runs).map fun y => (R, a + y, 0)),
      a + A.ap C x.tail 0⟩

theorem get_chunks (A : Agg) (C R a : ℕ) (x : RunVec) (i : ℕ) :
    (chunks A C R a x).get i = a + A.below C fun s => x.get (i / R * C + s) := by
  by_cases hR : R = 0
  · simp [chunks, hR]
  by_cases hx : x.runs = [] ∨ C = 0
  · have h : (x.runs.isEmpty || C == 0) = true := by
      rcases hx with hx | hx <;> simp [hx]
    unfold chunks
    rw [if_neg hR, if_pos h, get_const, ← A.below_const]
    congr 1
    rcases hx with hx | hC
    · obtain ⟨xs, t⟩ := x
      simp only at hx
      subst hx
      rfl
    · subst hC
      rfl
  · have h : (x.runs.isEmpty || C == 0) = false := by
      simp only [not_or] at hx
      simp [hx.1, hx.2]
    have hC : 0 < C := by omega
    unfold chunks
    rw [if_neg hR, if_neg (by simp [h])]
    change runsGet _ (merge ((chunksAux A x.tail C _ x.runs).map fun y => (R, a + y, 0))) i = _
    rw [runsGet_merge, runsGet_map_rows _ R (Nat.pos_of_ne_zero hR), length_chunksAux]
    split_ifs with hi
    · rw [getD_chunksAux A x.tail C _ x.runs (b := i / R)
        (Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi))]
      rfl
    · change a + A.ap C x.tail 0 = _
      rw [← A.below_const]
      congr 1
      refine A.below_congr fun s _ => (get_of_le x ?_).symm
      have hm : (x.len + C - 1) / C ≤ i / R := by
        by_contra h
        exact hi (calc i < (i / R + 1) * R :=
            Nat.lt_mul_of_div_lt (Nat.lt_succ_self _) (Nat.pos_of_ne_zero hR)
          _ ≤ (x.len + C - 1) / C * R := Nat.mul_le_mul_right _ (by omega))
      have : x.len ≤ (x.len + C - 1) / C * C := by
        have h1 := Nat.div_add_mod (x.len + C - 1) C
        have h2 := Nat.mod_lt (x.len + C - 1) hC
        rw [Nat.mul_comm]
        omega
      calc x.len ≤ (x.len + C - 1) / C * C := this
        _ ≤ i / R * C := Nat.mul_le_mul_right _ hm
        _ ≤ i / R * C + s := Nat.le_add_right _ _

/-! ## The largest coordinate -/

/-- **The largest value of runs**: each run's last value (runs being nondecreasing), among runs of
positive count. -/
def runsMax : List (ℕ × ℕ × ℕ) → ℕ
  | [] => 0
  | (c, a, s) :: rs => Max.max (if c = 0 then 0 else a + s * (c - 1)) (runsMax rs)

theorem runsMax_eq (t : ℕ) :
    ∀ rs : List (ℕ × ℕ × ℕ), runsMax rs = maxBelow (runsLen rs) (runsGet t rs)
  | [] => rfl
  | (c, a, s) :: rs => by
    simp only [runsMax, runsLen, maxBelow_add, runsMax_eq t rs]
    congr 1
    · rw [← Agg.max_below]
      change Agg.max.ap c a s = _
      rw [← Agg.below_ap]
      exact Agg.below_congr _ fun s' hs => by simp [runsGet, hs]
    · exact maxBelow_congr fun s' _ => by simp [runsGet, show ¬ c + s' < c by omega]

/-- **The largest of the first `n` coordinates of `x`.** -/
def maxUpTo (n : ℕ) (x : RunVec) : ℕ := runsMax (takeRuns x.tail n x.runs)

theorem maxUpTo_eq (n : ℕ) (x : RunVec) : maxUpTo n x = maxBelow n x.get := by
  rw [maxUpTo, runsMax_eq x.tail, runsLen_takeRuns]
  exact maxBelow_congr fun s hs => runsGet_takeRuns _ _ hs

end RunVec

end GordieHowe.RealizedProgram
