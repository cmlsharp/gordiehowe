-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Check
public import GordieHowe.Language.RealizedProgram.OpsLemmas

@[expose] public section

/-!
# GordieHowe: intervals of the integer readings of expressions

An interval evaluator for the integer reading of an expression (`Expr.evalInt`, the reading of a
`mod_q`), as the C++ interval propagation computes it (compiler/range.h, `lin_interval`):

* **Intervals** (`Ivl`): closed intervals of integers, with sums, differences, products, constant
  multiples, sums of `w` terms and hulls, each containing the results of its operation on members
  (`Ivl.add_mem`, `Ivl.mul_mem`, …).
* **The evaluator** (`Expr.ivl`): an interval for every coordinate of an expression, from the
  intervals of the values it reads (`leafI`) and of the shared expressions (`refI`), on sums,
  differences, constant multiples by constants below the characteristic, products, views,
  concatenations, sums of groups (`sum w`, `batched b (sum w)`, `NamedOp.sumWidth`) and shared
  expressions; `none` (no interval) on every other form. Through the shared expressions it is
  computed once per entry (`GordieHowe.RealizedProgram.ivlT`, `GordieHowe.RealizedProgram.ivlOf`).
* **Soundness** (`GordieHowe.RealizedProgram.evalIntWith_mem_ivlOf`): on a well-formed expression, every coordinate of
  the integer reading lies in the interval, given intervals of the values' coordinates
  (`hleaf`).
* **Casts** (`GordieHowe.RealizedProgram.evalIntWith_cast`): where every value read has its integer reading cast to
  the field equal to its value (`hcast`: prime-subfield reads), the integer reading of an expression
  with an interval casts to its value in the field.

**The integer readings of a field** (`Interp.Lawful`): the integer reading of an element is below
the characteristic, inverts the cast of a natural below it, constants below it decode to their
casts, and the elements of a prime-subfield node are the casts of their readings. A property of the
model (the interpretation of the fields), discharged once per concrete field.
-/

namespace GordieHowe.RealizedProgram

open Export

/-! ## Intervals -/

/-- **A closed interval of integers** `[lo, hi]`. -/
structure Ivl where
  /-- The lower end. -/
  lo : ℤ
  /-- The upper end. -/
  hi : ℤ
  deriving Repr, DecidableEq, Inhabited

namespace Ivl

/-- Membership in an interval. -/
instance : Membership ℤ Ivl := ⟨fun J x => J.lo ≤ x ∧ x ≤ J.hi⟩

theorem mem_def {x : ℤ} {J : Ivl} : x ∈ J ↔ J.lo ≤ x ∧ x ≤ J.hi := Iff.rfl

@[simp] theorem mem_mk {x lo hi : ℤ} : x ∈ (⟨lo, hi⟩ : Ivl) ↔ lo ≤ x ∧ x ≤ hi := Iff.rfl

/-- **The sum** of two intervals. -/
def add (J J' : Ivl) : Ivl := ⟨J.lo + J'.lo, J.hi + J'.hi⟩

/-- **The difference** of two intervals. -/
def sub (J J' : Ivl) : Ivl := ⟨J.lo - J'.hi, J.hi - J'.lo⟩

/-- **The product** of two intervals: the hull of the four products of their ends. -/
def mul (J J' : Ivl) : Ivl :=
  ⟨min (min (J.lo * J'.lo) (J.lo * J'.hi)) (min (J.hi * J'.lo) (J.hi * J'.hi)),
    max (max (J.lo * J'.lo) (J.lo * J'.hi)) (max (J.hi * J'.lo) (J.hi * J'.hi))⟩

/-- **A constant multiple** of an interval. -/
def smul (c : ℤ) (J : Ivl) : Ivl := mul ⟨c, c⟩ J

/-- **The sums of `w` members** of an interval. -/
def nsmul (w : ℕ) (J : Ivl) : Ivl := ⟨w * J.lo, w * J.hi⟩

/-- **The hull** of two intervals. -/
def hull (J J' : Ivl) : Ivl := ⟨min J.lo J'.lo, max J.hi J'.hi⟩

/-- **The interval lies within `[lo, hi]`.** -/
def Within (J : Ivl) (lo hi : ℤ) : Prop := lo ≤ J.lo ∧ J.hi ≤ hi

instance (J : Ivl) (lo hi : ℤ) : Decidable (J.Within lo hi) := inferInstanceAs (Decidable (_ ∧ _))

variable {x y : ℤ} {J J' : Ivl}

theorem add_mem (hx : x ∈ J) (hy : y ∈ J') : x + y ∈ J.add J' :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem sub_mem (hx : x ∈ J) (hy : y ∈ J') : x - y ∈ J.sub J' :=
  ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

/-- A product with a member of `[a, b]` lies between the products with `a` and `b`. -/
theorem min_le_mul_of_mem {a b x : ℤ} (hx : a ≤ x ∧ x ≤ b) (y : ℤ) :
    min (a * y) (b * y) ≤ x * y ∧ x * y ≤ max (a * y) (b * y) := by
  rcases le_total 0 y with hy | hy
  · exact ⟨(min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 hy),
      (mul_le_mul_of_nonneg_right hx.2 hy).trans (le_max_right _ _)⟩
  · exact ⟨(min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 hy),
      (mul_le_mul_of_nonpos_right hx.1 hy).trans (le_max_left _ _)⟩

theorem mul_mem (hx : x ∈ J) (hy : y ∈ J') : x * y ∈ J.mul J' := by
  obtain ⟨h1, h2⟩ := min_le_mul_of_mem hx y
  have hl := min_le_mul_of_mem hy J.lo
  have hh := min_le_mul_of_mem hy J.hi
  simp only [mul_comm _ J.lo, mul_comm _ J.hi] at hl hh
  exact ⟨(le_min ((min_le_left _ _).trans hl.1) ((min_le_right _ _).trans hh.1)).trans h1,
    h2.trans (max_le (hl.2.trans (le_max_left _ _)) (hh.2.trans (le_max_right _ _)))⟩

theorem smul_mem (c : ℤ) (hy : y ∈ J) : c * y ∈ J.smul c :=
  mul_mem ⟨le_rfl, le_rfl⟩ hy

theorem hull_mem_left (hx : x ∈ J) : x ∈ J.hull J' :=
  ⟨(min_le_left _ _).trans hx.1, hx.2.trans (le_max_left _ _)⟩

theorem hull_mem_right (hx : x ∈ J') : x ∈ J.hull J' :=
  ⟨(min_le_right _ _).trans hx.1, hx.2.trans (le_max_right _ _)⟩

/-- **A sum of `w` members** lies in `nsmul w`. -/
theorem sum_mem {w : ℕ} {g : Fin w → ℤ} (hg : ∀ s, g s ∈ J) : ∑ s, g s ∈ J.nsmul w := by
  constructor
  · have := Finset.card_nsmul_le_sum Finset.univ g J.lo fun s _ => (hg s).1
    simpa [nsmul] using this
  · have := Finset.sum_le_card_nsmul Finset.univ g J.hi fun s _ => (hg s).2
    simpa [nsmul] using this

theorem mem_of_within {lo hi : ℤ} (hJ : J.Within lo hi) (hx : x ∈ J) : lo ≤ x ∧ x ≤ hi :=
  ⟨hJ.1.trans hx.1, hx.2.trans hJ.2⟩

end Ivl

/-- **The symmetric interval** `[−m, m]`. -/
def Ivl.sym (m : ℕ) : Ivl := ⟨-(m : ℤ), m⟩

/-- **The magnitude of an interval**: the larger absolute value of its ends. -/
def Ivl.mag (J : Ivl) : ℕ := max J.lo.natAbs J.hi.natAbs

theorem Ivl.abs_le_mag {x : ℤ} {J : Ivl} (hx : x ∈ J) : |x| ≤ J.mag := by
  obtain ⟨h1, h2⟩ := hx
  simp only [Ivl.mag, Nat.cast_max, Int.natCast_natAbs]
  rw [abs_le]
  constructor
  · have := neg_abs_le J.lo
    have := le_max_left |J.lo| |J.hi|
    linarith
  · have := le_abs_self J.hi
    have := le_max_right |J.lo| |J.hi|
    linarith

theorem Ivl.mem_sym {x : ℤ} {m : ℕ} : x ∈ Ivl.sym m ↔ |x| ≤ m := by
  rw [Ivl.sym, Ivl.mem_mk, abs_le]

/-- **An optional interval lies within `[lo, hi]`**: some interval within it (`none` lies within
nothing). -/
def IvlWithin : Option Ivl → ℤ → ℤ → Prop
  | some J, lo, hi => J.Within lo hi
  | none, _, _ => False

instance (o : Option Ivl) (lo hi : ℤ) : Decidable (IvlWithin o lo hi) := by
  cases o <;> unfold IvlWithin <;> infer_instance

/-- **A constant read in `(−p/2, p/2)`** (`FieldInterp.centered` at the characteristic `p`). -/
def centeredZ (p c : ℕ) : ℤ := if 2 * c < p then c else (c : ℤ) - p

theorem FieldInterp.centered_eq (F : FieldInterp) (c : ℕ) :
    F.centered c = centeredZ F.spec.characteristic c := rfl

/-- **A centred constant casts to the constant** in characteristic `p`. -/
theorem centeredZ_cast {K : Type} [Ring K] (p : ℕ) [CharP K p] (c : ℕ) :
    ((centeredZ p c : ℤ) : K) = (c : K) := by
  unfold centeredZ
  split_ifs
  · simp
  · simp [CharP.cast_eq_zero]

/-- **The integer reading of a small integer's cast is the integer**: `coefInt (z : K) = z` for
`2 |z| < p`, where the integer reading inverts the cast of a natural below `p`. -/
theorem FieldInterp.coefInt_intCast {F : FieldInterp} {p : ℕ} (hp : F.spec.characteristic = p)
    (hchar : CharP F.K p) (htn : ∀ k < p, F.toNat (k : F.K) = k) {z : ℤ} (hz : 2 * |z| < p) :
    F.coefInt (z : F.K) = z := by
  rw [FieldInterp.coefInt, FieldInterp.centered_eq, hp]
  rcases le_or_gt 0 z with h0 | h0
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    rw [abs_of_nonneg h0] at hz
    rw [Int.cast_natCast, htn n (by omega)]
    unfold centeredZ
    rw [if_pos (by omega)]
  · rw [abs_of_neg h0] at hz
    set m : ℕ := ((p : ℤ) + z).toNat with hm
    have hm' : ((m : ℕ) : ℤ) = (p : ℤ) + z := by
      rw [hm, Int.toNat_of_nonneg (by omega)]
    have hcast : ((z : ℤ) : F.K) = ((m : ℕ) : F.K) := by
      rw [← Int.cast_natCast, hm', Int.cast_add, Int.cast_natCast, CharP.cast_eq_zero, zero_add]
    rw [hcast, htn m (by omega)]
    unfold centeredZ
    rw [if_neg (by omega)]
    omega

/-- **`getD` below the length** is the entry. -/
theorem getD_of_lt {α : Type*} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- **`getD` past the length** is the default. -/
theorem getD_of_ge {α : Type*} {l : List α} {i : ℕ} (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-! ## Index maps stay in range -/

namespace IndexMap

/-- **Every entry of an index map in range of `n` is below `n`.** -/
theorem entry_lt_of_inRange : ∀ {m : IndexMap} {n : ℕ}, m.inRange n = true →
    ∀ {i : ℕ}, i < m.size → m.entry i < n
  | [], _, _, _, hi => by simp [size] at hi
  | (s, d, c) :: rest, n, h, i, hi => by
    simp only [inRange, List.all_cons, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
      decide_eq_true_eq] at h
    simp only [size, List.map_cons, List.sum_cons] at hi
    simp only [entry]
    split_ifs with hic
    · rcases h.1 with hc | ⟨⟨h0, hs⟩, hl⟩
      · omega
      · have hc1 : ((c - 1 : ℕ) : ℤ) = (c : ℤ) - 1 := by omega
        rw [hc1] at h0 hl
        have hi' : (i : ℤ) ≤ (c : ℤ) - 1 := by omega
        have hi0 : (0 : ℤ) ≤ i := by omega
        have hbound : (s : ℤ) + d * i < n ∧ 0 ≤ (s : ℤ) + d * i := by
          rcases le_total 0 d with hd | hd
          · constructor
            · nlinarith
            · nlinarith
          · constructor
            · nlinarith
            · nlinarith
        omega
    · exact entry_lt_of_inRange (m := rest) (by simpa [inRange] using h.2) (by simp [size]; omega)

end IndexMap

/-! ## Sums of groups -/

/-- **The width of a named operator that sums groups**: `w` for `sum w` and `batched b (sum w)`
with `b ≥ 1` (output coordinate `j` the sum of coordinates `j w, …, j w + w − 1`); none
otherwise. -/
def NamedOp.sumWidth : NamedOp → Option ℕ
  | .sum w => some w
  | .batched b (.sum w) => if 0 < b then some w else none
  | _ => none

/-! ## Masked views and the MAC convolution -/

section

variable (ir : RealizedProgram)

/-- **Value `z` is a constant holding `0`** at every entry (so at every coordinate). -/
def zeroConstB (z : ℕ) : Bool :=
  match (ir.value z).kind with
  | .constant es => es.all (· == 0)
  | _ => false

/-- **Two masked views of disjoint supports**: `reindex m (concat (leaf a) (leaf z))` and
`reindex m' (concat (leaf a') (leaf z'))`, with `z`, `z'` constants holding `0`, such that at every
coordinate `i` of `m` at least one of the two reads its zero constant (`m(i) ≥ |a|` or
`m'(i) ≥ |a'|`). Their sum is then, at each coordinate, one of the two views (a disjoint
superposition, as the C++'s `Bit` views of a cross-field `equal`'s operand). -/
def maskedPairB : Expr → Expr → Bool
  | .reindex m (.concat (.leaf a) (.leaf z)), .reindex m' (.concat (.leaf a') (.leaf z')) =>
    ir.zeroConstB z && ir.zeroConstB z' &&
      (List.range m.size).all fun i =>
        decide ((ir.value a).size ≤ m.entry i) || decide ((ir.value a').size ≤ m'.entry i)
  | _, _ => false

end

/-- **The coordinates of a run that read below `A`**: for the run `(s, d, c)` at offset `o` of an
index map, an interval `[lo, hi)` of coordinates holding every `o + t` (`t < c`) whose entry
`s + d t` is below `A`: the first `⌈(A − s) / d⌉` coordinates for `d > 0`, the whole run for `d ≤ 0`
when `s < A`, none for `d ≥ 0` when `s ≥ A`, and the whole run otherwise. -/
def runNz (A o : ℕ) : ℕ × ℤ × ℕ → ℕ × ℕ
  | (s, d, c) =>
    if s < A then
      if 0 < d then (o, o + min c ((A - s + d.toNat - 1) / d.toNat)) else (o, o + c)
    else if 0 ≤ d then (o, o) else (o, o + c)

/-- **The coordinates of an index map that read below `A`**: the intervals `runNz` of its runs, the
first at offset `o`. -/
def mapNz (A : ℕ) : ℕ → IndexMap → List (ℕ × ℕ)
  | _, [] => []
  | o, r :: rest => runNz A o r :: mapNz A (o + r.2.2) rest

/-- **Two lists of intervals `[lo, hi)` are disjoint**, pairwise (an empty interval is disjoint from
every interval). -/
def disjointNz (L L' : List (ℕ × ℕ)) : Bool :=
  L.all fun a => L'.all fun b =>
    decide (a.2 ≤ a.1) || decide (b.2 ≤ b.1) || decide (a.2 ≤ b.1) || decide (b.2 ≤ a.1)

theorem runNz_mem {A o s c t : ℕ} {d : ℤ} (ht : t < c) (hA : ((s : ℤ) + d * t).toNat < A) :
    (runNz A o (s, d, c)).1 ≤ o + t ∧ o + t < (runNz A o (s, d, c)).2 := by
  simp only [runNz]
  have hdt : 0 ≤ d → 0 ≤ d * t := fun hd => mul_nonneg hd (Int.natCast_nonneg t)
  split_ifs with hs hd hd'
  · obtain ⟨D, rfl⟩ := Int.eq_ofNat_of_zero_le hd.le
    simp only [Int.toNat_natCast]
    have hD : 0 < D := by exact_mod_cast hd
    have hlt : s + D * t < A := by
      have : ((s : ℤ) + (D : ℤ) * t).toNat = s + D * t := by
        rw [show ((s : ℤ) + (D : ℤ) * t) = ((s + D * t : ℕ) : ℤ) by push_cast; ring]
        exact Int.toNat_natCast _
      omega
    refine ⟨by omega, ?_⟩
    have : t + 1 ≤ (A - s + D - 1) / D := by
      refine (Nat.le_div_iff_mul_le hD).2 ?_
      rw [Nat.succ_mul, Nat.mul_comm t D]
      omega
    omega
  · exact ⟨by omega, by omega⟩
  · have := hdt hd'
    omega
  · exact ⟨by omega, by omega⟩

/-- **A coordinate whose entry reads below `A`** lies in one of the intervals `mapNz`. -/
theorem mem_mapNz {A : ℕ} : ∀ (m : IndexMap) (o : ℕ) {i : ℕ}, i < m.size → m.entry i < A →
    ∃ iv ∈ mapNz A o m, iv.1 ≤ o + i ∧ o + i < iv.2
  | [], _, i, hi, _ => by simp [IndexMap.size] at hi
  | (s, d, c) :: rest, o, i, hi, hA => by
    simp only [IndexMap.size, List.map_cons, List.sum_cons] at hi
    simp only [IndexMap.entry] at hA
    split_ifs at hA with hic
    · exact ⟨_, List.mem_cons_self .., runNz_mem hic hA⟩
    · obtain ⟨iv, hiv, h1, h2⟩ := mem_mapNz rest (o + c) (i := i - c)
        (by simp only [IndexMap.size]; omega) hA
      refine ⟨iv, List.mem_cons_of_mem _ hiv, ?_, ?_⟩ <;> omega

/-- **Disjoint intervals share no coordinate.** -/
theorem not_mem_of_disjointNz {L L' : List (ℕ × ℕ)} (h : disjointNz L L' = true) {i : ℕ}
    {a b : ℕ × ℕ} (ha : a ∈ L) (hb : b ∈ L') (hia : a.1 ≤ i ∧ i < a.2) : ¬ (b.1 ≤ i ∧ i < b.2) := by
  have := List.all_eq_true.1 (List.all_eq_true.1 h a ha) b hb
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  omega

section

variable (ir : RealizedProgram)

/-- **A sum of masked views of disjoint supports**, and the coordinates where it may be nonzero: a
masked view `reindex m (concat (leaf a) (leaf z))` (`z` a constant holding `0`) is nonzero only
where its entry reads `a` (`mapNz`); a sum of two such sums is nonzero only on the union, when
their coordinates are disjoint (`disjointNz`). At every coordinate at most one view of the sum is
nonzero (the C++'s `Bit` views of a cross-field `equal`'s operand, one per joined copy). -/
def maskedNz : Expr → Option (List (ℕ × ℕ))
  | .reindex m (.concat (.leaf a) (.leaf z)) =>
    if ir.zeroConstB z then some (mapNz (ir.value a).size 0 m) else none
  | .add e e' =>
    match maskedNz e, maskedNz e' with
    | some L, some L' => if disjointNz L L' then some (L ++ L') else none
    | _, _ => none
  | _ => none

end

/-- **The largest row sum of the MAC convolution's matrices** on bits, `Conv.convMax w taps`,
computed from the packed row sums (`Conv.accPacked`, lanes of `32` bits;
`Conv.convMax_eq_packed`) for distinct taps other than `w`; none when the taps repeat or contain `w`,
or a lane could overflow. -/
def macConvMax? (w : ℕ) (taps : List ℕ) : Option ℕ :=
  if (w :: taps).Nodup ∧ (2 * w - 1) * w < 2 ^ 32 then
    some (Finset.univ.sup fun m : Fin w => Conv.lane 32 (Conv.accPacked 32 w (Conv.phiList 32 w taps)).2 m)
  else none

theorem convMax_of_macConvMax? {w c : ℕ} {taps : List ℕ} (h : macConvMax? w taps = some c) :
    Conv.convMax w taps.toFinset = c := by
  unfold macConvMax? at h
  split_ifs at h with hn
  rw [Option.some_inj] at h
  rw [← h]
  exact Conv.convMax_eq_packed (by norm_num) hn.2 hn.1 rfl

/-- **The interval of the MAC convolution** `macConv r w nch taps` at the characteristic `p`, on an
operand with interval `J`: `[0, nch · c]`, `c = convMax w taps` (`macConvMax?`), when the operand
lies within `[0, 1]`, `w > 0` and `2 w < p` (each matrix entry is a natural at most `w`,
`Conv.matrix_le_width`, read as itself); none for any other operator. -/
def NamedOp.macIvl (p : ℕ) (J : Ivl) : NamedOp → Option Ivl
  | .macConv _ w nch taps =>
    if J.Within 0 1 ∧ 0 < w ∧ 2 * w < p then
      match macConvMax? w taps with
      | some c => some ⟨0, nch * c⟩
      | none => none
    else none
  | _ => none

/-- **The sum of a digit decomposition's weights** `Σ_{l<k} base^l`. -/
def digitsWeight (base k : ℕ) : ℕ := ∑ l ∈ Finset.range k, base ^ l

/-- **A sum with nonnegative weights of members of an interval** lies in the interval scaled by the
weights' sum. -/
theorem Ivl.sum_weight_mem {k : ℕ} (c : Fin k → ℕ) (y : Fin k → ℤ) {J : Ivl} (hy : ∀ l, y l ∈ J) :
    ∑ l, (c l : ℤ) * y l ∈ (⟨(∑ l, c l : ℕ) * J.lo, (∑ l, c l : ℕ) * J.hi⟩ : Ivl) := by
  push_cast
  rw [Finset.sum_mul, Finset.sum_mul]
  exact ⟨Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hy l).1 (Nat.cast_nonneg _),
    Finset.sum_le_sum fun l _ => mul_le_mul_of_nonneg_left (hy l).2 (Nat.cast_nonneg _)⟩

/-- **The interval of a public polynomial operand in its form** (`NamedOp.formPoly`): its values'
interval `leafI h` in coefficient form; none in transform form. -/
def formIvl (leafI : ℕ → Option Ivl) (h : ℕ) : ConvForm → Option Ivl
  | .coefficients => leafI h
  | .ntt _ => none

/-- **The largest absolute row sum** of `R` rows of `W` entries `es` (row-major, `0` past the
entries), each entry read centred at `p` (`centeredZ`). -/
def rowAbsMax (p W : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | R + 1, es =>
    max ((es.take W).map fun c => (centeredZ p c).natAbs).sum (rowAbsMax p W R (es.drop W))

/-- **The interval of a row-form operator** (`rowDot` by a constant matrix, `acyclicConv` by a
public operand with nonnegative entries) at the characteristic `p`, on an operand with interval
`J` (compiler/range.h, `lin_interval`: an operator's row bound):

* `rowDot M R W` with `M` a constant of entries `es` read centred, `R W` within its size, each entry
  of magnitude below `p / 2`: `[−S m, S m]`, `S` the largest absolute row sum (`rowAbsMax`) and `m`
  the magnitude of `J`;
* `acyclicConv h lx` with `h`'s interval within `[0, H]`, `2 H < p`: each row has at most
  `min(lx, lh)` entries, in `[0, H]`, so `[min(lo, 0) r, max(hi, 0) r]` for `r = min(lx, lh) H`.

None for any other operator. -/
def NamedOp.rowFormIvl (ir : RealizedProgram) (leafI : ℕ → Option Ivl) (p : ℕ) (J : Ivl) :
    NamedOp → Option Ivl
  | .rowDot M R W =>
    match (ir.value M).kind with
    | .constant es =>
      if (leafI M).isSome ∧ 0 < p ∧ R * W ≤ (ir.value M).size ∧
          es.all (fun c => decide (2 * |centeredZ p c| < p)) then
        some (Ivl.sym (rowAbsMax p W R es * J.mag))
      else none
    | _ => none
  | .acyclicConv h lx => (leafI h).bind fun A =>
    if 0 ≤ A.lo ∧ 0 ≤ A.hi ∧ 2 * A.hi < p then
      some ⟨min J.lo 0 * ((min lx (ir.value h).size : ℕ) * A.hi),
        max J.hi 0 * ((min lx (ir.value h).size : ℕ) * A.hi)⟩
    else none
  | _ => none

/-- **The interval of a public polynomial operator** (`negacyclicConv` in coefficient form,
`polyMatVec`, `polyBroadcast` on coefficients) at the characteristic `p`, on an operand with
interval `J`: `[−m, m]` with `m = cols · M · mag J`, `M` the magnitude of the public operand's
interval (`formIvl` for `negacyclicConv`: in coefficient form), when `2 M < p` (each matrix entry is `0` or `±` a coefficient of the public operand, read
as itself); none for any other operator. -/
def NamedOp.polyIvl (ir : RealizedProgram) (leafI : ℕ → Option Ivl) (p : ℕ)
    (J : Ivl) : NamedOp → Option Ivl
  | .batched b op =>
    match op with
    | .fromDigits k base =>
      if 0 < b ∧ base < p ∧ (List.range k).all (fun l => decide (2 * base ^ l < p)) then
        some ⟨(digitsWeight base k : ℤ) * J.lo, (digitsWeight base k : ℤ) * J.hi⟩
      else none
    | op => if 0 < b then NamedOp.rowFormIvl ir leafI p J op else none
  | .negacyclicConv h form => (formIvl leafI h form).bind fun A =>
    if 2 * A.mag < p then some (Ivl.sym ((ir.value h).size * A.mag * J.mag)) else none
  | .polyMatVec a K L .coefficients => (leafI a).bind fun A =>
    if 2 * A.mag < p then
      some (Ivl.sym (NamedOp.cols ir (.polyMatVec a K L .coefficients) * A.mag * J.mag))
    else none
  | .polyBroadcast t K .coefficients => (leafI t).bind fun A =>
    if 2 * A.mag < p then
      some (Ivl.sym (NamedOp.cols ir (.polyBroadcast t K .coefficients) * A.mag * J.mag))
    else none
  | .rowDot M R W => NamedOp.rowFormIvl ir leafI p J (.rowDot M R W)
  | .acyclicConv h lx => NamedOp.rowFormIvl ir leafI p J (.acyclicConv h lx)
  | _ => none

/-! ### Linear maps and sums of constant multiples -/

/-- **The interval of a sparse row** `Σ_t c_t · x_t` at the characteristic `p`, on an operand with
interval `J`: each coefficient a constant `c < p` read centred (`centeredZ`); none on a public
coefficient. -/
def linRowIvl (p : ℕ) (J : Ivl) : List (ℕ × Coef) → Option Ivl
  | [] => some ⟨0, 0⟩
  | (_, .const c) :: ts =>
    if c < p then (linRowIvl p J ts).map (Ivl.add (J.smul (centeredZ p c))) else none
  | (_, .node _ _) :: _ => none

/-- **The interval of a linear map's coordinates** (`linear rows e`): the hull of its rows'
intervals (`linRowIvl`), `[0, 0]` for no rows. -/
def linIvl (p : ℕ) (J : Ivl) : List (List (ℕ × Coef)) → Option Ivl
  | [] => some ⟨0, 0⟩
  | [r] => linRowIvl p J r
  | r :: r' :: rs => (linRowIvl p J r).bind fun A => (linIvl p J (r' :: rs)).map A.hull

/-- **The interval of a sum of constant multiples** `Σ_s c_s x_s` of members `x_s` of `A`: the sum
of the multiples' intervals. -/
def groupSumIvl (A : Ivl) : List ℤ → Ivl
  | [] => ⟨0, 0⟩
  | c :: cs => (A.smul c).add (groupSumIvl A cs)

/-- **The hull of `n ≥ 1` groups' sums of constant multiples**: group `g` the constants
`g w, …, g w + w − 1` of `cs` (`groupSumIvl`); none for no group. -/
def groupsIvl (A : Ivl) (w : ℕ) : ℕ → List ℤ → Option Ivl
  | 0, _ => none
  | 1, cs => some (groupSumIvl A (cs.take w))
  | n + 2, cs => (groupsIvl A w (n + 1) (cs.drop w)).map (groupSumIvl A (cs.take w)).hull

/-- **The coordinates of a constant view** at the characteristic `p`, read centred: a constant
`leaf C` (its entries, `0` past them) or a view `reindex m (leaf C)` of one, where `C` has an
interval (`leafI`); none otherwise. -/
def constCoords (ir : RealizedProgram) (p : ℕ) (leafI : ℕ → Option Ivl) : Expr → Option (List ℤ)
  | .leaf C =>
    match (ir.value C).kind with
    | .constant es =>
      if (leafI C).isSome then
        some (((es ++ List.replicate (ir.value C).size 0).take (ir.value C).size).map
          (centeredZ p))
      else none
    | _ => none
  | .reindex m (.leaf C) =>
    match (ir.value C).kind with
    | .constant es =>
      if (leafI C).isSome then some (m.toList.map fun k => centeredZ p (es.getD k 0)) else none
    | _ => none
  | _ => none

/-! ## The evaluator -/

mutual

/-- **The interval of an expression's coordinates** at the characteristic `p` (see the module
docstring): the values' intervals `leafI`, the shared expressions' `refI`; a constant multiple by a
constant `c < p` read centred (`centeredZ`); the sum of two masked views of disjoint supports
(`RealizedProgram.maskedPairB`) the hull of their intervals; a sum of groups at `p > 2`; the MAC convolution
of an operand within `[0, 1]` (`NamedOp.macIvl`); a public polynomial operator
(`NamedOp.polyIvl`); a Logic builder on arguments within `[0, 1]` the
interval `[0, 1]`; `none` on any other form. -/
def Expr.ivl (ir : RealizedProgram) (p : ℕ) (leafI : ℕ → Option Ivl)     (refI : ℕ → Option Ivl) :
    Expr → Option Ivl
  | .leaf v => leafI v
  | .add e e' => (Expr.ivl ir p leafI refI e).bind fun J => (Expr.ivl ir p leafI refI e').map
      fun J' => if (ir.maskedNz (.add e e')).isSome || ir.maskedPairB e e' then J.hull J'
        else J.add J'
  | .sub e e' => (Expr.ivl ir p leafI refI e).bind fun J =>
      (Expr.ivl ir p leafI refI e').map J.sub
  | .scale (.const c) e =>
    if c < p then (Expr.ivl ir p leafI refI e).map (Ivl.smul (centeredZ p c)) else none
  | .mul e e' => (Expr.ivl ir p leafI refI e).bind fun J =>
      (Expr.ivl ir p leafI refI e').map J.mul
  | .reindex _ e => Expr.ivl ir p leafI refI e
  | .concat e e' => (Expr.ivl ir p leafI refI e).bind fun J =>
      (Expr.ivl ir p leafI refI e').map J.hull
  | .ref k => refI k
  | .linear rows e => (Expr.ivl ir p leafI refI e).bind fun J => linIvl p J rows
  | .apply op e =>
    match op.sumWidth with
    | some w => if 2 < p then (Expr.ivl ir p leafI refI e).map fun J =>
        (Expr.ivlGrouped ir p leafI refI w e).getD (Ivl.nsmul w J) else none
    | none => (Expr.ivl ir p leafI refI e).bind fun J =>
      match op.macIvl p J with
      | some J' => some J'
      | none => op.polyIvl ir leafI p J
  | .logic _ _ args => if Expr.ivlBits ir p leafI refI args then some ⟨0, 1⟩ else none
  | _ => none

/-- **The interval of the sums of groups of `w` of a product by a constant view** (compiler/range.h,
`expr_interval`: a sum of an operand times constants, each group's sum of the operand's interval
times its constants): `mul a c` with `c` (or `a`) a constant view (`constCoords`), the hull of the
groups' sums (`groupsIvl`); none otherwise. -/
def Expr.ivlGrouped (ir : RealizedProgram) (p : ℕ) (leafI : ℕ → Option Ivl)
    (refI : ℕ → Option Ivl) (w : ℕ) : Expr → Option Ivl
  | .mul a c =>
    match constCoords ir p leafI c with
    | some cs => (Expr.ivl ir p leafI refI a).bind fun A => groupsIvl A w (cs.length / w) cs
    | none =>
      match constCoords ir p leafI a with
      | some cs => (Expr.ivl ir p leafI refI c).bind fun A => groupsIvl A w (cs.length / w) cs
      | none => none
  | _ => none

/-- **Every expression of the list has an interval within `[0, 1]`** (`Expr.ivl`). -/
def Expr.ivlBits (ir : RealizedProgram) (p : ℕ) (leafI : ℕ → Option Ivl)     (refI : ℕ → Option Ivl) :
    List Expr → Bool
  | [] => true
  | e :: es =>
    (match Expr.ivl ir p leafI refI e with
      | some J => decide (J.Within 0 1)
      | none => false) && Expr.ivlBits ir p leafI refI es

end

mutual

theorem Expr.ivl_congr {ir : RealizedProgram} {p : ℕ} {leafI : ℕ → Option Ivl}
    {r r' : ℕ → Option Ivl} :
    ∀ e : Expr, (∀ k ∈ e.refs, r k = r' k) → e.ivl ir p leafI r = e.ivl ir p leafI r'
  | .leaf _, _ => rfl
  | .add e e', h | .sub e e', h | .mul e e', h | .concat e e', h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.ivl, Expr.ivl_congr e fun k hk => h k (.inl hk),
      Expr.ivl_congr e' fun k hk => h k (.inr hk)]
  | .scale (.const _) e, h | .linear _ e, h => by
    simp only [Expr.refs] at h
    simp only [Expr.ivl, Expr.ivl_congr e h]
  | .apply _ e, h => by
    simp only [Expr.refs] at h
    simp only [Expr.ivl, Expr.ivl_congr e h, Expr.ivlGrouped_congr e h]
  | .scale (.node _ _) _, _ => rfl
  | .reindex _ e, h => by
    simp only [Expr.refs] at h
    simp only [Expr.ivl, Expr.ivl_congr e h]
  | .ref k, h => by simp only [Expr.ivl, h k (by simp [Expr.refs])]
  | .logic _ _ args, h => by
    simp only [Expr.refs] at h
    simp only [Expr.ivl, Expr.ivlBits_congr args h]
  | .prod _ _, _ | .mux _ _ _, _ => rfl

theorem Expr.ivlGrouped_congr {ir : RealizedProgram} {p : ℕ} {leafI : ℕ → Option Ivl}
    {r r' : ℕ → Option Ivl} {w : ℕ} :
    ∀ e : Expr, (∀ k ∈ e.refs, r k = r' k) →
      e.ivlGrouped ir p leafI r w = e.ivlGrouped ir p leafI r' w
  | .mul a c, h => by
    simp only [Expr.refs, List.mem_append] at h
    simp only [Expr.ivlGrouped, Expr.ivl_congr a fun k hk => h k (.inl hk),
      Expr.ivl_congr c fun k hk => h k (.inr hk)]
  | .leaf _, _ | .add _ _, _ | .sub _ _, _ | .scale _ _, _ | .reindex _ _, _ | .concat _ _, _
  | .linear _ _, _ | .prod _ _, _ | .mux _ _ _, _ | .apply _ _, _ | .ref _, _
  | .logic _ _ _, _ => rfl

theorem Expr.ivlBits_congr {ir : RealizedProgram} {p : ℕ} {leafI : ℕ → Option Ivl}
    {r r' : ℕ → Option Ivl} :
    ∀ es : List Expr, (∀ k ∈ Expr.refsList es, r k = r' k) →
      Expr.ivlBits ir p leafI r es = Expr.ivlBits ir p leafI r' es
  | [], _ => rfl
  | e :: es, h => by
    simp only [Expr.refsList, List.mem_append] at h
    simp only [Expr.ivlBits, Expr.ivl_congr e fun k hk => h k (.inl hk),
      Expr.ivlBits_congr es fun k hk => h k (.inr hk)]

end

/-! ## Tables with an index-dependent relation -/

section MemoIdx

variable {γ β : Type} [Inhabited γ] {F : (ℕ → β) → ℕ → γ → β} {d : β} {L : List γ}
  {D : ℕ → List ℕ}

/-- **A recursion with fuel agrees with the table, entry by entry** (`iter_rel_memo` with a relation
`R j` that depends on the entry `j`). -/
theorem iter_rel_memo_idx {β' : Type} {R : ℕ → β' → β → Prop} {iter : ℕ → ℕ → β'}
    {G : (ℕ → β') → ℕ → β'} (hiter : ∀ n j, iter (n + 1) j = G (iter n) j)
    (hrel : ∀ j < L.length, ∀ (r : ℕ → β') (r' : ℕ → β), (∀ k ∈ D j, R k (r k) (r' k)) →
      R j (G r j) (F r' j (L.getD j default)))
    (hF : MemoDeps F L D) :
    ∀ n j, j < n → j < L.length → R j (iter n j) ((memo F d L).getD j d)
  | 0, _, h, _ => absurd h (Nat.not_lt_zero _)
  | n + 1, j, hjn, hj => by
    rw [hiter, memo_getD hF hj]
    exact hrel j hj _ _ fun k hk => by
      have := hF.lt j hj k hk
      exact iter_rel_memo_idx hiter hrel hF n k (by omega) (by omega)

end MemoIdx

/-! ## Sums of groups on the field and on the integers -/

/-- **A sum of unit coordinates**: `Σ_{s<w} [a + s = t]` is `1` on `[a, a + w)`, `0` elsewhere. -/
theorem sum_fin_ite_eq {K : Type} [AddCommMonoidWithOne K] (a t w : ℕ) :
    (∑ s : Fin w, if a + (s : ℕ) = t then (1 : K) else 0) =
      if a ≤ t ∧ t < a + w then 1 else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨t - a, by omega⟩]
    · exact ite_eq_left (show a + (t - a) = t by omega)
    · intro s _ hs
      refine ite_eq_right fun h' => hs (Fin.ext ?_)
      simp only
      omega
    · simp
  · refine Finset.sum_eq_zero fun s _ => ite_eq_right fun h' => h ⟨by omega, by omega⟩

/-- **The coordinates `[a, a + w)` of a sum over `[0, n)`**: `Σ_{t<n} [a ≤ t < a + w] x(c + t)` is
`Σ_{s<w} x(c + a + s)` when `a + w ≤ n`. -/
theorem sum_fin_indicator {M : Type} [AddCommMonoid M] (c a w n : ℕ) (x : ℕ → M)
    (h : a + w ≤ n) :
    (∑ t : Fin n, if a ≤ (t : ℕ) ∧ (t : ℕ) < a + w then x (c + t) else 0) =
      ∑ s : Fin w, x (c + (a + s)) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if a ≤ t ∧ t < a + w then x (c + t) else 0) n,
    Fin.sum_univ_eq_sum_range (fun s => x (c + (a + s))) w, ← Finset.sum_filter]
  have hf : (Finset.range n).filter (fun t => a ≤ t ∧ t < a + w) = Finset.Ico a (a + w) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [hf, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-! ## Linear operators -/

/-- **A sum against a unit vector picks its coordinate.** -/
theorem sum_mul_unit {K : Type*} [Semiring K] (n : ℕ) (C : ℕ → K) {t : ℕ} (ht : t < n) :
    ∑ k ∈ Finset.range n, C k * (if k = t then 1 else 0) = C t := by
  simp [mul_ite, ht]

/-- **A double sum over `Fin n` is the double sum over `[0, n)`.** -/
theorem sum_fin_fin_eq_sum_range {M : Type*} [AddCommMonoid M] (n : ℕ) (g : ℕ → ℕ → M) :
    ∑ a : Fin n, ∑ b : Fin n, g a b = ∑ a ∈ Finset.range n, ∑ b ∈ Finset.range n, g a b := by
  rw [Fin.sum_univ_eq_sum_range (fun a => ∑ b : Fin n, g a b)]
  exact Finset.sum_congr rfl fun a _ => Fin.sum_univ_eq_sum_range (g a) n

/-- **The negacyclic convolution is linear in its input**: below `n`, coordinate `j` is
`Σ_k C_k x_k` with `C_k = Σ_i [i + k = j] h_i − Σ_i [i + k = j + n] h_i`. -/
theorem Ops.negacyclic_eq_sum {K : Type*} [Field K] (n : ℕ) (h x : ℕ → K) {j : ℕ} (hj : j < n) :
    Ops.negacyclic n h x j = ∑ k ∈ Finset.range n,
      ((∑ i ∈ Finset.range n, if i + k = j then h i else 0) -
        ∑ i ∈ Finset.range n, if i + k = j + n then h i else 0) * x k := by
  rw [Ops.negacyclic_apply n h x hj,
    sum_fin_fin_eq_sum_range n (fun i k => if i + k = j then h i * x k else 0),
    sum_fin_fin_eq_sum_range n (fun i k => if i + k = j + n then h i * x k else 0)]
  simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, ite_mul, zero_mul]
  congr 1 <;> exact Finset.sum_comm

/-- **The negacyclic coefficient** `C_k(j) = Σ_i [i + k = j] h_i − Σ_i [i + k = j + n] h_i`. -/
def Ops.negCoef {K : Type*} [AddCommGroup K] (n : ℕ) (h : ℕ → K) (j k : ℕ) : K :=
  (∑ i ∈ Finset.range n, if i + k = j then h i else 0) -
    ∑ i ∈ Finset.range n, if i + k = j + n then h i else 0

theorem sum_range_ite_add_eq {K : Type*} [AddCommMonoid K] (n k m : ℕ) (h : ℕ → K) :
    (∑ i ∈ Finset.range n, if i + k = m then h i else 0) =
      if k ≤ m ∧ m - k < n then h (m - k) else 0 := by
  have : ∀ i, (i + k = m) ↔ (i = m - k ∧ k ≤ m) := fun i => by omega
  simp only [this, ite_and]
  rw [Finset.sum_ite_eq' (Finset.range n) (m - k) (fun i => if k ≤ m then h i else 0)]
  simp only [Finset.mem_range]
  split_ifs <;> rfl

/-- **A negacyclic coefficient is `0` or `± h_i`** for some `i < n`. -/
theorem Ops.negCoef_signed {K : Type*} [AddCommGroup K] (n : ℕ) (h : ℕ → K) (j k : ℕ) :
    Ops.negCoef n h j k = 0 ∨ ∃ i < n, Ops.negCoef n h j k = h i ∨ Ops.negCoef n h j k = -h i := by
  unfold Ops.negCoef
  rw [sum_range_ite_add_eq, sum_range_ite_add_eq]
  split_ifs with h1 h2 h2
  · omega
  · exact .inr ⟨_, h1.2, .inl (sub_zero _)⟩
  · exact .inr ⟨_, h2.2, .inr (zero_sub _)⟩
  · exact .inl (sub_zero _)

/-- **A negacyclic coefficient in closed form**: `h (j − k)` when `k ≤ j < n + k`, `−h (j + n − k)`
when `j < k ≤ j + n`, else `0` (the two cases exclude each other). -/
theorem Ops.negCoef_eq {K : Type*} [AddCommGroup K] (n : ℕ) (h : ℕ → K) (j k : ℕ) :
    Ops.negCoef n h j k = (if k ≤ j ∧ j - k < n then h (j - k) else 0) -
      if k ≤ j + n ∧ j + n - k < n then h (j + n - k) else 0 := by
  unfold Ops.negCoef
  rw [sum_range_ite_add_eq, sum_range_ite_add_eq]

/-- **An additive map of a negacyclic coefficient** is the coefficient of the mapped entries. -/
theorem Ops.negCoef_map {K L : Type*} [AddCommGroup K] [AddCommGroup L] (g : K →+ L) (n : ℕ)
    (h : ℕ → K) (j k : ℕ) : g (Ops.negCoef n h j k) = Ops.negCoef n (fun s => g (h s)) j k := by
  rw [Ops.negCoef_eq, Ops.negCoef_eq, map_sub]
  split_ifs <;> simp

/-- **The negacyclic convolution is its coefficients' sum** (`Ops.negacyclic_eq_sum`). -/
theorem Ops.negacyclic_eq_sum_negCoef {K : Type*} [Field K] (n : ℕ) (h x : ℕ → K) {j : ℕ}
    (hj : j < n) : Ops.negacyclic n h x j = ∑ k ∈ Finset.range n, Ops.negCoef n h j k * x k :=
  Ops.negacyclic_eq_sum n h x hj

/-- **The integer reading of a negacyclic coefficient** of entries that are small integers' casts is
the coefficient of the integers (`FieldInterp.coefInt_intCast`). -/
theorem FieldInterp.coefInt_negCoef {F : FieldInterp} {p : ℕ} (hp : F.spec.characteristic = p)
    (hchar : CharP F.K p) (htn : ∀ k < p, F.toNat (k : F.K) = k) (hp0 : 0 < p) (n : ℕ)
    {h : ℕ → F.K} {z : ℕ → ℤ} (hz : ∀ s < n, 2 * |z s| < p ∧ h s = (z s : F.K)) (j k : ℕ) :
    F.coefInt (Ops.negCoef n h j k) = Ops.negCoef n z j k := by
  rw [Ops.negCoef_eq, Ops.negCoef_eq]
  split_ifs with h1 h2 h2
  · omega
  · obtain ⟨hlt, heq⟩ := hz _ h1.2
    rw [sub_zero, sub_zero, heq, FieldInterp.coefInt_intCast hp hchar htn hlt]
  · obtain ⟨hlt, heq⟩ := hz _ h2.2
    rw [zero_sub, zero_sub, heq, ← Int.cast_neg,
      FieldInterp.coefInt_intCast hp hchar htn (by rwa [abs_neg])]
  · rw [sub_zero, sub_zero, show (0 : F.K) = ((0 : ℤ) : F.K) from Int.cast_zero.symm,
      FieldInterp.coefInt_intCast hp hchar htn (by simpa using hp0)]

namespace NamedOp

variable (ir : RealizedProgram) {I : Interp}

/-- **A sum of groups has `rows ≥ 1` blocks of `rows · w` columns.** -/
theorem rows_cols_of_sumWidth {op : NamedOp} {w : ℕ} (h : op.sumWidth = some w) :
    0 < rows ir op ∧ cols ir op = rows ir op * w := by
  match op, h with
  | .sum w, rfl => exact ⟨Nat.one_pos, (Nat.one_mul w).symm⟩
  | .batched b (.sum w'), h =>
    simp only [sumWidth] at h
    split_ifs at h with hb
    cases h
    exact ⟨by simpa [rows] using hb, by simp [rows, cols]⟩

/-- **A sum of groups on one block**: output coordinate `j < rows` is the sum of coordinates
`j w, …, j w + w − 1`. -/
theorem block_of_sumWidth {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp} {w : ℕ}
    (h : op.sumWidth = some w) (y : ℕ → (I f).K) {j : ℕ} (hj : j < rows ir op) :
    block ir f leaf op y j = ∑ s : Fin w, y (j * w + s) := by
  match op, h with
  | .sum w, rfl =>
    simp only [rows] at hj
    obtain rfl : j = 0 := by omega
    simp [block, Ops.sum]
  | .batched b (.sum w'), h =>
    simp only [sumWidth] at h
    split_ifs at h with hb
    cases h
    simp only [rows, Nat.mul_one] at hj
    simp only [block, rows, cols, Nat.mul_one, ite_eq_left hj, Nat.div_one, Nat.mod_one, Ops.sum,
      ↓reduceIte]

/-- **A sum of groups along the last axis**: coordinate `j` is the sum of coordinates
`j w, …, j w + w − 1` of the operand. -/
theorem apply_of_sumWidth {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp} {w : ℕ}
    (h : op.sumWidth = some w) (x : ℕ → (I f).K) (j : ℕ) :
    apply ir f leaf op x j = ∑ s : Fin w, x (j * w + s) := by
  obtain ⟨hr, hc⟩ := rows_cols_of_sumWidth ir h
  unfold apply
  rw [block_of_sumWidth ir h _ (Nat.mod_lt _ hr)]
  refine Finset.sum_congr rfl fun s _ => congrArg x ?_
  rw [hc]
  have := Nat.div_add_mod j (rows ir op)
  nlinarith [Nat.div_add_mod j (rows ir op)]

/-- **A sum of groups on the integers**: coordinate `j` is the sum of coordinates
`j w, …, j w + w − 1`, when the integer readings of `0` and `1` are `0` and `1`. -/
theorem applyInt_of_sumWidth {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp} {w : ℕ}
    (h : op.sumWidth = some w) (h0 : (I f).coefInt 0 = 0) (h1 : (I f).coefInt 1 = 1)
    (x : ℕ → ℤ) (j : ℕ) :
    applyInt ir f leaf op x j = ∑ s : Fin w, x (j * w + s) := by
  obtain ⟨hr, hc⟩ := rows_cols_of_sumWidth ir h
  unfold applyInt
  have hblock : ∀ t : Fin (cols ir op),
      (I f).coefInt (block ir f leaf op (fun s => if s = t then 1 else 0) (j % rows ir op)) *
          x (j / rows ir op * cols ir op + t) =
        if j % rows ir op * w ≤ (t : ℕ) ∧ (t : ℕ) < j % rows ir op * w + w then
          x (j / rows ir op * cols ir op + t) else 0 := by
    intro t
    rw [block_of_sumWidth ir h _ (Nat.mod_lt _ hr), sum_fin_ite_eq]
    split_ifs <;> simp [h0, h1]
  simp only [hblock]
  have hmod := Nat.mod_lt j hr
  rw [RealizedProgram.sum_fin_indicator _ _ w _ x (by rw [hc]; nlinarith)]
  refine Finset.sum_congr rfl fun s _ => congrArg x ?_
  rw [hc]
  nlinarith [Nat.div_add_mod j (rows ir op)]

/-- **A sum of groups reads inside its operand**: an output coordinate below the length reads
coordinates below the operand's length `L`. -/
theorem lt_of_sumWidth {op : NamedOp} {w : ℕ} (h : op.sumWidth = some w) {L j : ℕ}
    (hj : j < L / cols ir op * rows ir op) (s : Fin w) : j * w + s < L := by
  obtain ⟨hr, hc⟩ := rows_cols_of_sumWidth ir h
  rw [hc] at hj
  have h1 : (j + 1) * w ≤ L / (rows ir op * w) * rows ir op * w :=
    Nat.mul_le_mul_right _ (by omega)
  have h2 : L / (rows ir op * w) * rows ir op * w ≤ L := by
    rw [Nat.mul_assoc]
    exact Nat.div_mul_le_self L _
  have := s.2
  nlinarith

/-! ### The MAC convolution -/

/-- **The bits `R_c` of the MAC powers** `r_c` (value `r` read by `leaf`) in their field's
polynomial basis, as `NamedOp.block` reads them for `macConv r w nch taps`. -/
def macRb (leaf : ir.Valuation I) (r w : ℕ) : ℕ → Fin w → ℕ :=
  fun c j => if ((I (ir.valueField r)).toNat (leaf r c)).testBit j then 1 else 0

theorem macRb_le_one (leaf : ir.Valuation I) (r w c : ℕ) (j : Fin w) : macRb ir leaf r w c j ≤ 1 := by
  unfold macRb
  split <;> omega

/-- **A sum over the columns `c w + j` of `nch` chunks of `w`**, through `finProdFinEquiv`. -/
theorem sum_fin_mul {M : Type} [AddCommMonoid M] {n nch w : ℕ} (h : n = nch * w) (g : ℕ → M) :
    ∑ t : Fin n, g t = ∑ c : Fin nch, ∑ j : Fin w, g (c * w + j) := by
  subst h
  rw [← Fintype.sum_prod_type', ← Fintype.sum_equiv finProdFinEquiv (fun x => g (x.1 * w + x.2))
    (fun t => g t) (fun x => by rw [finProdFinEquiv_apply_val]; ring_nf)]

/-- **The MAC convolution along the last axis**: output coordinate `i` is
`Σ_c Σ_j Conv(r_c)[i mod w][j] · x(⌊i / w⌋ · nch w + c w + j)`. -/
theorem apply_macConv {f : ℕ} (leaf : ir.Valuation I) {r w nch : ℕ} {taps : List ℕ} (hw : 0 < w)
    (x : ℕ → (I f).K) (i : ℕ) :
    apply ir f leaf (.macConv r w nch taps) x i =
      ∑ c : Fin nch, ∑ j : Fin w,
        (Conv.matrix taps.toFinset (macRb ir leaf r w c) ⟨i % w, Nat.mod_lt _ hw⟩ j : (I f).K) *
          x (i / w * (nch * w) + (c * w + j)) := by
  simp only [apply, block, Ops.macConv]
  rw [dif_pos (show i % rows ir (.macConv r w nch taps) < w from Nat.mod_lt i hw)]
  rfl

/-- **The MAC convolution on the integers**: output coordinate `i` is
`Σ_c Σ_j Conv(r_c)[i mod w][j] · x(⌊i / w⌋ · nch w + c w + j)`, the matrix entries read as
themselves, when twice the width `w` is below the characteristic `p` (every entry lies in `[0, w]`,
`Conv.matrix_le_width`) and the integer reading inverts the cast of a natural below `p`. -/
theorem applyInt_macConv {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k) (leaf : ir.Valuation I) {r w nch : ℕ}
    {taps : List ℕ} (hw : 0 < w) (hc : 2 * w < p) (x : ℕ → ℤ) (i : ℕ) :
    applyInt ir f leaf (.macConv r w nch taps) x i =
      ∑ c : Fin nch, ∑ j : Fin w,
        (Conv.matrix taps.toFinset (macRb ir leaf r w c) ⟨i % w, Nat.mod_lt _ hw⟩ j : ℤ) *
          x (i / w * (nch * w) + (c * w + j)) := by
  unfold applyInt
  refine (sum_fin_mul (nch := nch) (w := w) (n := cols ir (.macConv r w nch taps)) rfl
    (fun t => (I f).coefInt (block ir f leaf (.macConv r w nch taps)
      (fun s => if s = t then 1 else 0) (i % rows ir (.macConv r w nch taps))) *
        x (i / rows ir (.macConv r w nch taps) * cols ir (.macConv r w nch taps) + t))).trans ?_
  refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
  have hb := Nat.mod_lt i hw
  have hblk : block ir f leaf (.macConv r w nch taps)
      (fun s => if s = (c : ℕ) * w + j then (1 : (I f).K) else 0)
        (i % rows ir (.macConv r w nch taps)) =
      (Conv.matrix taps.toFinset (macRb ir leaf r w c) ⟨i % w, hb⟩ j : (I f).K) :=
    Ops.macConv_single w nch taps (macRb ir leaf r w) hb c j
  have hle := Conv.matrix_le_width taps.toFinset (macRb_le_one ir leaf r w c) ⟨i % w, hb⟩ j
  rw [hblk, FieldInterp.coefInt, htn _ (by omega), FieldInterp.centered, hp, if_pos (by omega)]
  rfl

/-- **A sum of products of naturals with members of `[0, 1]`** lies in `[0, Σ n]`. -/
theorem sum_mul_mem {ι : Type} (s : Finset ι) (n : ι → ℕ) (y : ι → ℤ)
    (hy : ∀ t ∈ s, 0 ≤ y t ∧ y t ≤ 1) :
    0 ≤ ∑ t ∈ s, (n t : ℤ) * y t ∧ ∑ t ∈ s, (n t : ℤ) * y t ≤ ∑ t ∈ s, (n t : ℤ) :=
  ⟨Finset.sum_nonneg fun t ht => mul_nonneg (Nat.cast_nonneg _) (hy t ht).1,
    Finset.sum_le_sum fun t ht => mul_le_of_le_one_right (Nat.cast_nonneg _) (hy t ht).2⟩

/-- **A named operator reads inside its operand**: an output coordinate below the length reads
coordinates below the operand's length `L`. -/
theorem lt_of_cols {op : NamedOp} (hr : 0 < rows ir op) {L j : ℕ}
    (hj : j < L / cols ir op * rows ir op) {t : ℕ} (ht : t < cols ir op) :
    j / rows ir op * cols ir op + t < L := by
  have h1 : j / rows ir op < L / cols ir op := by
    rw [Nat.div_lt_iff_lt_mul hr]
    exact hj
  have h2 : (j / rows ir op + 1) * cols ir op ≤ L / cols ir op * cols ir op :=
    Nat.mul_le_mul_right _ h1
  have h3 := Nat.div_mul_le_self L (cols ir op)
  rw [Nat.add_mul, Nat.one_mul] at h2
  omega

/-- **The MAC convolution's interval is sound** (`NamedOp.macIvl`): on an operand whose
coordinates below `L` lie in `J₁ ⊆ [0, 1]`, every output coordinate below the length lies in
`[0, nch · convMax]`. -/
theorem applyInt_mem_macIvl {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k) (leaf : ir.Valuation I) {op : NamedOp}
    {J₁ J : Ivl} (h : op.macIvl p J₁ = some J) {x : ℕ → ℤ} {L : ℕ} (hx : ∀ t < L, x t ∈ J₁)
    {i : ℕ} (hi : i < L / cols ir op * rows ir op) : applyInt ir f leaf op x i ∈ J := by
  match op, h with
  | .macConv r w nch taps, h =>
    simp only [macIvl] at h
    split_ifs at h with h1
    split at h
    · rename_i c hcm
      cases h
      have hcm' := convMax_of_macConvMax? hcm
      rw [applyInt_macConv ir hp htn leaf h1.2.1 h1.2.2]
      have hy : ∀ c' : Fin nch, ∀ j : Fin w,
          0 ≤ x (i / w * (nch * w) + (c' * w + j)) ∧ x (i / w * (nch * w) + (c' * w + j)) ≤ 1 := by
        intro c' j
        have hlt : (c' : ℕ) * w + j < nch * w := by
          have := c'.2
          have := j.2
          nlinarith
        exact Ivl.mem_of_within h1.1 (hx _ (lt_of_cols ir (op := .macConv r w nch taps) h1.2.1 hi hlt))
      constructor
      · exact Finset.sum_nonneg fun c' _ =>
          (sum_mul_mem _ _ _ fun j _ => hy c' j).1
      · calc _ ≤ ∑ c' : Fin nch, ∑ j : Fin w,
              (Conv.matrix taps.toFinset (macRb ir leaf r w c') ⟨i % w, Nat.mod_lt _ h1.2.1⟩ j : ℤ) :=
              Finset.sum_le_sum fun c' _ => (sum_mul_mem _ _ _ fun j _ => hy c' j).2
          _ ≤ ∑ _c' : Fin nch, (c : ℤ) := Finset.sum_le_sum fun c' _ => by
              rw [← hcm']
              exact_mod_cast Conv.matrix_rowSum_le_convMax taps.toFinset
                (macRb_le_one ir leaf r w c') ⟨i % w, Nat.mod_lt _ h1.2.1⟩
          _ = ((nch * c : ℕ) : ℤ) := by simp
    · cases h

/-! ### Public polynomial operators -/

/-- The `l`-th polynomial of row `r` of a `polyMatVec a K L` matrix in field `f`. -/
def pmvPoly {f : ℕ} (leaf : ir.Valuation I) (a K L r l : ℕ) : ℕ → (I f).K :=
  fun s => castElt (leaf a ((r * L + l) * ((ir.value a).size / (K * L)) + s))

theorem block_polyMatVec {f : ℕ} (leaf : ir.Valuation I) (a K L : ℕ) (y : ℕ → (I f).K) {j : ℕ}
    (hj : j < K * ((ir.value a).size / (K * L))) :
    block ir f leaf (.polyMatVec a K L .coefficients) y j =
      ∑ l : Fin L, ∑ k : Fin ((ir.value a).size / (K * L)),
        Ops.negCoef ((ir.value a).size / (K * L))
          (pmvPoly ir leaf a K L (j / ((ir.value a).size / (K * L))) l)
          (j % ((ir.value a).size / (K * L))) k *
            y (l * ((ir.value a).size / (K * L)) + k) := by
  set n := (ir.value a).size / (K * L) with hn
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, Nat.mul_zero] at hj
      omega
    · exact h
  simp only [block, formPoly]
  rw [← hn]
  simp only [hj, ↓reduceIte]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Ops.negacyclic_eq_sum _ _ _ (Nat.mod_lt _ hn0), Fin.sum_univ_eq_sum_range
    (fun k => Ops.negCoef n (pmvPoly ir leaf a K L (j / n) l) (j % n) k * y (l * n + k)) n]
  rfl

/-- **A `polyMatVec` matrix entry**: column `t = l n + k` of row `j` is the negacyclic coefficient
`C_k(j mod n)` of polynomial `(⌊j / n⌋, l)`. -/
theorem block_polyMatVec_unit {f : ℕ} (leaf : ir.Valuation I) (a K L : ℕ) {j : ℕ}
    (hj : j < K * ((ir.value a).size / (K * L))) (l : Fin L)
    (k : Fin ((ir.value a).size / (K * L))) :
    block ir f leaf (.polyMatVec a K L .coefficients)
        (fun s => if s = l * ((ir.value a).size / (K * L)) + k then 1 else 0) j =
      Ops.negCoef ((ir.value a).size / (K * L))
        (pmvPoly ir leaf a K L (j / ((ir.value a).size / (K * L))) l)
        (j % ((ir.value a).size / (K * L))) k := by
  rw [block_polyMatVec ir leaf a K L _ hj, Finset.sum_eq_single l]
  · rw [Finset.sum_eq_single k]
    · simp
    · intro k' _ hk'
      have : (k' : ℕ) ≠ k := fun h => hk' (Fin.ext h)
      simp [this]
    · simp
  · intro l' _ hl'
    refine Finset.sum_eq_zero fun k' _ => ?_
    have : (l' : ℕ) * ((ir.value a).size / (K * L)) + k' ≠
        l * ((ir.value a).size / (K * L)) + k := by
      intro h
      apply hl'
      apply Fin.ext
      have h1 : ((l' : ℕ) * ((ir.value a).size / (K * L)) + k') /
          ((ir.value a).size / (K * L)) = l' := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by have := k'.2; omega),
          Nat.div_eq_of_lt k'.2, Nat.zero_add]
      have h2 : ((l : ℕ) * ((ir.value a).size / (K * L)) + k) /
          ((ir.value a).size / (K * L)) = l := by
        rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by have := k.2; omega),
          Nat.div_eq_of_lt k.2, Nat.zero_add]
      rw [← h1, ← h2, h]
    simp [this]
  · simp

/-- **`polyMatVec` along the last axis**: output coordinate `j` is
`Σ_l Σ_k C_k(j' mod n) · x(⌊j / rows⌋ · cols + l n + k)`, `j' = j mod rows`. -/
theorem apply_polyMatVec {f : ℕ} (leaf : ir.Valuation I) (a K L : ℕ) (x : ℕ → (I f).K) (j : ℕ) :
    apply ir f leaf (.polyMatVec a K L .coefficients) x j =
      ∑ l : Fin L, ∑ k : Fin ((ir.value a).size / (K * L)),
        Ops.negCoef ((ir.value a).size / (K * L))
          (pmvPoly ir leaf a K L (j % rows ir (.polyMatVec a K L .coefficients) /
            ((ir.value a).size / (K * L))) l)
          (j % rows ir (.polyMatVec a K L .coefficients) % ((ir.value a).size / (K * L))) k *
            x (j / rows ir (.polyMatVec a K L .coefficients) *
              cols ir (.polyMatVec a K L .coefficients) +
                (l * ((ir.value a).size / (K * L)) + k)) := by
  rcases Nat.eq_zero_or_pos ((ir.value a).size / (K * L)) with h0 | h0
  · have : IsEmpty (Fin ((ir.value a).size / (K * L))) := by
      rw [h0]
      infer_instance
    simp only [apply, block, h0, Nat.mul_zero, Nat.not_lt_zero, ↓reduceIte]
    simp
  · have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with hK | hK
      · rw [hK, Nat.zero_mul, Nat.div_zero] at h0
        omega
      · exact hK
    have hr : j % rows ir (.polyMatVec a K L .coefficients) <
        K * ((ir.value a).size / (K * L)) := Nat.mod_lt _ (Nat.mul_pos hK h0)
    unfold apply
    rw [block_polyMatVec ir leaf a K L _ hr]

/-- **`polyMatVec` on the integers**: as `apply_polyMatVec`, the coefficients read by
`FieldInterp.coefInt`. -/
theorem applyInt_polyMatVec {f : ℕ} (leaf : ir.Valuation I) (a K L : ℕ) (x : ℕ → ℤ) (j : ℕ) :
    applyInt ir f leaf (.polyMatVec a K L .coefficients) x j =
      ∑ l : Fin L, ∑ k : Fin ((ir.value a).size / (K * L)),
        (I f).coefInt (Ops.negCoef ((ir.value a).size / (K * L))
          (pmvPoly ir leaf a K L (j % rows ir (.polyMatVec a K L .coefficients) /
            ((ir.value a).size / (K * L))) l)
          (j % rows ir (.polyMatVec a K L .coefficients) % ((ir.value a).size / (K * L))) k) *
            x (j / rows ir (.polyMatVec a K L .coefficients) *
              cols ir (.polyMatVec a K L .coefficients) +
                (l * ((ir.value a).size / (K * L)) + k)) := by
  unfold applyInt
  refine (sum_fin_mul (n := cols ir (.polyMatVec a K L .coefficients)) (nch := L)
    (w := (ir.value a).size / (K * L)) rfl (fun t => (I f).coefInt
      (block ir f leaf (.polyMatVec a K L .coefficients) (fun s => if s = t then 1 else 0)
        (j % rows ir (.polyMatVec a K L .coefficients))) *
      x (j / rows ir (.polyMatVec a K L .coefficients) *
        cols ir (.polyMatVec a K L .coefficients) + t))).trans ?_
  rcases Nat.eq_zero_or_pos ((ir.value a).size / (K * L)) with h0 | h0
  · have : IsEmpty (Fin ((ir.value a).size / (K * L))) := by
      rw [h0]
      infer_instance
    simp
  · have hK : 0 < K := by
      rcases Nat.eq_zero_or_pos K with hK | hK
      · rw [hK, Nat.zero_mul, Nat.div_zero] at h0
        omega
      · exact hK
    have hr : j % rows ir (.polyMatVec a K L .coefficients) <
        K * ((ir.value a).size / (K * L)) := Nat.mod_lt _ (Nat.mul_pos hK h0)
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => ?_
    rw [block_polyMatVec_unit ir leaf a K L hr]

/-- The polynomial of row block `r` of a `polyBroadcast t K` operator in field `f`. -/
def pbPoly {f : ℕ} (leaf : ir.Valuation I) (t K r : ℕ) : ℕ → (I f).K :=
  fun s => castElt (leaf t (r * ((ir.value t).size / K) + s))

/-- **A `polyBroadcast` matrix entry**: column `k` of row `j` is the negacyclic coefficient
`C_k(j mod n)` of polynomial `⌊j / n⌋`, below `K n` rows, and `0` past them. -/
def pbEntry {f : ℕ} (leaf : ir.Valuation I) (t K j k : ℕ) : (I f).K :=
  if j < K * ((ir.value t).size / K) then
    Ops.negCoef ((ir.value t).size / K) (pbPoly ir leaf t K (j / ((ir.value t).size / K)))
      (j % ((ir.value t).size / K)) k
  else 0

theorem block_polyBroadcast {f : ℕ} (leaf : ir.Valuation I) (t K : ℕ) (y : ℕ → (I f).K) (j : ℕ) :
    block ir f leaf (.polyBroadcast t K .coefficients) y j =
      ∑ k : Fin ((ir.value t).size / K), pbEntry ir leaf t K j k * y k := by
  simp only [block, formPoly, pbEntry]
  split_ifs with hj
  · have hn0 : 0 < (ir.value t).size / K := by
      rcases Nat.eq_zero_or_pos ((ir.value t).size / K) with h | h
      · rw [h, Nat.mul_zero] at hj
        omega
      · exact h
    rw [Ops.negacyclic_eq_sum _ _ _ (Nat.mod_lt _ hn0), Fin.sum_univ_eq_sum_range
      (fun k => Ops.negCoef ((ir.value t).size / K)
        (pbPoly ir leaf t K (j / ((ir.value t).size / K))) (j % ((ir.value t).size / K)) k *
          y k) ((ir.value t).size / K)]
    rfl
  · simp

theorem block_polyBroadcast_unit {f : ℕ} (leaf : ir.Valuation I) (t K j : ℕ)
    (k : Fin ((ir.value t).size / K)) :
    block ir f leaf (.polyBroadcast t K .coefficients) (fun s => if s = k then 1 else 0) j =
      pbEntry ir leaf t K j k := by
  rw [block_polyBroadcast, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    have : (k' : ℕ) ≠ k := fun h => hk' (Fin.ext h)
    simp [this]
  · simp

theorem apply_polyBroadcast {f : ℕ} (leaf : ir.Valuation I) (t K : ℕ) (x : ℕ → (I f).K)
    (j : ℕ) :
    apply ir f leaf (.polyBroadcast t K .coefficients) x j =
      ∑ k : Fin ((ir.value t).size / K),
        pbEntry ir leaf t K (j % rows ir (.polyBroadcast t K .coefficients)) k *
          x (j / rows ir (.polyBroadcast t K .coefficients) *
            cols ir (.polyBroadcast t K .coefficients) + k) := by
  unfold apply
  rw [block_polyBroadcast]

theorem applyInt_polyBroadcast {f : ℕ} (leaf : ir.Valuation I) (t K : ℕ) (x : ℕ → ℤ) (j : ℕ) :
    applyInt ir f leaf (.polyBroadcast t K .coefficients) x j =
      ∑ k : Fin ((ir.value t).size / K),
        (I f).coefInt (pbEntry ir leaf t K (j % rows ir (.polyBroadcast t K .coefficients)) k) *
          x (j / rows ir (.polyBroadcast t K .coefficients) *
            cols ir (.polyBroadcast t K .coefficients) + k) := by
  unfold applyInt
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [block_polyBroadcast_unit ir leaf t K _ (k : Fin ((ir.value t).size / K))]

/-- **An entry `0` or `± h_i` of small integers' casts is a small integer's cast.** -/
theorem signed_small {K : Type*} [Field K] {n M : ℕ} {h : ℕ → K}
    (hh : ∀ i < n, ∃ z : ℤ, |z| ≤ M ∧ h i = (z : K)) {E : K}
    (hE : E = 0 ∨ ∃ i < n, E = h i ∨ E = -h i) : ∃ z : ℤ, |z| ≤ M ∧ E = (z : K) := by
  rcases hE with rfl | ⟨i, hi, rfl | rfl⟩
  · exact ⟨0, by simp, by simp⟩
  · exact hh i hi
  · obtain ⟨z, hz, hzh⟩ := hh i hi
    exact ⟨-z, by rwa [abs_neg], by rw [hzh, Int.cast_neg]⟩

/-- **A polynomial operator's entries are small integers' casts**: every matrix entry the operator
reads (`pmvPoly`, `pbEntry`) is the cast of an integer of magnitude at most `M`, where the public
operand's integer readings lie in an interval of magnitude `M` and cast to its entries. -/
theorem pmv_entry_small {f : ℕ} {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ} {a K L : ℕ} {A : Ivl}
    (hA : ∀ s < (ir.value a).size, il a s ∈ A ∧ ((il a s : ℤ) : (I f).K) = castElt (leaf a s))
    {j : ℕ} (hj : j < K * ((ir.value a).size / (K * L))) (l : Fin L) (k : ℕ) :
    ∃ z : ℤ, |z| ≤ A.mag ∧ Ops.negCoef ((ir.value a).size / (K * L))
      (pmvPoly ir leaf a K L (j / ((ir.value a).size / (K * L))) l)
      (j % ((ir.value a).size / (K * L))) k = (z : (I f).K) := by
  refine signed_small (fun i hi => ?_) (Ops.negCoef_signed _ _ _ _)
  set n := (ir.value a).size / (K * L) with hn
  have hr : j / n < K := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    exact hj
  have hidx : (j / n * L + l) * n + i < (ir.value a).size := by
    have h1 : (j / n * L + l + 1) * n ≤ K * L * n := by
      apply Nat.mul_le_mul_right
      have := l.2
      nlinarith
    have h2 : K * L * n ≤ (ir.value a).size := by
      rw [hn, Nat.mul_comm (K * L)]
      exact Nat.div_mul_le_self _ _
    nlinarith
  obtain ⟨hm, hc⟩ := hA _ hidx
  exact ⟨_, Ivl.abs_le_mag hm, hc.symm⟩

theorem pb_entry_small {f : ℕ} {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ} {t K : ℕ} {A : Ivl}
    (hA : ∀ s < (ir.value t).size, il t s ∈ A ∧ ((il t s : ℤ) : (I f).K) = castElt (leaf t s))
    (j k : ℕ) : ∃ z : ℤ, |z| ≤ A.mag ∧ pbEntry ir leaf t K j k = (z : (I f).K) := by
  unfold pbEntry
  split_ifs with hj
  · refine signed_small (fun i hi => ?_) (Ops.negCoef_signed _ _ _ _)
    set n := (ir.value t).size / K with hn
    have hr : j / n < K := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      exact hj
    have hidx : j / n * n + i < (ir.value t).size := by
      have h1 : (j / n + 1) * n ≤ K * n := Nat.mul_le_mul_right _ hr
      have h2 : K * n ≤ (ir.value t).size := by
        rw [hn, Nat.mul_comm]
        exact Nat.div_mul_le_self _ _
      nlinarith
    obtain ⟨hm, hc⟩ := hA _ hidx
    exact ⟨_, Ivl.abs_le_mag hm, hc.symm⟩
  · exact ⟨0, by simp, by simp⟩

/-- **A double sum of products bounded by `M` and `B`** has magnitude at most `L n M B`. -/
theorem abs_sum_sum_le {L n M B : ℕ} (g : Fin L → Fin n → ℤ) (y : Fin L → Fin n → ℤ)
    (hg : ∀ l k, |g l k| ≤ M) (hy : ∀ l k, |y l k| ≤ B) :
    |∑ l : Fin L, ∑ k : Fin n, g l k * y l k| ≤ ((L * n * M * B : ℕ) : ℤ) := by
  calc _ ≤ ∑ l : Fin L, |∑ k : Fin n, g l k * y l k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l : Fin L, ∑ k : Fin n, |g l k * y l k| :=
        Finset.sum_le_sum fun l _ => Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _l : Fin L, ∑ _k : Fin n, ((M : ℤ) * B) :=
        Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun k _ => by
          rw [abs_mul]
          exact mul_le_mul (hg l k) (hy l k) (abs_nonneg _) (by positivity)
    _ = ((L * n * M * B : ℕ) : ℤ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

/-- **A negacyclic convolution's matrix entry**: column `k` of row `j < n` is the negacyclic
coefficient `C_k(j)` of its public polynomial in its form. -/
theorem block_negacyclicConv_unit {f : ℕ} (leaf : ir.Valuation I) (h : ℕ) (form : ConvForm)
    {j : ℕ} (hj : j < (ir.value h).size) (k : Fin (ir.value h).size) :
    block ir f leaf (.negacyclicConv h form) (fun s => if s = k then 1 else 0) j =
      Ops.negCoef (ir.value h).size
        (formPoly f (ir.value h).size (fun s => castElt (leaf h s)) form) j k := by
  simp only [block]
  rw [Ops.negacyclic_eq_sum_negCoef _ _ _ hj, sum_mul_unit _ _ k.2]

theorem applyInt_negacyclicConv {f : ℕ} (leaf : ir.Valuation I) (h : ℕ) (form : ConvForm)
    (x : ℕ → ℤ) {j : ℕ} (hn : 0 < (ir.value h).size) :
    applyInt ir f leaf (.negacyclicConv h form) x j =
      ∑ k : Fin (ir.value h).size,
        (I f).coefInt (Ops.negCoef (ir.value h).size
          (formPoly f (ir.value h).size (fun s => castElt (leaf h s)) form)
          (j % (ir.value h).size) k) *
          x (j / (ir.value h).size * (ir.value h).size + k) := by
  unfold applyInt
  simp only [rows, cols]
  exact Finset.sum_congr rfl fun k _ => by
    rw [block_negacyclicConv_unit ir leaf h form (Nat.mod_lt _ hn) k]

theorem apply_negacyclicConv {f : ℕ} (leaf : ir.Valuation I) (h : ℕ) (form : ConvForm)
    (y : ℕ → (I f).K) {j : ℕ} (hn : 0 < (ir.value h).size) :
    apply ir f leaf (.negacyclicConv h form) y j =
      ∑ k : Fin (ir.value h).size,
        Ops.negCoef (ir.value h).size
          (formPoly f (ir.value h).size (fun s => castElt (leaf h s)) form)
          (j % (ir.value h).size) k *
          y (j / (ir.value h).size * (ir.value h).size + k) := by
  unfold apply
  simp only [block, rows, cols]
  rw [Ops.negacyclic_eq_sum_negCoef _ _ _ (Nat.mod_lt _ hn),
    Fin.sum_univ_eq_sum_range (fun k => Ops.negCoef (ir.value h).size
      (formPoly f (ir.value h).size (fun s => castElt (leaf h s)) form) (j % (ir.value h).size) k *
        y (j / (ir.value h).size * (ir.value h).size + k)) (ir.value h).size]

/-- **A batch of numbers from their digits on one block**: column `t` of row `j < b` is
`base^(t − j k)` on the row's digits `[j k, j k + k)`, `0` elsewhere. -/
theorem block_batched_fromDigits_unit {f : ℕ} (leaf : ir.Valuation I) {b k base j : ℕ}
    (hj : j < b) (t : ℕ) :
    block ir f leaf (.batched b (.fromDigits k base)) (fun s => if s = t then 1 else 0) j =
      if j * k ≤ t ∧ t < j * k + k then (I f).decode base ^ (t - j * k) else 0 := by
  simp only [block, rows, cols, Nat.mul_one, if_pos hj, Nat.div_one, Nat.mod_one, Ops.fromDigits,
    ite_true, mul_ite, mul_one, mul_zero]
  split_ifs with ht
  · rw [Finset.sum_eq_single ⟨t - j * k, by omega⟩]
    · rw [if_pos (by simp only; omega)]
    · intro l _ hl
      rw [if_neg]
      intro h
      exact hl (Fin.ext (by simp only; omega))
    · simp
  · refine Finset.sum_eq_zero fun l _ => if_neg fun h => ht ⟨by omega, by have := l.2; omega⟩

theorem applyInt_batched_fromDigits {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (hchar : CharP (I f).K p) (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k) (hp0 : 0 < p)
    (leaf : ir.Valuation I) {b k base : ℕ} (hb : 0 < b)
    (hdec : (I f).decode base = (base : (I f).K)) (hw : ∀ l < k, 2 * base ^ l < p)
    (x : ℕ → ℤ) (j : ℕ) :
    applyInt ir f leaf (.batched b (.fromDigits k base)) x j =
      ∑ l : Fin k, ((base ^ (l : ℕ) : ℕ) : ℤ) * x (j / b * (b * k) + (j % b * k + l)) := by
  have hjb : j % b < b := Nat.mod_lt _ hb
  set c := j / b * (b * k)
  set a := j % b * k
  let g : ℕ → ℤ := fun t => if a ≤ t ∧ t < a + k then
    ((base ^ ((c + t) - (c + a)) : ℕ) : ℤ) * x (c + t) else 0
  have hentry : ∀ t : Fin (cols ir (.batched b (.fromDigits k base))),
      (I f).coefInt (block ir f leaf (.batched b (.fromDigits k base))
        (fun s => if s = (t : ℕ) then 1 else 0) (j % rows ir (.batched b (.fromDigits k base)))) *
        x (j / rows ir (.batched b (.fromDigits k base)) *
          cols ir (.batched b (.fromDigits k base)) + t) = g t := by
    intro t
    simp only [rows, cols, Nat.mul_one]
    rw [block_batched_fromDigits_unit ir leaf hjb]
    simp only [g]
    split_ifs with ht
    · rw [hdec, ← Nat.cast_pow, show (c + t) - (c + a) = t - j % b * k by omega]
      have hl := hw (t - j % b * k) (by omega)
      rw [show ((base ^ (t - j % b * k) : ℕ) : (I f).K) = (((base ^ (t - j % b * k) : ℕ) : ℤ) :
        (I f).K) by simp, FieldInterp.coefInt_intCast hp hchar htn (by
          rw [abs_of_nonneg (by positivity)]; exact_mod_cast hl)]
    · have h0 : (0 : (I f).K) = ((0 : ℤ) : (I f).K) := by simp
      rw [h0, FieldInterp.coefInt_intCast hp hchar htn (by simpa using hp0), zero_mul]
  unfold applyInt
  rw [Finset.sum_congr rfl fun t _ => hentry t,
    Fin.sum_univ_eq_sum_range g (cols ir (.batched b (.fromDigits k base)))]
  change ∑ t ∈ Finset.range (b * k), g t = _
  rw [← Fin.sum_univ_eq_sum_range g (b * k)]
  have hak : a + k ≤ b * k := by
    have : (j % b + 1) * k ≤ b * k := Nat.mul_le_mul_right _ hjb
    simp only [a]
    nlinarith
  rw [RealizedProgram.sum_fin_indicator c a k (b * k)
    (fun u => ((base ^ (u - (c + a)) : ℕ) : ℤ) * x u) hak]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 3
  omega

theorem apply_batched_fromDigits' {f : ℕ} (leaf : ir.Valuation I) {b k base : ℕ} (hb : 0 < b)
    (y : ℕ → (I f).K) (j : ℕ) :
    apply ir f leaf (.batched b (.fromDigits k base)) y j =
      ∑ l : Fin k, (I f).decode base ^ (l : ℕ) * y (j / b * (b * k) + (j % b * k + l)) := by
  have hjb : j % b < b := Nat.mod_lt _ hb
  simp only [apply, block, rows, cols, Nat.mul_one, if_pos hjb, Nat.div_one, Nat.mod_one,
    Ops.fromDigits, ite_true]

/-- **A polynomial operand's coefficients in its form are small integers' casts** (`formIvl`): in
coefficient form from the values' intervals (`hA`). -/
theorem formPoly_small {f : ℕ} {leaf : ir.Valuation I} {leafI : ℕ → Option Ivl}
    {il : ℕ → ℕ → ℤ}
    (hA : ∀ v A, leafI v = some A → ∀ s < (ir.value v).size,
      il v s ∈ A ∧ ((il v s : ℤ) : (I f).K) = castElt (leaf v s))
    {h : ℕ} {form : ConvForm} {A : Ivl}
    (hF : formIvl leafI h form = some A) {s : ℕ} (hs : s < (ir.value h).size) :
    ∃ z : ℤ, |z| ≤ A.mag ∧
      formPoly f (ir.value h).size (fun s => castElt (leaf h s)) form s = (z : (I f).K) := by
  cases form with
  | coefficients =>
    obtain ⟨hm, hc⟩ := hA h A hF s hs
    exact ⟨_, Ivl.abs_le_mag hm, hc.symm⟩
  | ntt psi => cases hF

/-! ### Row-form operators -/

/-- **A row-form operator** with coefficients `κ`: on one block, output `r < rows` is
`Σ_{c < cols} κ r c · x_c`. -/
def RowForm (f : ℕ) (leaf : ir.Valuation I) (op : NamedOp) (κ : ℕ → ℕ → (I f).K) : Prop :=
  ∀ (x : ℕ → (I f).K) (r : ℕ), r < rows ir op →
    block ir f leaf op x r = ∑ c : Fin (cols ir op), κ r c * x c

/-- **A sum against a unit vector at an offset** picks its coordinate when it lies in the window. -/
theorem sum_fin_mul_unit {K : Type*} [Semiring K] (C a t : ℕ) (κ : ℕ → K) :
    ∑ c : Fin C, κ c * (if a + (c : ℕ) = t then 1 else 0) =
      if a ≤ t ∧ t < a + C then κ (t - a) else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨t - a, by omega⟩]
    · simp only [show a + (t - a) = t by omega, if_true, mul_one]
    · intro c _ hc
      have : a + (c : ℕ) ≠ t := fun h' => hc (Fin.ext (by simp only; omega))
      simp [this]
    · simp
  · refine Finset.sum_eq_zero fun c _ => ?_
    have : a + (c : ℕ) ≠ t := fun h' => h ⟨by omega, by have := c.2; omega⟩
    simp [this]

theorem block_unit_of_rowForm {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp}
    {κ : ℕ → ℕ → (I f).K} (h : RowForm ir f leaf op κ) {r : ℕ} (hr : r < rows ir op)
    (t : Fin (cols ir op)) : block ir f leaf op (fun s => if s = t then 1 else 0) r = κ r t := by
  rw [h _ r hr]
  have := sum_fin_mul_unit (cols ir op) 0 t (κ r)
  simp only [Nat.zero_add, Nat.zero_le, true_and, t.2, if_true, Nat.sub_zero] at this
  exact this

/-- **A row-form operator along the last axis, on the integers**: coordinate `j` is
`Σ_c ⌊κ (j mod R) c⌉ x(⌊j / R⌋ C + c)`. -/
theorem applyInt_of_rowForm {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp}
    {κ : ℕ → ℕ → (I f).K} (h : RowForm ir f leaf op κ) (hr : 0 < rows ir op) (x : ℕ → ℤ)
    (j : ℕ) : applyInt ir f leaf op x j = ∑ c : Fin (cols ir op),
      (I f).coefInt (κ (j % rows ir op) c) * x (j / rows ir op * cols ir op + c) := by
  unfold applyInt
  exact Finset.sum_congr rfl fun t _ => by rw [block_unit_of_rowForm ir h (Nat.mod_lt _ hr) t]

/-- **A row-form operator along the last axis**: coordinate `j` is
`Σ_c κ (j mod R) c · y(⌊j / R⌋ C + c)`. -/
theorem apply_of_rowForm {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp}
    {κ : ℕ → ℕ → (I f).K} (h : RowForm ir f leaf op κ) (hr : 0 < rows ir op)
    (y : ℕ → (I f).K) (j : ℕ) : apply ir f leaf op y j = ∑ c : Fin (cols ir op),
      κ (j % rows ir op) c * y (j / rows ir op * cols ir op + c) := by
  unfold apply
  rw [h _ _ (Nat.mod_lt _ hr)]

/-- **The index arithmetic of a batch** of `b` blocks of `R` rows and `C` columns: coordinate `j`
is row `j mod R` of block `⌊j / R⌋`. -/
theorem batch_index {b R C j : ℕ} (hb : 0 < b) (hR : 0 < R) :
    j % (b * R) % R = j % R ∧ j % (b * R) < b * R ∧
      j / (b * R) * (b * C) + j % (b * R) / R * C = j / R * C ∧ j % (b * R) / R < b := by
  have h1 : j % (b * R) / R = j / R % b := by rw [Nat.mul_comm b R, Nat.mod_mul_right_div_self]
  have h2 : j / (b * R) = j / R / b := by rw [Nat.mul_comm b R, Nat.div_div_eq_div_mul]
  refine ⟨Nat.mod_mul_left_mod _ _ _, Nat.mod_lt _ (Nat.mul_pos hb hR), ?_, ?_⟩
  · rw [h1, h2]
    have := Nat.div_add_mod (j / R) b
    calc j / R / b * (b * C) + j / R % b * C = (b * (j / R / b) + j / R % b) * C := by ring
      _ = j / R * C := by rw [this]
  · rw [h1]
    exact Nat.mod_lt _ hb

/-- **A batch of a row-form operator along the last axis**: as the operator itself
(`apply_of_rowForm`). -/
theorem apply_batched_of_rowForm {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp}
    {κ : ℕ → ℕ → (I f).K} (h : RowForm ir f leaf op κ) {b : ℕ} (hb : 0 < b)
    (hr : 0 < rows ir op) (y : ℕ → (I f).K) (j : ℕ) :
    apply ir f leaf (.batched b op) y j = ∑ c : Fin (cols ir op),
      κ (j % rows ir op) c * y (j / rows ir op * cols ir op + c) := by
  obtain ⟨i1, i2, i3, -⟩ := batch_index (C := cols ir op) (j := j) hb hr
  simp only [apply, block, rows, cols, i2, if_true]
  rw [h _ _ (Nat.mod_lt _ hr), i1]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Nat.add_assoc, i3]

/-- **A batch of a row-form operator along the last axis, on the integers**: as the operator itself
(`applyInt_of_rowForm`), where the integer reading of `0` is `0`. -/
theorem applyInt_batched_of_rowForm {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp}
    {κ : ℕ → ℕ → (I f).K} (h : RowForm ir f leaf op κ) {b : ℕ} (hb : 0 < b)
    (hr : 0 < rows ir op) (hz : (I f).coefInt 0 = 0) (x : ℕ → ℤ) (j : ℕ) :
    applyInt ir f leaf (.batched b op) x j = ∑ c : Fin (cols ir op),
      (I f).coefInt (κ (j % rows ir op) c) * x (j / rows ir op * cols ir op + c) := by
  obtain ⟨i1, i2, i3, i4⟩ := batch_index (C := cols ir op) (j := j) hb hr
  have haC : j % (b * rows ir op) / rows ir op * cols ir op + cols ir op ≤ b * cols ir op := by
    have := Nat.mul_le_mul_right (cols ir op)
      (show j % (b * rows ir op) / rows ir op + 1 ≤ b by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    exact this
  let q := j / (b * rows ir op) * (b * cols ir op)
  let a := j % (b * rows ir op) / rows ir op * cols ir op
  let g : ℕ → ℤ := fun v => (I f).coefInt (κ (j % rows ir op) (v - (q + a))) * x v
  have hterm : ∀ t : Fin (cols ir (.batched b op)),
      (I f).coefInt (block ir f leaf (.batched b op) (fun s => if s = (t : ℕ) then 1 else 0)
        (j % rows ir (.batched b op))) * x (j / rows ir (.batched b op) *
          cols ir (.batched b op) + t) =
        if a ≤ t ∧ (t : ℕ) < a + cols ir op then g (q + t) else 0 := by
    intro t
    simp only [rows, cols, block, i2, if_true]
    rw [h _ _ (Nat.mod_lt _ hr), i1]
    erw [sum_fin_mul_unit (cols ir op) (j % (b * rows ir op) / rows ir op * cols ir op) t
      (κ (j % rows ir op))]
    simp only [g, q, a]
    split_ifs with ht
    · rw [show j / (b * rows ir op) * (b * cols ir op) + (t : ℕ) -
          (j / (b * rows ir op) * (b * cols ir op) + j % (b * rows ir op) / rows ir op * cols ir op)
          = t - j % (b * rows ir op) / rows ir op * cols ir op by omega]
    · rw [hz, zero_mul]
  unfold applyInt
  rw [Finset.sum_congr rfl fun t _ => hterm t]
  change ∑ t : Fin (b * cols ir op), _ = _
  rw [RealizedProgram.sum_fin_indicator q a (cols ir op) (b * cols ir op) g haC]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [g, q, a]
  rw [show j / (b * rows ir op) * (b * cols ir op) +
      (j % (b * rows ir op) / rows ir op * cols ir op + (c : ℕ)) -
      (j / (b * rows ir op) * (b * cols ir op) + j % (b * rows ir op) / rows ir op * cols ir op)
      = c by omega, ← Nat.add_assoc, i3]

/-- **`rowDot` is a row-form operator**: row `r` has the coefficients `M[r W + c]`. -/
theorem rowForm_rowDot {f : ℕ} (leaf : ir.Valuation I) (M R W : ℕ) :
    RowForm ir f leaf (.rowDot M R W) fun r c => castElt (leaf M (r * W + c)) := by
  intro x r hr
  simp only [block, Ops.rowDot, rows] at hr ⊢
  rw [if_pos hr]
  rfl

/-- **A sum over `Fin n` of a window indicator** of `h`: `Σ_b [a + b = r] h_b`. -/
theorem sum_fin_ite_add {K : Type*} [AddCommMonoid K] (n a r : ℕ) (h : ℕ → K) :
    (∑ b : Fin n, if a + (b : ℕ) = r then h b else 0) =
      if a ≤ r ∧ r - a < n then h (r - a) else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun b => if a + b = r then h b else 0) n]
  have := sum_range_ite_add_eq n a r h
  simp only [show ∀ b, (a + b = r) = (b + a = r) from fun b => by rw [Nat.add_comm]]
  exact this

/-- **`acyclicConv` is a row-form operator**: row `i` has the coefficients
`h_{i − a}` for `a ≤ i`, `i − a < lh`, else `0`. -/
theorem rowForm_acyclicConv {f : ℕ} (leaf : ir.Valuation I) (h lx : ℕ) :
    RowForm ir f leaf (.acyclicConv h lx) fun i a =>
      if a ≤ i ∧ i - a < (ir.value h).size then castElt (leaf h (i - a)) else 0 := by
  intro x r hr
  simp only [rows] at hr
  simp only [block, Ops.acyclic, cols]
  rw [if_pos (by omega)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← sum_fin_ite_add (ir.value h).size a r (fun s => castElt (leaf h s)), Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> ring

/-- **The absolute row sums of a row-major list** are at most the largest (`rowAbsMax`). -/
theorem sum_fin_getD_eq {p : ℕ} : ∀ (W : ℕ) (es : List ℕ),
    (∑ c : Fin W, (centeredZ p (es.getD c 0)).natAbs) =
      ((es.take W).map fun c => (centeredZ p c).natAbs).sum
  | 0, _ => by simp
  | W + 1, [] => by
    simp only [List.getD_nil, List.take_nil, List.map_nil, List.sum_nil]
    refine Finset.sum_eq_zero fun _ _ => ?_
    simp [centeredZ]
  | W + 1, c :: es => by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, List.getD_cons_zero, Fin.val_succ, List.getD_cons_succ,
      List.take_succ_cons, List.map_cons, List.sum_cons]
    rw [sum_fin_getD_eq W es]

theorem rowAbs_le_rowAbsMax {p W : ℕ} : ∀ (R : ℕ) (es : List ℕ) {r : ℕ}, r < R →
    (∑ c : Fin W, (centeredZ p (es.getD (r * W + c) 0)).natAbs) ≤ rowAbsMax p W R es
  | 0, _, _, hr => absurd hr (Nat.not_lt_zero _)
  | R + 1, es, r, hr => by
    simp only [rowAbsMax]
    rcases r with _ | r
    · simp only [Nat.zero_mul, Nat.zero_add]
      rw [sum_fin_getD_eq]
      exact le_max_left _ _
    · refine le_trans ?_ (le_max_right _ _)
      have hdrop : ∀ c : Fin W, es.getD ((r + 1) * W + c) 0 = (es.drop W).getD (r * W + c) 0 := by
        intro c
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]
        congr 2
        ring
      simp only [hdrop]
      exact rowAbs_le_rowAbsMax R (es.drop W) (by omega)

/-- **A sum of products by members of `[lo, hi]`, nonnegative coefficients summing to at most `r`**
lies in `[min(lo, 0) r, max(hi, 0) r]`. -/
theorem sum_nonneg_mul_mem {n : ℕ} (e : Fin n → ℤ) (y : Fin n → ℤ) {J : Ivl} {r : ℤ}
    (he : ∀ c, 0 ≤ e c) (hsum : ∑ c, e c ≤ r) (hy : ∀ c, y c ∈ J) :
    ∑ c, e c * y c ∈ (⟨min J.lo 0 * r, max J.hi 0 * r⟩ : Ivl) := by
  have hlo : ∀ c, e c * min J.lo 0 ≤ e c * y c := fun c =>
    mul_le_mul_of_nonneg_left ((min_le_left _ _).trans (hy c).1) (he c)
  have hhi : ∀ c, e c * y c ≤ e c * max J.hi 0 := fun c =>
    mul_le_mul_of_nonneg_left ((hy c).2.trans (le_max_left _ _)) (he c)
  have hs0 : 0 ≤ ∑ c, e c := Finset.sum_nonneg fun c _ => he c
  constructor
  · calc min J.lo 0 * r ≤ min J.lo 0 * ∑ c, e c :=
          mul_le_mul_of_nonpos_left hsum (min_le_right _ _)
      _ = ∑ c, e c * min J.lo 0 := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => mul_comm _ _
      _ ≤ _ := Finset.sum_le_sum fun c _ => hlo c
  · calc ∑ c, e c * y c ≤ ∑ c, e c * max J.hi 0 := Finset.sum_le_sum fun c _ => hhi c
      _ = max J.hi 0 * ∑ c, e c := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun c _ => mul_comm _ _
      _ ≤ max J.hi 0 * r := mul_le_mul_of_nonneg_left hsum (le_max_right _ _)

/-- **A row of the acyclic convolution has at most `min(lx, lh)` entries.** -/
theorem card_acyclic_row_le (lx lh i : ℕ) :
    ((Finset.univ : Finset (Fin lx)).filter fun a : Fin lx => (a : ℕ) ≤ i ∧ i - (a : ℕ) < lh).card ≤
      min lx lh := by
  refine le_min ((Finset.card_filter_le _ _).trans (by simp)) ?_
  calc _ ≤ (Finset.range lh).card := by
        refine Finset.card_le_card_of_injOn (fun a => i - (a : ℕ)) (fun a ha => ?_) ?_
        · simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha
          simpa using ha.2
        · intro a ha a' ha' h
          simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at ha ha'
          simp only at h
          exact Fin.ext (by omega)
    _ = lh := Finset.card_range lh

/-- **The row-form operators' interval is sound and their integer reading casts**
(`NamedOp.rowFormIvl`): the operator is of row form with coefficients `κ` whose integer readings
cast back to them, and every row `u < rows` of the integer readings sends an operand within `J₁` to
`J`. -/
theorem rowFormIvl_sound {f p : ℕ} (hp : (I f).spec.characteristic = p) (hchar : CharP (I f).K p)
    (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k) (leaf : ir.Valuation I)
    {leafI : ℕ → Option Ivl} {il : ℕ → ℕ → ℤ}
    (hA : ∀ v A, leafI v = some A → ∀ s < (ir.value v).size,
      il v s ∈ A ∧ ((il v s : ℤ) : (I f).K) = castElt (leaf v s))
    (hconst : ∀ v J es, leafI v = some J → (ir.value v).kind = .constant es →
      ∀ s, il v s = centeredZ p (es.getD s 0))
    {op : NamedOp} {J₁ J : Ivl} (h : op.rowFormIvl ir leafI p J₁ = some J) :
    ∃ κ : ℕ → ℕ → (I f).K, RowForm ir f leaf op κ ∧ (I f).coefInt 0 = 0 ∧
      (∀ u < rows ir op, ∀ c < cols ir op,
        (((I f).coefInt (κ u c) : ℤ) : (I f).K) = κ u c) ∧
      ∀ u < rows ir op, ∀ y : Fin (cols ir op) → ℤ, (∀ c, y c ∈ J₁) →
        ∑ c : Fin (cols ir op), (I f).coefInt (κ u c) * y c ∈ J := by
  have hsmall : ∀ {z : ℤ}, 2 * |z| < p → (I f).coefInt (z : (I f).K) = z := fun hz =>
    FieldInterp.coefInt_intCast hp hchar htn hz
  match op, h with
  | .rowDot M R W, h =>
    simp only [rowFormIvl] at h
    split at h
    · rename_i es hk
      split_ifs at h with hc
      cases h
      obtain ⟨hM, hp0, hRW, hes⟩ := hc
      obtain ⟨A, hA'⟩ := Option.isSome_iff_exists.1 hM
      have hent : ∀ u < R, ∀ c < W, ∃ z : ℤ, z = centeredZ p (es.getD (u * W + c) 0) ∧
          2 * |z| < p ∧ castElt (leaf M (u * W + c)) = ((z : ℤ) : (I f).K) := by
        intro u hu c hc
        have hs : u * W + c < (ir.value M).size := by
          have : (u + 1) * W ≤ R * W := Nat.mul_le_mul_right _ hu
          nlinarith
        refine ⟨_, rfl, ?_, ?_⟩
        · rcases Nat.lt_or_ge (u * W + c) es.length with hl | hl
          · have hmem : es.getD (u * W + c) 0 ∈ es := by
              rw [getD_of_lt _ hl]
              exact List.getElem_mem hl
            simpa using List.all_eq_true.1 hes _ hmem
          · rw [getD_of_ge _ hl]
            simp only [centeredZ]
            split_ifs <;> simp <;> omega
        · rw [← (hA M A hA' _ hs).2, hconst M A es hA' hk]
      refine ⟨fun r c => castElt (leaf M (r * W + c)), rowForm_rowDot ir leaf M R W, ?_, ?_, ?_⟩
      · have := hsmall (z := 0) (by simpa using hp0)
        simpa using this
      · intro u hu c hc
        obtain ⟨z, -, hz, he⟩ := hent u hu c hc
        show (((I f).coefInt (castElt (leaf M (u * W + c))) : ℤ) : (I f).K) =
          castElt (leaf M (u * W + c))
        rw [he, hsmall hz]
      · intro u hu y hy
        rw [Ivl.mem_sym]
        have hcoef : ∀ c : Fin (cols ir (.rowDot M R W)),
            (I f).coefInt (castElt (leaf M (u * W + c))) = centeredZ p (es.getD (u * W + c) 0) := by
          intro c
          obtain ⟨z, rfl, hz, he⟩ := hent u hu c c.2
          rw [he, hsmall hz]
        simp only [hcoef]
        calc |∑ c : Fin (cols ir (.rowDot M R W)), centeredZ p (es.getD (u * W + c) 0) * y c|
            ≤ ∑ c : Fin (cols ir (.rowDot M R W)), |centeredZ p (es.getD (u * W + c) 0) * y c| :=
              Finset.abs_sum_le_sum_abs _ _
          _ ≤ ∑ c : Fin (cols ir (.rowDot M R W)),
                ((centeredZ p (es.getD (u * W + c) 0)).natAbs : ℤ) * J₁.mag :=
              Finset.sum_le_sum fun c _ => by
                rw [abs_mul, Int.natCast_natAbs]
                exact mul_le_mul_of_nonneg_left (Ivl.abs_le_mag (hy c)) (abs_nonneg _)
          _ = ((∑ c : Fin W, (centeredZ p (es.getD (u * W + c) 0)).natAbs : ℕ) : ℤ) * J₁.mag := by
              rw [Nat.cast_sum, Finset.sum_mul]
              rfl
          _ ≤ ((rowAbsMax p W R es * J₁.mag : ℕ) : ℤ) := by
              rw [Nat.cast_mul]
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast rowAbs_le_rowAbsMax R es hu)
                (Nat.cast_nonneg _)
    · cases h
  | .acyclicConv hv lx, h =>
    simp only [rowFormIvl, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA', h⟩ := h
    split_ifs at h with hc
    cases h
    obtain ⟨hlo, hhi0, hhi⟩ := hc
    have hp0 : 0 < p := by omega
    have hz0 : (I f).coefInt 0 = 0 := by simpa using hsmall (z := 0) (by simpa using hp0)
    have hent : ∀ i a, a ≤ i ∧ i - a < (ir.value hv).size →
        (I f).coefInt (castElt (leaf hv (i - a))) = il hv (i - a) ∧ 0 ≤ il hv (i - a) ∧
          il hv (i - a) ≤ A.hi ∧ castElt (leaf hv (i - a)) = ((il hv (i - a) : ℤ) : (I f).K) := by
      intro i a ha
      obtain ⟨hm, hc⟩ := hA hv A hA' _ ha.2
      have h1 : 0 ≤ il hv (i - a) := hlo.trans hm.1
      have h2 : 2 * |il hv (i - a)| < p := by
        rw [abs_of_nonneg h1]
        linarith [hm.2]
      exact ⟨by rw [← hc, hsmall h2], h1, hm.2, hc.symm⟩
    refine ⟨_, rowForm_acyclicConv ir leaf hv lx, hz0, ?_, ?_⟩
    · intro u _ c _
      split_ifs with ha
      · rw [(hent u c ha).2.2.2, hsmall (by
          rw [abs_of_nonneg (hent u c ha).2.1]
          linarith [(hent u c ha).2.2.1])]
      · rw [hz0]
        simp
    · intro u _ y hy
      have hnn : ∀ c : Fin (cols ir (.acyclicConv hv lx)), 0 ≤ (I f).coefInt
          (if (c : ℕ) ≤ u ∧ u - c < (ir.value hv).size then castElt (leaf hv (u - c)) else 0) := by
        intro c
        split_ifs with ha
        · rw [(hent u c ha).1]
          exact (hent u c ha).2.1
        · rw [hz0]
      refine sum_nonneg_mul_mem _ y hnn ?_ hy
      calc _ ≤ ∑ c : Fin lx, if (c : ℕ) ≤ u ∧ u - c < (ir.value hv).size then A.hi else 0 :=
            Finset.sum_le_sum fun c _ => by
              split_ifs with ha
              · rw [(hent u c ha).1]
                exact (hent u c ha).2.2.1
              · rw [hz0]
        _ = ((Finset.univ.filter fun a : Fin lx =>
              (a : ℕ) ≤ u ∧ u - a < (ir.value hv).size).card : ℤ) * A.hi := by
            rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((min lx (ir.value hv).size : ℕ) : ℤ) * A.hi :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast card_acyclic_row_le lx _ u)
              (by linarith)

/-- **A row-form interval gives the polynomial operators' conclusion** (`applyInt_polyIvl`) for the
operator itself. -/
theorem rowForm_conclude {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp} {κ : ℕ → ℕ → (I f).K}
    {J₁ J : Ivl} (hR : RowForm ir f leaf op κ)
    (hcast : ∀ u < rows ir op, ∀ c < cols ir op, (((I f).coefInt (κ u c) : ℤ) : (I f).K) = κ u c)
    (hmem : ∀ u < rows ir op, ∀ y : Fin (cols ir op) → ℤ, (∀ c, y c ∈ J₁) →
      ∑ c : Fin (cols ir op), (I f).coefInt (κ u c) * y c ∈ J)
    {x : ℕ → ℤ} {Len i : ℕ} (hi : i < Len / cols ir op * rows ir op) :
    ((∀ t < Len, x t ∈ J₁) → applyInt ir f leaf op x i ∈ J) ∧
      ∀ y : ℕ → (I f).K, (∀ t < Len, ((x t : ℤ) : (I f).K) = y t) →
        ((applyInt ir f leaf op x i : ℤ) : (I f).K) = apply ir f leaf op y i := by
  have hr : 0 < rows ir op := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hi
    omega
  have hidx : ∀ c : Fin (cols ir op), i / rows ir op * cols ir op + c < Len := fun c =>
    lt_of_cols ir hr hi c.2
  refine ⟨fun hx => ?_, fun y hy => ?_⟩
  · rw [applyInt_of_rowForm ir hR hr]
    exact hmem _ (Nat.mod_lt _ hr) _ fun c => hx _ (hidx c)
  · rw [applyInt_of_rowForm ir hR hr, apply_of_rowForm ir hR hr]
    push_cast
    exact Finset.sum_congr rfl fun c _ => by rw [hcast _ (Nat.mod_lt _ hr) _ c.2, hy _ (hidx c)]

/-- **A row-form interval gives the polynomial operators' conclusion** (`applyInt_polyIvl`) for a
batch of the operator. -/
theorem rowForm_batched_conclude {f : ℕ} {leaf : ir.Valuation I} {op : NamedOp}
    {κ : ℕ → ℕ → (I f).K} {J₁ J : Ivl} {b : ℕ} (hb : 0 < b) (hR : RowForm ir f leaf op κ)
    (hz : (I f).coefInt 0 = 0)
    (hcast : ∀ u < rows ir op, ∀ c < cols ir op, (((I f).coefInt (κ u c) : ℤ) : (I f).K) = κ u c)
    (hmem : ∀ u < rows ir op, ∀ y : Fin (cols ir op) → ℤ, (∀ c, y c ∈ J₁) →
      ∑ c : Fin (cols ir op), (I f).coefInt (κ u c) * y c ∈ J)
    {x : ℕ → ℤ} {Len i : ℕ} (hi : i < Len / cols ir (.batched b op) * rows ir (.batched b op)) :
    ((∀ t < Len, x t ∈ J₁) → applyInt ir f leaf (.batched b op) x i ∈ J) ∧
      ∀ y : ℕ → (I f).K, (∀ t < Len, ((x t : ℤ) : (I f).K) = y t) →
        ((applyInt ir f leaf (.batched b op) x i : ℤ) : (I f).K) =
          apply ir f leaf (.batched b op) y i := by
  have hr' : 0 < rows ir (.batched b op) := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hi
    omega
  have hr : 0 < rows ir op := by
    simp only [rows] at hr'
    exact Nat.pos_of_mul_pos_left hr'
  obtain ⟨-, -, i3, i4⟩ := batch_index (C := cols ir op) (j := i) hb hr
  have hidx : ∀ c : Fin (cols ir op), i / rows ir op * cols ir op + c < Len := fun c => by
    have := lt_of_cols ir hr' hi (t := i % (b * rows ir op) / rows ir op * cols ir op + c) (by
      simp only [cols]
      have := Nat.mul_le_mul_right (cols ir op)
        (show i % (b * rows ir op) / rows ir op + 1 ≤ b by omega)
      have := c.2
      nlinarith)
    simp only [rows, cols] at this
    rwa [← Nat.add_assoc, i3] at this
  refine ⟨fun hx => ?_, fun y hy => ?_⟩
  · rw [applyInt_batched_of_rowForm ir hR hb hr hz]
    exact hmem _ (Nat.mod_lt _ hr) _ fun c => hx _ (hidx c)
  · rw [applyInt_batched_of_rowForm ir hR hb hr hz, apply_batched_of_rowForm ir hR hb hr]
    push_cast
    exact Finset.sum_congr rfl fun c _ => by rw [hcast _ (Nat.mod_lt _ hr) _ c.2, hy _ (hidx c)]

/-- **The polynomial operators' interval is sound and their integer reading casts**
(`NamedOp.polyIvl`): on an operand whose coordinates below `Len` lie in `J₁`, every output
coordinate below the length lies in the interval, and casts to the operator's value on any
operand the integer coordinates cast to. -/
theorem applyInt_polyIvl {f p : ℕ} (hp : (I f).spec.characteristic = p) (hchar : CharP (I f).K p)
    (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k) (leaf : ir.Valuation I) {leafI : ℕ → Option Ivl}
    {il : ℕ → ℕ → ℤ}
    (hA : ∀ v A, leafI v = some A → ∀ s < (ir.value v).size,
      il v s ∈ A ∧ ((il v s : ℤ) : (I f).K) = castElt (leaf v s))
    (hdec0 : ∀ c < p, (I f).decode c = (c : (I f).K))
    (hconst : ∀ v J es, leafI v = some J → (ir.value v).kind = .constant es →
      ∀ s, il v s = centeredZ p (es.getD s 0))
    {op : NamedOp} {J₁ J : Ivl} (h : op.polyIvl ir leafI p J₁ = some J) {x : ℕ → ℤ} {Len : ℕ}
    {i : ℕ} (hi : i < Len / cols ir op * rows ir op) :
    ((∀ t < Len, x t ∈ J₁) → applyInt ir f leaf op x i ∈ J) ∧
      ∀ y : ℕ → (I f).K, (∀ t < Len, ((x t : ℤ) : (I f).K) = y t) →
        ((applyInt ir f leaf op x i : ℤ) : (I f).K) = apply ir f leaf op y i := by
  have hr : 0 < rows ir op := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, Nat.mul_zero] at hi
    omega
  have hcoef : ∀ {M : ℕ} {E : (I f).K}, 2 * M < p → (∃ z : ℤ, |z| ≤ M ∧ E = (z : (I f).K)) →
      |(I f).coefInt E| ≤ M ∧ (((I f).coefInt E : ℤ) : (I f).K) = E := by
    intro M E hM ⟨z, hz, hE⟩
    rw [hE, FieldInterp.coefInt_intCast hp hchar htn (by omega)]
    exact ⟨hz, rfl⟩
  match op, h with
  | .rowDot M R W, h =>
    simp only [polyIvl] at h
    obtain ⟨κ, hR, -, hc, hm⟩ := rowFormIvl_sound ir hp hchar htn leaf hA hconst h
    exact rowForm_conclude ir hR hc hm hi
  | .acyclicConv hv lx, h =>
    simp only [polyIvl] at h
    obtain ⟨κ, hR, -, hc, hm⟩ := rowFormIvl_sound ir hp hchar htn leaf hA hconst h
    exact rowForm_conclude ir hR hc hm hi
  | .batched b op, h =>
    simp only [polyIvl] at h
    split at h
    rotate_left
    · split_ifs at h with hb
      obtain ⟨κ, hR, hz, hc, hm⟩ := rowFormIvl_sound ir hp hchar htn leaf hA hconst h
      exact rowForm_batched_conclude ir hb hR hz hc hm hi
    rename_i k base
    split_ifs at h with hc
    cases h
    obtain ⟨hb, hbp, hw⟩ := hc
    have hw' : ∀ l < k, 2 * base ^ l < p := fun l hl => by
      simpa using List.all_eq_true.1 hw l (List.mem_range.2 hl)
    have hdec : (I f).decode base = (base : (I f).K) := hdec0 base hbp
    have hidx : ∀ l : Fin k, i / b * (b * k) + (i % b * k + l) < Len := fun l => by
      have := lt_of_cols ir (op := .batched b (.fromDigits k base)) hr hi
        (t := i % b * k + l) (by
          simp only [cols]
          have := Nat.mod_lt i hb
          have := l.2
          nlinarith)
      simpa [rows, cols] using this
    refine ⟨fun hx => ?_, fun y hy => ?_⟩
    · rw [applyInt_batched_fromDigits ir hp hchar htn (by omega) leaf hb hdec hw']
      have := Ivl.sum_weight_mem (fun l : Fin k => base ^ (l : ℕ))
        (fun l => x (i / b * (b * k) + (i % b * k + l))) (fun l => hx _ (hidx l))
      rwa [show (∑ l : Fin k, base ^ (l : ℕ)) = digitsWeight base k from
        Fin.sum_univ_eq_sum_range (base ^ ·) k] at this
    · rw [applyInt_batched_fromDigits ir hp hchar htn (by omega) leaf hb hdec hw',
        apply_batched_fromDigits' ir leaf hb]
      push_cast
      exact Finset.sum_congr rfl fun l _ => by rw [hdec, hy _ (hidx l)]
  | .negacyclicConv hv form, h =>
    simp only [polyIvl, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA', h⟩ := h
    split_ifs at h with hM
    cases h
    have hn : 0 < (ir.value hv).size := hr
    have hent := fun k : Fin (ir.value hv).size => hcoef hM
      (signed_small (fun s hs => formPoly_small ir hA hA' hs) (Ops.negCoef_signed _ _
        (i % (ir.value hv).size) k))
    have hidx : ∀ k : Fin (ir.value hv).size,
        i / (ir.value hv).size * (ir.value hv).size + k < Len := fun k =>
      lt_of_cols ir (op := .negacyclicConv hv form) hr hi k.2
    refine ⟨fun hx => ?_, fun y hy => ?_⟩
    · rw [applyInt_negacyclicConv ir leaf hv form x hn, Ivl.mem_sym]
      have := abs_sum_sum_le (L := 1) (fun _ k => (I f).coefInt (Ops.negCoef (ir.value hv).size
        (formPoly f (ir.value hv).size (fun s => castElt (leaf hv s)) form)
          (i % (ir.value hv).size) k))
        (fun _ k => x (i / (ir.value hv).size * (ir.value hv).size + k))
        (fun _ k => (hent k).1) (fun _ k => Ivl.abs_le_mag (hx _ (hidx k)))
      simpa using this
    · rw [applyInt_negacyclicConv ir leaf hv form x hn, apply_negacyclicConv ir leaf hv form y hn]
      push_cast
      exact Finset.sum_congr rfl fun k _ => by rw [(hent k).2, hy _ (hidx k)]
  | .polyMatVec a K L .coefficients, h =>
    simp only [polyIvl, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA', h⟩ := h
    split_ifs at h with hM
    cases h
    have hj : i % rows ir (.polyMatVec a K L .coefficients) <
        K * ((ir.value a).size / (K * L)) := Nat.mod_lt _ hr
    have hent := fun l k => hcoef hM (pmv_entry_small ir (hA a A hA') hj l k)
    have hidx : ∀ (l : Fin L) (k : Fin ((ir.value a).size / (K * L))),
        i / rows ir (.polyMatVec a K L .coefficients) * cols ir (.polyMatVec a K L .coefficients) +
          (l * ((ir.value a).size / (K * L)) + k) < Len := fun l k =>
      lt_of_cols ir hr hi (by
        show _ < L * _
        have := l.2
        have := k.2
        nlinarith)
    refine ⟨fun hx => ?_, fun y hy => ?_⟩
    · rw [applyInt_polyMatVec, Ivl.mem_sym]
      exact abs_sum_sum_le _ _ (fun l k => (hent l k).1)
        (fun l k => Ivl.abs_le_mag (hx _ (hidx l k)))
    · rw [applyInt_polyMatVec, apply_polyMatVec]
      push_cast
      exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by
        rw [(hent l k).2, hy _ (hidx l k)]
  | .polyBroadcast t K .coefficients, h =>
    simp only [polyIvl, Option.bind_eq_some_iff] at h
    obtain ⟨A, hA', h⟩ := h
    split_ifs at h with hM
    cases h
    have hent := fun k => hcoef hM (pb_entry_small ir (K := K) (hA t A hA')
      (i % rows ir (.polyBroadcast t K .coefficients)) k)
    have hidx : ∀ k : Fin ((ir.value t).size / K),
        i / rows ir (.polyBroadcast t K .coefficients) *
          cols ir (.polyBroadcast t K .coefficients) + k < Len := fun k =>
      lt_of_cols ir hr hi k.2
    refine ⟨fun hx => ?_, fun y hy => ?_⟩
    · rw [applyInt_polyBroadcast, Ivl.mem_sym]
      have := abs_sum_sum_le (L := 1) (fun _ k => (I f).coefInt (pbEntry ir leaf t K
        (i % rows ir (.polyBroadcast t K .coefficients)) k))
        (fun _ k => x (i / rows ir (.polyBroadcast t K .coefficients) *
          cols ir (.polyBroadcast t K .coefficients) + k))
        (fun _ k => (hent k).1) (fun _ k => Ivl.abs_le_mag (hx _ (hidx k)))
      simpa [cols] using this
    · rw [applyInt_polyBroadcast, apply_polyBroadcast]
      push_cast
      exact Finset.sum_congr rfl fun k _ => by rw [(hent k).2, hy _ (hidx k)]

end NamedOp

/-! ## Soundness and casts, by structure -/

section Core

variable (ir : RealizedProgram) {I : Interp}

/-- The integer readings of `0` and `1` at characteristic `p > 2` are `0` and `1`. -/
theorem coefInt_zero_one {F : FieldInterp} (h01 : F.toNat 0 = 0 ∧ F.toNat 1 = 1)
    (hp : 2 < F.spec.characteristic) : F.coefInt 0 = 0 ∧ F.coefInt 1 = 1 := by
  simp only [FieldInterp.coefInt, h01, FieldInterp.centered]
  constructor
  · rw [ite_eq_left (by omega)]
    rfl
  · rw [ite_eq_left (by omega)]
    rfl

/-- **One of two masked views of disjoint supports is `0`** at each coordinate below the length,
where the integer readings of the zero constants are `0` (`RealizedProgram.maskedPairB`). -/
theorem evalInt_masked_zero {f : ℕ} {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    (hzero : ∀ z, ir.zeroConstB z = true → ∀ i, il z i = 0) {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ}
    {e e' : Expr} (hm : ir.maskedPairB e e' = true) {i : ℕ} (hi : i < Expr.len ir rl e) :
    Expr.evalInt ir f leaf il iref rl e i = 0 ∨ Expr.evalInt ir f leaf il iref rl e' i = 0 := by
  unfold RealizedProgram.maskedPairB at hm
  split at hm
  · rename_i m a z m' a' z'
    simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true,
      decide_eq_true_eq] at hm
    obtain ⟨⟨hz, hz'⟩, hall⟩ := hm
    simp only [Expr.len] at hi
    rcases hall i hi with h | h
    · left
      simp only [Expr.evalInt]
      split_ifs with h'
      · simp only [Expr.len] at h'
        omega
      · exact hzero z hz _
    · right
      simp only [Expr.evalInt]
      split_ifs with h'
      · simp only [Expr.len] at h'
        omega
      · exact hzero z' hz' _
  · cases hm

/-- **A sum of masked views is `0` off its nonzero coordinates** (`RealizedProgram.maskedNz`), where
the integer readings of the zero constants are `0`. -/
theorem evalInt_eq_zero_of_maskedNz {f : ℕ} {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    (hzero : ∀ z, ir.zeroConstB z = true → ∀ i, il z i = 0) {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ} :
    ∀ (e : Expr) {L : List (ℕ × ℕ)}, ir.maskedNz e = some L → ir.shapeOkWith rl e = true →
      ∀ {i : ℕ}, i < Expr.len ir rl e → (∀ iv ∈ L, ¬ (iv.1 ≤ i ∧ i < iv.2)) →
        Expr.evalInt ir f leaf il iref rl e i = 0
  | .reindex m e, L, h, _, i, hi, hL => by
    unfold RealizedProgram.maskedNz at h
    split at h
    · rename_i _ m' a z heq
      cases heq
      split_ifs at h with hz
      cases h
      simp only [Expr.len] at hi
      simp only [Expr.evalInt]
      by_cases ha : m.entry i < (ir.value a).size
      · obtain ⟨iv, hiv, h1, h2⟩ := mem_mapNz m 0 hi ha
        exact absurd ⟨by simpa using h1, by simpa using h2⟩ (hL iv hiv)
      · rw [if_neg (by simpa only [Expr.len] using ha)]
        exact hzero z hz _
    · rename_i heq
      cases heq
    · cases h
  | .add e e', L, h, hs, i, hi, hL => by
    simp only [RealizedProgram.maskedNz] at h
    cases h₁ : ir.maskedNz e with
    | none => simp [h₁] at h
    | some L₁ =>
      cases h₂ : ir.maskedNz e' with
      | none => simp [h₁, h₂] at h
      | some L₂ =>
        simp only [h₁, h₂] at h
        split_ifs at h with hd
        cases h
        simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
        simp only [Expr.len] at hi
        simp only [Expr.evalInt]
        rw [evalInt_eq_zero_of_maskedNz hzero e h₁ hs.1.1 hi
            fun iv hiv => hL iv (List.mem_append_left _ hiv),
          evalInt_eq_zero_of_maskedNz hzero e' h₂ hs.1.2 (hs.2 ▸ hi)
            fun iv hiv => hL iv (List.mem_append_right _ hiv)]
        rfl
  | .leaf _, _, h, _, _, _, _ | .sub _ _, _, h, _, _, _, _ | .scale _ _, _, h, _, _, _, _
  | .mul _ _, _, h, _, _, _, _ | .concat _ _, _, h, _, _, _, _ | .linear _ _, _, h, _, _, _, _
  | .prod _ _, _, h, _, _, _, _ | .mux _ _ _, _, h, _, _, _, _ | .apply _ _, _, h, _, _, _, _
  | .ref _, _, h, _, _, _, _ | .logic _ _ _, _, h, _, _, _, _ => by
    simp [RealizedProgram.maskedNz] at h

/-- **One of two summands is `0`** at each coordinate below the length, where the sum is a sum of
masked views of disjoint supports (`RealizedProgram.maskedNz`) or a masked pair
(`RealizedProgram.maskedPairB`) and the integer readings of the zero constants are `0`. -/
theorem evalInt_maskedSum_zero {f : ℕ} {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    (hzero : ∀ z, ir.zeroConstB z = true → ∀ i, il z i = 0) {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ}
    {e e' : Expr} (hm : ((ir.maskedNz (.add e e')).isSome || ir.maskedPairB e e') = true)
    (hs : ir.shapeOkWith rl e = true) (hs' : ir.shapeOkWith rl e' = true)
    (hlen : Expr.len ir rl e = Expr.len ir rl e') {i : ℕ} (hi : i < Expr.len ir rl e) :
    Expr.evalInt ir f leaf il iref rl e i = 0 ∨ Expr.evalInt ir f leaf il iref rl e' i = 0 := by
  rcases Bool.or_eq_true_iff.1 hm with hm | hm
  · obtain ⟨L, hL⟩ := Option.isSome_iff_exists.1 hm
    simp only [RealizedProgram.maskedNz] at hL
    cases h₁ : ir.maskedNz e with
    | none => simp [h₁] at hL
    | some L₁ =>
      cases h₂ : ir.maskedNz e' with
      | none => simp [h₁, h₂] at hL
      | some L₂ =>
        simp only [h₁, h₂] at hL
        split_ifs at hL with hd
        by_cases hin : ∃ iv ∈ L₁, iv.1 ≤ i ∧ i < iv.2
        · obtain ⟨iv, hiv, hiv'⟩ := hin
          exact .inr (evalInt_eq_zero_of_maskedNz ir hzero e' h₂ hs' (hlen ▸ hi)
            fun iv' hiv'' => not_mem_of_disjointNz hd hiv hiv'' hiv')
        · push_neg at hin
          exact .inl (evalInt_eq_zero_of_maskedNz ir hzero e h₁ hs hi
            fun iv hiv h => absurd h.2 (not_lt.2 (hin iv hiv h.1)))
  · exact evalInt_masked_zero ir hzero hm hi

/-- **A sparse row's integer value lies in its interval** (`linRowIvl`), its operand's coordinates
in `J`. -/
theorem linRowIvl_mem {f p : ℕ} (hp : (I f).spec.characteristic = p) {il : ℕ → ℕ → ℤ} {J : Ivl}
    {y : ℕ → ℤ} : ∀ (ts : List (ℕ × Coef)) {K : Ivl}, linRowIvl p J ts = some K →
      (∀ t ∈ ts, y t.1 ∈ J) → (ts.map fun t => Coef.evalInt (I := I) f il t.2 * y t.1).sum ∈ K
  | [], K, h, _ => by
    simp only [linRowIvl, Option.some.injEq] at h
    subst h
    simp [Ivl.mem_mk]
  | (_, .const c) :: ts, K, h, hy => by
    simp only [linRowIvl] at h
    split_ifs at h with hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨K', hK', rfl⟩ := h
    have hc' : Coef.evalInt (I := I) f il (Coef.const c) = centeredZ p c := by
      simp [Coef.evalInt, FieldInterp.centered_eq, hp]
    simp only [List.map_cons, List.sum_cons, hc']
    exact Ivl.add_mem (Ivl.smul_mem _ (hy _ List.mem_cons_self))
      (linRowIvl_mem (il := il) hp ts hK' fun t ht => hy t (List.mem_cons_of_mem _ ht))
  | (_, .node _ _) :: _, _, h, _ => by simp [linRowIvl] at h

/-- **A sparse row's integer value casts to its value** (`linRowIvl`: constant coefficients below
the characteristic), its operand's integer coordinates casting to its values. -/
theorem linRowIvl_cast {f p : ℕ} (hp : (I f).spec.characteristic = p) (hchar : CharP (I f).K p)
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    {J : Ivl} {y : ℕ → ℤ} {z : ℕ → (I f).K} :
    ∀ (ts : List (ℕ × Coef)) {K : Ivl}, linRowIvl p J ts = some K →
      (∀ t ∈ ts, ((y t.1 : ℤ) : (I f).K) = z t.1) →
        (((ts.map fun t => Coef.evalInt (I := I) f il t.2 * y t.1).sum : ℤ) : (I f).K) =
          (ts.map fun t => Coef.eval ir f leaf t.2 * z t.1).sum
  | [], _, _, _ => by simp
  | (_, .const c) :: ts, K, h, hy => by
    simp only [linRowIvl] at h
    split_ifs at h with hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨K', hK', -⟩ := h
    have hc' : Coef.evalInt (I := I) f il (Coef.const c) = centeredZ p c := by
      simp [Coef.evalInt, FieldInterp.centered_eq, hp]
    have hc'' : Coef.eval ir f leaf (Coef.const c) = ((centeredZ p c : ℤ) : (I f).K) := by
      rw [centeredZ_cast]
      exact hdec c hc
    simp only [List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul, hc', hc'']
    rw [hy _ List.mem_cons_self,
      linRowIvl_cast (il := il) hp hchar hdec ts hK' fun t ht => hy t (List.mem_cons_of_mem _ ht)]
  | (_, .node _ _) :: _, _, h, _ => by simp [linRowIvl] at h

/-- **Every row of a linear map has an interval within the map's** (`linIvl`). -/
theorem linIvl_row {p : ℕ} {J : Ivl} : ∀ (rows : List (List (ℕ × Coef))) {K : Ivl},
    linIvl p J rows = some K → ∀ i < rows.length,
      ∃ A, linRowIvl p J (rows.getD i []) = some A ∧ ∀ x : ℤ, x ∈ A → x ∈ K
  | [], _, _, i, hi => absurd hi (by simp)
  | [r], K, h, i, hi => by
    simp only [List.length_singleton] at hi
    obtain rfl : i = 0 := by omega
    exact ⟨K, by simpa [linIvl] using h, fun _ hx => hx⟩
  | r :: r' :: rs, K, h, i, hi => by
    simp only [linIvl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨A, hA, B, hB, rfl⟩ := h
    rcases i with _ | i
    · exact ⟨A, by simpa using hA, fun _ hx => Ivl.hull_mem_left hx⟩
    · obtain ⟨A', hA', hsub⟩ := linIvl_row (r' :: rs) hB i (by simp at hi ⊢; omega)
      exact ⟨A', by simpa using hA', fun x hx => Ivl.hull_mem_right (hsub x hx)⟩

/-- **A sum of constant multiples of members of `A`** lies in `groupSumIvl`. -/
theorem groupSum_mem {A : Ivl} : ∀ (cs : List ℤ) (x : ℕ → ℤ), (∀ s < cs.length, x s ∈ A) →
    ∑ s ∈ Finset.range cs.length, cs.getD s 0 * x s ∈ groupSumIvl A cs
  | [], _, _ => by simp [groupSumIvl, Ivl.mem_mk]
  | c :: cs, x, hx => by
    rw [List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, groupSumIvl]
    rw [add_comm]
    exact Ivl.add_mem (Ivl.smul_mem c (hx 0 (by simp)))
      (groupSum_mem cs (fun s => x (s + 1)) fun s hs => hx _ (by simp; omega))

theorem getD_take {cs : List ℤ} {w s : ℕ} (hs : s < w) : (cs.take w).getD s 0 = cs.getD s 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hs]

theorem getD_drop {cs : List ℤ} {w t : ℕ} : (cs.drop w).getD t 0 = cs.getD (w + t) 0 := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- **The sums of groups of constant multiples lie in the groups' hull** (`groupsIvl`): group
`j < n`, within the constants, of members of `A`. -/
theorem groupsIvl_mem {A : Ivl} {w : ℕ} : ∀ (n : ℕ) (cs : List ℤ) {K : Ivl},
    groupsIvl A w n cs = some K → ∀ j < n, (j + 1) * w ≤ cs.length → ∀ x : ℕ → ℤ,
      (∀ s < w, x s ∈ A) → ∑ s ∈ Finset.range w, cs.getD (j * w + s) 0 * x s ∈ K
  | 0, _, _, _, _, hj, _, _, _ => absurd hj (Nat.not_lt_zero _)
  | 1, cs, K, h, j, hj, hlen, x, hx => by
    obtain rfl : j = 0 := by omega
    simp only [groupsIvl, Option.some.injEq] at h
    subst h
    have hl : (cs.take w).length = w := by simp only [List.length_take]; omega
    have := groupSum_mem (A := A) (cs.take w) x (fun s hs => hx s (by omega))
    rw [hl] at this
    rw [Finset.sum_congr rfl fun s hs => by
      rw [Nat.zero_mul, Nat.zero_add, ← getD_take (Finset.mem_range.1 hs)]]
    exact this
  | n + 2, cs, K, h, j, hj, hlen, x, hx => by
    simp only [groupsIvl, Option.map_eq_some_iff] at h
    obtain ⟨K', hK', rfl⟩ := h
    rcases j with _ | j
    · refine Ivl.hull_mem_left ?_
      have hl : (cs.take w).length = w := by simp only [List.length_take]; omega
      have := groupSum_mem (A := A) (cs.take w) x (fun s hs => hx s (by omega))
      rw [hl] at this
      rw [Finset.sum_congr rfl fun s hs => by
        rw [Nat.zero_mul, Nat.zero_add, ← getD_take (Finset.mem_range.1 hs)]]
      exact this
    · refine Ivl.hull_mem_right ?_
      have := groupsIvl_mem (n + 1) (cs.drop w) hK' j (by omega)
        (by simp only [List.length_drop]; rw [Nat.add_mul] at hlen; omega) x hx
      rw [Finset.sum_congr rfl fun s _ => by
        rw [show (j + 1) * w + s = w + (j * w + s) by ring, ← getD_drop]]
      exact this

/-- **An index map has `size` entries.** -/
theorem IndexMap.length_toList (m : IndexMap) : m.toList.length = m.size := by
  induction m with
  | nil => rfl
  | cons r rest ih =>
    simp only [IndexMap.toList, List.flatMap_cons, List.length_append, List.length_map,
      List.length_range,
      IndexMap.size, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

/-- **A constant view's coordinates** (`constCoords`): its integer reading, coordinate by
coordinate, where the integer readings of the constants with an interval are their centred
entries (`hconst`). -/
theorem constCoords_eval {f p : ℕ} {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ} {leafI : ℕ → Option Ivl}
    (hconst : ∀ v J es, leafI v = some J → (ir.value v).kind = .constant es →
      ∀ s, il v s = centeredZ p (es.getD s 0))
    {c : Expr} {cs : List ℤ} (h : constCoords ir p leafI c = some cs) :
    cs.length = Expr.len ir rl c ∧
      ∀ t < Expr.len ir rl c, Expr.evalInt ir f leaf il iref rl c t = cs.getD t 0 := by
  unfold constCoords at h
  split at h
  · rename_i C
    split at h
    · rename_i es hk
      split_ifs at h with hC
      cases h
      obtain ⟨J, hJ⟩ := Option.isSome_iff_exists.1 hC
      refine ⟨by simp [Expr.len], fun t ht => ?_⟩
      simp only [Expr.len] at ht
      simp only [Expr.evalInt, hconst C J es hJ hk]
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      simp only [List.getElem?_map, List.getElem?_take, if_pos ht]
      rcases Nat.lt_or_ge t es.length with hl | hl
      · simp [List.getElem?_append_left hl, List.getElem?_eq_getElem hl]
      · simp [List.getElem?_append_right hl, List.getElem?_replicate,
          List.getElem?_eq_none hl, show t - es.length < (ir.value C).size by omega]
    · cases h
  · rename_i m C
    split at h
    · rename_i es hk
      split_ifs at h with hC
      cases h
      obtain ⟨J, hJ⟩ := Option.isSome_iff_exists.1 hC
      refine ⟨by simp [Expr.len, IndexMap.length_toList], fun t ht => ?_⟩
      simp only [Expr.len] at ht
      simp only [Expr.evalInt, hconst C J es hJ hk]
      rw [getD_of_lt (l := m.toList.map fun k => centeredZ p (es.getD k 0)) _
        (by simpa [IndexMap.length_toList] using ht), List.getElem_map,
        IndexMap.entry_eq_getD_toList,
        getD_of_lt (l := m.toList) _ (by simpa [IndexMap.length_toList] using ht)]
    · cases h
  · cases h

/-- The lengths of a list of expressions are their lengths. -/
theorem mem_lenList {rl : ℕ → ℕ} {e : Expr} : ∀ {es : List Expr}, e ∈ es →
    Expr.len ir rl e ∈ Expr.lenList ir rl es
  | _ :: _, .head _ => List.mem_cons_self ..
  | _ :: _, .tail _ h => List.mem_cons_of_mem _ (mem_lenList h)

/-- **A Logic builder's arguments have one length, a multiple of the width**, from
`logicShapeOk`: every argument has the length `L` of the first, and an output coordinate `i` below
the builder's length reads coordinates `i w + t < L`. -/
theorem logic_window {rl : ℕ → ℕ} {op : LogicOp} {w : ℕ} {args : List Expr}
    (h : RealizedProgram.logicShapeOk op w (Expr.lenList ir rl args) = true) :
    0 < w ∧ ∀ e ∈ args, Expr.len ir rl e = (Expr.lenList ir rl args).headD 0 := by
  simp only [RealizedProgram.logicShapeOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  exact ⟨h.1.1.1, fun e he => h.1.2 _ (mem_lenList ir he)⟩

theorem window_lt {w L i t : ℕ} (hi : i < L / w) (ht : t < w) : i * w + t < L := by
  have h1 : (i + 1) * w ≤ L / w * w := Nat.mul_le_mul_right _ hi
  have h2 := Nat.div_mul_le_self L w
  rw [Nat.add_mul, Nat.one_mul] at h1
  omega

/-- An integer in `[0, 1]` is `0` or `1`. -/
theorem int_bool_of_mem {x : ℤ} {J : Ivl} (hJ : J.Within 0 1) (hx : x ∈ J) : x = 0 ∨ x = 1 := by
  have := Ivl.mem_of_within hJ hx
  omega

mutual

/-- **The interval evaluator is sound**, by structure (see `RealizedProgram.evalIntWith_mem_ivlOf`): on an
expression of consistent lengths, every coordinate below its length lies in its interval, given
intervals of the values' coordinates below their sizes (`hleaf`), the zero constants read as `0`
(`hzero`), the integer reading inverting the cast of a natural below `p` (`htn`), and intervals of
the shared expressions' coordinates below their lengths. -/
theorem Expr.evalInt_mem_ivl {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (h01 : (I f).toNat 0 = 0 ∧ (I f).toNat 1 = 1) (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k)
    {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    {leafI : ℕ → Option Ivl}
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, il v i ∈ J)
    (hzero : ∀ z, ir.zeroConstB z = true → ∀ i, il z i = 0)
    (hchar : CharP (I f).K p)
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((il v i : ℤ) : (I f).K) = castElt (leaf v i))
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K))
    (hconst : ∀ v J es, leafI v = some J → (ir.value v).kind = .constant es →
      ∀ s, il v s = centeredZ p (es.getD s 0))
    {refI : ℕ → Option Ivl} {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ} :
    ∀ e : Expr, ir.shapeOkWith rl e = true →
      (∀ k ∈ e.refs, ∀ J, refI k = some J → ∀ i < rl k, iref k i ∈ J) →
      ∀ J, e.ivl ir p leafI refI = some J →
        ∀ i < Expr.len ir rl e, Expr.evalInt ir f leaf il iref rl e i ∈ J
  | .leaf v, _, _, J, h, i, hi => hleaf v J h i hi
  | .add e e', hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, J₂, h₂, rfl⟩ := h
    simp only [Expr.len] at hi
    have m₁ := Expr.evalInt_mem_ivl (leaf := leaf) hp h01 htn hleaf hzero hchar hcast hdec hconst e
      hs.1.1
      (fun k hk => hr k (.inl hk)) J₁ h₁ i hi
    have m₂ := Expr.evalInt_mem_ivl (leaf := leaf) hp h01 htn hleaf hzero hchar hcast hdec hconst e'
      hs.1.2
      (fun k hk => hr k (.inr hk)) J₂ h₂ i (hs.2 ▸ hi)
    simp only [Expr.evalInt]
    split_ifs with hm
    · rcases evalInt_maskedSum_zero ir hzero hm (f := f) (leaf := leaf) (iref := iref) hs.1.1
        hs.1.2 hs.2 hi with h0 | h0
      · rw [h0, zero_add]
        exact Ivl.hull_mem_right m₂
      · rw [h0, add_zero]
        exact Ivl.hull_mem_left m₁
    · exact Ivl.add_mem m₁ m₂
  | .sub e e', hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, J₂, h₂, rfl⟩ := h
    simp only [Expr.len] at hi
    exact Ivl.sub_mem
      (Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
          hchar hcast hdec hconst e hs.1.1 (fun k hk => hr k (.inl hk)) J₁ h₁ i
        hi)
      (Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
          hchar hcast hdec hconst e' hs.1.2 (fun k hk => hr k (.inr hk)) J₂ h₂ i
        (hs.2 ▸ hi))
  | .mul e e', hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, J₂, h₂, rfl⟩ := h
    simp only [Expr.len] at hi
    exact Ivl.mul_mem
      (Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
          hchar hcast hdec hconst e hs.1.1 (fun k hk => hr k (.inl hk)) J₁ h₁ i
        hi)
      (Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
          hchar hcast hdec hconst e' hs.1.2 (fun k hk => hr k (.inr hk)) J₂ h₂ i
        (hs.2 ▸ hi))
  | .concat e e', hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, J₂, h₂, rfl⟩ := h
    simp only [Expr.len] at hi
    simp only [Expr.evalInt]
    split_ifs with hie
    · exact Ivl.hull_mem_left
        (Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
            hchar hcast hdec hconst e hs.1 (fun k hk => hr k (.inl hk)) J₁ h₁ i
          hie)
    · exact Ivl.hull_mem_right
        (Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
            hchar hcast hdec hconst e' hs.2 (fun k hk => hr k (.inr hk)) J₂ h₂ _
          (by omega))
  | .scale (.const c) e, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl] at h
    split_ifs at h with hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, rfl⟩ := h
    simp only [Expr.len] at hi
    simp only [Expr.evalInt, Coef.evalInt, FieldInterp.centered_eq, hp]
    exact Ivl.smul_mem _ (Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
      hchar hcast hdec hconst e hs hr J₁ h₁ i hi)
  | .scale (.node _ _) _, _, _, _, h, _, _ => by simp [Expr.ivl] at h
  | .reindex idx e, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, IndexMap.inRangeNat_eq] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl] at h
    simp only [Expr.len] at hi
    exact Expr.evalInt_mem_ivl hp h01 htn hleaf hzero hchar hcast hdec hconst e hs.1 hr J h _
      (IndexMap.entry_lt_of_inRange hs.2 hi)
  | .ref k, _, hr, J, h, i, hi => hr k (by simp [Expr.refs]) J h i hi
  | .apply op e, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl] at h
    split at h
    · rename_i w hw
      split_ifs at h with hp2
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨J₁, h₁, rfl⟩ := h
      simp only [Expr.len] at hi
      obtain ⟨h0', h1'⟩ := coefInt_zero_one h01 (hp ▸ hp2)
      simp only [Expr.evalInt, NamedOp.applyInt_of_sumWidth ir hw h0' h1']
      cases hg : Expr.ivlGrouped ir p leafI refI w e with
      | none =>
        rw [Option.getD_none]
        exact Ivl.sum_mem fun s => Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
          hchar hcast hdec hconst e hs.1.1 hr J₁ h₁ _
          (NamedOp.lt_of_sumWidth ir hw hi s)
      | some K =>
        rw [Option.getD_some]
        exact Expr.evalInt_mem_ivlGrouped hp h01 htn hleaf hzero hchar hcast hdec hconst e hs.1.1
          hr K hg i fun s => NamedOp.lt_of_sumWidth ir hw hi s
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨J₁, h₁, hJ⟩ := h
      simp only [Expr.len] at hi
      simp only [Expr.evalInt]
      have hx := fun t ht =>
        Expr.evalInt_mem_ivl hp h01 htn hleaf hzero hchar hcast hdec hconst e hs.1.1 hr J₁ h₁ t ht
      split at hJ
      · rename_i J' hm
        cases hJ
        exact NamedOp.applyInt_mem_macIvl ir hp htn leaf hm hx hi
      · exact (NamedOp.applyInt_polyIvl ir hp hchar htn leaf
          (fun v A hA s hs => ⟨hleaf v A hA s hs, hcast v A hA s hs⟩) hdec hconst hJ hi).1 hx
  | .logic op w args, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl] at h
    split_ifs at h with hb
    cases h
    simp only [Expr.len] at hi
    obtain ⟨hw, hlen⟩ := logic_window ir hs.2
    simp only [Expr.evalInt]
    rcases LogicOp.eval_bool op w i (args := Expr.evalIntList ir f leaf il iref rl args)
      (fun g hg t ht => Expr.evalIntList_bool hp h01 htn hleaf hzero
          hchar hcast hdec hconst args hs.1 hr hb _ hlen g hg _
        (window_lt hi ht)) with h0 | h0 <;> rw [h0] <;> simp [Ivl.mem_mk]
  | .linear rows e, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff] at h
    obtain ⟨J₁, h₁, hJ⟩ := h
    simp only [Expr.len] at hi
    obtain ⟨A, hA, hsub⟩ := linIvl_row rows hJ i hi
    have hrow : rows.getD i [] ∈ rows := by
      rw [getD_of_lt _ hi]
      exact List.getElem_mem hi
    simp only [Expr.evalInt]
    exact hsub _ (linRowIvl_mem hp _ hA fun t ht => Expr.evalInt_mem_ivl hp h01 htn hleaf hzero
      hchar hcast hdec hconst e hs.1 hr J₁ h₁ _ (hs.2 _ hrow t ht))
  | .prod _ _, _, _, _, h, _, _ | .mux _ _ _, _, _, _, h, _, _ => by
    simp [Expr.ivl] at h

/-- **Expressions with intervals within `[0, 1]` read bits** (`Expr.ivlBits`), every coordinate
below their common length. -/
theorem Expr.evalIntList_bool {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (h01 : (I f).toNat 0 = 0 ∧ (I f).toNat 1 = 1) (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k)
    {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    {leafI : ℕ → Option Ivl}
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, il v i ∈ J)
    (hzero : ∀ z, ir.zeroConstB z = true → ∀ i, il z i = 0)
    (hchar : CharP (I f).K p)
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((il v i : ℤ) : (I f).K) = castElt (leaf v i))
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K))
    (hconst : ∀ v J es, leafI v = some J → (ir.value v).kind = .constant es →
      ∀ s, il v s = centeredZ p (es.getD s 0))
    {refI : ℕ → Option Ivl} {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ} :
    ∀ es : List Expr, ir.shapeOkWithList rl es = true →
      (∀ k ∈ Expr.refsList es, ∀ J, refI k = some J → ∀ i < rl k, iref k i ∈ J) →
      Expr.ivlBits ir p leafI refI es = true → ∀ L, (∀ e ∈ es, Expr.len ir rl e = L) →
        ∀ g ∈ Expr.evalIntList ir f leaf il iref rl es, ∀ i < L, g i = 0 ∨ g i = 1
  | [], _, _, _, _, _, g, hg, _, _ => absurd hg List.not_mem_nil
  | e :: es, hs, hr, hb, L, hlen, g, hg, i, hi => by
    simp only [RealizedProgram.shapeOkWithList, Bool.and_eq_true] at hs
    simp only [Expr.refsList, List.mem_append] at hr
    simp only [Expr.ivlBits, Bool.and_eq_true] at hb
    simp only [Expr.evalIntList, List.mem_cons] at hg
    rcases hg with rfl | hg
    · revert hb
      cases hJ : Expr.ivl ir p leafI refI e with
      | none => simp
      | some J =>
        rintro ⟨hW, -⟩
        simp only [decide_eq_true_eq] at hW
        exact int_bool_of_mem hW (Expr.evalInt_mem_ivl hp h01 htn hleaf hzero hchar hcast hdec
          hconst e hs.1
          (fun k hk => hr k (.inl hk)) J hJ i (by rw [hlen e (List.mem_cons_self ..)]; exact hi))
    · exact Expr.evalIntList_bool hp h01 htn hleaf hzero
          hchar hcast hdec hconst es hs.2 (fun k hk => hr k (.inr hk)) hb.2
        L (fun e' he' => hlen e' (List.mem_cons_of_mem _ he')) g hg i hi

/-- **The sums of groups of a product by a constant view lie in their interval**
(`Expr.ivlGrouped`): every group `j` of `w` coordinates within the length. -/
theorem Expr.evalInt_mem_ivlGrouped {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (h01 : (I f).toNat 0 = 0 ∧ (I f).toNat 1 = 1) (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k)
    {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    {leafI : ℕ → Option Ivl}
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, il v i ∈ J)
    (hzero : ∀ z, ir.zeroConstB z = true → ∀ i, il z i = 0)
    (hchar : CharP (I f).K p)
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((il v i : ℤ) : (I f).K) = castElt (leaf v i))
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K))
    (hconst : ∀ v J es, leafI v = some J → (ir.value v).kind = .constant es →
      ∀ s, il v s = centeredZ p (es.getD s 0))
    {refI : ℕ → Option Ivl} {iref : ℕ → ℕ → ℤ} {rl : ℕ → ℕ} {w : ℕ} :
    ∀ e : Expr, ir.shapeOkWith rl e = true →
      (∀ k ∈ e.refs, ∀ J, refI k = some J → ∀ i < rl k, iref k i ∈ J) →
      ∀ K, e.ivlGrouped ir p leafI refI w = some K →
        ∀ j, (∀ s : Fin w, j * w + s < Expr.len ir rl e) →
          ∑ s : Fin w, Expr.evalInt ir f leaf il iref rl e (j * w + s) ∈ K
  | .mul a c, hs, hr, K, h, j, hj => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.len] at hj
    have hgroups : ∀ {A : Ivl} {cs : List ℤ}, groupsIvl A w (cs.length / w) cs = some K →
        cs.length = Expr.len ir rl a →
        (∀ s : Fin w, Expr.evalInt ir f leaf il iref rl a (j * w + s) ∈ A) →
        ∑ s : Fin w, cs.getD (j * w + s) 0 * Expr.evalInt ir f leaf il iref rl a (j * w + s) ∈
          K := by
      intro A cs hK hlen hA
      have hw : 0 < w := by
        rcases Nat.eq_zero_or_pos w with h0 | h0
        · subst h0
          simp [groupsIvl] at hK
        · exact h0
      have hjl : (j + 1) * w ≤ cs.length := by
        have := hj ⟨w - 1, by omega⟩
        simp only at this
        rw [Nat.add_mul, Nat.one_mul]
        omega
      have hjn : j < cs.length / w := by
        have := (Nat.le_div_iff_mul_le hw).2 hjl
        omega
      have := groupsIvl_mem (cs.length / w) cs hK j hjn hjl
        (fun s => Expr.evalInt ir f leaf il iref rl a (j * w + s))
        (fun s hs => hA ⟨s, hs⟩)
      rwa [← Fin.sum_univ_eq_sum_range (fun s => cs.getD (j * w + s) 0 *
        Expr.evalInt ir f leaf il iref rl a (j * w + s)) w] at this
    simp only [Expr.ivlGrouped] at h
    simp only [Expr.evalInt]
    cases hc : constCoords ir p leafI c with
    | some cs =>
      rw [hc] at h
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨A, hA, hK⟩ := h
      obtain ⟨hlen, hev⟩ := constCoords_eval ir (f := f) (leaf := leaf) (iref := iref) (rl := rl)
        hconst hc
      have hmem := hgroups hK (by rw [hlen, hs.2]) (fun s => Expr.evalInt_mem_ivl hp h01 htn hleaf
        hzero hchar hcast hdec hconst a hs.1.1 (fun k hk => hr k (.inl hk)) A hA _ (hj s))
      rw [Finset.sum_congr rfl fun s _ => by rw [hev _ (hs.2 ▸ hj s), mul_comm]]
      exact hmem
    | none =>
      rw [hc] at h
      simp only at h
      cases ha : constCoords ir p leafI a with
      | none =>
        rw [ha] at h
        cases h
      | some cs =>
        rw [ha] at h
        simp only [Option.bind_eq_some_iff] at h
        obtain ⟨A, hA, hK⟩ := h
        obtain ⟨hlen, hev⟩ := constCoords_eval ir (f := f) (leaf := leaf) (iref := iref) (rl := rl)
          hconst ha
        have hw : 0 < w := by
          rcases Nat.eq_zero_or_pos w with h0 | h0
          · subst h0
            simp [groupsIvl] at hK
          · exact h0
        have hjl : (j + 1) * w ≤ cs.length := by
          have := hj ⟨w - 1, by omega⟩
          simp only at this
          rw [Nat.add_mul, Nat.one_mul, hlen]
          omega
        have hjn : j < cs.length / w := by
          have := (Nat.le_div_iff_mul_le hw).2 hjl
          omega
        have := groupsIvl_mem (cs.length / w) cs hK j hjn hjl
          (fun s => Expr.evalInt ir f leaf il iref rl c (j * w + s))
          (fun s hs' => Expr.evalInt_mem_ivl hp h01 htn hleaf hzero hchar hcast hdec hconst c
            hs.1.2 (fun k hk => hr k (.inr hk)) A hA _ (hs.2 ▸ hj ⟨s, hs'⟩))
        rw [← Fin.sum_univ_eq_sum_range (fun s => cs.getD (j * w + s) 0 *
          Expr.evalInt ir f leaf il iref rl c (j * w + s)) w] at this
        rw [Finset.sum_congr rfl fun s _ => by rw [hev _ (hj s)]]
        exact this
  | .leaf _, _, _, _, h, _, _ | .add _ _, _, _, _, h, _, _ | .sub _ _, _, _, _, h, _, _
  | .scale _ _, _, _, _, h, _, _ | .reindex _ _, _, _, _, h, _, _ | .concat _ _, _, _, _, h, _, _
  | .linear _ _, _, _, _, h, _, _ | .prod _ _, _, _, _, h, _, _ | .mux _ _ _, _, _, _, h, _, _
  | .apply _ _, _, _, _, h, _, _ | .ref _, _, _, _, h, _, _ | .logic _ _ _, _, _, _, h, _, _ => by
    simp [Expr.ivlGrouped] at h

end

mutual

/-- **The integer reading casts to the field**, by structure (see `RealizedProgram.evalIntWith_cast`): on an
expression of consistent lengths with an interval, every coordinate below its length of the integer
reading casts to the coordinate's value, given the same of the values (`hcast`) and of the shared
expressions. -/
theorem Expr.evalInt_cast {f p : ℕ} (hp : (I f).spec.characteristic = p) (hchar : CharP (I f).K p)
    (h01 : (I f).toNat 0 = 0 ∧ (I f).toNat 1 = 1) (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k)
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    {leafI : ℕ → Option Ivl}
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((il v i : ℤ) : (I f).K) = castElt (leaf v i))
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, il v i ∈ J)
    (hconst : ∀ v J es, leafI v = some J → (ir.value v).kind = .constant es →
      ∀ s, il v s = centeredZ p (es.getD s 0))
        {refI : ℕ → Option Ivl} {iref : ℕ → ℕ → ℤ} {ref : ℕ → ℕ → (I f).K} {rl : ℕ → ℕ} :
    ∀ e : Expr, ir.shapeOkWith rl e = true →
      (∀ k ∈ e.refs, ∀ J, refI k = some J → ∀ i < rl k, ((iref k i : ℤ) : (I f).K) = ref k i) →
      ∀ J, e.ivl ir p leafI refI = some J →
        ∀ i < Expr.len ir rl e,
          ((Expr.evalInt ir f leaf il iref rl e i : ℤ) : (I f).K) = Expr.eval ir f leaf ref rl e i
  | .leaf v, _, _, J, h, i, hi => hcast v J h i hi
  | .add e e', hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, J₂, h₂, -⟩ := h
    simp only [Expr.len] at hi
    simp only [Expr.evalInt, Expr.eval, Int.cast_add,
      Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e hs.1.1 (fun k hk => hr k (.inl hk)) J₁ h₁ i
        hi,
      Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e' hs.1.2 (fun k hk => hr k (.inr hk)) J₂ h₂ i
        (hs.2 ▸ hi)]
  | .sub e e', hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, J₂, h₂, rfl⟩ := h
    simp only [Expr.len] at hi
    simp only [Expr.evalInt, Expr.eval, Int.cast_sub,
      Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e hs.1.1 (fun k hk => hr k (.inl hk)) J₁ h₁ i
        hi,
      Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e' hs.1.2 (fun k hk => hr k (.inr hk)) J₂ h₂ i
        (hs.2 ▸ hi)]
  | .mul e e', hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, beq_iff_eq] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, J₂, h₂, rfl⟩ := h
    simp only [Expr.len] at hi
    simp only [Expr.evalInt, Expr.eval, Int.cast_mul,
      Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e hs.1.1 (fun k hk => hr k (.inl hk)) J₁ h₁ i
        hi,
      Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e' hs.1.2 (fun k hk => hr k (.inr hk)) J₂ h₂ i
        (hs.2 ▸ hi)]
  | .concat e e', hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true] at hs
    simp only [Expr.refs, List.mem_append] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, J₂, h₂, rfl⟩ := h
    simp only [Expr.len] at hi
    simp only [Expr.evalInt, Expr.eval]
    split_ifs with hie
    · exact Expr.evalInt_cast hp hchar h01 htn hdec
          hcast hleaf hconst e hs.1 (fun k hk => hr k (.inl hk)) J₁
        h₁ i hie
    · exact Expr.evalInt_cast hp hchar h01 htn hdec
          hcast hleaf hconst e' hs.2 (fun k hk => hr k (.inr hk)) J₂
        h₂ _ (by omega)
  | .scale (.const c) e, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl] at h
    split_ifs at h with hc
    simp only [Option.map_eq_some_iff] at h
    obtain ⟨J₁, h₁, rfl⟩ := h
    simp only [Expr.len] at hi
    simp only [Expr.evalInt, Expr.eval, Coef.evalInt, Coef.eval, FieldInterp.centered_eq, hp,
      Int.cast_mul, Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e hs hr J₁ h₁ i hi, hdec c hc,
      centeredZ_cast]
  | .scale (.node _ _) _, _, _, _, h, _, _ => by simp [Expr.ivl] at h
  | .reindex idx e, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, IndexMap.inRangeNat_eq] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl] at h
    simp only [Expr.len] at hi
    exact Expr.evalInt_cast hp hchar h01 htn hdec hcast hleaf hconst e hs.1 hr J h _
      (IndexMap.entry_lt_of_inRange hs.2 hi)
  | .ref k, _, hr, J, h, i, hi => hr k (by simp [Expr.refs]) J h i hi
  | .apply op e, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl] at h
    split at h
    · rename_i w hw
      split_ifs at h with hp2
      simp only [Option.map_eq_some_iff] at h
      obtain ⟨J₁, h₁, rfl⟩ := h
      simp only [Expr.len] at hi
      obtain ⟨h0', h1'⟩ := coefInt_zero_one h01 (hp ▸ hp2)
      simp only [Expr.evalInt, Expr.eval, NamedOp.applyInt_of_sumWidth ir hw h0' h1',
        NamedOp.apply_of_sumWidth ir hw, Int.cast_sum]
      exact Finset.sum_congr rfl fun s _ => Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e hs.1.1
        hr J₁ h₁ _ (NamedOp.lt_of_sumWidth ir hw hi s)
    · simp only [Option.bind_eq_some_iff] at h
      obtain ⟨J₁, h₁, hJ⟩ := h
      simp only [Expr.len] at hi
      simp only [Expr.evalInt, Expr.eval]
      split at hJ
      rotate_left
      · exact (NamedOp.applyInt_polyIvl ir hp hchar htn leaf
          (fun v A hA s hs => ⟨hleaf v A hA s hs, hcast v A hA s hs⟩) hdec hconst hJ hi).2 _
          fun t ht => Expr.evalInt_cast hp hchar h01 htn hdec hcast hleaf hconst e hs.1.1 hr J₁ h₁ t
            ht
      rename_i J' hJ'
      cases hJ
      match op, hJ' with
      | .macConv r w nch taps, hJ =>
        simp only [NamedOp.macIvl] at hJ
        split_ifs at hJ with hW
        split at hJ
        · rw [NamedOp.applyInt_macConv ir hp htn leaf hW.2.1 hW.2.2,
            NamedOp.apply_macConv ir leaf hW.2.1]
          push_cast
          refine Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun j _ => ?_
          have hlt : (c' : ℕ) * w + j < nch * w := by
            have := c'.2
            have := j.2
            nlinarith
          have hlt' : i / w * (nch * w) + ((c' : ℕ) * w + j) < Expr.len ir rl e :=
            NamedOp.lt_of_cols ir (op := .macConv r w nch taps) hW.2.1 hi hlt
          rw [Expr.evalInt_cast hp hchar h01 htn hdec hcast hleaf hconst e hs.1.1 hr J₁ h₁ _ hlt']
        · cases hJ
  | .logic op w args, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl] at h
    split_ifs at h with hb
    simp only [Expr.len] at hi
    obtain ⟨hw, hlen⟩ := logic_window ir hs.2
    simp only [Expr.evalInt, Expr.eval]
    rw [← eq_intCast (Int.castRingHom (I f).K), LogicOp.eval_map]
    refine LogicOp.eval_congr op w i ?_
    rw [List.forall₂_map_left_iff]
    exact (Expr.evalIntList_cast hp hchar h01 htn hdec hcast hleaf hconst args hs.1 hr hb _
      hlen).imp
      fun g g' hgg t ht => by simpa using hgg _ (window_lt hi ht)
  | .linear rows e, hs, hr, J, h, i, hi => by
    simp only [RealizedProgram.shapeOkWith, Bool.and_eq_true, List.all_eq_true,
      decide_eq_true_eq] at hs
    simp only [Expr.refs] at hr
    simp only [Expr.ivl, Option.bind_eq_some_iff] at h
    obtain ⟨J₁, h₁, hJ⟩ := h
    simp only [Expr.len] at hi
    obtain ⟨A, hA, -⟩ := linIvl_row rows hJ i hi
    have hrow : rows.getD i [] ∈ rows := by
      rw [getD_of_lt _ hi]
      exact List.getElem_mem hi
    simp only [Expr.evalInt, Expr.eval]
    exact linRowIvl_cast ir hp hchar hdec _ hA fun t ht => Expr.evalInt_cast hp hchar h01 htn hdec
      hcast hleaf hconst e hs.1 hr J₁ h₁ _ (hs.2 _ hrow t ht)
  | .prod _ _, _, _, _, h, _, _ | .mux _ _ _, _, _, _, h, _, _ => by
    simp [Expr.ivl] at h

/-- **The integer readings of expressions with intervals within `[0, 1]` cast to their values**
(`Expr.ivlBits`), every coordinate below their common length. -/
theorem Expr.evalIntList_cast {f p : ℕ} (hp : (I f).spec.characteristic = p)
    (hchar : CharP (I f).K p) (h01 : (I f).toNat 0 = 0 ∧ (I f).toNat 1 = 1)
    (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k)
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) {leaf : ir.Valuation I} {il : ℕ → ℕ → ℤ}
    {leafI : ℕ → Option Ivl}
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((il v i : ℤ) : (I f).K) = castElt (leaf v i))
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, il v i ∈ J)
    (hconst : ∀ v J es, leafI v = some J → (ir.value v).kind = .constant es →
      ∀ s, il v s = centeredZ p (es.getD s 0))
        {refI : ℕ → Option Ivl} {iref : ℕ → ℕ → ℤ} {ref : ℕ → ℕ → (I f).K} {rl : ℕ → ℕ} :
    ∀ es : List Expr, ir.shapeOkWithList rl es = true →
      (∀ k ∈ Expr.refsList es, ∀ J, refI k = some J → ∀ i < rl k,
        ((iref k i : ℤ) : (I f).K) = ref k i) →
      Expr.ivlBits ir p leafI refI es = true → ∀ L, (∀ e ∈ es, Expr.len ir rl e = L) →
        List.Forall₂ (fun g g' => ∀ i < L, ((g i : ℤ) : (I f).K) = g' i)
          (Expr.evalIntList ir f leaf il iref rl es) (Expr.evalList ir f leaf ref rl es)
  | [], _, _, _, _, _ => .nil
  | e :: es, hs, hr, hb, L, hlen => by
    simp only [RealizedProgram.shapeOkWithList, Bool.and_eq_true] at hs
    simp only [Expr.refsList, List.mem_append] at hr
    simp only [Expr.ivlBits, Bool.and_eq_true] at hb
    simp only [Expr.evalIntList, Expr.evalList]
    refine .cons ?_ (Expr.evalIntList_cast hp hchar h01 htn hdec hcast hleaf hconst es hs.2
      (fun k hk => hr k (.inr hk)) hb.2 L fun e' he' => hlen e' (List.mem_cons_of_mem _ he'))
    obtain ⟨hJ, -⟩ := hb
    revert hJ
    cases hJ' : Expr.ivl ir p leafI refI e with
    | none => simp
    | some J =>
      intro _ i hi
      exact Expr.evalInt_cast hp hchar h01 htn hdec
        hcast hleaf hconst e hs.1 (fun k hk => hr k (.inl hk)) J hJ'
        i (by rw [hlen e (List.mem_cons_self ..)]; exact hi)

end

end Core

/-! ## Through the shared expressions -/

section

variable (ir : RealizedProgram)

/-- **The intervals of the shared expressions** at the characteristic `p` and the values' intervals
`leafI`, each entry computed once from the earlier ones. -/
def ivlT (p : ℕ) (leafI : ℕ → Option Ivl) : NatTrie (Option Ivl) :=
  memo (fun r _ e => e.ivl ir p leafI r) none ir.exprs

/-- **The interval of an expression's coordinates** at the characteristic `p` and the values'
intervals `leafI`, through the shared expressions' intervals (`ivlT`). -/
def ivlOf (p : ℕ) (leafI : ℕ → Option Ivl) (e : Expr) :
    Option Ivl :=
  e.ivl ir p leafI ((ir.ivlT p leafI).getD · none)

variable {ir} {I : Interp}

/-- **A constant holding `0` has integer reading `0`** at every coordinate. -/
theorem intOf_of_zeroConstB (rd : ir.Valuation I) {z : ℕ} (h : ir.zeroConstB z = true) (i : ℕ) :
    ir.intOf rd z i = 0 := by
  unfold zeroConstB at h
  unfold intOf
  split at h
  · rename_i es hk
    rw [hk]
    have h0 : es.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hes : es[i]? with
      | none => rfl
      | some c =>
        have := List.all_eq_true.1 h c (List.mem_of_getElem? hes)
        simpa using this
    simp only [h0, FieldInterp.centered]
    split_ifs with hc <;> simp <;> omega
  · cases h

/-- **A constant of field `f` has integer reading its centred entries.** -/
theorem intOf_const_of_field (rd : ir.Valuation I) {f p : ℕ} (hp : (I f).spec.characteristic = p)
    {v : ℕ} {es : List ℕ} (hv : ir.valueField v = f) (hk : (ir.value v).kind = .constant es)
    (s : ℕ) : ir.intOf rd v s = centeredZ p (es.getD s 0) := by
  unfold intOf
  rw [hk]
  simp only
  rw [hv, FieldInterp.centered_eq, hp]

/-- **A shared expression's length is its entry's at the program's depth.** -/
theorem refLen_eq_len (ho : ir.RefsOrdered) {k : ℕ} (hk : k < ir.exprs.length) :
    ir.refLen ir.exprs.length k = Expr.len ir (ir.refLen ir.exprs.length) (ir.expr k) := by
  obtain ⟨n, hn⟩ : ∃ n, ir.exprs.length = n + 1 := ⟨ir.exprs.length - 1, by omega⟩
  rw [hn, show ir.refLen (n + 1) k = Expr.len ir (ir.refLen n) (ir.expr k) from rfl]
  refine Expr.len_congr ir _ fun k' hk' => ?_
  have := ho k hk k' hk'
  rw [lenT_getD ho (n := n) (by omega) (by omega), lenT_getD ho (n := n + 1) (by omega) (by omega)]

/-- **The shared expressions' integer readings lie in their intervals** (`ivlT`), for a program
whose shared expressions read earlier entries and have consistent lengths. -/
theorem refInt_mem_ivlT (hx : ir.ExprsOk) {rd : ir.Valuation I} {f p : ℕ}
    (hp : (I f).spec.characteristic = p) (h01 : (I f).toNat 0 = 0 ∧ (I f).toNat 1 = 1)
    (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k) {leafI : ℕ → Option Ivl}
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, ir.intOf rd v i ∈ J)
    (hchar : CharP (I f).K p)
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((ir.intOf rd v i : ℤ) : (I f).K) = castElt (rd v i))
        (hdec : ∀ c < p, (I f).decode c = (c : (I f).K))
    (hfield : ∀ v J, leafI v = some J → ir.valueField v = f) :
    ∀ k < ir.exprs.length, ∀ J, (ir.ivlT p leafI).getD k none = some J →
      ∀ i < ir.refLen ir.exprs.length k, ir.refInt rd f ir.exprs.length k i ∈ J := by
  have ho : ir.RefsOrdered := fun k hk => (hx k hk).1
  intro k hk
  refine iter_rel_memo_idx (iter := fun n j => ir.refInt rd f n j)
    (R := fun j x o => ∀ J, o = some J → ∀ i < ir.refLen ir.exprs.length j, x i ∈ J)
    (G := fun r j i => Expr.evalInt ir f rd (ir.intOf rd) r (ir.refLen ir.exprs.length) (ir.expr j) i)
    (fun _ _ => rfl) (fun j hj r r' hR => ?_)
    (memoDeps_exprs ho fun _ _ _ e h => Expr.ivl_congr e h) _ k hk hk
  intro J hJ i hi
  rw [refLen_eq_len ho hj] at hi
  have hs := (hx j hj).2
  rw [exprShapeOk_eq] at hs
  exact Expr.evalInt_mem_ivl ir hp h01 htn hleaf (fun z hz => intOf_of_zeroConstB rd hz) hchar
    hcast hdec (fun v J es hJ hk s => intOf_const_of_field rd hp (hfield v J hJ) hk s)
    (ir.expr j) hs (fun k hk => hR k hk) J hJ i hi

/-- **The interval evaluator is sound** (see the module docstring): for a well-formed expression of
domain `d` with an interval, every coordinate of its integer reading lies in the interval, given
intervals of the values' coordinates below their sizes (`hleaf`), the integer readings of `0`
and `1` (`h01`), and the integer reading inverting the cast of a natural below `p` (`htn`). -/
theorem evalIntWith_mem_ivlOf (hx : ir.ExprsOk) {rd : ir.Valuation I} {d p : ℕ}
    (hp : (I (ir.domainField d)).spec.characteristic = p)
    (h01 : (I (ir.domainField d)).toNat 0 = 0 ∧ (I (ir.domainField d)).toNat 1 = 1)
    (htn : ∀ k < p, (I (ir.domainField d)).toNat (k : (I (ir.domainField d)).K) = k)
    {leafI : ℕ → Option Ivl}
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, ir.intOf rd v i ∈ J)
    (hchar : CharP (I (ir.domainField d)).K p)
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((ir.intOf rd v i : ℤ) : (I (ir.domainField d)).K) = castElt (rd v i))
    (hdec : ∀ c < p, (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K))
    (hfield : ∀ v J, leafI v = some J → ir.valueField v = ir.domainField d)
    {e : Expr} (he : ir.exprShapeOk e = true) (hr : ∀ k ∈ e.refs, k < ir.exprs.length)
    {J : Ivl} (h : ir.ivlOf p leafI e = some J) :
    ∀ i < ir.exprLen e, ir.evalIntWith rd d e i ∈ J := by
  rw [exprShapeOk_eq] at he
  exact Expr.evalInt_mem_ivl ir hp h01 htn hleaf (fun z hz => intOf_of_zeroConstB rd hz) hchar
    hcast hdec (fun v J es hJ hk s => intOf_const_of_field rd hp (hfield v J hJ) hk s) e he
    (fun k hk => refInt_mem_ivlT hx hp h01 htn hleaf hchar hcast hdec hfield k (hr k hk)) J h

/-- **The shared expressions' integer readings cast to their values**, where the values' do. -/
theorem refInt_cast_ivlT (hx : ir.ExprsOk) {rd : ir.Valuation I} {f p : ℕ}
    (hp : (I f).spec.characteristic = p) (hchar : CharP (I f).K p)
    (h01 : (I f).toNat 0 = 0 ∧ (I f).toNat 1 = 1) (htn : ∀ k < p, (I f).toNat (k : (I f).K) = k)
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) {leafI : ℕ → Option Ivl}
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((ir.intOf rd v i : ℤ) : (I f).K) = castElt (rd v i))
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, ir.intOf rd v i ∈ J)
    (hfield : ∀ v J, leafI v = some J → ir.valueField v = f) :
    ∀ k < ir.exprs.length, ∀ J, (ir.ivlT p leafI).getD k none = some J →
      ∀ i < ir.refLen ir.exprs.length k,
        ((ir.refInt rd f ir.exprs.length k i : ℤ) : (I f).K) =
          ir.refVal rd ir.exprs.length f k i := by
  have ho : ir.RefsOrdered := fun k hk => (hx k hk).1
  intro k hk
  refine iter_rel_memo_idx (iter := fun n j => (ir.refInt rd f n j, ir.refVal rd n f j))
    (R := fun j x o => ∀ J, o = some J →
      ∀ i < ir.refLen ir.exprs.length j, ((x.1 i : ℤ) : (I f).K) = x.2 i)
    (G := fun r j =>
      (fun i => Expr.evalInt ir f rd (ir.intOf rd) (fun k => (r k).1) (ir.refLen ir.exprs.length)
        (ir.expr j) i,
       fun i => Expr.eval ir f rd (fun k => (r k).2) (ir.refLen ir.exprs.length) (ir.expr j) i))
    (fun _ _ => rfl) (fun j hj r r' hR => ?_)
    (memoDeps_exprs ho fun _ _ _ e h => Expr.ivl_congr e h) _ k hk hk
  intro J hJ i hi
  rw [refLen_eq_len ho hj] at hi
  have hs := (hx j hj).2
  rw [exprShapeOk_eq] at hs
  exact Expr.evalInt_cast ir hp hchar h01 htn hdec
    hcast hleaf (fun v J es hJ hk s => intOf_const_of_field rd hp (hfield v J hJ) hk s)
    (ir.expr j) hs (fun k hk => hR k hk) J hJ i hi

/-- **The integer reading casts to the field** (see the module docstring): for a well-formed
expression of domain `d` with an interval, every coordinate of its integer reading casts to its
value, where every value read with an interval (`hcast`, the prime-subfield reads) does. -/
theorem evalIntWith_cast (hx : ir.ExprsOk) {rd : ir.Valuation I} {d p : ℕ}
    (hp : (I (ir.domainField d)).spec.characteristic = p)
    (hchar : CharP (I (ir.domainField d)).K p)
    (h01 : (I (ir.domainField d)).toNat 0 = 0 ∧ (I (ir.domainField d)).toNat 1 = 1)
    (htn : ∀ k < p, (I (ir.domainField d)).toNat (k : (I (ir.domainField d)).K) = k)
    (hdec : ∀ c < p, (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K))
    {leafI : ℕ → Option Ivl}
    (hcast : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size,
      ((ir.intOf rd v i : ℤ) : (I (ir.domainField d)).K) = castElt (rd v i))
    (hleaf : ∀ v J, leafI v = some J → ∀ i < (ir.value v).size, ir.intOf rd v i ∈ J)
    (hfield : ∀ v J, leafI v = some J → ir.valueField v = ir.domainField d)
    {e : Expr} (he : ir.exprShapeOk e = true) (hr : ∀ k ∈ e.refs, k < ir.exprs.length)
    {J : Ivl} (h : ir.ivlOf p leafI e = some J) :
    ∀ i < ir.exprLen e, ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) =
      ir.evalWith rd d e i := by
  rw [exprShapeOk_eq] at he
  exact Expr.evalInt_cast ir hp hchar h01 htn hdec hcast hleaf
    (fun v J es hJ hk s => intOf_const_of_field rd hp (hfield v J hJ) hk s) e he
    (fun k hk => refInt_cast_ivlT hx hp hchar h01 htn hdec hcast hleaf hfield k (hr k hk)) J h

end

/-! ## The integer readings of a program's fields -/

/-- **The integer readings of the program's fields are lawful** (a property of the model, the
interpretation of the fields), with `primeNodes d` the names of domain `d`'s prime-subfield nodes:
the integer reading of an element of a field of odd characteristic is below the characteristic (a
binary field's integer reading is its polynomial-basis coefficients), inverts the cast of a natural below
it, a constant below it decodes to its cast, an element of a prime-subfield node is the cast of
its integer reading, the node of a field's own name is the whole field (the root of its packing
tree), and an opaque function computing a `Bit` value returns `0` or `1`. -/
structure Interp.Lawful (I : Interp) (ir : RealizedProgram) (primeNodes : ℕ → List String) : Prop where
  /-- The integer reading is below the characteristic, in odd characteristic. -/
  toNat_lt : ∀ f < ir.fields.length, 2 < (ir.field f).characteristic → ∀ x : (I f).K,
    (I f).toNat x < (ir.field f).characteristic
  /-- The integer reading inverts the cast of a natural below the characteristic. -/
  toNat_natCast : ∀ f < ir.fields.length, ∀ k < (ir.field f).characteristic,
    (I f).toNat (k : (I f).K) = k
  /-- A constant below the characteristic decodes to its cast. -/
  decode_natCast : ∀ f < ir.fields.length, ∀ c < (ir.field f).characteristic,
    (I f).decode c = (c : (I f).K)
  /-- An element of a prime-subfield node is the cast of its integer reading. -/
  natCast_toNat : ∀ d < ir.domains.length, ∀ E ∈ primeNodes d,
    ∀ x ∈ (I (ir.domainField d)).node E,
      ((I (ir.domainField d)).toNat x : (I (ir.domainField d)).K) = x
  /-- The node of a field's own name is the whole field. -/
  rootNode : ∀ f < ir.fields.length, (I f).node (ir.field f).name = ⊤
  /-- An opaque function computing a value of type `Bit` (from arguments) returns `0` or `1`. -/
  opaqueBit : ∀ v < ir.values.length, ∀ name args, (ir.value v).kind = .pub (.opaque name args) →
    args ≠ [] → (ir.value v).type = .bit → ∀ xs i, I.opaqueFn name xs i < 2

end GordieHowe.RealizedProgram
