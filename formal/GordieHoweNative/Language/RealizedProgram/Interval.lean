-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.RealizedProgram.Check

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.RealizedProgram.Interval`

The definitions of `GordieHowe.Language.RealizedProgram.Interval` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/RealizedProgram/Interval.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open Export

/-- **A closed interval of integers** `[lo, hi]`. -/
structure Ivl where
  /-- The lower end. -/
  lo : ℤ
  /-- The upper end. -/
  hi : ℤ
  deriving Repr, DecidableEq, Inhabited

namespace Ivl

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

end Ivl

/-- **The symmetric interval** `[−m, m]`. -/
def Ivl.sym (m : ℕ) : Ivl := ⟨-(m : ℤ), m⟩

/-- **The magnitude of an interval**: the larger absolute value of its ends. -/
def Ivl.mag (J : Ivl) : ℕ := max J.lo.natAbs J.hi.natAbs

/-- **An optional interval lies within `[lo, hi]`**: some interval within it (`none` lies within
nothing). -/
def IvlWithin : Option Ivl → ℤ → ℤ → Prop
  | some J, lo, hi => J.Within lo hi
  | none, _, _ => False

instance (o : Option Ivl) (lo hi : ℤ) : Decidable (IvlWithin o lo hi) := by
  cases o <;> unfold IvlWithin <;> infer_instance

/-- **A constant read in `(−p/2, p/2)`** (`FieldInterp.centered` at the characteristic `p`). -/
def centeredZ (p c : ℕ) : ℤ := if 2 * c < p then c else (c : ℤ) - p

/-- **The width of a named operator that sums groups**: `w` for `sum w` and `batched b (sum w)`
with `b ≥ 1` (output coordinate `j` the sum of coordinates `j w, …, j w + w − 1`); none
otherwise. -/
def NamedOp.sumWidth : NamedOp → Option ℕ
  | .sum w => some w
  | .batched b (.sum w) => if 0 < b then some w else none
  | _ => none

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
    some ((List.finRange w).foldr
      (fun (m : Fin w) a => max (Conv.lane 32 (Conv.accPacked 32 w (Conv.phiList 32 w taps)).2 m) a) 0)
  else none

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
def digitsWeight (base k : ℕ) : ℕ := ((List.range k).map (base ^ ·)).sum

/-- **The interval of a public polynomial operand in its form** (`NamedOp.formPoly`): its values'
interval `leafI h` in coefficient form; none in transform form. -/
def formIvl (leafI : ℕ → Option Ivl) (h : ℕ) : ConvForm → Option Ivl
  | .coefficients => leafI h
  | .ntt _ => none
  | .nttNatural _ => none

/-- **The absolute row sum of the first `W` entries `es`, and the entries after them**, each entry
read centred at `p`, in one pass over the row (`rowSplit_eq`: the sum over `es.take W`, and
`es.drop W`). -/
def rowSplit (p : ℕ) : ℕ → List ℕ → ℕ × List ℕ
  | 0, es => (0, es)
  | _ + 1, [] => (0, [])
  | W + 1, c :: es => ((centeredZ p c).natAbs + (rowSplit p W es).1, (rowSplit p W es).2)

/-- **The largest absolute row sum** of `R` rows of `W` entries `es` (row-major, `0` past the
entries), each entry read centred at `p` (`centeredZ`), each row read once (`rowSplit`). -/
def rowAbsMax (p W : ℕ) : ℕ → List ℕ → ℕ
  | 0, _ => 0
  | R + 1, es => max (rowSplit p W es).1 (rowAbsMax p W R (rowSplit p W es).2)

/-- **`(centeredZ p c).natAbs`, in natural arithmetic** (`centeredAbsN_eq`). -/
def centeredAbsN (p c : ℕ) : ℕ := cond (Nat.blt (2 * c) p) c (cond (Nat.blt c p) (p - c) (c - p))

theorem centeredAbsN_eq (p c : ℕ) : centeredAbsN p c = (centeredZ p c).natAbs := by
  unfold centeredAbsN centeredZ
  by_cases h : 2 * c < p
  · simp [h, Nat.blt_eq]
  · have h1 : Nat.blt (2 * c) p = false := by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h
    simp only [h1, Bool.cond_false, h, ↓reduceIte]
    by_cases h2 : c < p
    · have : Nat.blt c p = true := by rw [Nat.blt_eq]; exact h2
      rw [this, Bool.cond_true, show (c : ℤ) - p = -((p - c : ℕ) : ℤ) by omega, Int.natAbs_neg]
      simp
    · have : Nat.blt c p = false := by rw [Bool.eq_false_iff, ne_eq, Nat.blt_eq]; exact h2
      rw [this, Bool.cond_false, show (c : ℤ) - p = ((c - p : ℕ) : ℤ) by omega]
      simp

/-- **`rowSplit p W es`, its sum added to `a`**, by the recursors (`rowSplitAuxK_eq`). -/
noncomputable def rowSplitAuxK (p W : ℕ) : List ℕ → ℕ → ℕ × List ℕ :=
  @Nat.rec (fun _ => List ℕ → ℕ → ℕ × List ℕ) (fun es a => (a, es))
    (fun _ ih es a => @List.casesOn ℕ (fun _ => ℕ × List ℕ) es (a, []) fun c es' =>
      @Nat.casesOn (fun _ => ℕ × List ℕ) a (ih es' (centeredAbsN p c))
        fun k => ih es' (k + 1 + centeredAbsN p c)) W

theorem rowSplitAuxK_eq (p : ℕ) : ∀ (W : ℕ) (es : List ℕ) (a : ℕ),
    rowSplitAuxK p W es a = (a + (rowSplit p W es).1, (rowSplit p W es).2)
  | 0, _, _ => rfl
  | _ + 1, [], _ => rfl
  | W + 1, c :: es, a => by
    have : rowSplitAuxK p (W + 1) (c :: es) a = rowSplitAuxK p W es (a + centeredAbsN p c) := by
      cases a with
      | zero => change rowSplitAuxK p W es (centeredAbsN p c) = _; rw [Nat.zero_add]
      | succ k => rfl
    rw [this, rowSplitAuxK_eq p W es, rowSplit, centeredAbsN_eq]
    simp only [Prod.mk.injEq, and_true]
    omega

/-- **The larger of `m` and `rowAbsMax p W R es`**, by the recursors (`rowAbsMaxAuxK_eq`). -/
noncomputable def rowAbsMaxAuxK (p W : ℕ) : ℕ → List ℕ → ℕ → ℕ :=
  @Nat.rec (fun _ => List ℕ → ℕ → ℕ) (fun _ m => m)
    (fun _ ih es m => @Prod.casesOn ℕ (List ℕ) (fun _ => ℕ) (rowSplitAuxK p W es 0) fun s rest =>
      @Nat.casesOn (fun _ => ℕ) m (ih rest s)
        fun k => ih rest (cond (Nat.ble (k + 1) s) s (k + 1)))

theorem rowAbsMaxAuxK_eq (p W : ℕ) : ∀ (R : ℕ) (es : List ℕ) (m : ℕ),
    rowAbsMaxAuxK p W R es m = max m (rowAbsMax p W R es)
  | 0, _, m => (Nat.max_zero m).symm
  | R + 1, es, m => by
    have h : rowAbsMaxAuxK p W (R + 1) es m =
        rowAbsMaxAuxK p W R (rowSplit p W es).2 (max m (rowSplit p W es).1) := by
      change @Prod.casesOn ℕ (List ℕ) (fun _ => ℕ) (rowSplitAuxK p W es 0) (fun s rest =>
        @Nat.casesOn (fun _ => ℕ) m (rowAbsMaxAuxK p W R rest s)
          fun k => rowAbsMaxAuxK p W R rest (cond (Nat.ble (k + 1) s) s (k + 1))) = _
      rw [rowSplitAuxK_eq, Nat.zero_add]
      cases m with
      | zero => show rowAbsMaxAuxK p W R _ _ = _; rw [Nat.zero_max]
      | succ k =>
        change rowAbsMaxAuxK p W R _ (cond (Nat.ble (k + 1) _) _ (k + 1)) = _
        congr 1
        by_cases hk : k + 1 ≤ (rowSplit p W es).1
        · rw [Nat.ble_eq_true_of_le hk, Bool.cond_true, Nat.max_eq_right hk]
        · have : Nat.ble (k + 1) (rowSplit p W es).1 = false := by
            rw [Bool.eq_false_iff, ne_eq, Nat.ble_eq]; exact hk
          rw [this, Bool.cond_false, Nat.max_eq_left (by omega)]
    rw [h, rowAbsMaxAuxK_eq p W R, rowAbsMax, Nat.max_assoc]

/-- **`rowAbsMax`, by the recursors** (`rowAbsMaxK_eq`). -/
noncomputable def rowAbsMaxK (p W R : ℕ) (es : List ℕ) : ℕ := rowAbsMaxAuxK p W R es 0

theorem rowAbsMaxK_eq (p W R : ℕ) (es : List ℕ) : rowAbsMaxK p W R es = rowAbsMax p W R es := by
  rw [rowAbsMaxK, rowAbsMaxAuxK_eq, Nat.zero_max]

@[csimp] theorem rowAbsMaxK_csimp : @rowAbsMaxK = @rowAbsMax := by
  funext p W R es
  exact rowAbsMaxK_eq p W R es

/-- **Every entry's magnitude, read centred, is below `p / 2`**, by the recursor in natural
arithmetic (`centeredSmallK_eq`). -/
def centeredSmallK (p : ℕ) (es : List ℕ) : Bool :=
  allK (fun c => Nat.blt (2 * centeredAbsN p c) p) es

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
          centeredSmallK p es then
        some (Ivl.sym (rowAbsMaxK p W R es * J.mag))
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

/-- **The group hull accumulator**, comparing both endpoints before the next group.
The comparisons prevent a chain of unevaluated endpoint minima and maxima in kernel checks. -/
def groupsIvlAuxK (A : Ivl) (w : Nat) : Nat → List Int → Ivl → Ivl
  | 0, _, acc => acc
  | n+1, cs, acc =>
    let cur := groupSumIvl A (cs.take w)
    if cur.lo ≤ acc.lo then
      if acc.hi ≤ cur.hi then groupsIvlAuxK A w n (cs.drop w) cur
      else groupsIvlAuxK A w n (cs.drop w) ⟨cur.lo, acc.hi⟩
    else
      if acc.hi ≤ cur.hi then groupsIvlAuxK A w n (cs.drop w) ⟨acc.lo, cur.hi⟩
      else groupsIvlAuxK A w n (cs.drop w) acc
/-- **The group hull with evaluated accumulator endpoints** (`groupsIvlK_eq`).
Compiled checks use `groupsIvl`; this fold bounds kernel reduction depth for long views. -/
def groupsIvlK (A : Ivl) (w : Nat) : Nat → List Int → Option Ivl
  | 0, _ => none
  | n+1, cs => some (groupsIvlAuxK A w n (cs.drop w) (groupSumIvl A (cs.take w)))

/-- **The hull operation is associative.** -/
theorem Ivl.hull_assoc (a b c : Ivl) : (a.hull b).hull c = a.hull (b.hull c) := by
  cases a; cases b; cases c
  simp only [Ivl.hull]
  congr 1 <;> omega

private theorem groupsIvlAuxK_succ (A : Ivl) (w n : Nat) (cs : List Int) (acc : Ivl) :
    groupsIvlAuxK A w (n+1) cs acc =
      groupsIvlAuxK A w n (cs.drop w) (acc.hull (groupSumIvl A (cs.take w))) := by
  simp only [groupsIvlAuxK]
  split <;> split <;> apply congrArg (groupsIvlAuxK A w n (cs.drop w))
  all_goals
    cases hc : groupSumIvl A (cs.take w)
    cases acc
    simp only [hc] at *
    simp only [Ivl.hull]
    congr 1 <;> omega

/-- **A positive number of groups has a hull, including when the group width is zero.** -/
theorem groupsIvl_isSome (A : Ivl) (w n : Nat) (cs : List Int) :
    (groupsIvl A w (n+1) cs).isSome = true := by
  induction n generalizing cs with
  | zero => rfl
  | succ n ih => simpa only [groupsIvl, Option.isSome_map] using ih (cs.drop w)

/-- **The forced accumulator returns the hull of its input interval and the remaining groups.** -/
theorem groupsIvlAuxK_eq (A : Ivl) (w n : Nat) (cs : List Int) (acc : Ivl) :
    groupsIvlAuxK A w n cs acc = ((groupsIvl A w n cs).map acc.hull).getD acc := by
  induction n generalizing cs acc with
  | zero => rfl
  | succ n ih =>
    rw [groupsIvlAuxK_succ, ih]
    cases n with
    | zero => rfl
    | succ n =>
      simp only [groupsIvl]
      cases h : groupsIvl A w (n+1) (cs.drop w) <;> simp only [Option.map, Option.getD]
      · have hs := groupsIvl_isSome A w n (cs.drop w)
        simp only [h, Option.isSome_none, Bool.false_eq_true] at hs
      · exact Ivl.hull_assoc _ _ _

/-- **The kernel group fold returns exactly the canonical group hull for every input.** -/
theorem groupsIvlK_eq (A : Ivl) (w n : Nat) (cs : List Int) :
    groupsIvlK A w n cs = groupsIvl A w n cs := by
  cases n with
  | zero => rfl
  | succ n =>
    simp only [groupsIvlK, groupsIvlAuxK_eq]
    cases n with
    | zero => rfl
    | succ n =>
      simp only [groupsIvl]
      cases h : groupsIvl A w (n+1) (cs.drop w)
      · have hs := groupsIvl_isSome A w n (cs.drop w)
        simp only [h, Option.isSome_none, Bool.false_eq_true] at hs
      · rfl

/-- **Compiled checks retain the original group-hull implementation.** -/
@[csimp] theorem groupsIvlK_csimp : @groupsIvlK = @groupsIvl := by
  funext A w n cs
  exact groupsIvlK_eq A w n cs

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
    | some cs => (Expr.ivl ir p leafI refI a).bind fun A => groupsIvlK A w (cs.length / w) cs
    | none =>
      match constCoords ir p leafI a with
      | some cs => (Expr.ivl ir p leafI refI c).bind fun A => groupsIvlK A w (cs.length / w) cs
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

/-- **`ivlOf` with the table built once**: the code compiled for `ivlOf` (`ivlOf_csimp`).
Compiled code evaluates `ivlT p leafI` where it is read, once per reference; here it is built at
the first reference (a `Thunk`), and not at all for an expression without one. -/
def ivlOfC (p : ℕ) (leafI : ℕ → Option Ivl) (e : Expr) : Option Ivl :=
  let T := Thunk.mk fun _ => ir.ivlT p leafI
  e.ivl ir p leafI (T.get.getD · none)

@[csimp] theorem ivlOf_csimp : @ivlOf = @ivlOfC := rfl

end

end GordieHowe.RealizedProgram
