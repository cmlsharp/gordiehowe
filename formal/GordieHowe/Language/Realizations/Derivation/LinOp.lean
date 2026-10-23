-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Ntt

@[expose] public section

/-!
# GordieHowe: linear operators, for derivations

The rule `linop s` of a derivation, in four kinds of instances
(`GordieHowe.RealizedProgram.LinOpStep`):

* **congruence** (`congr k e`): from `eq d a b` (premise `k`) and `e` an operator applied to `a`
  (`.apply op a`, or `.linear rows a` with every column below `a`'s length), `eq d e e'`, `e'` the
  operator applied to `b`. A named operator's block reads only its operand's first `cols`
  coordinates (`NamedOp.block_congr_cols`), so the application reads `a` only below its length.
* **the matrix form** (`rows op x R N`): `eq d (.apply op x) (.linear R x)`, or
  `.linear R x − .linear N x` for `N` nonempty, `R` and `N` the operator's added and subtracted
  sparse rows (`GordieHowe.RealizedProgram.opRows`): `rowDot M R W` (`M[r W + c]`), `diagonal d`
  and `constDiagonal d` (`d_r`), `scale c` (`c_0`), `acyclicConv h lx` (`h_{r − a}`), `sum w` (the
  constant `1`) (`opRow`); the negacyclic products by a public operand in coefficient form,
  `negacyclicConv`, `polyBroadcast` and `polyMatVec`, `h_{r−k}` added and `h_{r+n−k}` subtracted
  (`negaRows`); `fromDigits k b`, the coefficients `bˡ mod p`, each the previous one times `b`
  (`digitRow`); and `batched b op` (`op`'s rows shifted to its block). A coefficient `M[k]` of a
  constant value `M` may be written as the constant entry itself (`coefMatch`). A user-defined
  operator is exported as `.linear` rows, so it needs no case here.
* **the spectral instance** (`spectral c k`): from the body of the products predicate of the
  spectrally realized convolution `c` (`holds c.products`, premise `k`), where `ConvOkAt d c`, the
  source convolution equals its reading through the transform: `eq d (.ref c.source) (.ref c.read)`
  (`convRead_eq_source`).
* **the transform instances** (`nttInv`, `inttInv`, `convNtt`, `convCoef`, `transposeInv`):
  structured identities of the negacyclic transforms at a root and a size the checker decides
  (`GordieHowe/Language/Realizations/Derivation/Ntt.lean`).
-/

namespace GordieHowe.RealizedProgram

open Export

section

variable (ir : RealizedProgram)

/-! ## Congruence -/

/-- **The operator application `e` with its operand `a` replaced by `b`**: `e` is `.apply op a`
or `.linear rows a`, every column of `rows` below `a`'s length; `none` otherwise. -/
def opSwap (a b : Expr) : Expr → Option Expr
  | .apply op a' => if a'.beq a = true then some (.apply op b) else none
  | .linear rows a' =>
    if a'.beq a = true ∧ (rows.all fun r => r.all fun t => decide (t.1 < ir.exprLen a)) = true then
      some (.linear rows b)
    else none
  | _ => none

/-! ## The matrix form -/

/-- **A row's columns shifted by `o`.** -/
def shiftRow (o : ℕ) (row : List (ℕ × Coef)) : List (ℕ × Coef) := row.map fun t => (o + t.1, t.2)

/-- **Row `r` of a core-language operator's block** as sparse coefficients (`r` below its
`rows`); `none` for an operator whose entries are not coefficients. -/
def opRow : NamedOp → ℕ → Option (List (ℕ × Coef))
  | .rowDot M _ W, r => some ((List.range W).map fun c => (c, .node M (r * W + c)))
  | .diagonal d, r => some [(r, .node d r)]
  | .constDiagonal d, r => some [(r, .node d r)]
  | .scale c, _ => some [(0, .node c 0)]
  | .acyclicConv h lx, r =>
    some (((List.range lx).filter fun a => decide (a ≤ r ∧ r - a < (ir.value h).size)).map
      fun a => (a, .node h (r - a)))
  | .sum w, _ => some ((List.range w).map fun t => (t, .const 1))
  | .batched _ op, r =>
    (opRow op (r % NamedOp.rows ir op)).map
      (shiftRow (r / NamedOp.rows ir op * NamedOp.cols ir op))
  | _, _ => none

/-- **The rows of a negacyclic product's output coordinate `r`** of length `n`, `hc s` the
coefficient of `h_s`, the operand's columns from `off`: `y_r = Σ_{k ≤ r} h_{r−k} x_k −
Σ_{k > r} h_{r+n−k} x_k`, the added and the subtracted entries. -/
def negaRows (n : ℕ) (hc : ℕ → Coef) (off r : ℕ) : List (ℕ × Coef) × List (ℕ × Coef) :=
  (((List.range n).filter fun k => decide (k ≤ r)).map fun k => (off + k, hc (r - k)),
    ((List.range n).filter fun k => decide (r < k)).map fun k => (off + k, hc (r + n - k)))

/-- **The row of a number from its digits** in base `b` modulo `p`, from column `l` with
coefficient `c`: the coefficients `c, c b, c b², …` reduced modulo `p`, each by one
multiplication. -/
def digitRow (p b : ℕ) : ℕ → ℕ → ℕ → List (ℕ × Coef)
  | _, _, 0 => []
  | l, c, n + 1 => (l, .const c) :: digitRow p b (l + 1) (c * b % p) n

/-- **Row `r` of a core-language operator's block** at the characteristic `p`, as the added and
the subtracted sparse coefficients (`r` below its `rows`): the rows of `opRow`, the negacyclic
products by a public operand in coefficient form (`negacyclicConv`, `polyBroadcast`,
`polyMatVec`: `negaRows`), and a number from its digits (`fromDigits`: `digitRow`); `none` for an
operator whose entries are not coefficients. -/
def opRows (p : ℕ) : NamedOp → ℕ → Option (List (ℕ × Coef) × List (ℕ × Coef))
  | .negacyclicConv h .coefficients, r => some (negaRows (ir.value h).size (.node h) 0 r)
  | .polyBroadcast t K .coefficients, j =>
    let n := (ir.value t).size / K
    if j < K * n then some (negaRows n (fun s => .node t (j / n * n + s)) 0 (j % n))
    else some ([], [])
  | .polyMatVec a K L .coefficients, j =>
    let n := (ir.value a).size / (K * L)
    if j < K * n then
      let rs := (List.range L).map fun l =>
        negaRows n (fun s => .node a ((j / n * L + l) * n + s)) (l * n) (j % n)
      some (rs.flatMap (·.1), rs.flatMap (·.2))
    else some ([], [])
  | .fromDigits k base, _ => if base < p then some (digitRow p base 0 (1 % p) k, []) else none
  | .batched _ op, r =>
    (opRows p op (r % NamedOp.rows ir op)).map fun PQ =>
      (shiftRow (r / NamedOp.rows ir op * NamedOp.cols ir op) PQ.1,
        shiftRow (r / NamedOp.rows ir op * NamedOp.cols ir op) PQ.2)
  | op, r => (ir.opRow op r).map fun P => (P, [])

/-- **The coefficient `got` reads as `want`** in field `f`: the same coefficient, or `want` is
coordinate `k` of a constant value of field `f` and `got` its entry `k`. -/
def coefMatch (f : ℕ) (want got : Coef) : Bool :=
  decide (got = want) ||
    match want with
    | .node v k =>
      match (ir.value v).kind with
      | .constant es => decide (ir.valueField v = f) && decide (got = .const (es.getD k 0))
      | _ => false
    | _ => false

/-- **The row `got` reads as the row `want`** in field `f`: entry by entry, the same columns and
matching coefficients. -/
def rowMatch (f : ℕ) : List (ℕ × Coef) → List (ℕ × Coef) → Bool
  | [], [] => true
  | w :: ws, g :: gs => decide (g.1 = w.1) && ir.coefMatch f w.2 g.2 && rowMatch f ws gs
  | _, _ => false

/-- **The rows `R` (added) and `N` (subtracted) from output coordinate `j` on are the
operator's** (`opRows`): row `j` of `.apply op ·` is row `j mod rows` of the block, shifted to
block `j / rows`; a missing subtracted row reads as empty. -/
def rowsOk (f : ℕ) (op : NamedOp) : ℕ → List (List (ℕ × Coef)) → List (List (ℕ × Coef)) → Bool
  | _, [], _ => true
  | j, r :: rs, N =>
    (match ir.opRows (ir.charOf f) op (j % NamedOp.rows ir op) with
      | some PQ =>
        ir.rowMatch f (shiftRow (j / NamedOp.rows ir op * NamedOp.cols ir op) PQ.1) r &&
          ir.rowMatch f (shiftRow (j / NamedOp.rows ir op * NamedOp.cols ir op) PQ.2) (N.headD [])
      | none => false) && rowsOk f op (j + 1) rs N.tail

/-! ## The rule -/

/-- **`linop s`** in domain `d` (`LinOpStep`): congruence, the matrix form, or the spectral
instance. -/
def linopFact (fs : List Fact) (d : ℕ) : LinOpStep → Option Fact
  | .congr k e =>
    match fs[k]? with
    | some (.eq d' a b) =>
      if d' = d then (ir.opSwap a b e).map fun e' => .eq d e e' else none
    | _ => none
  | .rows op x R N =>
    if d < ir.domains.length ∧ R.length = ir.exprLen (.apply op x) ∧
        (N = [] ∨ N.length = R.length) ∧ ir.rowsOk (ir.domainField d) op 0 R N = true then
      some (.eq d (.apply op x)
        (if N = [] then .linear R x else .sub (.linear R x) (.linear N x)))
    else none
  | .spectral c k =>
    match ir.convs[c]?, fs[k]? with
    | some sc, some (.holds q) =>
      if q = sc.products ∧ d < ir.domains.length ∧ ir.convOkAtB d sc = true then
        some (.eq d (.ref sc.source) (.ref sc.read))
      else none
    | _, _ => none
  | s => ir.nttFact d s

end

variable {ir : RealizedProgram} {I : Interp}

/-! ## Soundness -/

/-- A list sum over `List.range n` is the sum over `Finset.range n`. -/
theorem list_sum_map_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i ∈ Finset.range n, g i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

/-- A list sum over a filter is the sum of the indicator. -/
theorem list_sum_map_filter {M : Type*} [AddCommMonoid M] (p : ℕ → Bool) (g : ℕ → M) :
    ∀ l : List ℕ, ((l.filter p).map g).sum = (l.map fun a => if p a then g a else 0).sum
  | [] => rfl
  | a :: l => by
    by_cases h : p a <;> simp [h, list_sum_map_filter p g l]

/-- **A matching coefficient reads as the wanted one** (`coefMatch`), where constants read their
entries. -/
theorem coefMatch_eval {rd : ir.Valuation I} {f : ℕ}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {want got : Coef} (h : ir.coefMatch f want got = true) :
    Coef.eval ir f rd got = Coef.eval ir f rd want := by
  unfold coefMatch at h
  rcases Bool.or_eq_true_iff.1 h with h | h
  · rw [of_decide_eq_true h]
  · cases want with
    | const c => cases h
    | node v k =>
      simp only at h
      cases hk : (ir.value v).kind with
      | constant es =>
        rw [hk] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hf, rfl⟩ := h
        simp only [Coef.eval]
        rw [hK v es hk k, castElt_decode hf]
      | _ => rw [hk] at h; cases h

/-- **Matching rows read alike** (`rowMatch`). -/
theorem rowMatch_sum {rd : ir.Valuation I} {f : ℕ}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0)) (x : ℕ → (I f).K) :
    ∀ {want got : List (ℕ × Coef)}, ir.rowMatch f want got = true →
      (got.map fun t => Coef.eval ir f rd t.2 * x t.1).sum =
        (want.map fun t => Coef.eval ir f rd t.2 * x t.1).sum
  | [], [], _ => rfl
  | w :: ws, g :: gs, h => by
    simp only [rowMatch, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    simp only [List.map_cons, List.sum_cons, h1, coefMatch_eval hK h2, rowMatch_sum hK x h3]
  | [], _ :: _, h => by simp [rowMatch] at h
  | _ :: _, [], h => by simp [rowMatch] at h

/-- **A shifted row reads the shifted operand.** -/
theorem shiftRow_sum {rd : ir.Valuation I} {f : ℕ} (x : ℕ → (I f).K) (o : ℕ)
    (row : List (ℕ × Coef)) :
    ((shiftRow o row).map fun t => Coef.eval ir f rd t.2 * x t.1).sum =
      (row.map fun t => Coef.eval ir f rd t.2 * x (o + t.1)).sum := by
  simp [shiftRow, Function.comp_def]

/-- **A core-language operator's block row is its sparse row** (`opRow`), in a field decoding
`1` to `1`. -/
theorem block_eq_opRow {rd : ir.Valuation I} {f : ℕ} (h1 : (I f).decode 1 = 1) :
    ∀ (op : NamedOp) (x : ℕ → (I f).K) {r : ℕ} {row : List (ℕ × Coef)},
      r < NamedOp.rows ir op → ir.opRow op r = some row →
      NamedOp.block ir f rd op x r = (row.map fun t => Coef.eval ir f rd t.2 * x t.1).sum
  | .rowDot M R W, x, r, row, hr, h => by
    simp only [opRow, Option.some.injEq] at h
    subst h
    simp only [NamedOp.rows] at hr
    simp only [NamedOp.block, Ops.rowDot, if_pos hr, List.map_map, Function.comp_def, Coef.eval]
    rw [list_sum_map_range (fun c => castElt (rd M (r * W + c)) * x c), Finset.sum_range]
  | .diagonal d, x, r, row, hr, h => by
    simp only [opRow, Option.some.injEq] at h
    subst h
    simp only [NamedOp.rows] at hr
    simp [NamedOp.block, Ops.diagonal, if_pos hr, Coef.eval]
  | .constDiagonal d, x, r, row, hr, h => by
    simp only [opRow, Option.some.injEq] at h
    subst h
    simp only [NamedOp.rows] at hr
    simp [NamedOp.block, Ops.diagonal, if_pos hr, Coef.eval]
  | .scale c, x, r, row, hr, h => by
    simp only [opRow, Option.some.injEq] at h
    subst h
    simp only [NamedOp.rows] at hr
    obtain rfl : r = 0 := by omega
    simp [NamedOp.block, Coef.eval]
  | .acyclicConv h lx, x, r, row, hr, hrow => by
    simp only [opRow, Option.some.injEq] at hrow
    subst hrow
    simp only [NamedOp.rows] at hr
    simp only [NamedOp.block, Ops.acyclic, if_pos (show r + 1 < lx + (ir.value h).size by omega)]
    rw [List.map_map, list_sum_map_filter, list_sum_map_range, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases hp : (a : ℕ) ≤ r ∧ r - a < (ir.value h).size
    · rw [if_pos (by simpa using hp), Finset.sum_eq_single (⟨r - a, hp.2⟩ : Fin (ir.value h).size)]
      · simp [Coef.eval, show (a : ℕ) + (r - a) = r by omega, mul_comm]
      · intro b _ hb
        rw [if_neg]
        intro hab
        apply hb
        ext
        simp only
        omega
      · simp
    · rw [if_neg (by simpa using hp)]
      exact Finset.sum_eq_zero fun b _ => if_neg fun hab => hp ⟨by omega, by omega⟩
  | .sum w, x, r, row, hr, h => by
    simp only [opRow, Option.some.injEq] at h
    subst h
    simp only [NamedOp.rows] at hr
    obtain rfl : r = 0 := by omega
    simp only [NamedOp.block, Ops.sum, ite_true, List.map_map, Function.comp_def, Coef.eval, h1,
      one_mul]
    rw [list_sum_map_range (fun t => x t), Finset.sum_range]
  | .batched b op, x, r, row, hr, h => by
    simp only [opRow, Option.map_eq_some_iff] at h
    obtain ⟨row', h', rfl⟩ := h
    simp only [NamedOp.rows] at hr
    have hpos : 0 < NamedOp.rows ir op := by
      rcases Nat.eq_zero_or_pos (NamedOp.rows ir op) with h0 | h0
      · rw [h0, Nat.mul_zero] at hr
        omega
      · exact h0
    simp only [NamedOp.block, if_pos hr]
    rw [block_eq_opRow h1 op _ (Nat.mod_lt _ hpos) h', shiftRow_sum]
  | .negacyclicConv _ _, _, _, _, _, h => by simp [opRow] at h
  | .polyMatVec _ _ _ _, _, _, _, _, h => by simp [opRow] at h
  | .polyBroadcast _ _ _, _, _, _, _, h => by simp [opRow] at h
  | .ntt _ _ _, _, _, _, _, h => by simp [opRow] at h
  | .inverseNtt _ _, _, _, _, _, h => by simp [opRow] at h
  | .nttTranspose _ _, _, _, _, _, h => by simp [opRow] at h
  | .macConv _ _ _ _, _, _, _, _, h => by simp [opRow] at h
  | .fromDigits _ _, _, _, _, _, h => by simp [opRow] at h

/-- **A list sum over `List.range n` is the sum over `Fin n`.** -/
theorem list_sum_map_range_fin {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ((List.range n).map g).sum = ∑ i : Fin n, g i := by
  rw [list_sum_map_range, Finset.sum_range]

/-- **A negacyclic product's coordinate `r` as its added and subtracted terms**:
`Σ_{k ≤ r} h_{r−k} y_k − Σ_{k > r} h_{r+n−k} y_k` (`Ops.negacyclic_apply`). -/
theorem negacyclic_split {K : Type*} [Field K] (n : ℕ) (g y : ℕ → K) {r : ℕ} (hr : r < n) :
    Ops.negacyclic n g y r =
      (((List.range n).filter fun k => decide (k ≤ r)).map fun k => g (r - k) * y k).sum -
        (((List.range n).filter fun k => decide (r < k)).map fun k => g (r + n - k) * y k).sum := by
  rw [Ops.negacyclic_apply n g y hr, list_sum_map_filter, list_sum_map_filter,
    list_sum_map_range_fin, list_sum_map_range_fin]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) ≤ r
    · rw [if_pos (by simpa using hk), Finset.sum_eq_single (⟨r - k, by omega⟩ : Fin n)]
      · simp [show r - (k : ℕ) + k = r by omega]
      · intro i _ hi
        rw [if_neg]
        intro h
        exact hi (Fin.ext (by simp only; omega))
      · simp
    · rw [if_neg (by simpa using hk)]
      exact Finset.sum_eq_zero fun i _ => if_neg (by omega)
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hkn := k.isLt
    by_cases hk : r < (k : ℕ)
    · rw [if_pos (by simpa using hk), Finset.sum_eq_single (⟨r + n - k, by omega⟩ : Fin n)]
      · simp [show r + n - (k : ℕ) + k = r + n by omega]
      · intro i _ hi
        rw [if_neg]
        intro h
        exact hi (Fin.ext (by simp only; omega))
      · simp
    · rw [if_neg (by simpa using hk)]
      exact Finset.sum_eq_zero fun i _ => if_neg (by have := i.isLt; omega)

/-- **The rows of a negacyclic product read its terms** (`negaRows`), `hc s` reading `g s`. -/
theorem negaRows_sum {rd : ir.Valuation I} {f : ℕ} (x : ℕ → (I f).K) (n : ℕ) (hc : ℕ → Coef)
    (g : ℕ → (I f).K) (hg : ∀ s, Coef.eval ir f rd (hc s) = g s) (off r : ℕ) :
    ((negaRows n hc off r).1.map fun t => Coef.eval ir f rd t.2 * x t.1).sum =
        (((List.range n).filter fun k => decide (k ≤ r)).map
          fun k => g (r - k) * x (off + k)).sum ∧
      ((negaRows n hc off r).2.map fun t => Coef.eval ir f rd t.2 * x t.1).sum =
        (((List.range n).filter fun k => decide (r < k)).map
          fun k => g (r + n - k) * x (off + k)).sum := by
  simp [negaRows, Function.comp_def, hg]

/-- **A list sum over a flat map** is the sum of the sums. -/
theorem list_sum_map_flatMap {α β M : Type*} [AddCommMonoid M] (F : α → List β) (g : β → M) :
    ∀ l : List α, ((l.flatMap F).map g).sum = (l.map fun a => ((F a).map g).sum).sum
  | [] => rfl
  | a :: l => by simp [List.flatMap_cons, List.sum_append, list_sum_map_flatMap F g l]

/-- **The row of a number from its digits reads `Σ_i c bⁱ x_{l+i}`** (`digitRow`), in a field of
characteristic `p` decoding the naturals below `p` to their casts. -/
theorem digitRow_sum {rd : ir.Valuation I} {f p b : ℕ} [CharP (I f).K p] (hp : 0 < p)
    (hdec : ∀ c < p, (I f).decode c = (c : (I f).K)) (x : ℕ → (I f).K) :
    ∀ (n l c : ℕ), c < p →
      ((digitRow p b l c n).map fun t => Coef.eval ir f rd t.2 * x t.1).sum =
        ∑ i ∈ Finset.range n, (c : (I f).K) * (b : (I f).K) ^ i * x (l + i)
  | 0, _, _, _ => by simp [digitRow]
  | n + 1, l, c, hc => by
    simp only [digitRow, List.map_cons, List.sum_cons]
    rw [digitRow_sum hp hdec x n (l + 1) (c * b % p) (Nat.mod_lt _ hp)]
    change (I f).decode c * x l + _ = _
    rw [hdec c hc, Finset.sum_range_succ',
      ← CharP.natCast_eq_natCast_mod]
    simp only [Nat.cast_mul, pow_zero, mul_one, Nat.add_zero, pow_succ]
    rw [add_comm]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show l + 1 + i = l + (i + 1) by omega]
    ring

/-- **A core-language operator's block row is its added minus its subtracted sparse row**
(`opRows`), in a field of the program's characteristic decoding the naturals below it to their
casts. -/
theorem block_eq_opRows {rd : ir.Valuation I} {f : ℕ} [CharP (I f).K (ir.charOf f)]
    (hp : 0 < ir.charOf f) (h1 : (I f).decode 1 = 1)
    (hdec : ∀ c < ir.charOf f, (I f).decode c = (c : (I f).K)) :
    ∀ (op : NamedOp) (x : ℕ → (I f).K) {r : ℕ} {P Q : List (ℕ × Coef)},
      r < NamedOp.rows ir op → ir.opRows (ir.charOf f) op r = some (P, Q) →
      NamedOp.block ir f rd op x r = (P.map fun t => Coef.eval ir f rd t.2 * x t.1).sum -
        (Q.map fun t => Coef.eval ir f rd t.2 * x t.1).sum
  | .negacyclicConv h form, x, r, P, Q, hr, hPQ => by
    cases form with
    | coefficients =>
      simp only [opRows, Option.some.injEq] at hPQ
      simp only [NamedOp.rows] at hr
      obtain ⟨h1', h2'⟩ := negaRows_sum (rd := rd) x _ (.node h) (fun s => castElt (rd h s))
        (fun s => rfl) 0 r
      rw [hPQ] at h1' h2'
      rw [h1', h2']
      simp only [NamedOp.block, NamedOp.formPoly, Nat.zero_add]
      exact negacyclic_split _ _ _ hr
    | ntt psi => simp [opRows, opRow] at hPQ
  | .polyBroadcast t K form, x, j, P, Q, hr, hPQ => by
    cases form with
    | coefficients =>
      simp only [opRows] at hPQ
      split_ifs at hPQ with hj
      · simp only [Option.some.injEq] at hPQ
        have hn : 0 < (ir.value t).size / K := by
          rcases Nat.eq_zero_or_pos ((ir.value t).size / K) with h0 | h0
          · rw [h0, Nat.mul_zero] at hj
            omega
          · exact h0
        obtain ⟨h1', h2'⟩ := negaRows_sum (rd := rd) x _
          (fun s => .node t (j / ((ir.value t).size / K) * ((ir.value t).size / K) + s))
          (fun s => castElt (rd t (j / ((ir.value t).size / K) * ((ir.value t).size / K) + s)))
          (fun s => rfl) 0 (j % ((ir.value t).size / K))
        rw [hPQ] at h1' h2'
        rw [h1', h2']
        simp only [NamedOp.block, NamedOp.formPoly, if_pos hj, Nat.zero_add]
        exact negacyclic_split _ _ _ (Nat.mod_lt _ hn)
      · simp only [Option.some.injEq, Prod.mk.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        simp [NamedOp.block, if_neg hj]
    | ntt psi => simp [opRows, opRow] at hPQ
  | .polyMatVec a K L form, x, j, P, Q, hr, hPQ => by
    cases form with
    | coefficients =>
      simp only [opRows] at hPQ
      split_ifs at hPQ with hj
      · simp only [Option.some.injEq, Prod.mk.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        have hn : 0 < (ir.value a).size / (K * L) := by
          rcases Nat.eq_zero_or_pos ((ir.value a).size / (K * L)) with h0 | h0
          · rw [h0, Nat.mul_zero] at hj
            omega
          · exact h0
        simp only [NamedOp.block, NamedOp.formPoly, if_pos hj]
        rw [list_sum_map_flatMap, list_sum_map_flatMap, List.map_map, List.map_map,
          list_sum_map_range_fin, list_sum_map_range_fin, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        obtain ⟨h1', h2'⟩ := negaRows_sum (rd := rd) x _
          (fun s => .node a ((j / ((ir.value a).size / (K * L)) * L + l) *
            ((ir.value a).size / (K * L)) + s))
          (fun s => castElt (rd a ((j / ((ir.value a).size / (K * L)) * L + l) *
            ((ir.value a).size / (K * L)) + s)))
          (fun s => rfl) (l * ((ir.value a).size / (K * L))) (j % ((ir.value a).size / (K * L)))
        simp only [Function.comp_def]
        rw [h1', h2']
        exact negacyclic_split _ _ _ (Nat.mod_lt _ hn)
      · simp only [Option.some.injEq, Prod.mk.injEq] at hPQ
        obtain ⟨rfl, rfl⟩ := hPQ
        simp [NamedOp.block, if_neg hj]
    | ntt psi => simp [opRows, opRow] at hPQ
  | .fromDigits k base, x, r, P, Q, hr, hPQ => by
    simp only [opRows] at hPQ
    split_ifs at hPQ with hb
    simp only [Option.some.injEq, Prod.mk.injEq] at hPQ
    obtain ⟨rfl, rfl⟩ := hPQ
    simp only [NamedOp.rows] at hr
    obtain rfl : r = 0 := by omega
    rw [digitRow_sum hp hdec x k 0 (1 % ir.charOf f) (Nat.mod_lt _ hp), ← list_sum_map_range,
      list_sum_map_range_fin]
    simp only [NamedOp.block, Ops.fromDigits, ite_true, List.map_nil, List.sum_nil, sub_zero,
      hdec base hb, ← CharP.natCast_eq_natCast_mod, Nat.cast_one, one_mul, Nat.zero_add]
  | .batched b op, x, r, P, Q, hr, hPQ => by
    simp only [opRows, Option.map_eq_some_iff] at hPQ
    obtain ⟨⟨P', Q'⟩, h', hPQ⟩ := hPQ
    simp only [Prod.mk.injEq] at hPQ
    obtain ⟨rfl, rfl⟩ := hPQ
    simp only [NamedOp.rows] at hr
    have hpos : 0 < NamedOp.rows ir op := by
      rcases Nat.eq_zero_or_pos (NamedOp.rows ir op) with h0 | h0
      · rw [h0, Nat.mul_zero] at hr
        omega
      · exact h0
    simp only [NamedOp.block, if_pos hr]
    rw [block_eq_opRows hp h1 hdec op _ (Nat.mod_lt _ hpos) h', shiftRow_sum, shiftRow_sum]
  | .rowDot M R W, x, r, P, Q, hr, hPQ => by
    simp only [opRows, Option.map_eq_some_iff, Prod.mk.injEq] at hPQ
    obtain ⟨P', h', rfl, rfl⟩ := hPQ
    simp [block_eq_opRow h1 _ x hr h']
  | .diagonal d, x, r, P, Q, hr, hPQ => by
    simp only [opRows, Option.map_eq_some_iff, Prod.mk.injEq] at hPQ
    obtain ⟨P', h', rfl, rfl⟩ := hPQ
    simp [block_eq_opRow h1 _ x hr h']
  | .constDiagonal d, x, r, P, Q, hr, hPQ => by
    simp only [opRows, Option.map_eq_some_iff, Prod.mk.injEq] at hPQ
    obtain ⟨P', h', rfl, rfl⟩ := hPQ
    simp [block_eq_opRow h1 _ x hr h']
  | .scale c, x, r, P, Q, hr, hPQ => by
    simp only [opRows, Option.map_eq_some_iff, Prod.mk.injEq] at hPQ
    obtain ⟨P', h', rfl, rfl⟩ := hPQ
    simp [block_eq_opRow h1 _ x hr h']
  | .acyclicConv h lx, x, r, P, Q, hr, hPQ => by
    simp only [opRows, Option.map_eq_some_iff, Prod.mk.injEq] at hPQ
    obtain ⟨P', h', rfl, rfl⟩ := hPQ
    simp [block_eq_opRow h1 _ x hr h']
  | .sum w, x, r, P, Q, hr, hPQ => by
    simp only [opRows, Option.map_eq_some_iff, Prod.mk.injEq] at hPQ
    obtain ⟨P', h', rfl, rfl⟩ := hPQ
    simp [block_eq_opRow h1 _ x hr h']
  | .ntt _ _ _, _, _, _, _, _, h => by simp [opRows, opRow] at h
  | .inverseNtt _ _, _, _, _, _, _, h => by simp [opRows, opRow] at h
  | .nttTranspose _ _, _, _, _, _, _, h => by simp [opRows, opRow] at h
  | .macConv _ _ _ _, _, _, _, _, _, h => by simp [opRows, opRow] at h

/-- **Rows that check are the operator's**, row by row (`rowsOk`). -/
theorem rowsOk_getD {f : ℕ} {op : NamedOp} :
    ∀ {j : ℕ} {R N : List (List (ℕ × Coef))}, ir.rowsOk f op j R N = true → ∀ i < R.length,
      ∃ PQ, ir.opRows (ir.charOf f) op ((j + i) % NamedOp.rows ir op) = some PQ ∧
        ir.rowMatch f (shiftRow ((j + i) / NamedOp.rows ir op * NamedOp.cols ir op) PQ.1)
          (R.getD i []) = true ∧
        ir.rowMatch f (shiftRow ((j + i) / NamedOp.rows ir op * NamedOp.cols ir op) PQ.2)
          (N.getD i []) = true
  | _, [], _, _, i, hi => by simp at hi
  | j, r :: rs, N, h, i, hi => by
    simp only [rowsOk, Bool.and_eq_true] at h
    obtain ⟨h0, hrs⟩ := h
    cases i with
    | zero =>
      split at h0
      · rename_i PQ hPQ
        simp only [Bool.and_eq_true] at h0
        refine ⟨PQ, by simpa using hPQ, by simpa using h0.1, ?_⟩
        cases N <;> simpa using h0.2
      · cases h0
    | succ i =>
      obtain ⟨PQ, hPQ, hm, hn⟩ := rowsOk_getD hrs i (by simpa using hi)
      refine ⟨PQ, by rw [show j + (i + 1) = j + 1 + i by omega]; exact hPQ,
        by rw [show j + (i + 1) = j + 1 + i by omega]; simpa using hm, ?_⟩
      rw [show j + (i + 1) = j + 1 + i by omega]
      cases N <;> simpa using hn

/-- **An operator application reads its operand below the operand's length**: output coordinate
`j` below `exprLen (.apply op a)` reads block `j / rows`, whose coordinates lie below `a`'s
length. -/
theorem apply_reads_below {L c r j t : ℕ} (hj : j < L / c * r) (ht : t < c) :
    0 < r ∧ j / r * c + t < L := by
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, Nat.mul_zero] at hj
      omega
    · exact h0
  refine ⟨hr, ?_⟩
  have hq : j / r < L / c := (Nat.div_lt_iff_lt_mul hr).2 hj
  calc j / r * c + t < j / r * c + c := by omega
    _ = (j / r + 1) * c := by ring
    _ ≤ L / c * c := Nat.mul_le_mul_right _ hq
    _ ≤ L := Nat.div_mul_le_self L c

/-- **A zero constant reads `0`** at a reader whose constants read their entries, in a field
decoding `0` to `0` (`evalE_leaf_zeroConst` at any reader). -/
theorem evalE_leaf_zeroConst_of {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {f v : ℕ} (hv : ir.zeroConst v = true) (hf : ir.valueField v = f) (h0 : (I f).decode 0 = 0)
    (i : ℕ) : ir.evalE rd f (.leaf v) i = 0 := by
  unfold zeroConst at hv
  split at hv
  · rename_i es hk
    rw [evalE_leaf, hK v es hk i]
    have h00 : es.getD i 0 = 0 := by
      rw [List.getD_eq_getElem?_getD]
      cases hes : es[i]? with
      | none => rfl
      | some c =>
        have := List.all_eq_true.1 hv c (List.mem_of_getElem? hes)
        simpa using this
    rw [h00, castElt_decode hf, h0]
  · cases hv

/-- **`linopFact_sound`**: the rule is sound: its fact holds where its premises do, at the reader
of a reader whose constants read their entries (`hK`), of a well-formed program whose interpretation is registered and lawful. -/
theorem linopFact_sound {primeNodes : ℕ → List String} (hwf : ir.WellFormed)
    (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ} {s : LinOpStep} {f : Fact}
    (hf : ir.linopFact fs d s = some f) : f.HoldsWith ir rd := by
  cases s with
  | congr k E =>
    simp only [linopFact] at hf
    split at hf
    · rename_i d' a b hk
      split_ifs at hf with hd
      subst hd
      obtain ⟨E', hE', rfl⟩ := Option.map_eq_some_iff.1 hf
      have hab : Fact.HoldsWith ir (rd) (.eq d' a b) := hfs _ (List.mem_of_getElem? hk)
      unfold opSwap at hE'
      split at hE'
      · rename_i op a'
        split_ifs at hE' with ha
        cases hE'
        obtain rfl := Expr.eq_of_beq ha
        intro j hj
        rw [exprLen_apply] at hj
        simp only [evalWith, evalE_apply, NamedOp.apply]
        by_cases hc : NamedOp.cols ir op = 0
        · rw [hc, Nat.div_zero, Nat.zero_mul] at hj
          omega
        have hpos := (apply_reads_below (t := 0) hj (Nat.pos_of_ne_zero hc)).1
        exact NamedOp.block_congr_cols ir (rd) op (Nat.mod_lt _ hpos) fun t ht =>
          hab _ (apply_reads_below hj ht).2
      · rename_i rows a'
        split_ifs at hE' with ha
        cases hE'
        obtain rfl := Expr.eq_of_beq ha.1
        intro j _
        change (((rows.getD j []).map fun t =>
            Coef.eval ir _ (rd) t.2 * ir.evalE (rd) _ a' t.1).sum) =
          (((rows.getD j []).map fun t =>
            Coef.eval ir _ (rd) t.2 * ir.evalE (rd) _ b t.1).sum)
        refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
        have hlt : t.1 < ir.exprLen a' := by
          rw [List.getD_eq_getElem?_getD] at ht
          cases hr : rows[j]? with
          | none => rw [hr] at ht; simp at ht
          | some row =>
            rw [hr] at ht
            have hall := List.all_eq_true.1 ha.2 row (List.mem_of_getElem? hr)
            exact of_decide_eq_true (List.all_eq_true.1 hall t ht)
        exact congrArg _ (hab t.1 hlt)
      · cases hE'
    · cases hf
  | rows op x R N =>
    simp only [linopFact] at hf
    split at hf
    case isFalse => cases hf
    rename_i hc
    simp only [Option.some.injEq] at hf
    subst hf
    obtain ⟨hd, hlen, hN, hok⟩ := hc
    have hfd := domainField_lt hwf hd
    have hchar : CharP (I (ir.domainField d)).K (ir.charOf (ir.domainField d)) :=
      charP_field hI hfd
    have hne0 := CharP.char_ne_zero_of_finite (I (ir.domainField d)).K
      (ir.charOf (ir.domainField d))
    have hne1 := CharP.char_ne_one (I (ir.domainField d)).K (ir.charOf (ir.domainField d))
    have hdec : ∀ c < ir.charOf (ir.domainField d),
        (I (ir.domainField d)).decode c = (c : (I (ir.domainField d)).K) :=
      fun c hc => hL.decode_natCast _ hfd c hc
    have h1 : (I (ir.domainField d)).decode 1 = 1 := by
      rw [hdec 1 (by omega), Nat.cast_one]
    have key : ∀ j < ir.exprLen (.apply op x),
        ir.evalWith (rd) d (.apply op x) j =
          ir.evalWith (rd) d (.linear R x) j -
            ir.evalWith (rd) d (.linear N x) j := by
      intro j hj
      have hj' := hj
      rw [exprLen_apply] at hj'
      have hpos := (apply_reads_below (t := 0) hj' (Nat.zero_lt_of_ne_zero (by
        intro h0
        rw [h0, Nat.div_zero, Nat.zero_mul] at hj'
        omega))).1
      obtain ⟨⟨P, Q⟩, hrow, hm, hn⟩ := rowsOk_getD hok j (by rw [hlen]; exact hj)
      simp only [Nat.zero_add] at hrow hm hn
      have hb := block_eq_opRows (rd := rd) (Nat.pos_of_ne_zero hne0) h1 hdec op
        (fun t => ir.evalE (rd) (ir.domainField d) x
          (j / NamedOp.rows ir op * NamedOp.cols ir op + t)) (Nat.mod_lt _ hpos) hrow
      simp only [evalWith, evalE_apply, NamedOp.apply]
      rw [hb, ← shiftRow_sum, ← shiftRow_sum, ← rowMatch_sum hK _ hm, ← rowMatch_sum hK _ hn]
      rfl
    split_ifs with hN0
    · subst hN0
      intro j hj
      rw [key j hj]
      have h0 : ir.evalWith (rd) d (.linear [] x) j = 0 := by
        simp [evalWith, evalE, Expr.eval]
      rw [h0, sub_zero]
    · intro j hj
      rw [key j hj]
      rfl
  | spectral c k =>
    simp only [linopFact] at hf
    split at hf
    · rename_i sc q hc hk
      split_ifs at hf with hq
      cases hf
      obtain ⟨rfl, hd, hok⟩ := hq
      have hfd := domainField_lt hwf hd
      have hprod : Fact.HoldsWith ir (rd) (.holds sc.products) :=
        hfs _ (List.mem_of_getElem? hk)
      have := convRead_eq_source hwf.refsOrdered
        (fun v hv hfv i => evalE_leaf_zeroConst_of hK hv hfv
          (Interp.zeroDecodes_of_lawful hI hL _ hfd) i)
        (fun c hc => hL.decode_natCast _ hfd c hc) (charP_field hI hfd)
        ((ir.convOkAtB_iff d sc).1 hok) hprod
      exact this.2
    · cases hf
  | nttInv n psi x => exact nttFact_sound hwf hI hL (by simpa only [linopFact] using hf)
  | inttInv n psi y => exact nttFact_sound hwf hI hL (by simpa only [linopFact] using hf)
  | convNtt h psi x => exact nttFact_sound hwf hI hL (by simpa only [linopFact] using hf)
  | convCoef h psi x => exact nttFact_sound hwf hI hL (by simpa only [linopFact] using hf)
  | transposeInv n psi psi' x => exact nttFact_sound hwf hI hL (by simpa only [linopFact] using hf)
  | convBcastNtt t K psi x => exact nttFact_sound hwf hI hL (by simpa only [linopFact] using hf)
  | convMatNtt a K L psi x => exact nttFact_sound hwf hI hL (by simpa only [linopFact] using hf)
  | adjoint n psi y x => exact nttFact_sound hwf hI hL (by simpa only [linopFact] using hf)

end GordieHowe.RealizedProgram
