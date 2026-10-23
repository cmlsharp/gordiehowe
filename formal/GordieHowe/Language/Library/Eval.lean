-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.Protocol
public import GordieHowe.Language.RealizedProgram.Views
public import GordieHowe.Language.RealizedProgram.OpsLemmas
public import GordieHowe.Foundations.Probability.IdentDistrib
public import GordieHowe.Foundations.Probability.ChallengeEventCount

@[expose] public section

/-!
# GordieHowe frontend: evaluating the program's expressions

The library the frontend's proofs read the program through (the plan-level theorem's first half:
`GordieHowe.RealizedProgram.rbr_of_events` at the source program, `GordieHowe/Language/RealizedProgram/Protocol.lean`):

* **Index maps** (`IndexMap.entry_single`, `IndexMap.entry_replicate`): the entries of one run and
  of a repeated run.
* **Expressions** (`GordieHowe.RealizedProgram.evalE_leaf`, `evalE_reindex`, `evalE_concat`, `evalE_prod`,
  `evalE_mux`, `evalE_apply_sum`, `evalE_apply_batched_fromDigits`, `evalE_apply_negacyclicConv`,
  `evalE_logic_lt`, `evalE_ref`; `exprLen_*`; the integer readings
  `evalIntWith_*`): one step of `Expr.eval` or `Expr.evalInt` each.
* **Reading values** (`reader_of_bits_of_priv`, `reader_of_challenge`, `bitView_bool`,
  `reader_bool_of_bits`, `evalE_leaf_bool_of_isBitView`, `reader_eq_of_nodeReads_nil`,
  `evalE_leaf_of_isConstant`): a bit view is the `0`/`1` of a coordinate of its word, so `0` or `1`
  (in any field, `castElt_bool`); a challenge value is its challenge; a value that reads nothing
  from the run is fixed by the statement and the committed assignment; a constant reads its entries
  (`constRead`). A committed value is `GordieHowe.RealizedProgram.reader_of_priv`; the statement's values are
  `GordieHowe.RealizedProgram.reader_of_input` and `GordieHowe.RealizedProgram.reader_of_opaque_nil` (`GordieHowe/Language/RealizedProgram/Views.lean`).
* **Predicates by name** (`GordieHowe.RealizedProgram.predByName`): the identifier of the first predicate of a name;
  a source predicate of a satisfied source program holds (`SourceSatAt.holdsAt_of_predByName`).
  Its body is read through Option-valued matchers on `PredBody` and `Expr` (`Expr` has no decidable
  equality), which return the identifiers of a body of a known shape.
* **Named operators are linear** (`NamedOp.block_eq_sum_unit`): output coordinate `r` is
  `Σ_{t < cols} M_{r t} x_t`, `M_{r t}` the operator on the unit vector `t` (it reads only the first
  `cols` coordinates, `NamedOp.block_congr_cols`, vanishes at zero and past `rows`).
* **Bits read in two fields** (`Bits.natOfBits_eq_of_one_iff`): bits that are `1` at the same
  places denote the same natural.
* **A challenge of one coordinate drawn from the field** (`probUniform_badAt_setChal_le`): an event
  fixed before it has the challenge as a root with probability at most its degree over the field's
  size.
-/

namespace GordieHowe.RealizedProgram

open Export IOP
open scoped NNReal ENNReal

/-! ## Index maps -/

namespace IndexMap

/-- **The size of a run followed by more runs.** -/
theorem size_cons (r : ℕ × ℤ × ℕ) (m : IndexMap) : size (r :: m) = r.2.2 + size m := by
  simp [size]

/-- **The size of one run** is its count. -/
@[simp] theorem size_single (s : ℕ) (d : ℤ) (c : ℕ) : size [(s, d, c)] = c := by
  simp [size]

/-- **Entry `i` of one run**: `s + d i`, for `i` below its count. -/
theorem entry_single {s : ℕ} {d : ℤ} {c i : ℕ} (h : i < c) :
    entry [(s, d, c)] i = ((s : ℤ) + d * i).toNat := by
  simp [entry, h]

/-- **Entry `i` of a run of step `1`** is `s + i`, for `i` below its count. -/
theorem entry_step_one {s c i : ℕ} (h : i < c) : entry [(s, 1, c)] i = s + i := by
  rw [entry_single h]
  omega

/-- **Entry `i` of a run of step `0`** is `s`, for `i` below its count. -/
theorem entry_step_zero {s c i : ℕ} (h : i < c) : entry [(s, 0, c)] i = s := by
  rw [entry_single h]
  simp

/-- **Entry `i` of a run repeated `k` times**: the run's entry `i mod c`, for `i` below `k c`. -/
theorem entry_replicate {s : ℕ} {d : ℤ} {c : ℕ} :
    ∀ {k i : ℕ}, i < k * c →
      entry (List.replicate k (s, d, c)) i = ((s : ℤ) + d * (i % c : ℕ)).toNat
  | 0, _, h => by simp at h
  | k + 1, i, h => by
    rw [List.replicate_succ, entry]
    by_cases hi : i < c
    · rw [if_pos hi, Nat.mod_eq_of_lt hi]
    · rw [if_neg hi, entry_replicate (by rw [Nat.add_mul, Nat.one_mul] at h; omega)]
      conv_rhs => rw [Nat.mod_eq_sub_mod (by omega : c ≤ i)]

/-- **The size of concatenated runs** is the sum of the sizes. -/
theorem size_append (m m' : IndexMap) : size (m ++ m') = size m + size m' := by
  simp [size]

/-- **Entry `i` of concatenated runs**: the first runs' entry below their size, the second's
after. -/
theorem entry_append : ∀ (m m' : IndexMap) (i : ℕ),
    entry (m ++ m') i = if i < size m then entry m i else entry m' (i - size m)
  | [], m', i => by simp [size]
  | (s, d, c) :: rest, m', i => by
    rw [List.cons_append, entry, entry, size_cons, entry_append rest m' (i - c)]
    simp only
    by_cases hi : i < c
    · rw [if_pos hi, if_pos (by omega), if_pos hi]
    · rw [if_neg hi, if_neg hi]
      by_cases hr : i - c < size rest
      · rw [if_pos hr, if_pos (by omega)]
      · rw [if_neg hr, if_neg (by omega), Nat.sub_sub]

end IndexMap

section

variable {ir : RealizedProgram} {I : Interp}

/-! ## Shared expressions -/

/-- **A shared expression's value does not depend on the levels** past its index, when the shared
expressions read only entries of smaller index. -/
theorem refVal_stable (ho : ir.RefsOrdered) (leaf : ir.Valuation I) (f : ℕ) :
    ∀ k, k < ir.exprs.length → ∀ n m, k < n → k < m → ir.refVal leaf n f k = ir.refVal leaf m f k
  | k, hk, n + 1, m + 1, hn, hm => by
    funext i
    simp only [refVal]
    exact congrFun (Expr.eval_congr ir (ir.expr k) (fun _ _ => rfl) fun k' hk' =>
      have := ho k hk k' hk'
      refVal_stable ho leaf f k' (by omega) n m (by omega) (by omega)) i

/-- **A reference reads its shared expression.** -/
theorem evalE_ref (ho : ir.RefsOrdered) (leaf : ir.Valuation I) (f : ℕ) {k : ℕ}
    (hk : k < ir.exprs.length) : ir.evalE leaf f (.ref k) = ir.evalE leaf f (ir.expr k) := by
  funext i
  simp only [evalE, Expr.eval]
  rw [refVal_stable ho leaf f k hk _ (k + 1) hk (by omega)]
  simp only [refVal]
  exact congrFun (Expr.eval_congr ir (ir.expr k) (fun _ _ => rfl) fun k' hk' =>
    have := ho k hk k' hk'
    refVal_stable ho leaf f k' (by omega) _ _ (by omega) (by omega)) i

/-- **A reference has its shared expression's length.** -/
theorem exprLen_ref (ho : ir.RefsOrdered) {k : ℕ} (hk : k < ir.exprs.length) :
    ir.exprLen (.ref k) = ir.exprLen (ir.expr k) := by
  simp only [exprLen, Expr.len]
  rw [lenT_getD ho hk hk, ← lenT_getD ho (Nat.lt_succ_self k) hk]
  simp only [refLen]
  exact Expr.len_congr ir _ fun k' hk' => by
    have := ho k hk k' hk'
    rw [lenT_getD ho this (by omega), lenT_getD ho (by omega) (by omega)]

/-! ## One step of evaluation -/

/-- **A leaf's coordinate** is the value's coordinate, cast into the field. -/
theorem evalE_leaf (rd : ir.Valuation I) (f u i : ℕ) :
    ir.evalE rd f (.leaf u) i = castElt (rd u i) := rfl

/-- **A sum's coordinate** is the sum of the coordinates. -/
theorem evalE_add (rd : ir.Valuation I) (f : ℕ) (e e' : Expr) (i : ℕ) :
    ir.evalE rd f (.add e e') i = ir.evalE rd f e i + ir.evalE rd f e' i := rfl

/-- **A difference's coordinate** is the difference of the coordinates. -/
theorem evalE_sub (rd : ir.Valuation I) (f : ℕ) (e e' : Expr) (i : ℕ) :
    ir.evalE rd f (.sub e e') i = ir.evalE rd f e i - ir.evalE rd f e' i := rfl

/-- **A product's coordinate** is the product of the coordinates. -/
theorem evalE_mul (rd : ir.Valuation I) (f : ℕ) (e e' : Expr) (i : ℕ) :
    ir.evalE rd f (.mul e e') i = ir.evalE rd f e i * ir.evalE rd f e' i := rfl

/-- **A constant multiple's coordinate** is the decoded constant times the coordinate. -/
theorem evalE_scale_const (rd : ir.Valuation I) (f c : ℕ) (e : Expr) (i : ℕ) :
    ir.evalE rd f (.scale (.const c) e) i = (I f).decode c * ir.evalE rd f e i := rfl

/-- **A public multiple's coordinate** is the public coordinate, cast into the field, times the
coordinate. -/
theorem evalE_scale_node (rd : ir.Valuation I) (f v j : ℕ) (e : Expr) (i : ℕ) :
    ir.evalE rd f (.scale (.node v j) e) i = castElt (rd v j) * ir.evalE rd f e i := rfl

/-- **A view's coordinate `i`** is coordinate `idx[i]` of the expression. -/
theorem evalE_reindex (rd : ir.Valuation I) (f : ℕ) (idx : IndexMap) (e : Expr) (i : ℕ) :
    ir.evalE rd f (.reindex idx e) i = ir.evalE rd f e (idx.entry i) := rfl

/-- **A concatenation's coordinate**: the first expression's below its length, the second's
after. -/
theorem evalE_concat (rd : ir.Valuation I) (f : ℕ) (e e' : Expr) (i : ℕ) :
    ir.evalE rd f (.concat e e') i =
      if i < ir.exprLen e then ir.evalE rd f e i else ir.evalE rd f e' (i - ir.exprLen e) := rfl

/-- **A product along the last axis**: coordinate `i` is the product of coordinates
`i n, …, i n + n − 1`. -/
theorem evalE_prod (rd : ir.Valuation I) (f n : ℕ) (e : Expr) (i : ℕ) :
    ir.evalE rd f (.prod n e) i = ((List.range n).map fun t => ir.evalE rd f e (i * n + t)).prod :=
  rfl

/-- **A multiplexer's coordinate**: `b t + (1 − b) e`. -/
theorem evalE_mux (rd : ir.Valuation I) (f : ℕ) (b t e : Expr) (i : ℕ) :
    ir.evalE rd f (.mux b t e) i =
      ir.evalE rd f b i * ir.evalE rd f t i + (1 - ir.evalE rd f b i) * ir.evalE rd f e i := rfl

/-- **A named operator's coordinate** (`NamedOp.apply`). -/
theorem evalE_apply (rd : ir.Valuation I) (f : ℕ) (op : NamedOp) (e : Expr) (i : ℕ) :
    ir.evalE rd f (.apply op e) i = NamedOp.apply ir f rd op (ir.evalE rd f e) i := rfl

/-- **A sum of groups of `w`**: coordinate `i` is the sum of coordinates `i w, …, i w + w − 1`. -/
theorem evalE_apply_sum (rd : ir.Valuation I) (f w : ℕ) (e : Expr) (i : ℕ) :
    ir.evalE rd f (.apply (.sum w) e) i = ∑ t : Fin w, ir.evalE rd f e (i * w + t) := by
  simp [evalE_apply, NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols, Ops.sum, Nat.mod_one]

/-- **Numbers from `k` digits, batched `b` times** (`b > 0`): coordinate `i` is
`Σ_{l<k} base^l e[i k + l]`, as unbatched. -/
theorem evalE_apply_batched_fromDigits (rd : ir.Valuation I) (f : ℕ) {b : ℕ} (hb : 0 < b)
    (k base : ℕ) (e : Expr) (i : ℕ) :
    ir.evalE rd f (.apply (.batched b (.fromDigits k base)) e) i =
      ∑ l : Fin k, (I f).decode base ^ (l : ℕ) * ir.evalE rd f e (i * k + l) := by
  simp only [evalE_apply, NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols, Ops.fromDigits,
    Nat.mul_one, Nat.div_one, Nat.mod_one, ite_true]
  rw [if_pos (Nat.mod_lt _ hb)]
  refine Finset.sum_congr rfl fun l _ => ?_
  congr 2
  have := Nat.div_add_mod i b
  calc i / b * (b * k) + (i % b * k + l) = (b * (i / b) + i % b) * k + l := by ring
    _ = i * k + l := by rw [this]

/-- **A negacyclic convolution with `h` of size `n`**: coordinate `i` is coordinate `i mod n` of the
convolution of the polynomial operand with block `i / n`. -/
theorem evalE_apply_negacyclicConv (rd : ir.Valuation I) (f h : ℕ) (form : ConvForm) (e : Expr)
    (i : ℕ) :
    ir.evalE rd f (.apply (.negacyclicConv h form) e) i =
      Ops.negacyclic (ir.value h).size
        (NamedOp.formPoly f (ir.value h).size (fun s => castElt (rd h s)) form)
        (fun t => ir.evalE rd f e (i / (ir.value h).size * (ir.value h).size + t))
        (i % (ir.value h).size) := rfl

/-- **`a < b` on words of `w` bits** (`Logic::lt`): coordinate `i` compares the words
`i w, …, i w + w − 1` of the two arguments (`Ops.ltWord`). -/
theorem evalE_logic_lt (rd : ir.Valuation I) (f w : ℕ) (a b : Expr) (i : ℕ) :
    ir.evalE rd f (.logic .lt w [a, b]) i =
      Ops.ltWord w (fun t => ir.evalE rd f a (i * w + t)) (fun t => ir.evalE rd f b (i * w + t)) :=
  rfl

/-! ## Lengths -/

/-- A leaf has its value's size. -/
theorem exprLen_leaf (v : ℕ) : ir.exprLen (.leaf v) = (ir.value v).size := rfl

/-- A sum has its first operand's length. -/
theorem exprLen_add (e e' : Expr) : ir.exprLen (.add e e') = ir.exprLen e := rfl

/-- A difference has its first operand's length. -/
theorem exprLen_sub (e e' : Expr) : ir.exprLen (.sub e e') = ir.exprLen e := rfl

/-- A product has its first operand's length. -/
theorem exprLen_mul (e e' : Expr) : ir.exprLen (.mul e e') = ir.exprLen e := rfl

/-- A multiple has its operand's length. -/
theorem exprLen_scale (c : Coef) (e : Expr) : ir.exprLen (.scale c e) = ir.exprLen e := rfl

/-- A view has its index map's size. -/
theorem exprLen_reindex (idx : IndexMap) (e : Expr) : ir.exprLen (.reindex idx e) = idx.size := rfl

/-- A concatenation has the sum of the lengths. -/
theorem exprLen_concat (e e' : Expr) :
    ir.exprLen (.concat e e') = ir.exprLen e + ir.exprLen e' := rfl

/-- A product along an axis of length `n` has `1/n` of its operand's length. -/
theorem exprLen_prod (n : ℕ) (e : Expr) : ir.exprLen (.prod n e) = ir.exprLen e / n := rfl

/-- A multiplexer has its first branch's length. -/
theorem exprLen_mux (b t e : Expr) : ir.exprLen (.mux b t e) = ir.exprLen t := rfl

/-- **A named operator's length**: the operand's blocks of `cols` times `rows`. -/
theorem exprLen_apply (op : NamedOp) (e : Expr) :
    ir.exprLen (.apply op e) = ir.exprLen e / NamedOp.cols ir op * NamedOp.rows ir op := rfl

/-! ## One step of the integer reading -/

/-- **A leaf's integer reading** is the value's (`RealizedProgram.intOf`). -/
theorem evalIntWith_leaf (rd : ir.Valuation I) (d u i : ℕ) :
    ir.evalIntWith rd d (.leaf u) i = ir.intOf rd u i := rfl

/-- **A sum's integer reading** is the sum. -/
theorem evalIntWith_add (rd : ir.Valuation I) (d : ℕ) (e e' : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.add e e') i = ir.evalIntWith rd d e i + ir.evalIntWith rd d e' i := rfl

/-- **A difference's integer reading** is the difference. -/
theorem evalIntWith_sub (rd : ir.Valuation I) (d : ℕ) (e e' : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.sub e e') i = ir.evalIntWith rd d e i - ir.evalIntWith rd d e' i := rfl

/-- **A product's integer reading** is the product. -/
theorem evalIntWith_mul (rd : ir.Valuation I) (d : ℕ) (e e' : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.mul e e') i = ir.evalIntWith rd d e i * ir.evalIntWith rd d e' i := rfl

/-- **A constant multiple's integer reading**: the constant centred in `(−p/2, p/2)` times the
reading. -/
theorem evalIntWith_scale_const (rd : ir.Valuation I) (d c : ℕ) (e : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.scale (.const c) e) i =
      (I (ir.domainField d)).centered c * ir.evalIntWith rd d e i := rfl

/-- **A view's integer reading** at `i` is the expression's at `idx[i]`. -/
theorem evalIntWith_reindex (rd : ir.Valuation I) (d : ℕ) (idx : IndexMap) (e : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.reindex idx e) i = ir.evalIntWith rd d e (idx.entry i) := rfl

/-- **A concatenation's integer reading**. -/
theorem evalIntWith_concat (rd : ir.Valuation I) (d : ℕ) (e e' : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.concat e e') i =
      if i < ir.exprLen e then ir.evalIntWith rd d e i
      else ir.evalIntWith rd d e' (i - ir.exprLen e) := rfl

/-- **A product along the last axis, on the integers.** -/
theorem evalIntWith_prod (rd : ir.Valuation I) (d n : ℕ) (e : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.prod n e) i =
      ((List.range n).map fun t => ir.evalIntWith rd d e (i * n + t)).prod := rfl

/-- **A multiplexer, on the integers.** -/
theorem evalIntWith_mux (rd : ir.Valuation I) (d : ℕ) (b t e : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.mux b t e) i =
      ir.evalIntWith rd d b i * ir.evalIntWith rd d t i +
        (1 - ir.evalIntWith rd d b i) * ir.evalIntWith rd d e i := rfl

/-- **A named operator, on the integers** (`NamedOp.applyInt`: its matrix entries centred). -/
theorem evalIntWith_apply (rd : ir.Valuation I) (d : ℕ) (op : NamedOp) (e : Expr) (i : ℕ) :
    ir.evalIntWith rd d (.apply op e) i =
      NamedOp.applyInt ir (ir.domainField d) rd op (ir.evalIntWith rd d e) i := rfl

/-! ## Reading values -/

/-- **A bit view's coordinate is `0` or `1`**: the `0`/`1` of a coordinate of its word. -/
theorem bitView_bool (rd : ir.Valuation I) (v w : ℕ) (sel : IndexMap) (i : ℕ) :
    ir.bitView rd v w sel i = 0 ∨ ir.bitView rd v w sel i = 1 := by
  simp only [bitView, FieldInterp.ofBool]
  split <;> simp

/-- **A bit view reads its words from the committed assignment** when they are committed values:
coordinate `i` is the `0`/`1` of coordinate `i mod e` of word `sel[i / e]` in its subfield's basis,
`e` the bits per word. -/
theorem reader_of_bits_of_priv (e : ir.Env I) {v w : ℕ} {sel : IndexMap}
    (hk : (ir.value v).kind = .bits w sel) (hw : (ir.value w).kind = .priv) (i : ℕ) :
    ir.reader e v i = (I (ir.valueField v)).ofBool ((I (ir.valueField w)).coord
      ((ir.value w).type.nodeName.getD "") (e.asg.val w (sel.entry (i / ((ir.value v).size /
        sel.size)))) (i % ((ir.value v).size / sel.size))) := by
  have hn : ir.fuel = ir.values.length + 1 := rfl
  have hpos : 0 < ir.values.length := by
    by_contra h0
    have hnil : ir.values = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hv : ir.value v = default := by simp [RealizedProgram.value, hnil]
    rw [hv] at hk
    exact Kind.noConfusion hk
  obtain ⟨m, hm⟩ : ∃ m, ir.values.length = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hpos).symm⟩
  simp only [reader, hn, hm, read, hk, bitView, hw]

/-- **A bit view's reading is `0` or `1`.** -/
theorem reader_bool_of_bits (e : ir.Env I) {v w : ℕ} {sel : IndexMap}
    (hk : (ir.value v).kind = .bits w sel) (i : ℕ) :
    ir.reader e v i = 0 ∨ ir.reader e v i = 1 := by
  simp only [reader, fuel, read, hk]
  exact bitView_bool _ v w sel i

/-- **A cast keeps a bit a bit** (a cast across field identifiers is `0`). -/
theorem castElt_bool {a b : ℕ} {x : (I a).K} (h : x = 0 ∨ x = 1) :
    (castElt x : (I b).K) = 0 ∨ (castElt x : (I b).K) = 1 := by
  unfold castElt
  split
  · rename_i hab
    subst hab
    exact h
  · exact .inl rfl

/-- **Whether value `v` is a bit view** (`Kind.bits`). -/
def isBitView (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .bits _ _ => true
  | _ => false

/-- **A bit view reads `0` or `1`**, cast into any field. -/
theorem evalE_leaf_bool_of_isBitView (e : ir.Env I) {v : ℕ} (h : ir.isBitView v = true)
    (f i : ℕ) :
    ir.evalE (ir.reader e) f (.leaf v) i = 0 ∨ ir.evalE (ir.reader e) f (.leaf v) i = 1 := by
  unfold isBitView at h
  split at h
  · rename_i w sel hk
    exact castElt_bool (reader_bool_of_bits e hk i)
  · cases h

/-- **The challenge of a challenge value's kind**: `some c` for `.challenge c`, `none` for any
other kind. `Kind` has no decidable equality (it holds expressions), so a call site decides this
instead of the kind. -/
def _root_.GordieHowe.RealizedProgram.Kind.challenge? : Kind → Option ℕ
  | .challenge c => some c
  | _ => none

/-- A kind whose challenge is `c` is `.challenge c`. -/
theorem _root_.GordieHowe.RealizedProgram.Kind.eq_of_challenge? {k : Kind} {c : ℕ}
    (h : k.challenge? = some c) : k = .challenge c := by
  cases k <;> simp_all [Kind.challenge?]

/-- **A challenge value reads its challenge.** -/
theorem reader_of_challenge (e : ir.Env I) {v c : ℕ} (hk : (ir.value v).kind = .challenge c)
    (i : ℕ) : ir.reader e v i = castElt (e.chal c i) := by
  simp only [reader, fuel, read, hk]

/-- **A challenge value of its challenge's field, read in any field,** is the challenge read
there. -/
theorem castElt_reader_of_challenge (e : ir.Env I) {v c f : ℕ}
    (hk : (ir.value v).kind = .challenge c) (hf : ir.chalField c = ir.valueField v) (i : ℕ) :
    (castElt (ir.reader e v i) : (I f).K) = castElt (e.chal c i) := by
  rw [reader_of_challenge e hk, castElt_castElt_eq, if_pos hf]

/-- **A value that reads nothing from the run** (`RealizedProgram.nodeReads` empty) reads alike in two
environments of one statement and one committed assignment. -/
theorem reader_eq_of_nodeReads_nil {v : ℕ} (hv : ir.nodeReads ir.fuel v = []) {e e' : ir.Env I}
    (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) : ir.reader e v = ir.reader e' v :=
  read_congr _ v
    ⟨hs, ha, fun _ h => (by rw [hv] at h; cases h), fun _ h => (by rw [hv] at h; cases h)⟩

/-- **The entries of a constant value** (none for a value of another kind). -/
def constEntries (v : ℕ) : List ℕ :=
  match (ir.value v).kind with
  | .constant es => es
  | _ => []

/-- **Whether value `v` is a constant.** -/
def isConstant (v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .constant _ => true
  | _ => false

/-- A constant's kind lists its entries. -/
theorem kind_of_isConstant {v : ℕ} (h : ir.isConstant v = true) :
    (ir.value v).kind = .constant (ir.constEntries v) := by
  unfold isConstant at h
  unfold constEntries
  split at h
  · rename_i es hes
    rw [hes]
  · cases h

variable (I) in
/-- **Coordinate `i` of the constant `v`, read in field `f`**: its entry decoded in its field, cast
into `f`. -/
def constRead (f v i : ℕ) : (I f).K :=
  castElt ((I (ir.valueField v)).decode ((ir.constEntries v).getD i 0))

/-- **The integer reading of an element read in an equal field identifier** is its integer
reading. -/
theorem toNat_castElt {a b : ℕ} (h : a = b) (x : (I a).K) :
    (I b).toNat (castElt x : (I b).K) = (I a).toNat x := by
  subst h
  rw [castElt_self]

/-- **A decoded constant read in an equal field identifier** is the constant decoded there. -/
theorem castElt_decode {a b : ℕ} (h : a = b) (c : ℕ) :
    (castElt ((I a).decode c) : (I b).K) = (I b).decode c := by
  subst h
  exact castElt_self _

/-- **A constant read in its own field** is its decoded entry. -/
theorem constRead_of_valueField {f v : ℕ} (h : ir.valueField v = f) (i : ℕ) :
    ir.constRead I f v i = (I f).decode ((ir.constEntries v).getD i 0) :=
  castElt_decode h _

/-- **A constant leaf reads the constant** (`constRead`) in every environment. -/
theorem evalE_leaf_of_isConstant (e : ir.Env I) {v : ℕ} (h : ir.isConstant v = true) (f i : ℕ) :
    ir.evalE (ir.reader e) f (.leaf v) i = ir.constRead I f v i := by
  rw [evalE_leaf, reader_of_constant e (kind_of_isConstant h)]
  rfl

/-! ## Predicates by name -/

/-- **The predicate named `name`**: the identifier of the first predicate of that name. -/
def predByName (name : String) : Option ℕ := ir.predicates.findIdx? (·.name == name)

/-- **The predicate found by name** is a predicate of the program of that name. -/
theorem predByName_spec {name : String} {p : ℕ} (h : ir.predByName name = some p) :
    p < ir.predicates.length ∧ (ir.predicate p).name = name := by
  unfold predByName at h
  obtain ⟨hp, hname, -⟩ := List.findIdx?_eq_some_iff_getElem.1 h
  refine ⟨hp, ?_⟩
  rw [predicate, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hp, Option.getD_some]
  simpa using hname

/-- **A source predicate found by name holds** where the source program is satisfied. -/
theorem SourceSatAt.holdsAt_of_predByName {e : ir.Env I} (h : ir.SourceSatAt e) {name : String}
    {p : ℕ} (hp : ir.predByName name = some p) (hs : ir.inSource (ir.predicate p) = true) :
    ir.HoldsAt e (ir.predicate p).body :=
  h.preds _ (predicate_mem (predByName_spec hp).1) hs

/-! ## A challenge drawn from the field -/

/-- **Coordinate `0` of a set challenge.** -/
theorem setChal_chal_zero {j : ℕ} (e : ir.Env I) (c : ir.ChalVal I j)
    (h0 : 0 < (ir.challenge j).size) :
    (e.setChal j c).chal j 0 = (I (ir.chalField j)).samplerVal _ (c ⟨0, h0⟩) := by
  simp only [Env.setChal, Function.update_self]
  exact dite_eq_left_of_eq_true (eq_true h0)

/-- **An event at a challenge of one coordinate drawn from the field** (`size = 1`, sampler
`full`), read in an equal field identifier `f`: the challenge is a root with probability at most
the event's degree over `|K|` (Schwartz–Zippel, `ChallengeEvent.probUniform_badAt_le`). -/
theorem probUniform_badAt_setChal_le {j f : ℕ} (hsz : (ir.challenge j).size = 1)
    (hsm : (ir.challenge j).sampler = .full) (hf : ir.chalField j = f)
    (ev : ChallengeEvent (I f).K) (e : ir.Env I) :
    Pr[c ← ir.ChalVal I j : ev.BadAt (castElt ((e.setChal j c).chal j 0))] ≤
      ((ev.deg / Fintype.card (I f).K : ℝ≥0) : ℝ≥0∞) := by
  have h0 : 0 < (ir.challenge j).size := by rw [hsz]; omega
  simp only [setChal_chal_zero e _ h0]
  have key : ∀ (F : FieldInterp) (n : ℕ) (hn : n = 1) (h0 : 0 < n) (s : Sampler) (hs : s = .full)
      (P : F.K → Prop), Pr[c ← (Fin n → F.SamplerTy s) : P (F.samplerVal s (c ⟨0, h0⟩))] =
        Pr[a ← F.K : P a] := by
    intro F n hn h0 s hs P
    subst hn hs
    exact Uniform.probUniform_comp (f := fun c : Fin 1 → F.K => c ⟨0, h0⟩)
      (Uniform.of_equiv (Equiv.funUnique (Fin 1) F.K)) P
  rw [key _ _ hsz h0 _ hsm (fun a => ev.BadAt (castElt a))]
  subst hf
  simp only [castElt_self]
  exact ChallengeEvent.probUniform_badAt_le ev

end

/-! ## Named operators are linear -/

namespace NamedOp

variable (ir : RealizedProgram) {I : Interp} {f : ℕ} (leaf : ir.Valuation I)

/-- **A named operator vanishes at zero.** -/
theorem block_zero : ∀ (op : NamedOp) (r : ℕ), block ir f leaf op (fun _ => 0) r = 0
  | .negacyclicConv h form, r => by simp [block, Ops.negacyclic_eq]
  | .polyMatVec a K L form, r => by simp [block, Ops.negacyclic_eq]
  | .polyBroadcast t K form, r => by simp [block, Ops.negacyclic_eq]
  | .ntt n psi .scheme, r => by simp [block, Ops.nttScheme, Ops.nttNatural_eq]
  | .ntt n psi .natural, r => by simp [block, Ops.nttNatural_eq]
  | .inverseNtt n psi, r => by simp [block, Ops.inverseNtt]
  | .nttTranspose n psi, r => by simp [block, Ops.nttTranspose]
  | .rowDot M R W, r => by simp [block, Ops.rowDot]
  | .macConv r' w nch taps, r => by simp [block, Ops.macConv]
  | .acyclicConv h lx, r => by simp [block, Ops.acyclic]
  | .diagonal d, r => by simp [block, Ops.diagonal]
  | .scale c, r => by simp [block]
  | .constDiagonal d, r => by simp [block, Ops.diagonal]
  | .sum w, r => by simp [block, Ops.sum]
  | .fromDigits k base, r => by simp [block, Ops.fromDigits]
  | .batched b op, r => by
    simp only [block]
    split_ifs
    · exact block_zero op _
    · rfl

/-- **A named operator vanishes past its output width.** -/
theorem block_of_rows_le : ∀ (op : NamedOp) (x : ℕ → (I f).K) {r : ℕ}, rows ir op ≤ r →
    block ir f leaf op x r = 0
  | .negacyclicConv h form, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.negacyclic_eq, Nat.not_lt.2 hr]
  | .polyMatVec a K L form, x, r, hr => by
    simp only [rows] at hr
    simp [block, Nat.not_lt.2 hr]
  | .polyBroadcast t K form, x, r, hr => by
    simp only [rows] at hr
    simp only [block]
    rw [if_neg]
    intro h
    have := Nat.mul_div_le (ir.value t).size K
    omega
  | .ntt n psi .scheme, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.nttScheme, Nat.not_lt.2 hr]
  | .ntt n psi .natural, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.nttNatural_eq, Nat.not_lt.2 hr]
  | .inverseNtt n psi, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.inverseNtt, Nat.not_lt.2 hr]
  | .nttTranspose n psi, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.nttTranspose, Nat.not_lt.2 hr]
  | .rowDot M R W, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.rowDot, Nat.not_lt.2 hr]
  | .macConv r' w nch taps, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.macConv, Nat.not_lt.2 hr]
  | .acyclicConv h lx, x, r, hr => by
    simp only [rows] at hr
    simp only [block, Ops.acyclic]
    rw [if_neg (by omega)]
  | .diagonal d, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.diagonal, Nat.not_lt.2 hr]
  | .scale c, x, r, hr => by
    simp only [rows] at hr
    simp [block, show r ≠ 0 by omega]
  | .constDiagonal d, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.diagonal, Nat.not_lt.2 hr]
  | .sum w, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.sum, show r ≠ 0 by omega]
  | .fromDigits k base, x, r, hr => by
    simp only [rows] at hr
    simp [block, Ops.fromDigits, show r ≠ 0 by omega]
  | .batched b op, x, r, hr => by
    simp only [rows] at hr
    simp [block, Nat.not_lt.2 hr]

/-- The negacyclic convolution reads only the first `n` coordinates of its operand. -/
theorem negacyclic_congr {K : Type*} [Field K] {n : ℕ} {h x y : ℕ → K} (hxy : ∀ t < n, x t = y t)
    (j : ℕ) : Ops.negacyclic n h x j = Ops.negacyclic n h y j := by
  have : Ops.toFin n x = Ops.toFin n y := funext fun t => hxy t t.isLt
  simp only [Ops.negacyclic, this]

/-- The natural-order transform reads only the first `n` coordinates of its operand. -/
theorem nttNatural_congr {K : Type*} [Field K] {n : ℕ} {ψ : K} {x y : ℕ → K}
    (hxy : ∀ t < n, x t = y t) (j : ℕ) : Ops.nttNatural n ψ x j = Ops.nttNatural n ψ y j := by
  have : Ops.toFin n x = Ops.toFin n y := funext fun t => hxy t t.isLt
  simp only [Ops.nttNatural, this]

/-- **A named operator reads only the first `cols` coordinates of its operand** at an output
coordinate below `rows`. -/
theorem block_congr_cols : ∀ (op : NamedOp) {x y : ℕ → (I f).K} {r : ℕ}, r < rows ir op →
    (∀ t < cols ir op, x t = y t) → block ir f leaf op x r = block ir f leaf op y r
  | .negacyclicConv h form, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block]
    exact negacyclic_congr hxy _
  | .polyMatVec a K L form, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block]
    split_ifs
    · refine Finset.sum_congr rfl fun l _ => negacyclic_congr (fun s hs => hxy _ ?_) _
      have := l.isLt
      nlinarith
    · rfl
  | .polyBroadcast t K form, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block]
    split_ifs
    · exact negacyclic_congr hxy _
    · rfl
  | .ntt n psi .scheme, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block, Ops.nttScheme]
    split_ifs
    · exact nttNatural_congr hxy _
    · rfl
  | .ntt n psi .natural, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block]
    exact nttNatural_congr hxy _
  | .inverseNtt n psi, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block, Ops.inverseNtt]
    split_ifs
    · rw [Finset.sum_congr rfl fun m _ => by rw [hxy m m.isLt]]
    · rfl
  | .nttTranspose n psi, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block, Ops.nttTranspose]
    split_ifs
    · rw [Finset.sum_congr rfl fun m _ => by rw [hxy m m.isLt]]
    · rfl
  | .rowDot M R W, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block, Ops.rowDot]
    split_ifs
    · rw [Finset.sum_congr rfl fun c _ => by rw [hxy c c.isLt]]
    · rfl
  | .macConv r' w nch taps, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block, Ops.macConv]
    split_ifs
    · refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hxy _ (by have := c.isLt; have := i.isLt; nlinarith)]
    · rfl
  | .acyclicConv h lx, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block, Ops.acyclic]
    split_ifs
    · rw [Finset.sum_congr rfl fun a _ => by rw [hxy a a.isLt]]
    · rfl
  | .diagonal d, x, y, r, hr, hxy => by
    simp only [cols, rows] at hxy hr
    simp only [block, Ops.diagonal, if_pos hr]
    rw [hxy r hr]
  | .scale c, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block]
    split_ifs
    · rw [hxy 0 (by omega)]
    · rfl
  | .constDiagonal d, x, y, r, hr, hxy => by
    simp only [cols, rows] at hxy hr
    simp only [block, Ops.diagonal, if_pos hr]
    rw [hxy r hr]
  | .sum w, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block, Ops.sum]
    split_ifs
    · rw [Finset.sum_congr rfl fun t _ => by rw [hxy t t.isLt]]
    · rfl
  | .fromDigits k base, x, y, r, _, hxy => by
    simp only [cols] at hxy
    simp only [block, Ops.fromDigits]
    split_ifs
    · rw [Finset.sum_congr rfl fun l _ => by rw [hxy l l.isLt]]
    · rfl
  | .batched b op, x, y, r, hr, hxy => by
    simp only [cols, rows] at hxy hr
    simp only [block]
    rw [if_pos hr, if_pos hr]
    have hpos : 0 < rows ir op := by
      rcases Nat.eq_zero_or_pos (rows ir op) with h0 | h0
      · rw [h0, Nat.mul_zero] at hr
        omega
      · exact h0
    refine block_congr_cols op (Nat.mod_lt _ hpos) fun t ht => hxy _ ?_
    have hq : r / rows ir op < b := (Nat.div_lt_iff_lt_mul hpos).2 hr
    calc r / rows ir op * cols ir op + t < r / rows ir op * cols ir op + cols ir op := by omega
      _ = (r / rows ir op + 1) * cols ir op := by ring
      _ ≤ b * cols ir op := Nat.mul_le_mul_right _ hq

/-- **A named operator is linear in its operand's first `cols` coordinates**: its output
coordinate `r` is `Σ_{t < cols} M_{r t} x_t`, `M_{r t}` its value on the unit vector `t`. -/
theorem block_eq_sum_unit (op : NamedOp) (x : ℕ → (I f).K) (r : ℕ) :
    block ir f leaf op x r =
      ∑ t : Fin (cols ir op), block ir f leaf op (fun s => if s = t then 1 else 0) r * x t := by
  by_cases hr : r < rows ir op
  · set g : (Fin (cols ir op) → (I f).K) → (I f).K := fun z => block ir f leaf op (Ops.ofFin z) r
    have hcoord : ∀ t, IsAff fun z : Fin (cols ir op) → (I f).K => Ops.ofFin z t := fun t => by
      unfold Ops.ofFin
      exact IsAff.dite _ (fun h => isAff_proj (⟨t, h⟩ : Fin (cols ir op))) fun _ => isAff_zero
    have hg : IsAff g := RealizedProgram.NamedOp.block_isAff leaf op hcoord r
    have h1 : block ir f leaf op x r = g (Ops.toFin _ x) :=
      block_congr_cols ir leaf op hr fun t ht => by simp [Ops.ofFin, ht]
    have h0 : g 0 = 0 := by
      have : Ops.ofFin (0 : Fin (cols ir op) → (I f).K) = fun _ => 0 := funext fun t => by
        simp [Ops.ofFin]
      simp only [g, this]
      exact block_zero ir leaf op r
    have hu : ∀ t : Fin (cols ir op), g (fun j => if t = j then 1 else 0) =
        block ir f leaf op (fun s => if s = t then 1 else 0) r := fun t =>
      block_congr_cols ir leaf op hr fun s hs => by
        simp only [Ops.ofFin, hs, dite_true]
        by_cases hst : s = t
        · simp [hst]
        · rw [if_neg (fun h => hst (by rw [h])), if_neg hst]
    rw [h1, hg.eq_gradient, h0, zero_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hu t, sub_zero, mul_comm]
    rfl
  · rw [block_of_rows_le ir leaf op x (Nat.le_of_not_lt hr)]
    refine (Finset.sum_eq_zero fun t _ => ?_).symm
    rw [block_of_rows_le ir leaf op _ (Nat.le_of_not_lt hr), zero_mul]

/-! ## Batched sums on the integers -/

/-- **A sum over `Fin n` of an indicator of `[a, a + w)`** is the sum over the window. -/
theorem sum_fin_indicator {n a w : ℕ} (h : a + w ≤ n) (x : ℕ → ℤ) :
    ∑ t : Fin n, (if a ≤ (t : ℕ) ∧ (t : ℕ) < a + w then x t else 0) = ∑ s : Fin w, x (a + s) := by
  rw [Fin.sum_univ_eq_sum_range (fun t => if a ≤ t ∧ t < a + w then x t else 0),
    Fin.sum_univ_eq_sum_range (fun s => x (a + s)), ← Finset.sum_filter]
  have : (Finset.range n).filter (fun t => a ≤ t ∧ t < a + w) = Finset.Ico a (a + w) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    omega
  rw [this, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]

/-- **A sum of groups of `w`, batched `b` times, on the integers**: coordinate `j < b` is the sum of
coordinates `j w, …, j w + w − 1`, where the field reads `0` and `1` as themselves. -/
theorem applyInt_batched_sum {f : ℕ} (hc0 : (I f).coefInt 0 = 0) (hc1 : (I f).coefInt 1 = 1)
    {ir' : RealizedProgram} (leaf : ∀ v : ℕ, ℕ → (I (ir'.valueField v)).K) {b w : ℕ} (x : ℕ → ℤ) {j : ℕ}
    (hj : j < b) :
    applyInt ir' f leaf (.batched b (.sum w)) x j = ∑ s : Fin w, x (j * w + s) := by
  unfold applyInt
  simp only [rows, cols, Nat.mul_one, Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj, Nat.zero_mul,
    Nat.zero_add]
  have hentry : ∀ t : Fin (b * w), (I f).coefInt (block ir' f leaf (.batched b (.sum w))
      (fun s => if s = (t : ℕ) then 1 else 0) j) * x t =
      if j * w ≤ (t : ℕ) ∧ (t : ℕ) < j * w + w then x t else 0 := by
    intro t
    simp only [block, rows, cols, Nat.mul_one, if_pos hj, Nat.div_one, Nat.mod_one, Ops.sum,
      ite_true]
    by_cases ht : j * w ≤ (t : ℕ) ∧ (t : ℕ) < j * w + w
    · rw [if_pos ht]
      have : (∑ t' : Fin w, (if j * w + (t' : ℕ) = (t : ℕ) then (1 : (I f).K) else 0)) = 1 := by
        rw [Finset.sum_eq_single ⟨(t : ℕ) - j * w, by omega⟩]
        · rw [if_pos (by simp only; omega)]
        · intro t' _ hne
          rw [if_neg]
          intro h
          exact hne (Fin.ext (by simp only; omega))
        · intro h
          exact absurd (Finset.mem_univ _) h
      rw [this, hc1, one_mul]
    · rw [if_neg ht]
      have : (∑ t' : Fin w, (if j * w + (t' : ℕ) = (t : ℕ) then (1 : (I f).K) else 0)) = 0 := by
        refine Finset.sum_eq_zero fun t' _ => ?_
        rw [if_neg]
        intro h
        have := t'.isLt
        exact ht ⟨by omega, by omega⟩
      rw [this, hc0, zero_mul]
  rw [Finset.sum_congr rfl fun t _ => hentry t]
  exact sum_fin_indicator (by nlinarith) x

end NamedOp

end GordieHowe.RealizedProgram

/-! ## Bits read in two fields -/

namespace GordieHowe.Bits

/-- **Bits that are `1` at the same places denote the same natural**, in any two fields. -/
theorem natOfBits_eq_of_one_iff {K L : Type*} [Field K] [DecidableEq K] [Field L] [DecidableEq L]
    {m : ℕ} {a : BitWires K m} {b : BitWires L m} (h : ∀ i, a i = 1 ↔ b i = 1) :
    natOfBits a = natOfBits b := by
  unfold natOfBits
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases ha : a i = 1
  · rw [if_pos ha, if_pos ((h i).1 ha)]
  · rw [if_neg ha, if_neg (mt (h i).2 ha)]

end GordieHowe.Bits
