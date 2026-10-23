-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Library.Eval
public import GordieHowe.Applications.Keccak.Gadgets.Trace

@[expose] public section

/-!
# GordieHowe frontend: a program's Keccak rounds

A program's Keccak-f trace (`lib::keccak::keccak_batch`, the C++ batch the generated programs
export) holds each round's state as `1600` bits, bit `(x, y, z)` at position
`320 y + 64 x + z` (`keccakIdx`: lane `x + 5 y`, bit `z`, the lanes in FIPS 202's byte order), and
each round as one predicate

`S' + (B + (1 − B[x+1]) · B[x+2] + ι) = 0`,

`B` a shared expression computing `π (ρ (θ S))` by index maps from the column sums of `S` (another
shared expression). Read through the index maps' entries (`KeccakMaps`, decided per program), the
predicate is the round relation of the Keccak library (`KeccakTrace.RoundRelation`,
`roundRelation_of_holdsWith`), so on Boolean states it is `Keccak.round`
(`KeccakTrace.roundRelation_iff`).
-/

namespace GordieHowe.RealizedProgram

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.KeccakTrace

/-- **The position of state bit `(x, y, z)`** in a program's `1600`-bit state: lane `x + 5 y`, bit
`z`. -/
def keccakIdx (x y : Fin 5) (z : Fin 64) : ℕ := 320 * y + 64 * x + z

theorem keccakIdx_lt (x y : Fin 5) (z : Fin 64) : keccakIdx x y z < 1600 := by
  unfold keccakIdx
  have := x.isLt
  have := y.isLt
  have := z.isLt
  omega

/-- **A state read off a program's `1600` coordinates** (`keccakIdx`). -/
def stateOf {K : Type*} (g : ℕ → K) : State K := fun x y z => g (keccakIdx x y z)

/-- **Bit `j` of a state** in a program's `1600`-bit order (the inverse of `keccakIdx`); `0` past
`1600`. -/
def stateBit {K : Type*} [Zero K] (S : State K) (j : ℕ) : K :=
  if h : j < 1600 then S ⟨j % 320 / 64, by omega⟩ ⟨j / 320, by omega⟩ ⟨j % 64, by omega⟩ else 0

theorem stateBit_keccakIdx {K : Type*} [Zero K] (S : State K) (x y : Fin 5) (z : Fin 64) :
    stateBit S (keccakIdx x y z) = S x y z := by
  have hj := keccakIdx_lt x y z
  unfold stateBit keccakIdx at *
  rw [dif_pos hj]
  congr 1 <;> ext <;> simp only <;> omega

/-- **A state read off its bits is the state.** -/
theorem stateOf_stateBit {K : Type*} [Zero K] (S : State K) : stateOf (stateBit S) = S := by
  funext x y z
  exact stateBit_keccakIdx S x y z

/-- **The bits of a Boolean state are bits.** -/
theorem stateBit_bool {K : Type*} [Field K] {S : State K} (hS : ∀ x y, Bits.AllBool (S x y))
    (j : ℕ) : stateBit S j = 0 ∨ stateBit S j = 1 := by
  unfold stateBit
  split
  · exact hS _ _ _
  · exact Or.inl rfl

/-- **The words of a state** in the packing basis `P`: word `w` packs bits `16 w … 16 w + 15`
(`stateBit`), the program's committed state words. -/
def stateWords {K : Type*} [Field K] [DecidableEq K] (P : PackedClaim.PackedBasis K 4) (S : State K) (w : ℕ) : K :=
  PackedClaim.pack P fun b => decide (stateBit S (16 * w + b) = 1)

/-- **The index maps of a round's linear part**: `i13` is `π ∘ ρ` on positions, `i9 ∘ i10` and
`i11 ∘ i12 ∘ i10` read the column parities of columns `x + 4` at bit `z` and `x + 1` at bit `z − 1`
(`θ`), `i8` lists the five lanes of a column, `i14` and `i15` shift `x` by one and two (`χ`). -/
def KeccakMaps (i8 i9 i10 i11 i12 i13 i14 i15 : IndexMap) : Prop :=
  (∀ x y : Fin 5, ∀ z : Fin 64, i13.entry (keccakIdx x y z) =
      keccakIdx (x + 3 * y) x (z - Fin.ofNat 64 (rhoOffset (x + 3 * y) x))) ∧
    (∀ x y : Fin 5, ∀ z : Fin 64,
      i9.entry (i10.entry (keccakIdx x y z)) = 64 * ((x + 4 : Fin 5) : ℕ) + z) ∧
    (∀ x y : Fin 5, ∀ z : Fin 64, i11.entry (i12.entry (i10.entry (keccakIdx x y z))) =
      64 * ((x + 1 : Fin 5) : ℕ) + ((z - 1 : Fin 64) : ℕ)) ∧
    (∀ x : Fin 5, ∀ z : Fin 64, ∀ t : Fin 5, i8.entry ((64 * x + z) * 5 + t) = keccakIdx x t z) ∧
    (∀ x y : Fin 5, ∀ z : Fin 64, i14.entry (keccakIdx x y z) = keccakIdx (x + 1) y z) ∧
    (∀ x y : Fin 5, ∀ z : Fin 64, i15.entry (keccakIdx x y z) = keccakIdx (x + 2) y z)

instance (i8 i9 i10 i11 i12 i13 i14 i15 : IndexMap) :
    Decidable (KeccakMaps i8 i9 i10 i11 i12 i13 i14 i15) := by
  unfold KeccakMaps
  infer_instance

section

variable {ir : RealizedProgram} {I : Interp}

/-- **The column parity** of a state expression `S` read through `i8`: coordinate `64 x + z` is
`Σ_y S(x, y, z)`. -/
theorem evalE_colSum (rd : ir.Valuation I) (f : ℕ) {S : Expr} {i8 : IndexMap}
    (h8 : ∀ x : Fin 5, ∀ z : Fin 64, ∀ t : Fin 5, i8.entry ((64 * x + z) * 5 + t) = keccakIdx x t z)
    (x : Fin 5) (z : Fin 64) :
    ir.evalE rd f (.apply (.sum 5) (.reindex i8 S)) (64 * x + z) =
      ∑ y : Fin 5, stateOf (ir.evalE rd f S) x y z := by
  rw [evalE_apply_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [evalE_reindex, h8 x z t]
  rfl

/-- **A round's linear part** `B = π (ρ (θ S))`, read through its index maps (`KeccakMaps`), is the
Keccak library's `linB` at the state of `S`. -/
theorem evalE_linB (ho : ir.RefsOrdered) (rd : ir.Valuation I) (f : ℕ) {L C : ℕ} {S : Expr}
    {i8 i9 i10 i11 i12 i13 i14 i15 : IndexMap} (hL : L < ir.exprs.length)
    (hC : C < ir.exprs.length)
    (heL : ir.expr L = .reindex i13 (.add (.add S (.reindex i10 (.reindex i9 (.ref C))))
      (.reindex i10 (.reindex i12 (.reindex i11 (.ref C))))))
    (heC : ir.expr C = .apply (.sum 5) (.reindex i8 S))
    (hm : KeccakMaps i8 i9 i10 i11 i12 i13 i14 i15) (x y : Fin 5) (z : Fin 64) :
    ir.evalE rd f (.ref L) (keccakIdx x y z) =
      linB (flat (stateOf (ir.evalE rd f S))) (x, y, z) := by
  obtain ⟨hpi, hA, hB, h8, -, -⟩ := hm
  rw [evalE_ref ho _ _ hL, heL, evalE_reindex, hpi, evalE_add, evalE_add, evalE_reindex,
    evalE_reindex, evalE_reindex, evalE_reindex, evalE_reindex, hA, hB, evalE_ref ho _ _ hC, heC,
    evalE_colSum rd f h8, evalE_colSum rd f h8, linB_apply]
  rfl

/-- **A round predicate is the round relation** (`KeccakTrace.RoundRelation`): in characteristic
two, `S' + (B + (1 − B[x+1]) · B[x+2] + ι) = 0` with `B` the round's linear part
(`evalE_linB`), `1` and `0` constant states and `ι` the round constant's bits is `a b + c = 0`
with `a = 1 + B[x+1]`, `b = B[x+2]`, `c = S' + B + ι`. -/
theorem roundRelation_of_holdsWith (ho : ir.RefsOrdered) {rd : ir.Valuation I}
    {d out L C rc ones zeros : ℕ}
    {S : Expr} {tg : Target} {i8 i9 i10 i11 i12 i13 i14 i15 : IndexMap} {r : Fin 24}
    [CharP (I (ir.domainField d)).K 2]
    (hL : L < ir.exprs.length) (hC : C < ir.exprs.length)
    (heL : ir.expr L = .reindex i13 (.add (.add S (.reindex i10 (.reindex i9 (.ref C))))
      (.reindex i10 (.reindex i12 (.reindex i11 (.ref C))))))
    (heC : ir.expr C = .apply (.sum 5) (.reindex i8 S))
    (hm : KeccakMaps i8 i9 i10 i11 i12 i13 i14 i15) (hsize : 1600 ≤ (ir.value out).size)
    (hones : ∀ j < 1600, ir.evalE rd (ir.domainField d) (.leaf ones) j = 1)
    (hzeros : ∀ j < 1600, ir.evalE rd (ir.domainField d) (.leaf zeros) j = 0)
    (hrc : ∀ x y z, ir.evalE rd (ir.domainField d) (.leaf rc) (keccakIdx x y z) =
      iotaVec r (x, y, z))
    (h : ir.HoldsWith rd (.equal d (.add (.leaf out) (.add (.add (.ref L)
      (.mul (.sub (.leaf ones) (.reindex i14 (.ref L))) (.reindex i15 (.ref L)))) (.leaf rc)))
      (.leaf zeros) tg)) :
    RoundRelation r (stateOf (ir.evalE rd (ir.domainField d) S))
      (stateOf (ir.evalE rd (ir.domainField d) (.leaf out))) := by
  rintro ⟨x, y, z⟩
  have hj := h (keccakIdx x y z) (by
    rw [exprLen_add, exprLen_leaf]
    exact lt_of_lt_of_le (keccakIdx_lt x y z) hsize)
  change ir.evalE rd (ir.domainField d) _ _ = ir.evalE rd (ir.domainField d) _ _ at hj
  have hlin := evalE_linB ho rd (ir.domainField d) hL hC heL heC hm
  rw [hzeros _ (keccakIdx_lt x y z), evalE_add, evalE_add, evalE_add, evalE_mul, evalE_sub,
    evalE_reindex, evalE_reindex, hones _ (keccakIdx_lt x y z), hm.2.2.2.2.1, hm.2.2.2.2.2,
    hlin, hlin, hlin, hrc] at hj
  simp only [opA, opB, opC, shiftMat_mulVec, Pi.add_apply]
  rw [CharTwo.sub_eq_add] at hj
  change (1 + linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x + 1, y, z)) *
      linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x + 2, y, z) +
    (stateOf (ir.evalE rd (ir.domainField d) (.leaf out)) x y z +
      linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x, y, z) + iotaVec r (x, y, z)) = 0
  change stateOf (ir.evalE rd (ir.domainField d) (.leaf out)) x y z +
    (linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x, y, z) +
      (1 + linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x + 1, y, z)) *
        linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x + 2, y, z) +
      iotaVec r (x, y, z)) = 0 at hj
  linear_combination hj

/-- **Every position below `1600` is a state bit's** (`keccakIdx`). -/
theorem exists_keccakIdx {i : ℕ} (hi : i < 1600) : ∃ x y z, keccakIdx x y z = i :=
  ⟨⟨i % 320 / 64, by omega⟩, ⟨i / 320, by omega⟩, ⟨i % 64, by omega⟩, by
    unfold keccakIdx
    simp only
    omega⟩

/-- **The round relation gives a round predicate** (the converse of `roundRelation_of_holdsWith`):
where the states read by `S` and the output `out` (of `1600` coordinates) are in the round
relation, the predicate holds. -/
theorem holdsWith_of_roundRelation (ho : ir.RefsOrdered) {rd : ir.Valuation I}
    {d out L C rc ones zeros : ℕ}
    {S : Expr} {tg : Target} {i8 i9 i10 i11 i12 i13 i14 i15 : IndexMap} {r : Fin 24}
    [CharP (I (ir.domainField d)).K 2]
    (hL : L < ir.exprs.length) (hC : C < ir.exprs.length)
    (heL : ir.expr L = .reindex i13 (.add (.add S (.reindex i10 (.reindex i9 (.ref C))))
      (.reindex i10 (.reindex i12 (.reindex i11 (.ref C))))))
    (heC : ir.expr C = .apply (.sum 5) (.reindex i8 S))
    (hm : KeccakMaps i8 i9 i10 i11 i12 i13 i14 i15) (hsize : (ir.value out).size ≤ 1600)
    (hones : ∀ j < 1600, ir.evalE rd (ir.domainField d) (.leaf ones) j = 1)
    (hzeros : ∀ j < 1600, ir.evalE rd (ir.domainField d) (.leaf zeros) j = 0)
    (hrc : ∀ x y z, ir.evalE rd (ir.domainField d) (.leaf rc) (keccakIdx x y z) =
      iotaVec r (x, y, z))
    (h : RoundRelation r (stateOf (ir.evalE rd (ir.domainField d) S))
      (stateOf (ir.evalE rd (ir.domainField d) (.leaf out)))) :
    ir.HoldsWith rd (.equal d (.add (.leaf out) (.add (.add (.ref L)
      (.mul (.sub (.leaf ones) (.reindex i14 (.ref L))) (.reindex i15 (.ref L)))) (.leaf rc)))
      (.leaf zeros) tg) := by
  intro i hi
  rw [exprLen_add, exprLen_leaf] at hi
  obtain ⟨x, y, z, rfl⟩ := exists_keccakIdx (lt_of_lt_of_le hi hsize)
  have hj := h (x, y, z)
  change ir.evalE rd (ir.domainField d) _ _ = ir.evalE rd (ir.domainField d) _ _
  have hlin := evalE_linB ho rd (ir.domainField d) hL hC heL heC hm
  rw [hzeros _ (keccakIdx_lt x y z), evalE_add, evalE_add, evalE_add, evalE_mul, evalE_sub,
    evalE_reindex, evalE_reindex, hones _ (keccakIdx_lt x y z), hm.2.2.2.2.1, hm.2.2.2.2.2,
    hlin, hlin, hlin, hrc]
  simp only [opA, opB, opC, shiftMat_mulVec, Pi.add_apply] at hj
  rw [CharTwo.sub_eq_add]
  change (1 + linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x + 1, y, z)) *
      linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x + 2, y, z) +
    (stateOf (ir.evalE rd (ir.domainField d) (.leaf out)) x y z +
      linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x, y, z) + iotaVec r (x, y, z)) = 0
    at hj
  change stateOf (ir.evalE rd (ir.domainField d) (.leaf out)) x y z +
    (linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x, y, z) +
      (1 + linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x + 1, y, z)) *
        linB (flat (stateOf (ir.evalE rd (ir.domainField d) S))) (x + 2, y, z) +
      iotaVec r (x, y, z)) = 0
  linear_combination hj

end

/-! ## Matchers -/

/-- **The source of a round's input state**: a value or a shared expression. -/
inductive StateSrc where
  /-- Value `v`. -/
  | leaf (v : ℕ)
  /-- Shared expression `k`. -/
  | ref (k : ℕ)
  deriving DecidableEq, Repr

/-- The expression of a state source. -/
def StateSrc.expr : StateSrc → Expr
  | .leaf v => .leaf v
  | .ref k => .ref k

/-- **A state source** read off an expression: a leaf or a reference. -/
def Expr.stateSrc? : Expr → Option StateSrc
  | .leaf v => some (.leaf v)
  | .ref k => some (.ref k)
  | _ => none

theorem Expr.eq_of_stateSrc? {e : Expr} {s : StateSrc} (h : e.stateSrc? = some s) : e = s.expr := by
  unfold stateSrc? at h
  split at h <;> first | (cases h; rfl) | cases h

/-- **The shape of a round's linear part** `π (ρ (θ S))`: the input state, the column parities'
shared expression and the index maps. -/
structure LinShape where
  /-- The input state. -/
  src : StateSrc
  /-- The column parities (a shared expression). -/
  col : ℕ
  /-- The index maps. -/
  i9 : IndexMap
  i10 : IndexMap
  i11 : IndexMap
  i12 : IndexMap
  i13 : IndexMap
  deriving DecidableEq, Repr

/-- **A round's linear part**, read off a shared expression. -/
def Expr.linShape? : Expr → Option LinShape
  | .reindex i13 (.add (.add s (.reindex i10 (.reindex i9 (.ref c))))
      (.reindex i10' (.reindex i12 (.reindex i11 (.ref c'))))) =>
    match s.stateSrc? with
    | some src => if i10' = i10 ∧ c' = c then some ⟨src, c, i9, i10, i11, i12, i13⟩ else none
    | none => none
  | _ => none

theorem Expr.eq_of_linShape? {e : Expr} {sh : LinShape} (h : e.linShape? = some sh) :
    e = .reindex sh.i13 (.add (.add sh.src.expr (.reindex sh.i10 (.reindex sh.i9 (.ref sh.col))))
      (.reindex sh.i10 (.reindex sh.i12 (.reindex sh.i11 (.ref sh.col))))) := by
  unfold linShape? at h
  split at h
  · rename_i i13 s i10 i9 c i10' i12 i11 c'
    split at h
    · rename_i src hs
      split_ifs at h with hc
      cases h
      obtain ⟨rfl, rfl⟩ := hc
      rw [Expr.eq_of_stateSrc? hs]
    · cases h
  · cases h

/-- **A round's column parities**, read off a shared expression: the input state and `i8`. -/
def Expr.colShape? : Expr → Option (StateSrc × IndexMap)
  | .apply (.sum 5) (.reindex i8 s) => (s.stateSrc?).map fun src => (src, i8)
  | _ => none

theorem Expr.eq_of_colShape? {e : Expr} {src : StateSrc} {i8 : IndexMap}
    (h : e.colShape? = some (src, i8)) : e = .apply (.sum 5) (.reindex i8 src.expr) := by
  unfold colShape? at h
  split at h
  · rename_i i8' s
    obtain ⟨src', hs, he⟩ := Option.map_eq_some_iff.1 h
    cases he
    rw [Expr.eq_of_stateSrc? hs]
  · cases h

/-- **The shape of a round predicate**: its domain, output value, linear part's shared expression,
round-constant value, the constant states `1` and `0`, and the `χ` shifts. -/
structure RoundShape where
  /-- The domain. -/
  d : ℕ
  /-- The output state. -/
  out : ℕ
  /-- The linear part (a shared expression). -/
  lin : ℕ
  /-- The round constant's bits. -/
  rc : ℕ
  /-- The all-ones state. -/
  ones : ℕ
  /-- The zero state. -/
  zeros : ℕ
  /-- The `χ` shifts. -/
  i14 : IndexMap
  i15 : IndexMap
  deriving DecidableEq, Repr

/-- **A round predicate**, read off a predicate body. -/
def PredBody.roundShape? : PredBody → Option RoundShape
  | .equal d (.add (.leaf out) (.add (.add (.ref l)
      (.mul (.sub (.leaf ones) (.reindex i14 (.ref l'))) (.reindex i15 (.ref l'')))) (.leaf rc)))
      (.leaf zeros) _ =>
    if l' = l ∧ l'' = l then some ⟨d, out, l, rc, ones, zeros, i14, i15⟩ else none
  | _ => none

theorem PredBody.eq_of_roundShape? {b : PredBody} {sh : RoundShape} (h : b.roundShape? = some sh) :
    ∃ tg, b = .equal sh.d (.add (.leaf sh.out) (.add (.add (.ref sh.lin)
      (.mul (.sub (.leaf sh.ones) (.reindex sh.i14 (.ref sh.lin))) (.reindex sh.i15 (.ref sh.lin))))
      (.leaf sh.rc))) (.leaf sh.zeros) tg := by
  unfold roundShape? at h
  split at h
  · rename_i d out l ones i14 l' i15 l'' rc zeros tg
    split_ifs at h with hl
    cases h
    obtain ⟨rfl, rfl⟩ := hl
    exact ⟨tg, rfl⟩
  · cases h

section

variable {ir : RealizedProgram} {I : Interp}

/-- **A matched round predicate is the round relation** (`roundRelation_of_holdsWith` at the
shapes read by `PredBody.roundShape?`, `Expr.linShape?` and `Expr.colShape?`). -/
theorem roundRelation_of_shapes (ho : ir.RefsOrdered) {rd : ir.Valuation I} {b : PredBody}
    {sh : RoundShape} {ls : LinShape} {i8 : IndexMap} {r : Fin 24}
    [CharP (I (ir.domainField sh.d)).K 2] (hb : b.roundShape? = some sh)
    (hlin : (ir.expr sh.lin).linShape? = some ls)
    (hcol : (ir.expr ls.col).colShape? = some (ls.src, i8))
    (hL : sh.lin < ir.exprs.length) (hC : ls.col < ir.exprs.length)
    (hm : KeccakMaps i8 ls.i9 ls.i10 ls.i11 ls.i12 ls.i13 sh.i14 sh.i15)
    (hsize : 1600 ≤ (ir.value sh.out).size)
    (hones : ∀ j < 1600, ir.evalE rd (ir.domainField sh.d) (.leaf sh.ones) j = 1)
    (hzeros : ∀ j < 1600, ir.evalE rd (ir.domainField sh.d) (.leaf sh.zeros) j = 0)
    (hrc : ∀ x y z, ir.evalE rd (ir.domainField sh.d) (.leaf sh.rc) (keccakIdx x y z) =
      iotaVec r (x, y, z))
    (h : ir.HoldsWith rd b) :
    RoundRelation r (stateOf (ir.evalE rd (ir.domainField sh.d) ls.src.expr))
      (stateOf (ir.evalE rd (ir.domainField sh.d) (.leaf sh.out))) := by
  obtain ⟨tg, rfl⟩ := PredBody.eq_of_roundShape? hb
  exact roundRelation_of_holdsWith ho hL hC (Expr.eq_of_linShape? hlin) (Expr.eq_of_colShape? hcol)
    hm hsize hones hzeros hrc h

/-- **`roundRelation_of_shapes` read in a field identifier `f`** equal to the round's domain's
field. -/
theorem roundRelation_of_shapes_at (ho : ir.RefsOrdered) {rd : ir.Valuation I} {b : PredBody}
    {sh : RoundShape} {ls : LinShape} {i8 : IndexMap} {r : Fin 24} {f : ℕ}
    (hf : ir.domainField sh.d = f) [CharP (I f).K 2] (hb : b.roundShape? = some sh)
    (hlin : (ir.expr sh.lin).linShape? = some ls)
    (hcol : (ir.expr ls.col).colShape? = some (ls.src, i8))
    (hL : sh.lin < ir.exprs.length) (hC : ls.col < ir.exprs.length)
    (hm : KeccakMaps i8 ls.i9 ls.i10 ls.i11 ls.i12 ls.i13 sh.i14 sh.i15)
    (hsize : 1600 ≤ (ir.value sh.out).size)
    (hones : ∀ j < 1600, ir.evalE rd f (.leaf sh.ones) j = 1)
    (hzeros : ∀ j < 1600, ir.evalE rd f (.leaf sh.zeros) j = 0)
    (hrc : ∀ x y z, ir.evalE rd f (.leaf sh.rc) (keccakIdx x y z) = iotaVec r (x, y, z))
    (h : ir.HoldsWith rd b) :
    RoundRelation r (stateOf (ir.evalE rd f ls.src.expr))
      (stateOf (ir.evalE rd f (.leaf sh.out))) := by
  subst hf
  exact roundRelation_of_shapes ho hb hlin hcol hL hC hm hsize hones hzeros hrc h

/-- **The round relation gives a matched round predicate** (the converse of
`roundRelation_of_shapes`). -/
theorem holdsWith_of_shapes (ho : ir.RefsOrdered) {rd : ir.Valuation I} {b : PredBody}
    {sh : RoundShape} {ls : LinShape} {i8 : IndexMap} {r : Fin 24}
    [CharP (I (ir.domainField sh.d)).K 2] (hb : b.roundShape? = some sh)
    (hlin : (ir.expr sh.lin).linShape? = some ls)
    (hcol : (ir.expr ls.col).colShape? = some (ls.src, i8))
    (hL : sh.lin < ir.exprs.length) (hC : ls.col < ir.exprs.length)
    (hm : KeccakMaps i8 ls.i9 ls.i10 ls.i11 ls.i12 ls.i13 sh.i14 sh.i15)
    (hsize : (ir.value sh.out).size ≤ 1600)
    (hones : ∀ j < 1600, ir.evalE rd (ir.domainField sh.d) (.leaf sh.ones) j = 1)
    (hzeros : ∀ j < 1600, ir.evalE rd (ir.domainField sh.d) (.leaf sh.zeros) j = 0)
    (hrc : ∀ x y z, ir.evalE rd (ir.domainField sh.d) (.leaf sh.rc) (keccakIdx x y z) =
      iotaVec r (x, y, z))
    (h : RoundRelation r (stateOf (ir.evalE rd (ir.domainField sh.d) ls.src.expr))
      (stateOf (ir.evalE rd (ir.domainField sh.d) (.leaf sh.out)))) :
    ir.HoldsWith rd b := by
  obtain ⟨tg, rfl⟩ := PredBody.eq_of_roundShape? hb
  exact holdsWith_of_roundRelation ho hL hC (Expr.eq_of_linShape? hlin) (Expr.eq_of_colShape? hcol)
    hm hsize hones hzeros hrc h

/-- **`holdsWith_of_shapes` at a field identifier `f` equal to the round's domain field.** -/
theorem holdsWith_of_shapes_at (ho : ir.RefsOrdered) {rd : ir.Valuation I} {b : PredBody}
    {sh : RoundShape} {ls : LinShape} {i8 : IndexMap} {r : Fin 24} {f : ℕ}
    (hd : ir.domainField sh.d = f) [CharP (I f).K 2] (hb : b.roundShape? = some sh)
    (hlin : (ir.expr sh.lin).linShape? = some ls)
    (hcol : (ir.expr ls.col).colShape? = some (ls.src, i8))
    (hL : sh.lin < ir.exprs.length) (hC : ls.col < ir.exprs.length)
    (hm : KeccakMaps i8 ls.i9 ls.i10 ls.i11 ls.i12 ls.i13 sh.i14 sh.i15)
    (hsize : (ir.value sh.out).size ≤ 1600)
    (hones : ∀ j < 1600, ir.evalE rd f (.leaf sh.ones) j = 1)
    (hzeros : ∀ j < 1600, ir.evalE rd f (.leaf sh.zeros) j = 0)
    (hrc : ∀ x y z, ir.evalE rd f (.leaf sh.rc) (keccakIdx x y z) = iotaVec r (x, y, z))
    (h : RoundRelation r (stateOf (ir.evalE rd f ls.src.expr))
      (stateOf (ir.evalE rd f (.leaf sh.out)))) :
    ir.HoldsWith rd b := by
  subst hd
  exact holdsWith_of_shapes ho hb hlin hcol hL hC hm hsize hones hzeros hrc h

end

end GordieHowe.RealizedProgram
