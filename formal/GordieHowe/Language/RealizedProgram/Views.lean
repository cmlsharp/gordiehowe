-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.RealizedProgram.BatchRelation

@[expose] public section

/-!
# GordieHowe: bit views in a program's domain

A bit view (`Kind.bits w sel`) reads the bits of the committed `Sub(E)` words `sel` of the value `w`
(`GordieHowe.RealizedProgram.bitView`: bit `i mod e` of word `sel[i / e]`, `e` bits per word). The bits are not affine
over the field in the words' cells, so a predicate reading a bit view is lowered on the words' bits
as further coordinates of the domain (`Domain.View`, `GordieHowe.RealizedProgram.TargetsAdmit`):

* **The view coordinates** (`GordieHowe.RealizedProgram.cellBit`): bit `j < 16` of every cell, its coordinate in its
  value's node's basis (`FieldInterp.coord`). The bit views of the domain's checks read whole
  `16`-bit words of committed values (`GordieHowe.RealizedProgram.bitViewOk`), as domain H's `GF(2^16)` words.
* **The reading of the bit views from word bits** (`GordieHowe.RealizedProgram.bitValuation`): a valuation that reads
  every bit view from word-bit variables; at the cells' bits it is the cells' valuation at every
  bit view of the checks (`bitValuation_cellBits`).
* **The rows on views** (`GordieHowe.RealizedProgram.viewRow`, `Placement::kAffine` rows reading packed bits and bit
  views): a predicate with target `affine` reading bit views (`GordieHowe.RealizedProgram.isViewRow`) is a family of
  affine rows on the cells and the view coordinates, which hold exactly when the predicate placed
  holds (`viewRows_iff`).
* **The batch check** (`GordieHowe.RealizedProgram.BatchOk`, decided by
  `batchOkB`; `lem:batch`, `def:batched-relation`, `def:skip-domain`): any degree, the operand map
  `columns` or, in characteristic two, `bits` (`GordieHowe.RealizedProgram.atomOf`, `OperandMap.lane`), the
  characteristic's skip domain with `D(w − 1) + 1` points (`skipDomainName`, `SkipFits`), parts of
  one shape or merged by a challenge (`PartsOk`), the instances in whole lanes, the pads of the
  masked skip at the batch's relation; `colsBatchOkB` and `bitsBatchOkB` by operand map.
* **The batches on bits** (`GordieHowe.RealizedProgram.bitsBatchRelation`; the C++'s bit-operand map, `batch.h`,
  `BitOperandMap`): a batch in characteristic two whose operands are affine in the bits of words,
  the statement's values and constants (`GordieHowe.RealizedProgram.bitsAtomB`); its instances are bit-sliced (`64` per
  lane). Its batched relation on the cells has additive operands when the field's bit coordinates
  are additive (`FieldInterp.BitsAdditive`: a trace form, as the C++ reads bit `i` of a word); it
  holds exactly when every part placed holds (`bitsBatchRelation_holds_iff`).
-/

namespace GordieHowe.RealizedProgram

open Export

/-- **The bit coordinates of a field are additive**: every node's bit `j` is an additive function
of the element (a trace form, as the C++ reads bit `j` of a word, `batch.h`, `BitOperandMap`). A
fact about the interpretation of a binary field; an odd field reads no bits. -/
def FieldInterp.BitsAdditive (F : FieldInterp) : Prop :=
  ∀ (E : String) (j : ℕ) (x y : F.K),
    F.ofBool (F.coord E (x + y) j) = F.ofBool (F.coord E x j) + F.ofBool (F.coord E y j)

/-- **A field reading no bits has additive bit coordinates** (an odd field, every coordinate
`false`). -/
theorem FieldInterp.bitsAdditive_of_noBits {F : FieldInterp} (h : ∀ E x j, F.coord E x j = false) :
    F.BitsAdditive := fun E j x y => by
  simp [FieldInterp.ofBool, h]

/-- Additive bit coordinates read `0` at `0`. -/
theorem FieldInterp.BitsAdditive.ofBool_zero {F : FieldInterp} (h : F.BitsAdditive) (E : String)
    (j : ℕ) : F.ofBool (F.coord E 0 j) = 0 := by
  have h0 := h E j 0 0
  rw [add_zero] at h0
  have h2 : F.ofBool (F.coord E 0 j) + F.ofBool (F.coord E 0 j) =
      F.ofBool (F.coord E 0 j) + 0 := by
    rw [add_zero]
    exact h0.symm
  exact add_left_cancel h2

/-- **A cast of a bit coordinate** is the bit coordinate of the cast, between equal field
identifiers. -/
theorem castElt_ofBool_coord {I : Interp} {p q r : ℕ} (hpq : p = q) (hrp : r = p) (E : String)
    (y : (I p).K) (j : ℕ) :
    (castElt ((I p).ofBool ((I p).coord E y j)) : (I q).K) =
      (I q).ofBool ((I r).coord E (castElt y : (I r).K) j) := by
  subst hpq
  subst hrp
  simp

/-! ## Affine functions through the cells -/

section Lift

variable {K κ κ' : Type} [Field K]

/-- **An affine function read through a linear map of the variables is affine.** -/
theorem IsAff.comp_linear {g : (κ → K) → K} (h : IsAff g) (φ : (κ' → K) →ₗ[K] (κ → K)) :
    IsAff fun z => g (φ z) := by
  obtain ⟨l, c, h⟩ := h
  exact ⟨l ∘ₗ φ, c, fun z => h (φ z)⟩

omit [Field K] in
theorem IsConst.comp_any {β : Type*} {g : (κ → K) → β} (h : IsConst g) (φ : (κ' → K) → (κ → K)) :
    IsConst fun z => g (φ z) := fun _ _ => h _ _

end Lift

section

variable (ir : RealizedProgram) (I : Interp)

/-! ## The bits of the cells -/

/-- **The node of a cell's value**, whose basis gives the cell's bits (`""` for a pad or filler
cell). -/
def keyNode : CellKey → String
  | .val w _ => (ir.value w).type.nodeName.getD ""
  | _ => ""

/-- **Bit `j` of a cell** of domain `d`: the coordinate `j` of the cell's value in its node's basis
(`FieldInterp.coord`), `0` or `1`. -/
def cellBit (d : ℕ) (a : ir.Cell d → (I (ir.domainField d)).K) (k : ir.Cell d) (j : Fin 16) :
    (I (ir.domainField d)).K :=
  (I (ir.domainField d)).ofBool ((I (ir.domainField d)).coord (ir.keyNode k.1) (a k) j)

/-- **The bits of the cells**, as word-bit variables. -/
def cellBits (d : ℕ) (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.Cell d × Fin 16 → (I (ir.domainField d)).K :=
  fun kj => ir.cellBit I d a kj.1 kj.2

/-- **Bit `j` of word `k` of value `w`**, read from the word-bit variables `wb`: the variable when
the word is a cell of `d`, the bit of `0` otherwise. -/
def wordBit (d : ℕ) (wb : ir.Cell d × Fin 16 → (I (ir.domainField d)).K) (w k : ℕ) (j : Fin 16) :
    (I (ir.domainField d)).K :=
  if h : CellKey.val w k ∈ ir.cellKeys d then wb (⟨_, h⟩, j)
  else (I (ir.domainField d)).ofBool
    ((I (ir.domainField d)).coord ((ir.value w).type.nodeName.getD "") 0 j)

/-- The bit `i mod 16` of a bit view's coordinate `i`. -/
def bitPos (i : ℕ) : Fin 16 := ⟨i % 16, Nat.mod_lt _ (by norm_num)⟩

/-- **The valuation reading the bit views from word-bit variables** `wb`: coordinate `i` of a bit
view of the words `sel` of `w` is bit `i mod 16` of word `sel[i / 16]` (`wordBit`); every other
value is read by `base`. -/
def bitValuation (d : ℕ) (base : ir.Valuation I)
    (wb : ir.Cell d × Fin 16 → (I (ir.domainField d)).K) : ir.Valuation I := fun v i =>
  match (ir.value v).kind with
  | .bits w sel => castElt (ir.wordBit I d wb w (sel.entry (i / 16)) (bitPos i))
  | _ => base v i

/-- **A bit view of domain `d` reading whole `16`-bit words of a committed value of `d`**: the
bits of the words `sel` (nonempty) of a value `w` of kind `priv` of `d`, `16` bits per word. -/
def bitViewOk (d v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .bits w sel =>
    (ir.value v).domain == d && (ir.value w).domain == d && (ir.value w).kind.isPriv &&
      decide (0 < sel.size) && (ir.value v).size == 16 * sel.size
  | _ => false

variable {ir I}

/-- A value of a kind other than `priv` is a value of the program (the default value is
`priv`). -/
theorem lt_of_kind_bits {v w : ℕ} {sel : IndexMap} (hk : (ir.value v).kind = .bits w sel) :
    v < ir.values.length := by
  by_contra h
  rw [value, List.getD_eq_default _ _ (Nat.le_of_not_lt h)] at hk
  cases hk

theorem bitViewOk_spec {d v : ℕ} (hv : ir.bitViewOk d v = true) :
    ∃ w sel, (ir.value v).kind = .bits w sel ∧ (ir.value v).domain = d ∧
      (ir.value w).domain = d ∧ (ir.value w).kind = .priv ∧ 0 < sel.size ∧
      (ir.value v).size = 16 * sel.size := by
  unfold bitViewOk at hv
  split at hv
  · rename_i w sel hk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hv
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hv
    refine ⟨w, sel, hk, h1, h2, ?_, h4, h5⟩
    revert h3
    cases (ir.value w).kind <;> simp [Kind.isPriv]
  · cases hv

/-- **At the cells' bits, the bit views of the checks read as the cells' valuation does**: bit
`i mod 16` of word `sel[i / 16]` of the cells' value (`RealizedProgram.bitView` with `16` bits per word),
the bit of `0` off the cells. -/
theorem bitValuation_cellBits {d v : ℕ} (hv : ir.bitViewOk d v = true) (base : ir.Valuation I)
    (x : ir.Valuation I) (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.bitValuation I d base (ir.cellBits I d a) v = ir.cellValuation I d x r a v := by
  obtain ⟨w, sel, hk, hvd, hwd, hwk, hsel, hsz⟩ := bitViewOk_spec hv
  have hvlt := lt_of_kind_bits hk
  have he : (ir.value v).size / sel.size = 16 := by
    rw [hsz, Nat.mul_div_cancel _ hsel]
  have hfv : ir.domainField d = ir.valueField v := by
    rw [ir.valueField_of_allowsField (v := v) (by rw [hk]; rfl), hvd]
  have hfw : ir.valueField w = ir.domainField d := by
    rw [ir.valueField_of_allowsField (v := w) (by rw [hwk]; rfl), hwd]
  funext i
  obtain ⟨n, hn⟩ : ∃ n, ir.fuel = n + 1 + 1 := ⟨ir.values.length - 1, by
    unfold fuel
    omega⟩
  simp only [bitValuation, hk, cellValuation, reader, hn, read, bitView, he]
  simp only [hwk, layoutEnv, ir.bindAsg_val_of_isBound (v := w) _ (by rw [hwk]; rfl), ofCells]
  unfold wordBit
  split_ifs with hmem
  · exact castElt_ofBool_coord hfv hfw _ _ _
  · rw [castElt_ofBool_coord hfv hfw, castElt_zero]
    rfl

/-! ## Affine functions through the cells -/

/-- **A value affine in the cells is affine in the cells and further variables**, through
`Sum.inl`. -/
theorem LeafOk.comp_inl {κ κ' : Type} {f : ℕ} {V : (κ → (I f).K) → ir.Valuation I}
    {nd : ℕ → ℕ} {v : ℕ} (h : LeafOk ir V nd v) :
    LeafOk ir (fun z : κ ⊕ κ' → (I f).K => V (z ∘ Sum.inl)) nd v :=
  ⟨fun hd i => IsAff.comp_linear (h.aff hd i) (LinearMap.funLeft (I f).K (I f).K Sum.inl),
    fun hd => IsConst.comp_any (h.const hd) _⟩

/-! ## The rows on views -/

variable (ir) in
/-- **A value a row on views may read**: a value a row may read (`rowValueOk`), or a bit view
reading whole `16`-bit words of a committed value of `d` (`bitViewOk`). -/
def viewValueOk (d v : ℕ) : Bool := ir.rowValueOk v || ir.bitViewOk d v

variable (ir) in
/-- **A side a row on views may have**: every value it reads may be read by a row on views, every
coefficient and operand is public, and its degree in the cells and the bit views is at most one. -/
def viewExprOk (d : ℕ) (e : Expr) : Bool :=
  (ir.exprNodes e).all (ir.viewValueOk d) && (ir.closure Expr.coefNodes e).all (ir.cellNd · == 0) &&
    decide (ir.cellDeg e ≤ 1)

variable (ir) in
/-- **Predicate `p` is a family of affine rows on views of domain `d`**: a predicate with target
`affine` of `d` that is not an affine row on the cells (`isRow`) and whose sides may be rows' on
views (`viewExprOk`). -/
def isViewRow (d p : ℕ) : Bool :=
  match (ir.predicate p).body.rowSides d with
  | some (e, e') => !ir.isRow d p && ir.viewExprOk d e && ir.viewExprOk d e'
  | none => false

variable (ir) in
/-- **The predicates of domain `d` that are affine rows on views.** -/
def ViewRowPred (d : ℕ) : Type := {p : Fin ir.predicates.length // ir.isViewRow d p = true}

instance (d : ℕ) : Fintype (ir.ViewRowPred d) := Subtype.fintype _

/-- The view row predicates are encoded by their indices. -/
instance (d : ℕ) : Encodable (ir.ViewRowPred d) :=
  inferInstanceAs (Encodable {p : Fin ir.predicates.length // ir.isViewRow d p = true})

variable (ir) in
/-- **The rows on views of domain `d`**: one per predicate and coordinate of its left side. -/
def ViewRow (d : ℕ) : Type := Σ p : ir.ViewRowPred d, Fin (ir.exprLen (ir.rowLhs d p.1))

instance (d : ℕ) : Fintype (ir.ViewRow d) :=
  inferInstanceAs (Fintype (Σ _ : ir.ViewRowPred d, Fin _))

/-- The view rows are encoded as the sigma type. -/
instance (d : ℕ) : Encodable (ir.ViewRow d) :=
  inferInstanceAs (Encodable (Σ _ : ir.ViewRowPred d, Fin _))

variable (I) in
/-- **The valuation of the cells and the view coordinates** `z` of domain `d`: the cells'
valuation, every bit view read from the view coordinates (`bitValuation`). -/
def viewValuation (d : ℕ) (x : ir.Valuation I) (r : (ir.layout I).Run)
    (z : ir.Cell d ⊕ (ir.Cell d × Fin 16) → (I (ir.domainField d)).K) : ir.Valuation I :=
  ir.bitValuation I d (ir.cellValuation I d x r (z ∘ Sum.inl)) (z ∘ Sum.inr)

variable (I) in
/-- **The difference of row predicate `p` on views at coordinate `i`**, at the cells and the view
coordinates `z`. -/
def viewDiff (d : ℕ) (x : ir.Valuation I) (r : (ir.layout I).Run) (p i : ℕ)
    (z : ir.Cell d ⊕ (ir.Cell d × Fin 16) → (I (ir.domainField d)).K) : (I (ir.domainField d)).K :=
  ir.evalWith (ir.viewValuation I d x r z) d (ir.rowLhs d p) i -
    ir.evalWith (ir.viewValuation I d x r z) d (ir.rowRhs d p) i

variable (I) in
/-- **The row on views of predicate `p` at coordinate `i`** of domain `d`: the gradient of the
difference on the cells and the view coordinates as the linear form, the difference at zero as the
constant. -/
def viewRow (d : ℕ) (q : ir.ViewRow d) :
    AffineRow (ir.layout I) (ir.Valuation I) (I (ir.domainField d)).K
      (ir.Cell d ⊕ (ir.Cell d × Fin 16)) where
  form x r := ∑ k, (ir.viewDiff I d x r q.1.1 q.2 (fun j => if k = j then 1 else 0) -
    ir.viewDiff I d x r q.1.1 q.2 0) • LinearMap.proj k
  const x r := ir.viewDiff I d x r q.1.1 q.2 0

/-- **The view coordinates' valuation is affine, or constant, at every value a row on views may
read**: the cells' valuation at a value a row may read (`leafOk_cellValuation`), a view coordinate
or a constant at a bit view. -/
theorem leafOk_viewValuation {d : ℕ} {x : ir.Valuation I} {r : (ir.layout I).Run} {v : ℕ}
    (hv : ir.viewValueOk d v = true) :
    LeafOk ir (f := ir.domainField d) (ir.viewValuation I d x r) ir.cellNd v := by
  rcases Bool.or_eq_true_iff.1 hv with hv | hv
  · have hnb : ∀ w sel, (ir.value v).kind ≠ .bits w sel := fun w sel hk => by
      simp [rowValueOk, hk] at hv
    have hval : ∀ z, ir.viewValuation I d x r z v = ir.cellValuation I d x r (z ∘ Sum.inl) v :=
      fun z => by
        funext i
        unfold viewValuation bitValuation
        split
        · rename_i w sel hk
          exact absurd hk (hnb w sel)
        · rfl
    have hL := (leafOk_cellValuation (d := d) (x := x) (r := r) hv).comp_inl
      (κ' := ir.Cell d × Fin 16)
    refine ⟨fun hd i => ?_, fun hd z z' => ?_⟩
    · simp only [hval]
      exact hL.aff hd i
    · change ir.viewValuation I d x r z v = ir.viewValuation I d x r z' v
      rw [hval, hval]
      exact hL.const hd z z'
  · obtain ⟨w, sel, hk, -, -, -, -, -⟩ := bitViewOk_spec hv
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [viewValuation, bitValuation, hk, wordBit, castElt_dite, castElt_castElt]
      exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero)
        fun _ => (isConst_const _).isAff
    · simp [cellNd, isCommitted, hk] at h0

/-- **The difference of a row predicate on views is affine** in the cells and the view
coordinates. -/
theorem isAff_viewDiff {d p : ℕ} (hp : ir.isViewRow d p = true) (x : ir.Valuation I)
    (r : (ir.layout I).Run) (i : ℕ) : IsAff (ir.viewDiff I d x r p i) := by
  have hside : ∀ e, ir.viewExprOk d e = true →
      IsAff fun z => ir.evalWith (ir.viewValuation I d x r z) d e i := by
    intro e he
    simp only [viewExprOk, Bool.and_eq_true, List.all_eq_true, beq_iff_eq,
      decide_eq_true_eq] at he
    exact evalE_isAff (fun v hv => leafOk_viewValuation (he.1.1 v hv)) he.1.2 he.2 i
  unfold isViewRow at hp
  unfold viewDiff rowLhs rowRhs
  split at hp
  · rename_i e e' h
    simp only [Bool.and_eq_true] at hp
    simp only [h, Option.map_some, Option.getD_some]
    exact (hside e hp.1.2).sub (hside e' hp.2)
  · simp at hp

/-- **At the cells and their bits, the view coordinates' valuation is the cells' valuation** at
every value a row on views may read (`bitValuation_cellBits`). -/
theorem viewValuation_cellBits {d v : ℕ} (hv : ir.viewValueOk d v = true) (x : ir.Valuation I)
    (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.viewValuation I d x r (Sum.elim a (ir.cellBits I d a)) v = ir.cellValuation I d x r a v := by
  rcases Bool.or_eq_true_iff.1 hv with hv | hv
  · funext i
    unfold viewValuation bitValuation
    split
    · rename_i w sel hk
      simp [rowValueOk, hk] at hv
    · rfl
  · exact bitValuation_cellBits hv _ x r a

/-- **The row on views at any variables is the difference there** (the difference is affine,
`isAff_viewDiff`). -/
theorem viewRow_eval {d : ℕ} (q : ir.ViewRow d) (x : ir.Valuation I) (r : (ir.layout I).Run)
    (z : ir.Cell d ⊕ (ir.Cell d × Fin 16) → (I (ir.domainField d)).K) :
    (ir.viewRow I d q).form x r z + (ir.viewRow I d q).const x r =
      ir.viewDiff I d x r q.1.1 q.2 z := by
  have hform : (ir.viewRow I d q).form x r z = ∑ k, z k *
      (ir.viewDiff I d x r q.1.1 q.2 (fun j => if k = j then 1 else 0) -
        ir.viewDiff I d x r q.1.1 q.2 0) := by
    simp only [viewRow, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, mul_comm]
  rw [(isAff_viewDiff q.1.2 x r q.2).eq_gradient z, hform, add_comm]
  rfl

/-- **The row on views holds exactly when the predicate's coordinate does**, at the cells and their
bits. -/
theorem viewRow_holds_iff {d : ℕ} (q : ir.ViewRow d) (x : ir.Valuation I)
    (a : ir.Cell d → (I (ir.domainField d)).K) (r : (ir.layout I).Run) :
    (ir.viewRow I d q).Holds x (Sum.elim a (ir.cellBits I d a)) r ↔
      ir.evalWith (ir.cellValuation I d x r a) d (ir.rowLhs d q.1.1) q.2 =
        ir.evalWith (ir.cellValuation I d x r a) d (ir.rowRhs d q.1.1) q.2 := by
  set z := Sum.elim a (ir.cellBits I d a)
  have hform : (ir.viewRow I d q).form x r z = ∑ k, z k *
      (ir.viewDiff I d x r q.1.1 q.2 (fun j => if k = j then 1 else 0) -
        ir.viewDiff I d x r q.1.1 q.2 0) := by
    simp only [viewRow, LinearMap.sum_apply, LinearMap.smul_apply,
      LinearMap.proj_apply, smul_eq_mul, mul_comm]
  have hok : ∀ e, ir.viewExprOk d e = true →
      ir.evalWith (ir.viewValuation I d x r z) d e = ir.evalWith (ir.cellValuation I d x r a) d e :=
    fun e he => evalE_congr fun v hv => viewValuation_cellBits
      (List.all_eq_true.1 (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 he).1).1 v hv) x r a
  have hp := q.1.2
  unfold isViewRow at hp
  have hsides : ir.viewExprOk d (ir.rowLhs d q.1.1) = true ∧
      ir.viewExprOk d (ir.rowRhs d q.1.1) = true := by
    unfold rowLhs rowRhs
    split at hp
    · rename_i e e' h
      simp only [Bool.and_eq_true] at hp
      simp only [h, Option.map_some, Option.getD_some]
      exact ⟨hp.1.2, hp.2⟩
    · simp at hp
  rw [← sub_eq_zero, ← hok _ hsides.1, ← hok _ hsides.2]
  change _ ↔ ir.viewDiff I d x r q.1.1 q.2 z = 0
  rw [(isAff_viewDiff q.1.2 x r q.2).eq_gradient z, AffineRow.Holds, hform, add_comm]
  rfl

/-- **The rows on views of a predicate hold exactly when the predicate placed holds** at the cells'
valuation (`PlacedHolds`), at the cells and their bits. -/
theorem viewRows_iff {d : ℕ} (p : ir.ViewRowPred d) (x : ir.Valuation I)
    (a : ir.Cell d → (I (ir.domainField d)).K) (r : (ir.layout I).Run) :
    (∀ i, (ir.viewRow I d ⟨p, i⟩).Holds x (Sum.elim a (ir.cellBits I d a)) r) ↔
      ir.PlacedHolds (ir.cellValuation I d x r a) (ir.predicate p.1).body := by
  obtain ⟨e, e', h⟩ : ∃ e e', (ir.predicate p.1).body.rowSides d = some (e, e') := by
    have hp := p.2
    unfold isViewRow at hp
    split at hp
    · exact ⟨_, _, by assumption⟩
    · simp at hp
  have hl : ir.rowLhs d p.1 = e := by simp [rowLhs, h]
  have hr : ir.rowRhs d p.1 = e' := by simp [rowRhs, h]
  refine (forall_congr' fun i => viewRow_holds_iff ⟨p, i⟩ x a r).trans ?_
  dsimp only
  rw [placedHolds_iff_of_rowSides h]
  constructor
  · intro H i hi
    have := H ⟨i, hl ▸ hi⟩
    simp only [hl, hr] at this
    exact this
  · intro H i
    simp only [hl, hr]
    exact H i (hl ▸ i.2)

/-! ## The batches on bits -/

variable (ir) in
/-- **A value a bit operand may read** in domain `d`: a committed value of phase `0`, a pad copy, a
constant, a bit view of the checks (`bitViewOk`), or a statement value of `d` (an input, or an
opaque value of no argument, both read from the statement). -/
def bitsLeafOk (d v : ℕ) : Bool :=
  match (ir.value v).kind with
  | .priv => (ir.value v).phase == 0
  | .padCopy _ _ => true
  | .constant _ => true
  | .bits _ _ => ir.bitViewOk d v
  | .pub .input => (ir.value v).domain == d
  | .pub (.opaque _ []) => (ir.value v).domain == d
  | _ => false

variable (ir) in
/-- **The degree of a value in a bit operand's variables**: `0` for a constant, `1` for every other
value (the cells, the bits of words and the statement's values are the variables). -/
def bitsNd (v : ℕ) : ℕ :=
  match (ir.value v).kind with
  | .constant _ => 0
  | _ => 1

variable (ir) in
/-- **An atom of a bit operand** of domain `d`: an expression reading only values a bit operand may
read (`bitsLeafOk`), with constant coefficients, of degree at most one in the cells, the bits and
the statement's values together (so its linear part in the cells and the bits does not depend on
the statement). -/
def bitsAtomB (d : ℕ) (e : Expr) : Bool :=
  (ir.exprNodes e).all (ir.bitsLeafOk d) && (ir.closure Expr.coefNodes e).all (ir.bitsNd · == 0) &&
    decide (ir.degOf ir.bitsNd e ≤ 1)

/-! ## The batch check -/

variable (ir) in
/-- **The atom test of batch `b`** in domain `d` (`batch_form`'s leaves under the batch's operand
map): `atomB` on columns, `bitsAtomB d` on bits. -/
def atomOf (d b : ℕ) : Expr → Bool :=
  match (ir.batch b).operands with
  | .columns => ir.atomB
  | .bits => ir.bitsAtomB d

variable (ir) in
/-- **The coordinates part `j` occupies** in the batch's instances: its coordinates in whole lanes
(`OperandMap.lane`). -/
def partCount (d b j : ℕ) : ℕ :=
  (ir.partLen d b j + ((ir.batch b).operands.lane - 1)) / (ir.batch b).operands.lane *
    (ir.batch b).operands.lane

variable (ir) in
/-- **Batch `b` is a batch of domain `d` the proof system covers**: of `d`; its parts with forms at
the operand map's atom test (`PartsOk`: one shape, or merged by its challenge with one number of
coordinates), at least two parts when merged; a nonzero degree bounding every part's; an operand map
on bits only in characteristic two; the characteristic's skip domain (`skipDomainName`: the
integers, or the embedded bytes in characteristic two) with `D(w − 1) + 1` distinct points
(`SkipFits`); a nonzero width; the instances the parts' coordinates in whole lanes, side by side or,
merged, one part's; fitting the rows; the pads the masked skip's at the batch's relation
(`(D − 1)(w − 1) + nD + k` and one per product cell, `Shape.cells`). -/
structure BatchOk (d b : ℕ) : Prop where
  /-- An identifier of the program's batches. -/
  lt : b < ir.batches.length
  /-- A batch of `d`. -/
  domain : (ir.batch b).domain = d
  /-- Its parts have forms at the operand map's atom test. -/
  partsOk : ir.PartsOk (ir.atomOf d b) d b
  /-- A merged batch has at least two parts. -/
  merged : ir.merged b = true → 2 ≤ (ir.batch b).parts.length
  /-- The degree is nonzero. -/
  degree : 0 < (ir.batch b).degree
  /-- An operand map on bits is in characteristic two. -/
  bits : (ir.batch b).operands = .bits → (ir.field (ir.domainField d)).characteristic = 2
  /-- The skip domain is the characteristic's. -/
  skipName : (ir.batch b).skipDomain = skipDomainName (ir.field (ir.domainField d)).characteristic
  /-- The skip domain has `D(w − 1) + 1` distinct points. -/
  skip : SkipFits (ir.batch b).degree (ir.batch b).width (ir.field (ir.domainField d)).characteristic
  /-- The width is nonzero. -/
  width : 0 < (ir.batch b).width
  /-- The instances are the parts' coordinates in whole lanes. -/
  instances : (ir.batch b).operands.lane * (ir.batch b).instances =
    if ir.merged b then ir.partCount d b 0
    else ((List.range (ir.batch b).parts.length).map (ir.partCount d b)).sum
  /-- The instances fit the rows. -/
  rows : (ir.batch b).operands.lane * (ir.batch b).instances ≤
    2 ^ (ir.batch b).rounds * (ir.batch b).width
  /-- The pads are the masked skip's at the batch's relation, and on bits the bit sumcheck's two
  per round of its `4` rounds over the bit index of a `GF(2^16)` word. -/
  pads : (ir.batch b).pads = ((ir.batch b).degree - 1) * ((ir.batch b).width - 1) +
    ((ir.batch b).rounds * (ir.batch b).degree +
      ((ir.relShape (ir.atomOf d b) d b).k + (ir.relShape (ir.atomOf d b) d b).cells)) +
    (if (ir.batch b).operands = .bits then 2 * 4 else 0)

variable (ir) in
/-- **`BatchOk`, decided.** -/
def batchOkB (d b : ℕ) : Bool :=
  decide (b < ir.batches.length) && decide ((ir.batch b).domain = d) &&
    ir.partsOkB (ir.atomOf d b) d b &&
    (!ir.merged b || decide (2 ≤ (ir.batch b).parts.length)) &&
    decide (0 < (ir.batch b).degree) &&
    (((ir.batch b).operands != .bits) ||
      decide ((ir.field (ir.domainField d)).characteristic = 2)) &&
    decide ((ir.batch b).skipDomain = skipDomainName (ir.field (ir.domainField d)).characteristic) &&
    decide (SkipFits (ir.batch b).degree (ir.batch b).width
      (ir.field (ir.domainField d)).characteristic) &&
    decide (0 < (ir.batch b).width) &&
    decide ((ir.batch b).operands.lane * (ir.batch b).instances =
      if ir.merged b then ir.partCount d b 0
      else ((List.range (ir.batch b).parts.length).map (ir.partCount d b)).sum) &&
    decide ((ir.batch b).operands.lane * (ir.batch b).instances ≤
      2 ^ (ir.batch b).rounds * (ir.batch b).width) &&
    decide ((ir.batch b).pads = ((ir.batch b).degree - 1) * ((ir.batch b).width - 1) +
      ((ir.batch b).rounds * (ir.batch b).degree +
        ((ir.relShape (ir.atomOf d b) d b).k + (ir.relShape (ir.atomOf d b) d b).cells)) +
      (if (ir.batch b).operands = .bits then 2 * 4 else 0))

theorem batchOkB_iff (d b : ℕ) : ir.batchOkB d b = true ↔ ir.BatchOk d b := by
  simp only [batchOkB, Bool.and_eq_true, decide_eq_true_eq, partsOkB_iff, Bool.or_eq_true,
    Bool.not_eq_true', bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h7'⟩, h8⟩, h9⟩, h10⟩, h11⟩
    refine ⟨h1, h2, h3, fun hm => h4.resolve_left (by simp [hm]), h5, fun hb => h6.resolve_left
      (by simp [hb]), h7, h7', h8, h9, h10, h11⟩
  · intro h
    refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.lt, h.domain⟩, h.partsOk⟩, ?_⟩, h.degree⟩, ?_⟩, h.skipName⟩, h.skip⟩,
      h.width⟩, h.instances⟩, h.rows⟩, h.pads⟩
    · cases hm : ir.merged b
      · exact .inl rfl
      · exact .inr (h.merged hm)
    · by_cases hb : (ir.batch b).operands = .bits
      · exact .inr (h.bits hb)
      · exact .inl hb

variable (ir) in
/-- **A covered batch on columns**: `BatchOk` with the operand map `columns`. -/
def colsBatchOkB (d b : ℕ) : Bool := ir.batchOkB d b && (ir.batch b).operands == .columns

variable (ir) in
/-- **A covered batch on bits**: `BatchOk` with the operand map `bits`. -/
def bitsBatchOkB (d b : ℕ) : Bool := ir.batchOkB d b && (ir.batch b).operands == .bits

/-- A covered batch on columns passes the check, its parts with forms at `atomB`. -/
theorem colsBatchOk {d b : ℕ} (h : ir.colsBatchOkB d b = true) :
    ir.BatchOk d b ∧ (ir.batch b).operands = .columns := by
  simp only [colsBatchOkB, Bool.and_eq_true, beq_iff_eq, batchOkB_iff] at h
  exact h

/-- A covered batch on bits passes the check, its parts with forms at `bitsAtomB`. -/
theorem bitsBatchOk {d b : ℕ} (h : ir.bitsBatchOkB d b = true) :
    ir.BatchOk d b ∧ (ir.batch b).operands = .bits := by
  simp only [bitsBatchOkB, Bool.and_eq_true, beq_iff_eq, batchOkB_iff] at h
  exact h

/-- The parts of a covered batch on columns have forms at `atomB`. -/
theorem partsOk_of_cols {d b : ℕ} (h : ir.colsBatchOkB d b = true) : ir.PartsOk ir.atomB d b := by
  obtain ⟨hb, ho⟩ := colsBatchOk h
  have := hb.partsOk
  simp only [atomOf, ho] at this
  exact this

/-- The parts of a covered batch on bits have forms at `bitsAtomB`. -/
theorem partsOk_of_bits {d b : ℕ} (h : ir.bitsBatchOkB d b = true) :
    ir.PartsOk (ir.bitsAtomB d) d b := by
  obtain ⟨hb, ho⟩ := bitsBatchOk h
  have := hb.partsOk
  simp only [atomOf, ho] at this
  exact this

/-! ### The variables of a bit operand -/

variable (ir) in
/-- **The variables of a bit operand** of domain `d`: the cells, the bits of the cells, and the
statement's coordinates. -/
abbrev BitsVar (d : ℕ) : Type := ir.Cell d ⊕ (ir.Cell d × Fin 16) ⊕ (ℕ × ℕ)

variable (I) in
/-- **The valuation of the variables of a bit operand** `z`: the committed values read from the
cells (through the realized assignment), the bit views from the cells' bits (`bitValuation`), the
statement from the statement's coordinates; no challenge and no late value. -/
def bitsReader (d : ℕ) (z : ir.BitsVar d → (I (ir.domainField d)).K) : ir.Valuation I :=
  ir.bitValuation I d
    (ir.reader ⟨fun v i => castElt (z (.inr (.inr (v, i)))),
      ir.bindAsg (ir.ofCells I d (z ∘ Sum.inl)), fun _ _ => 0, 0⟩)
    (z ∘ Sum.inr ∘ Sum.inl)

/-- A statement value read by the reader of an environment: the statement's coordinate. -/
theorem reader_of_input (e : ir.Env I) {v : ℕ} (hk : (ir.value v).kind = .pub .input) :
    ir.reader e v = e.stmt v := by
  funext i
  simp [reader, fuel, read, hk]

/-- An opaque value of no argument read by the reader of an environment: the statement's
coordinate. -/
theorem reader_of_opaque_nil (e : ir.Env I) {v : ℕ} {name : String}
    (hk : (ir.value v).kind = .pub (.opaque name [])) : ir.reader e v = e.stmt v := by
  funext i
  simp [reader, fuel, read, hk]

/-- **The variables' valuation is affine, or constant, at every value a bit operand may read**:
a cell's value or zero, a bit variable or a constant, a statement coordinate, a constant. -/
theorem leafOk_bitsReader {d v : ℕ} (hv : ir.bitsLeafOk d v = true) :
    LeafOk ir (f := ir.domainField d) (ir.bitsReader I d) ir.bitsNd v := by
  unfold bitsLeafOk at hv
  split at hv
  · rename_i hk
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [bitsReader, bitValuation, hk, reader_of_priv _ hk,
        ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl), ofCells, castElt_dite,
        castElt_castElt]
      exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ =>
        (isConst_const _).isAff
    · simp [bitsNd, hk] at h0
  · rename_i u m hk
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [bitsReader, bitValuation, hk, reader_of_padCopy _ hk,
        ir.bindAsg_val_of_isBound (v := v) _ (by rw [hk]; rfl), ofCells, castElt_dite,
        castElt_castElt]
      exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ =>
        (isConst_const _).isAff
    · simp [bitsNd, hk] at h0
  · rename_i es hk
    have hc : IsConst fun z => ir.bitsReader I d z v := fun z z' => by
      funext i
      simp only [bitsReader, bitValuation, hk, reader_of_constant _ hk]
    exact ⟨fun _ i => (hc.comp fun g => (castElt (g i) : (I (ir.domainField d)).K)).isAff,
      fun _ => hc⟩
  · rename_i w sel hk
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [bitsReader, bitValuation, hk, wordBit, castElt_dite, castElt_castElt]
      exact IsAff.dite _ (fun _ => IsAff.ite _ (isAff_proj _) isAff_zero) fun _ =>
        (isConst_const _).isAff
    · simp [bitsNd, hk] at h0
  · rename_i hk
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [bitsReader, bitValuation, hk, reader_of_input _ hk, castElt_castElt]
      exact IsAff.ite _ (isAff_proj _) isAff_zero
    · simp [bitsNd, hk] at h0
  · rename_i name hk
    refine ⟨fun _ i => ?_, fun h0 => ?_⟩
    · simp only [bitsReader, bitValuation, hk, reader_of_opaque_nil _ hk, castElt_castElt]
      exact IsAff.ite _ (isAff_proj _) isAff_zero
    · simp [bitsNd, hk] at h0
  · cases hv

/-- **An atom of a bit operand is affine in its variables.** -/
theorem isAff_bitsAtom {d : ℕ} {a : Expr} (ha : ir.bitsAtomB d a = true) (i : ℕ) :
    IsAff fun z => ir.evalWith (ir.bitsReader I d z) d a i := by
  simp only [bitsAtomB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, decide_eq_true_eq] at ha
  exact evalE_isAff (fun v hv => leafOk_bitsReader (ha.1.1 v hv)) ha.1.2 ha.2 i

/-- **An operand of atoms of bit operands is affine in its variables.** -/
theorem isAff_bitsOperand {d : ℕ} {o : BOperand}
    (ho : (∃ a, o = .atom a ∧ ir.bitsAtomB d a = true) ∨
      (∃ ts, o = .lin ts ∧ ∀ t ∈ ts, ir.bitsAtomB d t.2 = true) ∨ o = .zero) (i : ℕ) :
    IsAff fun z => ir.opValAt I d (ir.bitsReader I d z) o i := by
  rcases ho with ⟨a, rfl, ha⟩ | ⟨ts, rfl, hts⟩ | rfl
  · exact isAff_bitsAtom ha i
  · exact IsAff.list_sum ts fun t ht => IsAff.const_mul (isConst_const _) (isAff_bitsAtom (hts t ht) i)
  · exact (isConst_const _).isAff

variable (I) in
/-- **The variables of the cells `a`** at the statement `x`: the cells, their bits
(`cellBits`), the statement's coordinates. -/
def bitsLift (d : ℕ) (x : ir.Valuation I) (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.BitsVar d → (I (ir.domainField d)).K :=
  Sum.elim a (Sum.elim (ir.cellBits I d a) fun vi => castElt (x vi.1 vi.2))

/-- **At the variables of the cells, the variables' valuation is the cells' valuation** at every
value a bit operand may read (`bitValuation_cellBits` at a bit view). -/
theorem bitsReader_bitsLift {d v : ℕ} (hv : ir.bitsLeafOk d v = true) (x : ir.Valuation I)
    (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.bitsReader I d (ir.bitsLift I d x a) v = ir.cellValuation I d x r a v := by
  unfold bitsLeafOk at hv
  split at hv
  · rename_i hk
    funext i
    simp only [bitsReader, bitValuation, hk, reader_of_priv _ hk, cellValuation, layoutEnv]
    rfl
  · rename_i u m hk
    funext i
    simp only [bitsReader, bitValuation, hk, reader_of_padCopy _ hk, cellValuation, layoutEnv]
    rfl
  · rename_i es hk
    funext i
    simp only [bitsReader, bitValuation, hk, reader_of_constant _ hk, cellValuation]
  · exact bitValuation_cellBits hv _ x r a
  · rename_i hk
    have hd : ir.domainField d = ir.valueField v := by
      simp only [beq_iff_eq] at hv
      rw [ir.valueField_of_allowsField (v := v) (by rw [hk]; rfl), hv]
    funext i
    simp only [bitsReader, bitValuation, hk, reader_of_input _ hk, cellValuation, layoutEnv,
      bitsLift, Sum.elim_inr]
    exact castElt_castElt_of_eq hd.symm _
  · rename_i name hk
    have hd : ir.domainField d = ir.valueField v := by
      simp only [beq_iff_eq] at hv
      rw [ir.valueField_of_allowsField (v := v) (by rw [hk]; rfl), hv]
    funext i
    simp only [bitsReader, bitValuation, hk, reader_of_opaque_nil _ hk, cellValuation, layoutEnv,
      bitsLift, Sum.elim_inr]
    exact castElt_castElt_of_eq hd.symm _
  · cases hv

/-- **An operand of atoms is read alike** at the variables of the cells and by the cells'
valuation. -/
theorem opValAt_bitsLift {d : ℕ} {o : BOperand}
    (ho : (∃ a, o = .atom a ∧ ir.bitsAtomB d a = true) ∨
      (∃ ts, o = .lin ts ∧ ∀ t ∈ ts, ir.bitsAtomB d t.2 = true) ∨ o = .zero) (x : ir.Valuation I)
    (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K) (i : ℕ) :
    ir.opValAt I d (ir.bitsReader I d (ir.bitsLift I d x a)) o i =
      ir.opValAt I d (ir.cellValuation I d x r a) o i := by
  have hat : ∀ e, ir.bitsAtomB d e = true →
      ir.evalWith (ir.bitsReader I d (ir.bitsLift I d x a)) d e =
        ir.evalWith (ir.cellValuation I d x r a) d e := fun e he => by
    simp only [bitsAtomB, Bool.and_eq_true, List.all_eq_true] at he
    exact evalE_congr fun v hv => bitsReader_bitsLift (he.1.1 v hv) x r a
  rcases ho with ⟨e, rfl, he⟩ | ⟨ts, rfl, hts⟩ | rfl
  · simp only [opValAt, BOperand.val, hat e he]
  · simp only [opValAt, BOperand.val]
    exact sum_map_congr fun t ht => by rw [hat t.2 (hts t ht)]
  · rfl

/-- **The variables of the cells split**: at the statement `x`, those of the cells at the zero
statement plus those of the zero cells at `x`, when the bits of `0` are `0`. -/
theorem bitsLift_split {d : ℕ} (hadd : (I (ir.domainField d)).BitsAdditive) (x : ir.Valuation I)
    (a : ir.Cell d → (I (ir.domainField d)).K) :
    ir.bitsLift I d x a = ir.bitsLift I d 0 a + ir.bitsLift I d x 0 := by
  funext z
  rcases z with k | kj | vi
  · simp [bitsLift]
  · simp [bitsLift, cellBits, cellBit, hadd.ofBool_zero]
  · simp [bitsLift]

/-- **The variables of the cells are additive at the zero statement**, when the field's bit
coordinates are additive. -/
theorem bitsLift_add {d : ℕ} (hadd : (I (ir.domainField d)).BitsAdditive)
    (a a' : ir.Cell d → (I (ir.domainField d)).K) :
    ir.bitsLift I d 0 (a + a') = ir.bitsLift I d 0 a + ir.bitsLift I d 0 a' := by
  funext z
  rcases z with k | kj | vi
  · simp [bitsLift]
  · simp [bitsLift, cellBits, cellBit, hadd _ _ (a kj.1) (a' kj.1)]
  · simp [bitsLift]

/-- The variables of the zero cells at the zero statement are zero. -/
theorem bitsLift_zero {d : ℕ} (hadd : (I (ir.domainField d)).BitsAdditive) :
    ir.bitsLift I d 0 0 = 0 := by
  funext z
  rcases z with k | kj | vi
  · simp [bitsLift]
  · simp [bitsLift, cellBits, cellBit, hadd.ofBool_zero]
  · simp [bitsLift]

/-! ### The batched relation of a batch on bits -/

variable (I) in
/-- **Operand `o` of instance `t` of batch `b` on bits** at the variables `z`. -/
def bitsOperandAt (d b : ℕ) (t : Σ j : Fin (ir.batch b).parts.length, Fin (ir.partLen d b j))
    (o : ℕ) (z : ir.BitsVar d → (I (ir.domainField d)).K) : (I (ir.domainField d)).K :=
  ir.opValAt I d (ir.bitsReader I d z) (ir.instOperand (ir.bitsAtomB d) d b t.1 o) t.2

/-- **The operands of a covered batch on bits are affine** in the variables. -/
theorem isAff_bitsOperandAt {d b : ℕ} (hb : ir.PartsOk (ir.bitsAtomB d) d b)
    (t : Σ j : Fin (ir.batch b).parts.length, Fin (ir.partLen d b j)) (o : ℕ) :
    IsAff (ir.bitsOperandAt I d b t o) := by
  obtain ⟨e, e', pf, -, hpf, hsh, hops⟩ := hb.exists_part t.1
  have hk : (ir.partShape (ir.bitsAtomB d) d b t.1).k = pf.operands.length := by rw [hsh]; rfl
  exact isAff_bitsOperand (instOperand_atoms hpf hops hk o) t.2

variable (I) in
/-- **The additive part of an operand of a covered batch on bits**: its value at the variables of
the cells at the zero statement, minus its value at zero; additive when the field's bit
coordinates are (`bitsLift_add`, `isAff_bitsOperandAt`). -/
def bitsAddPart {d b : ℕ} (hb : ir.bitsBatchOkB d b = true)
    (hadd : (I (ir.domainField d)).BitsAdditive)
    (t : Σ j : Fin (ir.batch b).parts.length, Fin (ir.partLen d b j))
    (o : Fin (ir.relShape (ir.bitsAtomB d) d b).k) :
    (ir.Cell d → (I (ir.domainField d)).K) →+ (I (ir.domainField d)).K where
  toFun a := ir.bitsOperandAt I d b t o (ir.bitsLift I d 0 a) - ir.bitsOperandAt I d b t o 0
  map_zero' := by
    simp only [bitsLift_zero hadd, sub_self]
  map_add' a a' := by
    obtain ⟨l, c, h⟩ := isAff_bitsOperandAt (I := I) (partsOk_of_bits hb) t o
    simp only [bitsLift_add hadd, h, map_add, map_zero]
    ring

variable (I) in
/-- **The batched relation of batch `b` on bits** on the cells of domain `d`, for a covered batch
when the field's bit coordinates are additive: the relation of the batch's shape (`relShape`); the
instances every coordinate of every part; operand `o` of an instance its additive part
(`bitsAddPart`), its offset its value at the zero cells and the statement. -/
def bitsBatchRelation (d b : ℕ) (hb : ir.bitsBatchOkB d b = true)
    (hadd : (I (ir.domainField d)).BitsAdditive) :
    BatchRelation (ir.Valuation I) (I (ir.domainField d)).K (ir.Cell d) where
  arity := (ir.relShape (ir.bitsAtomB d) d b).k
  Q := (ir.relShape (ir.bitsAtomB d) d b).evalFin
  Inst := Σ j : Fin (ir.batch b).parts.length, Fin (ir.partLen d b j)
  operand t o := ir.bitsAddPart I hb hadd t o
  offset x t o := ir.bitsOperandAt I d b t o (ir.bitsLift I d x 0)

/-- **An operand plus its offset is the operand at the variables of the cells** (`bitsLift_split`,
the operand affine). -/
theorem bitsBatchRelation_operand {d b : ℕ} (hb : ir.bitsBatchOkB d b = true)
    (hadd : (I (ir.domainField d)).BitsAdditive) (x : ir.Valuation I)
    (a : ir.Cell d → (I (ir.domainField d)).K)
    (t : Σ j : Fin (ir.batch b).parts.length, Fin (ir.partLen d b j))
    (o : Fin (ir.relShape (ir.bitsAtomB d) d b).k) :
    (ir.bitsBatchRelation I d b hb hadd).operand t o a +
        (ir.bitsBatchRelation I d b hb hadd).offset x t o =
      ir.bitsOperandAt I d b t o (ir.bitsLift I d x a) := by
  obtain ⟨l, c, h⟩ := isAff_bitsOperandAt (I := I) (partsOk_of_bits hb) t o
  change (ir.bitsOperandAt I d b t o (ir.bitsLift I d 0 a) - ir.bitsOperandAt I d b t o 0) +
    ir.bitsOperandAt I d b t o (ir.bitsLift I d x 0) = _
  rw [bitsLift_split hadd x a, h, h, h, h, map_add, map_zero]
  ring

/-- **The batched relation on bits at an instance of part `j` is the part's shape** on the part's
operands at the cells' valuation (`bitsBatchRelation_operand`, `opValAt_bitsLift`). -/
theorem bitsBatchRelation_Q_cellValuation {d b : ℕ} (hb : ir.bitsBatchOkB d b = true)
    (hadd : (I (ir.domainField d)).BitsAdditive) (j : Fin (ir.batch b).parts.length)
    {e e' : Expr} {pf : PartForm} (hs : ir.partSides d b j = some (e, e'))
    (hpf : ir.partForm (ir.bitsAtomB d) e e' = some pf)
    (x : ir.Valuation I) (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K)
    (i : Fin (ir.partLen d b j)) :
    (ir.bitsBatchRelation I d b hb hadd).Q (fun o =>
        (ir.bitsBatchRelation I d b hb hadd).operand ⟨j, i⟩ o a +
          (ir.bitsBatchRelation I d b hb hadd).offset x ⟨j, i⟩ o) =
      pf.shape.evalAt
        (fun o => ir.opValAt I d (ir.cellValuation I d x r a) (pf.operands.getD o default) i) := by
  have hpo := partsOk_of_bits hb
  have hsh : ir.partShape (ir.bitsAtomB d) d b j = pf.shape := by
    simp [partShape, partFormAt, hs, hpf]
  have hops : ir.partOperands (ir.bitsAtomB d) d b j = pf.operands := by
    simp [partOperands, partFormAt, hs, hpf]
  have hk : (ir.partShape (ir.bitsAtomB d) d b j).k = pf.operands.length := by rw [hsh]; rfl
  have hval : (fun o : Fin (ir.relShape (ir.bitsAtomB d) d b).k =>
      (ir.bitsBatchRelation I d b hb hadd).operand ⟨j, i⟩ o a +
          (ir.bitsBatchRelation I d b hb hadd).offset x ⟨j, i⟩ o) =
        fun o : Fin (ir.relShape (ir.bitsAtomB d) d b).k => ir.opValAt I d
          (ir.cellValuation I d x r a) (ir.instOperand (ir.bitsAtomB d) d b j o) i := by
    funext o
    rw [bitsBatchRelation_operand hb hadd x a, bitsOperandAt]
    exact opValAt_bitsLift (instOperand_atoms hpf hops hk o) x r a i
  calc (ir.bitsBatchRelation I d b hb hadd).Q _
      = (ir.relShape (ir.bitsAtomB d) d b).evalFin (fun o : Fin (ir.relShape (ir.bitsAtomB d) d b).k =>
          ir.opValAt I d (ir.cellValuation I d x r a) (ir.instOperand (ir.bitsAtomB d) d b j o) i) := by
        rw [← hval]
        rfl
    _ = _ := by
        rw [evalFin_instOperand hpo
            (fun op => ir.opValAt I d (ir.cellValuation I d x r a) op i) rfl j,
          relShape_evalAt_instOperand hpo
            (fun op => ir.opValAt I d (ir.cellValuation I d x r a) op i) rfl j, hsh, hops]

/-- **The batched relation on bits at an instance of part `j` is the part's shape** on the part's
operands read from the variables of the cells at the statement (`bitsBatchRelation_operand`,
`relShape_evalAt_instOperand`). -/
theorem bitsBatchRelation_Q {d b : ℕ} (hb : ir.bitsBatchOkB d b = true)
    (hadd : (I (ir.domainField d)).BitsAdditive) (j : Fin (ir.batch b).parts.length)
    (x : ir.Valuation I) (a : ir.Cell d → (I (ir.domainField d)).K) (i : Fin (ir.partLen d b j)) :
    (ir.bitsBatchRelation I d b hb hadd).Q (fun o =>
        (ir.bitsBatchRelation I d b hb hadd).operand ⟨j, i⟩ o a +
          (ir.bitsBatchRelation I d b hb hadd).offset x ⟨j, i⟩ o) =
      (ir.partShape (ir.bitsAtomB d) d b j).evalAt (fun o =>
        ir.opValAt I d (ir.bitsReader I d (ir.bitsLift I d x a))
          ((ir.partOperands (ir.bitsAtomB d) d b j).getD o default) i) := by
  have hpo := partsOk_of_bits hb
  have hval : (fun o : Fin (ir.relShape (ir.bitsAtomB d) d b).k =>
      (ir.bitsBatchRelation I d b hb hadd).operand ⟨j, i⟩ o a +
          (ir.bitsBatchRelation I d b hb hadd).offset x ⟨j, i⟩ o) =
        fun o : Fin (ir.relShape (ir.bitsAtomB d) d b).k => ir.opValAt I d
          (ir.bitsReader I d (ir.bitsLift I d x a)) (ir.instOperand (ir.bitsAtomB d) d b j o) i := by
    funext o
    rw [bitsBatchRelation_operand hb hadd x a]
    rfl
  calc (ir.bitsBatchRelation I d b hb hadd).Q _
      = (ir.relShape (ir.bitsAtomB d) d b).evalFin (fun o : Fin (ir.relShape (ir.bitsAtomB d) d b).k =>
          ir.opValAt I d (ir.bitsReader I d (ir.bitsLift I d x a))
            (ir.instOperand (ir.bitsAtomB d) d b j o) i) := by
        rw [← hval]
        rfl
    _ = _ := (evalFin_instOperand hpo
        (fun op => ir.opValAt I d (ir.bitsReader I d (ir.bitsLift I d x a)) op i) rfl j).trans
      (relShape_evalAt_instOperand hpo
        (fun op => ir.opValAt I d (ir.bitsReader I d (ir.bitsLift I d x a)) op i) rfl j)

/-- **An instance of the batched relation on bits is its part's field equation**: at coordinate `i`
of part `j`, the relation on the operands plus their offsets is `e − e'` at the cells' valuation,
when the program's fields decode `0` to `0` (`hz`, a property of the model). -/
theorem bitsBatchRelation_instance (hz : ir.ZeroDecodes I) {d b : ℕ}
    (hb : ir.bitsBatchOkB d b = true)
    (hadd : (I (ir.domainField d)).BitsAdditive) (j : Fin (ir.batch b).parts.length)
    {e e' : Expr} {pf : PartForm} (hs : ir.partSides d b j = some (e, e'))
    (hpf : ir.partForm (ir.bitsAtomB d) e e' = some pf)
    (x : ir.Valuation I) (r : (ir.layout I).Run) (a : ir.Cell d → (I (ir.domainField d)).K)
    (i : Fin (ir.partLen d b j)) :
    (ir.bitsBatchRelation I d b hb hadd).Q (fun o =>
        (ir.bitsBatchRelation I d b hb hadd).operand ⟨j, i⟩ o a +
          (ir.bitsBatchRelation I d b hb hadd).offset x ⟨j, i⟩ o) =
      ir.evalWith (ir.cellValuation I d x r a) d e i -
        ir.evalWith (ir.cellValuation I d x r a) d e' i := by
  rw [bitsBatchRelation_Q_cellValuation hb hadd j hs hpf x r a i]
  exact (partForm_eval (leaf := ir.cellValuation I d x r a)
    (ref := ir.refVal (ir.cellValuation I d x r a) ir.exprs.length (ir.domainField d))
    (rl := ir.refLen ir.exprs.length) (fun _ ha i => eval_cellValuation_zeroLeaf hz ha i) hpf i).symm

/-- **The batched relation on bits reads the cells through their valuation**: at cells of one
valuation, it holds at both or at neither. -/
theorem bitsBatchRelation_holds_congr {d b : ℕ} (hb : ir.bitsBatchOkB d b = true)
    (hadd : (I (ir.domainField d)).BitsAdditive) {x : ir.Valuation I}
    {r r' : (ir.layout I).Run} {a a' : ir.Cell d → (I (ir.domainField d)).K}
    (h : ir.cellValuation I d x r a = ir.cellValuation I d x r' a') :
    (ir.bitsBatchRelation I d b hb hadd).Holds x a ↔
      (ir.bitsBatchRelation I d b hb hadd).Holds x a' := by
  refine forall_congr' fun t => ?_
  obtain ⟨j, i⟩ := t
  obtain ⟨e, e', pf, hs, hpf, -, -⟩ := (partsOk_of_bits hb).exists_part j
  rw [bitsBatchRelation_Q_cellValuation hb hadd j hs hpf x r a i,
    bitsBatchRelation_Q_cellValuation hb hadd j hs hpf x r' a' i, h]

/-- **The batched relation on bits holds exactly when every part placed holds** at the cells'
valuation (`PlacedHolds`), for a covered batch when the field's bit coordinates are additive and
the program's fields decode `0` to `0`. -/
theorem bitsBatchRelation_holds_iff (hz : ir.ZeroDecodes I) {d b : ℕ}
    (hb : ir.bitsBatchOkB d b = true)
    (hadd : (I (ir.domainField d)).BitsAdditive) (x : ir.Valuation I) (r : (ir.layout I).Run)
    (a : ir.Cell d → (I (ir.domainField d)).K) :
    (ir.bitsBatchRelation I d b hb hadd).Holds x a ↔
      ∀ p ∈ (ir.batch b).parts, ir.PlacedHolds (ir.cellValuation I d x r a) (ir.predicate p).body := by
  have hok := partsOk_of_bits hb
  have hpred : ∀ n (hn : n < (ir.batch b).parts.length), ir.partPred b n = (ir.batch b).parts[n] :=
    fun n hn => List.getD_eq_getElem _ _ hn
  constructor
  · intro h p hp
    obtain ⟨n, hn, rfl⟩ := List.mem_iff_getElem.1 hp
    obtain ⟨e, e', pf, hs, hpf, -, -⟩ := hok.exists_part ⟨n, hn⟩
    have hs' := hs
    simp only [partSides, hpred n hn] at hs'
    rw [placedHolds_iff_of_batchSides hs']
    intro i hi
    have hlen : ir.partLen d b n = ir.exprLen e := by simp [partLen, hs]
    have := h ⟨⟨n, hn⟩, ⟨i, by rw [hlen]; exact hi⟩⟩
    rw [bitsBatchRelation_instance hz hb hadd ⟨n, hn⟩ hs hpf x r a] at this
    exact sub_eq_zero.1 this
  · rintro h ⟨j, i⟩
    obtain ⟨e, e', pf, hs, hpf, -, -⟩ := hok.exists_part j
    rw [bitsBatchRelation_instance hz hb hadd j hs hpf x r a, sub_eq_zero]
    have hs' := hs
    simp only [partSides, hpred j j.2] at hs'
    have hlen : ir.partLen d b j = ir.exprLen e := by simp [partLen, hs]
    exact (placedHolds_iff_of_batchSides hs' _).1 (h _ (List.getElem_mem _)) i (hlen ▸ i.2)

/-! ## Quadratic triples -/

variable (ir) in
/-- **A cell of domain `d`'s quadratic test** (answer 11): a committed value of `d`, of kind `priv`
and phase `0`, typed `Field`, at no node (a root cell). -/
def quadCellB (d v : ℕ) : Bool :=
  ir.isCellValue d v && (ir.value v).phase == 0 && (ir.value v).type == .field &&
    (ir.value v).node.isNone &&
    match (ir.value v).kind with
    | .priv => true
    | _ => false

variable (ir) in
/-- **The cells of quadratic predicate `p` of domain `d`**: `a · b = c` with target `quadratic` on
cells of the quadratic test (`quadCellB`). -/
def quadLeaves (d p : ℕ) : Option (ℕ × ℕ × ℕ) :=
  match (ir.predicate p).body with
  | .equal d' (.mul (.leaf a) (.leaf b)) (.leaf c) .quadratic =>
    if d' = d ∧ ir.quadCellB d a = true ∧ ir.quadCellB d b = true ∧ ir.quadCellB d c = true then
      some (a, b, c) else none
  | _ => none

variable (ir) in
/-- **Predicate `p` is a quadratic triple of domain `d`** (`quadLeaves`). -/
def isQuad (d p : ℕ) : Bool := (ir.quadLeaves d p).isSome

end

end GordieHowe.RealizedProgram
