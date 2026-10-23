-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.FieldSkipPads

@[expose] public section

/-!
# Relations as monomials: pad products and the honest round messages at any degree

The C++ batch driver (`lib/gordiehowe/compiler/field_skip.h`, `MaskedFieldSkip`; `batch.h`, `BatchKernel`)
proves a relation given as a list of monomials (`FieldRelation`): each a coefficient and the
operands its factors read, with repetition, none constant. This file states that representation
and the two computations of the masked skip that depend on it, at any degree `D`:

* **The relation** (`MonoRelation K k D`, extending its shape `MonoShape k`): the monomials, each
  a coefficient, a degree between `1` and `D` and its factors' operands (`FieldRelation::error`:
  no constant monomial, so the zero rows that pad the instances satisfy it). Its value `eval` is
  the C++ `FieldRelation::eval`; its polynomial `poly` makes it a `FieldSkip.Relation K k D`
  (`toRelation`). **Merging** (`merge`, `FieldOperands::relation(gamma)`): parts on one operand
  vector (the C++ concatenates the parts' operands; here each part reads its own operands of the
  shared vector), part `p`'s coefficients scaled by `γ^p`. The merged shape does not depend on `γ`.
* **The pad products** (`PadLayout`): the masked terminal check `claim = eq(ρ, s) · Q(m − P)`
  expands `Q(m − P)` over the terminal pads `P`, and a monomial's product of two or more pads is a
  committed product cell (`field_skip.h`, `terminal_expr`, `pad_monomials`). Each product cell is
  one quadratic triple (`pad_quadratic`): a smaller product or a terminal pad, times a terminal
  pad. A layout records the triples (`left`, `right`), the multiset of terminal pads each cell
  holds (`mono`), and for every monomial and nonempty set of its factors the coordinate holding the
  factors' pad product (`cell`: a terminal pad for one factor, a product cell otherwise). When the
  triples hold (`TriplesHold`), every cell holds its multiset's product (`read_eq_prod`), and
  `Q(m − P) = Q(m) + padTerm m` (`eval_sub_eq`), the pad term linear in the cells. The honest
  product values are `fill` (`fill_pads`).
* **The honest round messages at degree `D`** (`honestRoundsMono`, `MaskedFieldSkip::prove`):
  each round's coefficients `1, …, D` of `Σ_x eq(ρ_{>i}, x) Q(a(x) + X d(x))` by field operations
  (`round_sums`: per monomial the coefficients of a product of lines, `lineProdCoeff`); equal to
  `EqFactoredDeg.honest` (`honestRoundsMono_eq`). The whole honest transcript by field operations
  is `SkipRelation.honestT` (`GordieHowe/ProofSystem/Zerocheck/FieldSkipMasked.lean`).
-/

namespace GordieHowe.Sumcheck.FieldSkip

open Polynomial

/-! ### Monomial relations -/

/-- **The shape of a relation's monomials** (`field_skip.h`, `FieldRelation::monomials`, in order;
`Monomial::ops`): `nm` monomials, each with its degree and the operand each factor reads (operands
may repeat). -/
structure MonoShape (k : ℕ) where
  /-- The number of monomials. -/
  nm : ℕ
  /-- The degree of each monomial. -/
  deg : Fin nm → ℕ
  /-- The operand of each factor. -/
  ops : (i : Fin nm) → Fin (deg i) → Fin k

/-- **A relation as monomials** (`field_skip.h`, `FieldRelation`): a shape, a coefficient per
monomial, every monomial of degree between `1` and `D` (`FieldRelation::error`: "monomial i is
constant; Q has no constant term"). -/
structure MonoRelation (K : Type) (k D : ℕ) extends MonoShape k where
  /-- The coefficient of each monomial. -/
  coeff : Fin nm → K
  /-- No monomial is constant. -/
  deg_pos : ∀ i, 0 < deg i
  /-- Every monomial has degree at most `D`. -/
  deg_le : ∀ i, deg i ≤ D

namespace MonoRelation

variable {K : Type} [Field K] {k D : ℕ} (R : MonoRelation K k D)

/-- The relation's value on operands `x` (`FieldRelation::eval`). -/
def eval (x : Fin k → K) : K := ∑ i, R.coeff i * ∏ t, x (R.ops i t)

/-- The relation's polynomial. -/
noncomputable def poly : MvPolynomial (Fin k) K :=
  ∑ i, MvPolynomial.C (R.coeff i) * ∏ t, MvPolynomial.X (R.ops i t)

theorem eval_poly (x : Fin k → K) : MvPolynomial.eval x R.poly = R.eval x := by
  simp [poly, eval]

theorem totalDegree_poly_le : R.poly.totalDegree ≤ D := by
  refine MvPolynomial.totalDegree_finsetSum_le fun i _ => ?_
  refine (MvPolynomial.totalDegree_mul _ _).trans ?_
  rw [MvPolynomial.totalDegree_C, zero_add]
  refine (MvPolynomial.totalDegree_finsetProd _ _).trans ?_
  simp only [MvPolynomial.totalDegree_X, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_eq_mul, mul_one]
  exact R.deg_le i

theorem constantCoeff_poly : MvPolynomial.constantCoeff R.poly = 0 := by
  simp only [poly, map_sum, map_mul, map_prod, MvPolynomial.constantCoeff_X]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [Finset.prod_eq_zero (Finset.mem_univ ⟨0, R.deg_pos i⟩) rfl, mul_zero]

/-- **The relation as a `FieldSkip.Relation`** of degree `D`. -/
noncomputable def toRelation : Relation K k D where
  Q := R.poly
  totalDegree_le := R.totalDegree_poly_le
  constantCoeff_eq := R.constantCoeff_poly

theorem eval_toRelation (x : Fin k → K) : MvPolynomial.eval x R.toRelation.Q = R.eval x :=
  R.eval_poly x

/-- **The batch holds** exactly when the relation's value vanishes on every instance. -/
theorem holds_toRelation_iff {w n : ℕ} (ops : Operands K w n k) :
    Holds R.toRelation ops ↔ ∀ r z, R.eval (ops r z) = 0 := by
  simp only [Holds, residual, eval_toRelation]

/-- A relation vanishes on zero operands. -/
theorem eval_zero : R.eval 0 = 0 := by
  rw [← eval_toRelation]
  exact R.toRelation.eval_zero_Q

/-! ### Merging -/

/-- **The merged shape** of parts on one operand vector: the parts' monomials in order
(`FieldOperands::relation`), through `finSigmaFinEquiv`. -/
def mergeShape {np : ℕ} (Rs : Fin np → MonoRelation K k D) : MonoShape k where
  nm := ∑ p, (Rs p).nm
  deg m := (Rs (finSigmaFinEquiv.symm m).1).deg (finSigmaFinEquiv.symm m).2
  ops m := (Rs (finSigmaFinEquiv.symm m).1).ops (finSigmaFinEquiv.symm m).2

/-- **The merged relation** `Σ_p γ^p Q_p` of parts on one operand vector (`batch.h`,
`FieldOperands::relation(gamma)`: the parts' monomials in order, part `p`'s coefficients scaled by
`γ^p`). Its shape is `mergeShape`, whatever `γ`. -/
def merge {np : ℕ} (Rs : Fin np → MonoRelation K k D) (γ : K) : MonoRelation K k D where
  toMonoShape := mergeShape Rs
  coeff m := γ ^ (finSigmaFinEquiv.symm m).1.val *
    (Rs (finSigmaFinEquiv.symm m).1).coeff (finSigmaFinEquiv.symm m).2
  deg_pos _ := (Rs _).deg_pos _
  deg_le _ := (Rs _).deg_le _

theorem eval_merge {np : ℕ} (Rs : Fin np → MonoRelation K k D) (γ : K) (x : Fin k → K) :
    (merge Rs γ).eval x = ∑ p, γ ^ p.val * (Rs p).eval x := by
  simp only [eval, Finset.mul_sum]
  refine (Fintype.sum_equiv (finSigmaFinEquiv (n := fun p => (Rs p).nm)).symm _
    (fun σ : (Σ p, Fin (Rs p).nm) =>
      γ ^ σ.1.val * ((Rs σ.1).coeff σ.2 * ∏ t, x ((Rs σ.1).ops σ.2 t)))
    fun _ => mul_assoc _ _ _).trans ?_
  exact Fintype.sum_sigma _

/-- The merged relation's value is `FieldSkip.merge`'s at the parts' polynomials. -/
theorem eval_merge_poly {np : ℕ} (Rs : Fin np → MonoRelation K k D) (γ : K) (x : Fin k → K) :
    (merge Rs γ).eval x = MvPolynomial.eval x (FieldSkip.merge (fun p => (Rs p).poly) γ) := by
  rw [eval_merge, FieldSkip.eval_merge]
  simp only [eval_poly]

/-- The merged shape does not depend on `γ`. -/
theorem merge_toMonoShape {np : ℕ} (Rs : Fin np → MonoRelation K k D) (γ : K) :
    (merge Rs γ).toMonoShape = mergeShape Rs := rfl

end MonoRelation

/-! ### The pad products -/

/-- The multiset of terminal pads a coordinate holds: `{j}` for terminal pad `j`, `mono c` for
product cell `c`. -/
def monoOf {k : ℕ} {C : Type} (mono : C → Multiset (Fin k)) : Fin k ⊕ C → Multiset (Fin k)
  | .inl j => {j}
  | .inr c => mono c

/-- **The product cells of a masked skip** for a monomial shape `S` (`field_skip.h`,
`pad_monomials` and `pad_quadratic`): cells `C`, each one quadratic triple `left c · right c = c`
of a terminal pad or smaller product cell and a terminal pad, holding the product of the terminal
pads in its multiset `mono c`; and for every monomial `i` and choice `x` of a pad (`1`) or a sent
value (`0`) per factor, with some pad, the coordinate holding the chosen factors' pads (`cell i x`:
the terminal pad of a single factor, a product cell for two or more; `terminal_expr`'s masks). -/
structure PadLayout {k : ℕ} (S : MonoShape k) (C : Type) where
  /-- The multiset of terminal pads each product cell holds. -/
  mono : C → Multiset (Fin k)
  /-- The triple's first factor: a terminal pad or a product cell. -/
  left : C → Fin k ⊕ C
  /-- The triple's second factor: a terminal pad. -/
  right : C → Fin k
  /-- A cell's multiset is its first factor's with the second added. -/
  mono_eq : ∀ c, mono c = right c ::ₘ monoOf mono (left c)
  /-- The coordinate of a monomial's chosen factors' pads. -/
  cell : (i : Fin S.nm) → (Fin (S.deg i) → Fin 2) → Fin k ⊕ C
  /-- It holds the pads of the chosen factors. -/
  monoOf_cell : ∀ i x, x ≠ 0 →
    monoOf mono (cell i x) = (Finset.univ.filter fun t => x t = 1).val.map (S.ops i)

namespace PadLayout

variable {K : Type} [Field K] {k : ℕ} {C : Type} {S : MonoShape k} (L : PadLayout S C)

/-- **The pads' quadratic constraints** (`pad_quadratic`) on terminal pads `P` and product cells
`Pr`: each product cell is its first factor times its second. -/
def TriplesHold (P : Fin k → K) (Pr : C → K) : Prop :=
  ∀ c, Sum.elim P Pr (L.left c) * P (L.right c) = Pr c

/-- **The honest product cells** of terminal pads `P` (`fill_pads`): each the product of its
multiset's pads. -/
def fill (P : Fin k → K) : C → K := fun c => ((L.mono c).map P).prod

/-- A coordinate's value at the honest product cells is its multiset's product. -/
theorem elim_fill (P : Fin k → K) (y : Fin k ⊕ C) :
    Sum.elim P (L.fill P) y = ((monoOf L.mono y).map P).prod := by
  rcases y with j | c
  · simp [monoOf]
  · rfl

theorem triplesHold_fill (P : Fin k → K) : L.TriplesHold P (L.fill P) := fun c => by
  rw [elim_fill, fill, L.mono_eq c, Multiset.map_cons, Multiset.prod_cons, mul_comm]

/-- **Under the triples every coordinate holds its multiset's product**, by induction on the
multiset's size. -/
theorem read_eq_prod {P : Fin k → K} {Pr : C → K} (h : L.TriplesHold P Pr)
    (y : Fin k ⊕ C) : Sum.elim P Pr y = ((monoOf L.mono y).map P).prod := by
  suffices H : ∀ d y, Multiset.card (monoOf L.mono y) ≤ d →
      Sum.elim P Pr y = ((monoOf L.mono y).map P).prod from H _ y le_rfl
  intro d
  induction d with
  | zero =>
    intro y hy
    rcases y with j | c
    · simp [monoOf] at hy
    · have := L.mono_eq c
      simp only [monoOf] at hy
      rw [this, Multiset.card_cons] at hy
      omega
  | succ d ih =>
    intro y hy
    rcases y with j | c
    · simp [monoOf]
    · have hc := L.mono_eq c
      have hlt : Multiset.card (monoOf L.mono (L.left c)) ≤ d := by
        simp only [monoOf] at hy
        rw [hc, Multiset.card_cons] at hy
        omega
      change Pr c = ((L.mono c).map P).prod
      rw [← h c, ih _ hlt, hc, Multiset.map_cons, Multiset.prod_cons, mul_comm]

/-- **The coordinate of a monomial's chosen factors** holds the product of their pads. -/
theorem read_cell {P : Fin k → K} {Pr : C → K} (h : L.TriplesHold P Pr) (i : Fin S.nm)
    {x : Fin (S.deg i) → Fin 2} (hx : x ≠ 0) :
    Sum.elim P Pr (L.cell i x) = ∏ t ∈ Finset.univ.filter (fun t => x t = 1), P (S.ops i t) := by
  rw [L.read_eq_prod h, L.monoOf_cell i x hx, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

end PadLayout

/-! ### The product chains of the C++ -/

namespace MonoShape

variable {k : ℕ} (S : MonoShape k)

/-- **The operands a monomial's factors read**, as a multiset. -/
def factors (i : Fin S.nm) : Multiset (Fin k) := Finset.univ.val.map (S.ops i)

/-- **The operands a monomial's chosen factors read** (`x t = 1`: factor `t` is a pad). -/
def chosen (i : Fin S.nm) (x : Fin (S.deg i) → Fin 2) : Multiset (Fin k) :=
  (Finset.univ.filter fun t => x t = 1).val.map (S.ops i)

/-- The chosen factors' operands are among the monomial's. -/
theorem chosen_le_factors (i : Fin S.nm) (x : Fin (S.deg i) → Fin 2) :
    S.chosen i x ≤ S.factors i :=
  Multiset.map_le_map (Finset.val_le_iff.mpr (Finset.filter_subset _ _))

/-- A choice with some pad chooses some operand. -/
theorem chosen_ne_zero {i : Fin S.nm} {x : Fin (S.deg i) → Fin 2} (hx : x ≠ 0) :
    S.chosen i x ≠ 0 := by
  obtain ⟨t, ht⟩ := Function.ne_iff.mp hx
  have h1 : x t = 1 := by
    rcases Fin.exists_fin_two.mp ⟨x t, rfl⟩ with h | h
    · exact absurd h ht
    · exact h
  rw [← Multiset.card_pos, chosen, Multiset.card_map, ← Finset.card_def]
  exact Finset.card_pos.mpr ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ t, h1⟩⟩

/-- **The product cells of the masked skip** (`field_skip.h`, `pad_monomials`): the multisets of at
least two operands contained in the factors of some monomial. The C++ inserts, for every monomial
and every choice of its factors, the prefixes of length at least two of the sorted chosen operands;
these are the same multisets (a prefix of a chosen multiset is chosen by fewer factors, and every
such multiset is its own full prefix). -/
def padMonomials : Finset (Multiset (Fin k)) :=
  Finset.univ.biUnion fun i => (S.factors i).powerset.toFinset.filter fun M => 2 ≤ Multiset.card M

theorem mem_padMonomials {M : Multiset (Fin k)} :
    M ∈ S.padMonomials ↔ 2 ≤ Multiset.card M ∧ ∃ i, M ≤ S.factors i := by
  simp only [padMonomials, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter,
    Multiset.mem_toFinset, Multiset.mem_powerset]
  exact ⟨fun ⟨i, h, h2⟩ => ⟨h2, i, h⟩, fun ⟨h2, i, h⟩ => ⟨i, h, h2⟩⟩

/-- **A product cell** of the masked skip: an element of `padMonomials`. -/
abbrev ChainCell : Type := S.padMonomials

/-- **The largest operand of a nonempty multiset** (the C++ sorts a cell's operands and peels the
last). -/
def chainTop (M : Multiset (Fin k)) (h : M ≠ 0) : Fin k :=
  M.toFinset.max' (Multiset.toFinset_nonempty.mpr h)

theorem chainTop_mem {M : Multiset (Fin k)} (h : M ≠ 0) : chainTop M h ∈ M :=
  Multiset.mem_toFinset.mp (Finset.max'_mem _ _)

/-- A multiset of one operand is that operand's singleton. -/
theorem eq_singleton_chainTop {M : Multiset (Fin k)} (h : M ≠ 0) (h1 : Multiset.card M = 1) :
    M = {chainTop M h} := by
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.mp h1
  rw [Multiset.mem_singleton.mp (chainTop_mem h)]

/-- **The coordinate holding the product of a nonempty multiset of at most a monomial's
operands**: the terminal pad of its one operand, or its product cell. -/
def chainCoord (M : Multiset (Fin k)) (h0 : M ≠ 0) (hle : ∃ i, M ≤ S.factors i) :
    Fin k ⊕ S.ChainCell :=
  if h2 : 2 ≤ Multiset.card M then .inr ⟨M, (S.mem_padMonomials).mpr ⟨h2, hle⟩⟩
  else .inl (chainTop M h0)

theorem monoOf_chainCoord (M : Multiset (Fin k)) (h0 : M ≠ 0) (hle : ∃ i, M ≤ S.factors i) :
    monoOf Subtype.val (S.chainCoord M h0 hle) = M := by
  unfold chainCoord
  split_ifs with h2
  · rfl
  · have h1 : Multiset.card M = 1 := by
      have := Multiset.card_pos.mpr h0
      omega
    exact (eq_singleton_chainTop h0 h1).symm

/-- A product cell is nonempty. -/
theorem chainCell_ne_zero (c : S.ChainCell) : c.val ≠ 0 := fun h => by
  have := ((S.mem_padMonomials).mp c.2).1
  rw [h, Multiset.card_zero] at this
  omega

/-- A product cell without its largest operand is nonempty. -/
theorem chainRest_ne_zero (c : S.ChainCell) :
    c.val.erase (chainTop c.val (S.chainCell_ne_zero c)) ≠ 0 := by
  intro h
  have h2 := ((S.mem_padMonomials).mp c.2).1
  have := Multiset.card_erase_add_one (chainTop_mem (S.chainCell_ne_zero c))
  rw [h, Multiset.card_zero] at this
  omega

/-- A product cell without its largest operand is at most a monomial's operands. -/
theorem chainRest_le (c : S.ChainCell) :
    ∃ i, c.val.erase (chainTop c.val (S.chainCell_ne_zero c)) ≤ S.factors i := by
  obtain ⟨i, hi⟩ := ((S.mem_padMonomials).mp c.2).2
  exact ⟨i, (Multiset.erase_le _ _).trans hi⟩

/-- **The product chains of the masked skip** (`field_skip.h`, `pad_monomials` and
`pad_quadratic`), at any degree: the product cells are `padMonomials`; cell `M`'s triple is the
product of `M` without its largest operand `j` (a terminal pad when one operand remains, else a
smaller cell) times terminal pad `j` (`pad_quadratic.push_back({x, terminal + m.back(), product +
i})`, the prefix `x` without the last sorted operand); the coordinate of a monomial's chosen factors
is the terminal pad of a single chosen factor or the cell of the chosen operands (`terminal_expr`'s
`at`). `hpos` (no constant monomial) supplies a coordinate for the choice of no pad, which nothing
reads. -/
def chainLayout (hpos : ∀ i, 0 < S.deg i) : PadLayout S S.ChainCell where
  mono c := c.val
  left c := S.chainCoord _ (S.chainRest_ne_zero c) (S.chainRest_le c)
  right c := chainTop c.val (S.chainCell_ne_zero c)
  mono_eq c := by
    rw [monoOf_chainCoord, Multiset.cons_erase (chainTop_mem _)]
  cell i x :=
    if h0 : S.chosen i x = 0 then .inl (S.ops i ⟨0, hpos i⟩)
    else S.chainCoord _ h0 ⟨i, S.chosen_le_factors i x⟩
  monoOf_cell i x hx := by
    simp only [S.chosen_ne_zero hx, ↓reduceDIte]
    rw [monoOf_chainCoord]
    rfl

end MonoShape

namespace MonoRelation

variable {K : Type} [Field K] {k D : ℕ} (R : MonoRelation K k D)

/-- **The product chains of a relation** (`MaskedFieldSkip`'s `products` and `pad_quadratic`):
`MonoShape.chainLayout`, its monomials having positive degree. -/
abbrev chainLayout : PadLayout R.toMonoShape R.ChainCell := R.toMonoShape.chainLayout R.deg_pos

end MonoRelation

namespace MonoRelation

variable {K : Type} [Field K] {k D : ℕ} {C : Type} (R : MonoRelation K k D)
  (L : PadLayout R.toMonoShape C)

/-- The term of a choice `x` of pads (`1`) and sent values (`0`) per factor in the expansion of a
product of differences: `(−1)^#pads · Π_{sent} a · read`, zero for the choice of no pad. -/
def choiceTerm {d : ℕ} (x : Fin d → Fin 2) (a : Fin d → K) (v : K) : K :=
  if x = 0 then 0 else
    (-1) ^ (Finset.univ.filter fun t => x t = 1).card *
      (∏ t ∈ Finset.univ.filter (fun t => x t = 0), a t) * v

/-- **The pad term of the terminal check** (`terminal_expr`): `Q(m − P) − Q(m)` expanded over the
choices `x` of a pad or a sent value per factor of each monomial, each choice with a pad read from
the coordinate `cell i x`; linear in the coordinates `read` of the pads and product cells. -/
def padTerm (m : Fin k → K) (read : Fin k ⊕ C → K) : K :=
  ∑ i, R.coeff i * ∑ x : Fin (R.deg i) → Fin 2,
    choiceTerm x (fun t => m (R.ops i t)) (read (L.cell i x))

/-- A product of differences over the factors: the choice of no pad, plus the signed products of
the other choices. -/
theorem prod_sub_eq {d : ℕ} (a b : Fin d → K) :
    ∏ t, (a t - b t) = ∏ t, a t +
      ∑ x : Fin d → Fin 2, choiceTerm x a (∏ t ∈ Finset.univ.filter (fun t => x t = 1), b t) := by
  have h := Finset.prod_univ_sum (fun _ : Fin d => (Finset.univ : Finset (Fin 2)))
    (fun t (j : Fin 2) => if j = 0 then a t else -b t)
  simp only [Fin.sum_univ_two, Fin.isValue, ↓reduceIte, one_ne_zero, Fintype.piFinset_univ] at h
  have hsplit := Finset.add_sum_erase Finset.univ
    (fun x : Fin d → Fin 2 => ∏ i, if x i = 0 then a i else -b i) (Finset.mem_univ 0)
  have hsplit' := Finset.add_sum_erase Finset.univ
    (fun x => choiceTerm x a (∏ t ∈ Finset.univ.filter (fun t => x t = 1), b t))
    (Finset.mem_univ (0 : Fin d → Fin 2))
  rw [show (∏ t, (a t - b t)) = ∏ t, (a t + -b t) from
    Finset.prod_congr rfl fun t _ => sub_eq_add_neg _ _, h, ← hsplit, ← hsplit', choiceTerm,
    ite_eq_left rfl, zero_add]
  refine congrArg₂ (· + ·) (by simp) ?_
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
    rw [choiceTerm, ite_eq_right hx0, ← Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun t => x t = 0)]
    have hfilter : (Finset.univ.filter fun t => ¬ x t = 0) =
        Finset.univ.filter fun t => x t = 1 := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h0
        rcases Fin.exists_fin_two.mp ⟨x t, rfl⟩ with h | h
        · exact absurd h h0
        · exact h
      · intro h1
        rw [h1]
        decide
    rw [hfilter]
    have h0 : ∏ t ∈ Finset.univ.filter (fun t => x t = 0),
        (if x t = 0 then a t else -b t) = ∏ t ∈ Finset.univ.filter (fun t => x t = 0), a t :=
      Finset.prod_congr rfl fun t ht => ite_eq_left (Finset.mem_filter.mp ht).2
    have h1 : ∏ t ∈ Finset.univ.filter (fun t => x t = 1),
        (if x t = 0 then a t else -b t) = ∏ t ∈ Finset.univ.filter (fun t => x t = 1), -b t :=
      Finset.prod_congr rfl fun t ht => by
        rw [ite_eq_right]
        rw [(Finset.mem_filter.mp ht).2]
        decide
    rw [h0, h1, Finset.prod_neg]
    ring

/-- **The terminal check's expansion**: under the pads' triples, `Q(m − P) = Q(m) + padTerm m`
at the pads and product cells. -/
theorem eval_sub_eq {P : Fin k → K} {Pr : C → K} (h : L.TriplesHold P Pr) (m : Fin k → K) :
    R.eval (m - P) = R.eval m + R.padTerm L m (Sum.elim P Pr) := by
  simp only [eval, padTerm, Pi.sub_apply, ← Finset.sum_add_distrib, ← mul_add]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [prod_sub_eq]
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases hx : x = 0
  · simp [choiceTerm, hx]
  · rw [L.read_cell h i hx]

end MonoRelation

/-! ### The honest round messages at any degree -/

section Honest

variable {K : Type} [Field K]

/-- **The coefficients of a product of lines** `Pr_{t < d} (a t + b t X)` (`round_sums`: the
coefficient vector multiplied by one line per factor), coefficient `j`. -/
def lineProdCoeff : (d : ℕ) → (Fin d → K) → (Fin d → K) → ℕ → K
  | 0, _, _, j => if j = 0 then 1 else 0
  | d + 1, a, b, 0 => a (Fin.last d) * lineProdCoeff d (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) 0
  | d + 1, a, b, j + 1 =>
    a (Fin.last d) * lineProdCoeff d (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) (j + 1) +
      b (Fin.last d) * lineProdCoeff d (a ∘ Fin.castSucc) (b ∘ Fin.castSucc) j

theorem lineProdCoeff_eq (d : ℕ) (a b : Fin d → K) (j : ℕ) :
    lineProdCoeff d a b j = (∏ t, (C (a t) + C (b t) * X)).coeff j := by
  induction d generalizing j with
  | zero =>
    simp only [lineProdCoeff, Finset.univ_eq_empty, Finset.prod_empty, coeff_one]
  | succ d ih =>
    rw [Fin.prod_univ_castSucc, mul_add, ← mul_assoc, coeff_add, mul_comm _ (C (a (Fin.last d))),
      coeff_C_mul, mul_comm _ (C (b (Fin.last d))), mul_assoc, coeff_C_mul]
    cases j with
    | zero =>
      simp only [lineProdCoeff, coeff_mul_X_zero, mul_zero, add_zero, ih]
      rfl
    | succ j =>
      simp only [lineProdCoeff, coeff_mul_X, ih]
      rfl

variable {w n k D : ℕ} (R : MonoRelation K k D) (ops : Operands K w n k) (dom : SkipPoints K w D)

open GKR.ClaimEvaluation (evalTable mle)

/-- **The honest round messages by field operations** at degree `D`: coefficients `1, …, D` of
round `i`'s factor `Σ_x eq(ρ_{>i}, x) · Q(a(x) + X d(x))`, where `a_j`, `d_j` are the constant and
linear coefficients in coordinate `i` of operand `j`'s multilinear extension at the prefix `s_{<i}`
and the Boolean suffix `x` (`MaskedFieldSkip::round_sums`: per monomial the coefficients of the
product of its factors' lines). Equal to `EqFactoredDeg.honest` (`honestRoundsMono_eq`). -/
def honestRoundsMono (ρ : Fin n → K) (r : K) (s : Fin n → K) (i : Fin n) : Fin D → K :=
  fun d => GKR.LayerSumcheck.marginalFn (fun e => EqFactored.eqAfterEval ρ i e *
      ∑ q, R.coeff q * lineProdCoeff (R.deg q)
        (fun t => opEvalDec ops dom (R.ops q t) (Function.update e i 0) r)
        (fun t => opEvalDec ops dom (R.ops q t) (Function.update e i 1) r -
          opEvalDec ops dom (R.ops q t) (Function.update e i 0) r) (d.val + 1))
    (Coefficient.prefixPoint s i) (Coefficient.suffix n (i.val + 1))

/-- The substitution with `X` at `i` of the summand factor `eq(ρ_{>i}, ·) · Q(Â)` at `e`: a
constant times the relation of the operands' lines. -/
theorem eval₂_eqAfter_mul_residualMle_mono (ρ : Fin n → K) (r : K) (i : Fin n) (e : Fin n → K) :
    MvPolynomial.eval₂ Polynomial.C (Function.update (Polynomial.C ∘ e) i Polynomial.X)
        (EqFactored.eqAfter ρ i * residualMle R.toRelation ops dom r) =
      Polynomial.C (EqFactored.eqAfterEval ρ i e) *
        ∑ q, Polynomial.C (R.coeff q) * ∏ t,
          (Polynomial.C (opEvalDec ops dom (R.ops q t) (Function.update e i 0) r) +
            Polynomial.C (opEvalDec ops dom (R.ops q t) (Function.update e i 1) r -
              opEvalDec ops dom (R.ops q t) (Function.update e i 0) r) * Polynomial.X) := by
  have hQ : residualMle R.toRelation ops dom r =
      ∑ q, MvPolynomial.C (R.coeff q) * ∏ t, mle (opTable ops dom (R.ops q t) r) := by
    simp [residualMle, MonoRelation.toRelation, MonoRelation.poly]
  rw [hQ, MvPolynomial.eval₂_mul, EqFactored.eval₂_eqAfter, MvPolynomial.eval₂_sum]
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_prod,
    eval₂_mle_opTable]

theorem honestRoundsMono_eq (ρ : Fin n → K) (r : K) (s : Fin n → K) :
    honestRoundsMono R ops dom ρ r s =
      EqFactoredDeg.honest ρ (residualMle R.toRelation ops dom r) s := by
  funext i d
  simp only [honestRoundsMono, EqFactoredDeg.honest, EqFactored.coeff_quad,
    eval₂_eqAfter_mul_residualMle_mono, Polynomial.coeff_C_mul, Polynomial.finsetSum_coeff,
    lineProdCoeff_eq]

end Honest

end GordieHowe.Sumcheck.FieldSkip
