-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.SkipBatchPhase
public import GordieHowe.ProofSystem.FieldProof.MaskedReduction
public import GordieHowe.ProofSystem.FieldProof.UniformSim
public import GordieHowe.ProofSystem.FieldProof.ClaimSupport

@[expose] public section

/-!
# The batch stage: one masked skip zerocheck for any batched relation

The C++ batch driver (`lib/gordiehowe/compiler/batch.h`, `BatchKernel`; `field_skip.h`,
`MaskedFieldSkip`) proves every batched relation of a domain the same way: a relation `Q` of degree
at most `D` with no constant term (`FieldSkip.MonoRelation`, the C++ `FieldRelation`), on operands
that are affine views of the domain's phase-0 committed cells, padded with zero instances to
`2^n w`, by the masked univariate-skip zerocheck; the terminal operand claims, combined by `u`, are
one linear claim on the logical coordinates (the operand map's adjoint), which the domain's packing
tree opens. This file is that stage as a masked reduction, in either characteristic and at any degree within
the skip domain's limit (`SkipPoints`: `D(w − 1) < p` in odd characteristic, `D(w − 1) + 1 ≤ 256` in
characteristic two).

* **The operand map** (`OperandMap`, the C++ `FieldOperandMap` and `BitOperandMap`): per public
  input, the zerocheck's operands as a function of the logical assignment, and the verifier's
  adjoint, an affine form on the logical coordinates whose value is the `u`-combination of the
  operands' multilinear extensions at `(s, r)` (`eval_adjoint`). Offsets and per-instance public
  coefficients enter through the public input. The affine map of the C++ (`OperandMap.affine`,
  `AffineOperandMap`): `N` instances at `t = r w + z`, each operand an affine form, zero beyond `N`;
  its adjoint is the instance weights `eq(s, ⌊t/w⌋) L_{t mod w}(r)` against the forms
  (`AffineOperandMap::adjoint`, `instance_weights`). A system's batched relation
  (`GordieHowe.BatchRelation`) holds exactly when the stage's relation holds on the affine map whose
  forms are its operands (for the plan's batches on bits, `GordieHowe.RealizedProgram.bitsBatchAt_holds_iff` in
  `GordieHowe/ProofSystem/Program/FieldClaim.lean`). In characteristic two a bit operand map (the Keccak and
  SHA-256 batches) is an `OperandMap` on the words' bits.
* **The cells** (`PadCells`): the skip pads, `D` per round, the `k` terminal pads and the product
  cells of a `FieldSkip.PadLayout`, each product cell one quadratic triple (`pad_quadratic`).
* **The masked reduction** (`maskedReduction`): the phase `GordieHowe.BatchedZerocheck.spec`, the terminal row on the cells
  (`terminalRow`, `rows_of`), the products, and the opening claim on the logical coordinates
  (`openingClaim`, `opening_row`: `Σ_j u_j (m_j − P_j) − adjoint = 0`). Soundness
  (`maskedReductionSound`): the relation on the operands and the pads' products, with the phase's errors
  `n/|K|`, `D(w − 1)/|K|`, `(D + 1)/|K|` per round and `1/|K|`. The honest prover (`maskedReductionHonest`):
  the honest masked skip by field operations (`SkipRelation.honestT`), simulated by uniform
  messages.
* **Merging** (`mergedMaskedReduction`, `FieldOperands::relation(gamma)`): `np` relations on one operand
  vector merged as `Σ_p γ^p Q_p` with `γ` drawn first (`gordiehowe.field-batch.gamma`), then the
  masked reduction of the merged relation. Its soundness charges `γ` with `(np − 1)/|K|`
  (`FieldSkip.mergeEvent`) and keeps every other charge. The C++ records no charge for this `γ`.
* **No constant term.** The zero instances that pad the batch satisfy `Q` only because `Q` has no
  constant term (`FieldRelation::error`, `relation_error`); the C++ keeps this as a validity
  condition of the relation and enters a constant monomial as a monomial of a constant operand
  (`domain.h`, `batch_parts`), so the Lean keeps it too (`MonoRelation.deg_pos`).
-/

namespace GordieHowe.BatchedZerocheck

open IOP Sumcheck.FieldSkip Sumcheck.FieldSkipMasked
open scoped NNReal

variable {K : Type} [Field K]

/-! ### Operand maps -/

section OperandMaps

variable {w D : ℕ} (dom : SkipPoints K w D)

/-- **The operand map of a batch** (`batch.h`, `FieldOperandMap` and `BitOperandMap`): for each
public input, the zerocheck's operands as a function of the logical assignment (`ops`), and the
verifier's adjoint at `(s, r, u)` (`adjoint`, `FieldOperandMap::adjoint`,
`BitOperandMap::adjoint`): an affine form on the logical coordinates whose value is the
`u`-combination of the operands' multilinear extensions at `(s, r)` (`eval_adjoint`). -/
structure OperandMap (Pub V : Type) (n k : ℕ) where
  /-- The operands of the zerocheck at a logical assignment. -/
  ops : Pub → (V → K) → Operands K w n k
  /-- The adjoint at `(s, r, u)`. -/
  adjoint : Pub → (Fin n → K) → K → (Fin k → K) → AffineForm K V
  /-- Its value is the combined operand claim. -/
  eval_adjoint : ∀ p z s r u, (adjoint p s r u).eval z = batch u (trueTerminal (ops p z) dom s r)

/-- **The instance weight** of the instance at row `row` and skip coordinate `c` at `(s, r)`:
`eq(s, row) · L_c(r)` (`MaskedFieldSkip::instance_weights`). -/
def instWeight {n : ℕ} (s : Fin n → K) (r : K) (row : Fin (2 ^ n)) (c : Fin w) : K :=
  PackedClaim.eqPt s row.val * Lagrange.basisEval Finset.univ dom.pt c r

/-- The batched true terminal of any operands: the instance weights against the operands. -/
theorem batch_trueTerminal_eq {n k : ℕ} (ops : Operands K w n k) (s : Fin n → K) (r : K)
    (u : Fin k → K) :
    batch u (trueTerminal ops dom s r) =
      ∑ j, u j * ∑ row : Fin (2 ^ n), ∑ c : Fin w, instWeight dom s r row c * ops row c j := by
  simp only [batch, trueTerminal, opEval, GKR.ClaimEvaluation.evalTable, SkipPoints.eval_interp,
    SkipPoints.interpEval, Finset.mul_sum, instWeight]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun row _ =>
    Finset.sum_congr rfl fun c _ => ?_
  ring

variable {Pub V : Type} {n k : ℕ}

/-- The form of operand `j` at row `row` and skip coordinate `c` of an affine map with `N`
instances: instance `row w + c`'s form, zero beyond `N`. -/
def affineForm (N : ℕ) (form : Pub → Fin N → Fin k → AffineForm K V) (p : Pub) (row c : ℕ)
    (j : Fin k) : AffineForm K V :=
  if h : row * w + c < N then form p ⟨_, h⟩ j else 0

/-- **The affine operand map** (`batch.h`, `AffineOperandMap`): `N` instances, instance `t` at
row `⌊t / w⌋` and skip coordinate `t mod w`, operand `j` the affine form `form p t j` of the
logical assignment (its constant read from the public input), zero beyond `N`; the adjoint is the
instance weights against the forms (`AffineOperandMap::adjoint`). -/
def OperandMap.affine (N : ℕ) (form : Pub → Fin N → Fin k → AffineForm K V) :
    OperandMap dom Pub V n k where
  ops p z row c j := (affineForm (w := w) N form p row c j).eval z
  adjoint p s r u := AffineForm.sumFin fun j => u j • AffineForm.sumFin fun row : Fin (2 ^ n) =>
    AffineForm.sumFin fun c : Fin w => instWeight dom s r row c • affineForm (w := w) N form p row c j
  eval_adjoint p z s r u := by
    rw [batch_trueTerminal_eq]
    simp only [AffineForm.eval_sumFin, AffineForm.eval_smul]

/-- **The affine map's adjoint reads what the forms read.** -/
theorem readsOnly_affine_adjoint [DecidableEq V] (N : ℕ) (form : Pub → Fin N → Fin k → AffineForm K V)
    {T : V → Prop} (h : ∀ p t j, (form p t j).ReadsOnly T) (p : Pub) (s : Fin n → K) (r : K)
    (u : Fin k → K) : ((OperandMap.affine dom N form).adjoint p s r u).ReadsOnly T :=
  AffineForm.ReadsOnly.sumFin fun j => (AffineForm.ReadsOnly.sumFin fun row =>
    AffineForm.ReadsOnly.sumFin fun c => by
      refine AffineForm.ReadsOnly.smul _ ?_
      unfold affineForm
      split
      · exact h _ _ _
      · exact AffineForm.ReadsOnly.zero).smul _

/-- An affine map's operands at an instance below `N` are the instance's forms. -/
theorem affine_ops_of_lt (N : ℕ) (form : Pub → Fin N → Fin k → AffineForm K V) (p : Pub)
    (z : V → K) {row : Fin (2 ^ n)} {c : Fin w} (h : row.val * w + c.val < N) :
    (OperandMap.affine dom N form).ops p z row c = fun j => (form p ⟨_, h⟩ j).eval z := by
  funext j
  simp only [OperandMap.affine, affineForm, h, ↓reduceDIte]

theorem affine_ops_of_not_lt (N : ℕ) (form : Pub → Fin N → Fin k → AffineForm K V) (p : Pub)
    (z : V → K) {row : Fin (2 ^ n)} {c : Fin w} (h : ¬ row.val * w + c.val < N) :
    (OperandMap.affine dom N form).ops p z row c = 0 := by
  funext j
  simp only [OperandMap.affine, affineForm, h, ↓reduceDIte, AffineForm.eval_zero, Pi.zero_apply]

/-- **The relation holds on an affine map's operands** exactly when it vanishes on every
instance's forms, when the instances fit the rows (`N ≤ 2^n w`, a parameter condition): the zero
instances beyond `N` satisfy it because it has no constant term. -/
theorem affine_holds_iff {Rel : SkipRelation K k D} {Q : Relation K k D} (hX : Rel.Computes Q)
    {N : ℕ} (hN : N ≤ 2 ^ n * w)
    (form : Pub → Fin N → Fin k → AffineForm K V) (p : Pub) (z : V → K) :
    Holds Q ((OperandMap.affine (n := n) dom N form).ops p z) ↔
      ∀ t, Rel.eval (fun j => (form p t j).eval z) = 0 := by
  rw [SkipRelation.holds_iff hX]
  constructor
  · intro h t
    have hw : 0 < w := by
      rcases Nat.eq_zero_or_pos w with h0 | h0
      · rw [h0, mul_zero] at hN
        exact absurd (t.isLt.trans_le hN) (Nat.not_lt_zero _)
      · exact h0
    have hr : t.val / w < 2 ^ n := by
      rw [Nat.div_lt_iff_lt_mul hw]
      exact t.isLt.trans_le hN
    have ht : (t.val / w) * w + t.val % w = t.val := Nat.div_add_mod' t.val w
    have hlt : t.val / w * w + t.val % w < N := by
      rw [ht]
      exact t.isLt
    have hres := h ⟨t.val / w, hr⟩ ⟨t.val % w, Nat.mod_lt _ hw⟩
    rw [affine_ops_of_lt dom N form p z (row := ⟨t.val / w, hr⟩) (c := ⟨t.val % w, Nat.mod_lt _ hw⟩)
      hlt] at hres
    have hfin : (⟨t.val / w * w + t.val % w, hlt⟩ : Fin N) = t := Fin.ext ht
    rw [hfin] at hres
    exact hres
  · intro h row c
    by_cases hlt : row.val * w + c.val < N
    · rw [affine_ops_of_lt dom N form p z hlt]
      exact h _
    · rw [affine_ops_of_not_lt dom N form p z hlt]
      exact SkipRelation.eval_zero hX

end OperandMaps

/-! ### The cells -/

section Cells

variable {ι C : Type} {e D w n k : ℕ}

/-- **The committed cells of a batch's pads** (`MaskedFieldSkip::Layout`: the skip values, `D` per
round, the terminal claims, then the product cells; `domain.h`: "each reduction's pads are
committed ambient cells after every variable"). -/
structure PadCells (ι : Type) (e D n k : ℕ) (C : Type) where
  /-- The pad of each skip value. -/
  skip : Fin e → ι
  /-- The pads of each round's `D` coefficients. -/
  rounds : Fin n → Fin D → ι
  /-- The terminal pads. -/
  terminal : Fin k → ι
  /-- The product cells. -/
  product : C → ι

namespace PadCells

variable (pc : PadCells ι e D n k C)

/-- The cell of a terminal pad or a product cell. -/
def padCell : Fin k ⊕ C → ι := Sum.elim pc.terminal pc.product

/-- The pads read from the cells, the skip pads at the skip domain's points (`he`). -/
def read (he : (D - 1) * (w - 1) = e) (x : ι → K) : Pads K w D n k C :=
  ⟨fun i => x (pc.skip (Fin.cast he i)), fun i d => x (pc.rounds i d), x ∘ pc.terminal,
    x ∘ pc.product⟩

/-- The message pads read from the cells. -/
def readMsg (he : (D - 1) * (w - 1) = e) (x : ι → K) : Transcript K w D n k :=
  ⟨(pc.read he x).skip, (pc.read he x).rounds, (pc.read he x).terminal⟩

omit [Field K] in
theorem elim_read (he : (D - 1) * (w - 1) = e) (x : ι → K) (y : Fin k ⊕ C) :
    Sum.elim (pc.read he x).terminal (pc.read he x).product y = x (pc.padCell y) := by
  rcases y with j | c <;> rfl

end PadCells

/-- **The pads' quadratic constraints** (`pad_quadratic`): each product cell is its triple's
product. -/
def PadCells.products (T : PadTriples k) (pc : PadCells ι e D n k T.Cell) :
    Ligero.Routing.ProductLayout ι T.Cell where
  source c := ![pc.padCell (T.left c), pc.terminal (T.right c), pc.product c]

theorem PadCells.sourceProducts_iff (T : PadTriples k) (pc : PadCells ι e D n k T.Cell)
    (he : (D - 1) * (w - 1) = e) (x : ι → K) :
    Ligero.Routing.SourceProducts (pc.products T) x ↔ ProductHolds T (pc.read he x) := by
  simp only [Ligero.Routing.SourceProducts, PadCells.products, ProductHolds, PadCells.elim_read]
  rfl

end Cells

/-! ### The rows -/

section Rows

variable {ι C : Type} {e D w n k : ℕ}

/-- **The running claims as affine forms** (computable), at `D` coefficients per round: the
verifier's claims from the initial form `init`, each round's coefficients the cells `msg i`
(`EqFactoredDeg.claims`). -/
def claimsForm (init : AffineForm K ι) (ρ : Fin n → K) (msg : Fin n → Fin D → ι)
    (s : Fin n → K) (j : Fin (n + 1)) : AffineForm K ι :=
  Fin.induction (motive := fun _ => AffineForm K ι) init
    (fun i c => Sumcheck.EqFactored.eqLin (ρ i) (s i) • c +
      Sumcheck.EqFactored.prefixEq ρ s (i.val + 1) •
        AffineForm.sumFin fun d : Fin D => (s i ^ (d.val + 1) - ρ i) • AffineForm.var (msg i d)) j

theorem eval_claimsForm (init : AffineForm K ι) (ρ : Fin n → K) (msg : Fin n → Fin D → ι)
    (s : Fin n → K) (j : Fin (n + 1)) (x : ι → K) :
    (claimsForm init ρ msg s j).eval x =
      Sumcheck.EqFactoredDeg.claims (init.eval x) ρ (fun i d => x (msg i d)) s j := by
  induction j using Fin.induction with
  | zero => rfl
  | succ i ih =>
    rw [Sumcheck.EqFactoredDeg.claims_succ, ← ih]
    simp only [claimsForm, Fin.induction_succ, Sumcheck.EqFactoredDeg.step, AffineForm.eval_add,
      AffineForm.eval_smul, AffineForm.eval_sumFin, AffineForm.eval_var, smul_eq_mul]

variable (dom : SkipPoints K w D) (he : (D - 1) * (w - 1) = e)

/-- The skip claim of the skip pads as an affine form on the cells (`rows_of`:
`claim += skip_j · l[w + j]`). -/
def skipClaimForm (skip : Fin e → ι) (r : K) : AffineForm K ι :=
  AffineForm.sumFin fun i : Fin ((D - 1) * (w - 1)) =>
    Lagrange.basisEval Finset.univ dom.point (Sum.inr i) r • AffineForm.var (skip (Fin.cast he i))

theorem eval_skipClaimForm (pc : PadCells ι e D n k C) (r : K) (x : ι → K) :
    (skipClaimForm dom he pc.skip r).eval x = dom.skipClaim (pc.read he x).skip r := by
  simp only [skipClaimForm, AffineForm.eval_sumFin, AffineForm.eval_smul, AffineForm.eval_var,
    SkipPoints.skipClaim, PadCells.read]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- The pads' running claim, its value the verifier's claim on the pads read from the cells. -/
theorem eval_padClaims (pc : PadCells ι e D n k C) (ch : Challenges K n k) (x : ι → K)
    (j : Fin (n + 1)) :
    (claimsForm (skipClaimForm dom he pc.skip ch.r) ch.rho pc.rounds ch.s j).eval x =
      Sumcheck.EqFactoredDeg.claims (dom.skipClaim (pc.read he x).skip ch.r) ch.rho
        (pc.read he x).rounds ch.s j := by
  rw [eval_claimsForm, eval_skipClaimForm]
  rfl

variable (Rel : SkipRelation K k D)

/-- **The pad term as an affine form on the cells** (`terminal_expr`): the relation's pad term with
each terminal pad and product cell read at its cell. -/
def padTermForm (pc : PadCells ι e D n k Rel.Cell) (m : Fin k → K) : AffineForm K ι :=
  (Rel.padForm m).rename pc.padCell

theorem eval_padTermForm (pc : PadCells ι e D n k Rel.Cell) (m : Fin k → K) (x : ι → K) :
    (padTermForm Rel pc m).eval x =
      (Rel.padForm m).eval (Sum.elim (pc.read he x).terminal (pc.read he x).product) := by
  rw [padTermForm, AffineForm.eval_rename]
  congr 1
  funext y
  exact (pc.elim_read he x y).symm

/-- **The terminal row** (`rows_of`: the last claim from the sent values minus the claim from the
pads equals `eq(ρ, s) · Q(m − P)`, expanded by `terminal_expr`): the sent part minus `eq(ρ, s) Q(m)`,
minus the pads' claim, minus `eq(ρ, s)` times the pad term. -/
def terminalRow (pc : PadCells ι e D n k Rel.Cell) (ch : Challenges K n k) (tr : Transcript K w D n k) :
    AffineForm K ι :=
  AffineForm.ofConst (Sumcheck.EqFactoredDeg.claims (dom.skipClaim tr.skip ch.r) ch.rho tr.rounds
      ch.s (Fin.last n) - EqPolynomial.eqProd ch.rho ch.s * Rel.eval tr.terminal) -
    claimsForm (skipClaimForm dom he pc.skip ch.r) ch.rho pc.rounds ch.s (Fin.last n) -
    EqPolynomial.eqProd ch.rho ch.s • padTermForm Rel pc tr.terminal

/-- **The terminal row holds** exactly when the masked verifier's terminal equation does. -/
theorem terminalRow_eval_eq_zero_iff (pc : PadCells ι e D n k Rel.Cell) (ch : Challenges K n k)
    (tr : Transcript K w D n k) (x : ι → K) :
    (terminalRow dom he Rel pc ch tr).eval x = 0 ↔
      Sumcheck.EqFactoredDeg.claims (dom.skipClaim tr.skip ch.r) ch.rho tr.rounds ch.s
          (Fin.last n) -
        Sumcheck.EqFactoredDeg.claims (dom.skipClaim (pc.read he x).skip ch.r) ch.rho
          (pc.read he x).rounds ch.s (Fin.last n) =
      EqPolynomial.eqProd ch.rho ch.s * (Rel.eval tr.terminal +
        (Rel.padForm tr.terminal).eval (Sum.elim (pc.read he x).terminal (pc.read he x).product)) := by
  simp only [terminalRow, AffineForm.eval_sub, AffineForm.eval_ofConst, AffineForm.eval_smul,
    eval_padClaims, eval_padTermForm he Rel]
  constructor <;> intro h <;> linear_combination h

end Rows

/-! ### The masked reduction -/

section MaskedReduction

variable {ι V : Type} {e D w n k : ℕ} (dom : SkipPoints K w D)
  (he : (D - 1) * (w - 1) = e) (Rel : SkipRelation K k D) {Pub : Type}

/-- **The opening claim** on the logical coordinates (`opening_row`: `Σ_c A_c W_c + Σ_j u_j P_j =
Σ_j u_j m_j − constant`): `Σ_j u_j (m_j − P_j)` minus the operand map's adjoint, the terminal pads
read through the level's cells. -/
def openingClaim {C : Type} (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k C) (Lv : Level K ι V)
    (p : Pub) (ch : Challenges K n k) (tr : Transcript K w D n k) : AffineForm K V :=
  AffineForm.sumFin (fun j => ch.u j • (AffineForm.ofConst (tr.terminal j) -
      AffineForm.var (Lv.cell (pc.terminal j)))) - M.adjoint p ch.s ch.r ch.u

theorem eval_openingClaim {C : Type} (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k C)
    (Lv : Level K ι V) (p : Pub) (ch : Challenges K n k) (tr : Transcript K w D n k)
    (x : ι → K) :
    (openingClaim dom M pc Lv p ch tr).eval (Lv.view x) =
      batch ch.u tr.terminal - batch ch.u (pc.read he x).terminal -
        batch ch.u (trueTerminal (M.ops p (Lv.view x)) dom ch.s ch.r) := by
  simp only [openingClaim, AffineForm.eval_sub, AffineForm.eval_sumFin, AffineForm.eval_smul,
    AffineForm.eval_ofConst, AffineForm.eval_var, Lv.view_cell, M.eval_adjoint, batch,
    PadCells.read, Function.comp_apply, mul_sub, Finset.sum_sub_distrib]

omit [Field K] in
/-- **The opening claim reads what the adjoint reads and the terminal pads.** -/
theorem readsOnly_openingClaim [Field K] [DecidableEq V] {C : Type} (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k C) (Lv : Level K ι V) {T : V → Prop}
    (hM : ∀ p s r u, (M.adjoint p s r u).ReadsOnly T) (hT : ∀ i, T (Lv.cell i)) (p : Pub)
    (ch : Challenges K n k) (tr : Transcript K w D n k) :
    (openingClaim dom M pc Lv p ch tr).ReadsOnly T :=
  (AffineForm.ReadsOnly.sumFin fun j => ((AffineForm.ReadsOnly.ofConst _).sub
    (AffineForm.ReadsOnly.var (hT _))).smul _).sub (hM _ _ _ _)

variable [Fintype ι] [Fintype K] [DecidableEq K] (Pub)

/-- **The batch as a masked reduction**: the batch phase, the terminal row and the pads' products on the
cells, and the opening claim on the logical coordinates. -/
def maskedReduction (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k Rel.Cell) (Lv : Level K ι V) :
    FieldProof.MaskedReduction K ι Pub (ι → K) id V 1 where
  n := _
  spec := spec K e D n k
  Lin := Unit
  linear _ tr _ := terminalRow dom he Rel pc (challenges tr) (messages he tr)
  Q := Rel.Cell
  products := pc.products Rel.toPadTriples
  claims p tr _ := openingClaim dom M pc Lv p (challenges tr) (messages he tr)

/-- **The batch's claim reads what the adjoint reads and the pads.** -/
theorem readsOnly_maskedReduction [DecidableEq V] (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k Rel.Cell) (Lv : Level K ι V) {T : V → Prop}
    (hM : ∀ p s r u, (M.adjoint p s r u).ReadsOnly T) (hT : ∀ i, T (Lv.cell i)) :
    (maskedReduction dom he Rel Pub M pc Lv).ReadsOnly fun _ => T := fun p tr _ =>
  readsOnly_openingClaim dom M pc Lv hM hT p _ _

variable {Pub}

/-- **The relation the batch proves** on the cells at public input `p`: the relation on the
operands of the logical assignment, and the pads' products. -/
structure Sat (Q : Relation K k D) (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k Rel.Cell)
    (Lv : Level K ι V) (p : Pub) (x : ι → K) : Prop where
  /-- The relation on the operands. -/
  holds : Holds Q (M.ops p (Lv.view x))
  /-- The pads' products. -/
  product : ProductHolds Rel.toPadTriples (pc.read he x)

/-- **The output of the batch's masked reduction** is the pads' products and the masked verifier's
deferred equations on the pads read from the cells. -/
theorem outHolds_iff (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k Rel.Cell)
    (Lv : Level K ι V) (p : Pub) (tr : Full K e D n k GKR.Schedule.empty) (x : ι → K) :
    (maskedReduction dom he Rel Pub M pc Lv).OutHolds Lv.view p tr x ↔
      ProductHolds Rel.toPadTriples (pc.read he x) ∧
        Deferred Rel dom (M.ops p (Lv.view x)) (challenges tr) (messages he tr)
          (pc.read he x) := by
  constructor
  · intro h
    have hprod := (pc.sourceProducts_iff Rel.toPadTriples he x).mp h.rows.products
    refine ⟨hprod, ⟨?_, ?_⟩⟩
    · exact (terminalRow_eval_eq_zero_iff dom he Rel pc _ _ x).mp (h.rows.linear ())
    · have hc := h.claims 0
      change (openingClaim dom M pc Lv p (challenges tr) (messages he tr)).eval (Lv.view x) = 0
        at hc
      rw [eval_openingClaim dom he] at hc
      linear_combination hc
  · rintro ⟨hprod, hdef⟩
    refine ⟨⟨fun _ => (terminalRow_eval_eq_zero_iff dom he Rel pc _ _ x).mpr hdef.terminal,
      (pc.sourceProducts_iff Rel.toPadTriples he x).mpr hprod⟩, fun _ => ?_⟩
    change (openingClaim dom M pc Lv p (challenges tr) (messages he tr)).eval (Lv.view x) = 0
    rw [eval_openingClaim dom he]
    linear_combination hdef.opening

/-- **The output of the batch's masked reduction gives the verifier's checks** on the transcript unmasked
by the pads read from the cells, and the pads' products. -/
theorem accepts_of_outHolds {Rel : SkipRelation K k D} {Q : Relation K k D} (hX : Rel.Computes Q)
    {M : OperandMap dom Pub V n k} {pc : PadCells ι e D n k Rel.Cell}
    {Lv : Level K ι V} {p : Pub} {tr : Full K e D n k GKR.Schedule.empty} {x : ι → K}
    (h : (maskedReduction dom he Rel Pub M pc Lv).OutHolds Lv.view p tr x) :
    ProductHolds Rel.toPadTriples (pc.read he x) ∧
      Accepts Q (M.ops p (Lv.view x)) dom (challenges tr)
        (unmaskBy (pc.readMsg he x) (messages he tr)) := by
  have h' := (outHolds_iff dom he Rel M pc Lv p tr x).mp h
  exact ⟨h'.1, (deferred_iff hX dom _ h'.1).mp h'.2⟩

/-- **Soundness of the batch's masked reduction**: the phase's reduction from the relation on the operands
and the pads' products, with the phase's errors (`error`: `n/|K|`, `D(w − 1)/|K|`, `(D + 1)/|K|` per
round, `1/|K|`). `NeZero D`: a relation has degree at least one (a parameter condition). -/
noncomputable def maskedReductionSound [NeZero D] {Q : Relation K k D} (hX : Rel.Computes Q)
    (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k Rel.Cell) (Lv : Level K ι V) :
    (maskedReduction dom he Rel Pub M pc Lv).Sound Lv.view (fun p x => Sat dom he Rel Q M pc Lv p x)
      (error K e D n k GKR.Schedule.empty w) where
  reduction := reduction he (fun _ => Q) dom
    (fun c : FieldProof.MaskedRowReduction.Instance Pub (ι → K) => M.ops c.pub (Lv.view c.wit))
    (fun c => pc.readMsg he c.wit)
    (fun c => ProductHolds Rel.toPadTriples (pc.read he c.wit))
    (fun c tr => (maskedReduction dom he Rel Pub M pc Lv).OutHolds Lv.view c.pub tr c.wit)
    fun _ _ h => accepts_of_outHolds dom he hX h
  claim_iff _ _ := ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.holds, h.product⟩⟩
  claimOut_iff _ _ _ := Iff.rfl

/-! ### The honest prover -/

section Causal

omit [Fintype ι] [Fintype K] [DecidableEq K]
variable {Rel} {Q : Relation K k D} (hX : Rel.Computes Q) (ops : Operands K w n k)
  (π : Pads K w D n k Rel.Cell)
include hX

theorem mask_honestMono_skipCausal :
    SkipCausal fun c => mask π (Rel.honestT ops dom c) := by
  intro c c' h
  simp only [SkipRelation.honestT_eq hX, mask, honest, h]

theorem mask_honestMono_roundCausal :
    RoundCausal fun c => mask π (Rel.honestT ops dom c) := by
  intro c c' j hρ hr hs
  simp only [SkipRelation.honestT_eq hX, mask, honest, Pi.add_apply, hρ, hr,
    Sumcheck.EqFactoredDeg.honest_congr c'.rho _ j fun v hv => hs v hv]

theorem mask_honestMono_terminalCausal :
    TerminalCausal fun c => mask π (Rel.honestT ops dom c) := by
  intro c c' _ hr hs
  simp only [SkipRelation.honestT_eq hX, mask, honest, hr, hs]

end Causal

/-- **The honest masked batch phase** on operands `ops` at the free pads `φ`: the honest transcript
by field operations (`SkipRelation.honestT`) sent plus the committed pads of `φ`. -/
def maskedFamily (ops : Operands K w n k) (φ : FreePads K w D n k) :
    CausalTranscript (spec K e D n k) :=
  phaseFamily he (fun c => mask (φ.pads Rel) (Rel.honestT ops dom c))
    fun _ => CausalTranscript.empty _

/-- **The simulated batch phase** at values `v`: the batch transcript that sends the coordinates
of `v` as its messages, whatever the challenges. No prover runs. -/
def valueFamily (v : FreePads K w D n k) : CausalTranscript (spec K e D n k) :=
  valuePhase he v fun _ => CausalTranscript.empty _

omit [Fintype ι] [DecidableEq K] in
/-- **Hiding of the batch phase.** For fixed challenges, the honest masked batch transcript under
uniform free pads has the law of the value family under uniform values, for every operand set. -/
theorem maskedFamily_identDistrib {Q : Relation K k D} (hX : Rel.Computes Q) (ops : Operands K w n k)
    (ch : (spec K e D n k).Challenges) :
    (fun φ => (maskedFamily dom he Rel ops φ).transcript ch) =ᵈ
      (fun v => (valueFamily he v).transcript ch) := by
  have hon : Rel.honestT ops dom = honest Q ops dom := funext (SkipRelation.honestT_eq hX ops dom)
  have h := maskedPhase_identDistrib he (honest_skipCausal Q ops dom)
    (honest_roundCausal Q ops dom) (honest_terminalCausal Q ops dom)
    (tail := fun _ => CausalTranscript.empty _) ch
  simp only [maskedFamily, valueFamily, hon]
  exact h

omit [Fintype ι] [Fintype K] [DecidableEq K] in
/-- **The cells commit the logical assignment and the batch's pads**: the pad cells hold the
free pads, the product cells meet the triples, and the operands of the logical assignment are
the honest assignment's. -/
structure Commits (T : PadTriples k) (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k T.Cell) (Lv : Level K ι V) (p : Pub) (z : V → K)
    (φ : FreePads K w D n k) (x : ι → K) : Prop where
  /-- The message pads' cells hold the free pads. -/
  pads : pc.readMsg he x = ofRevealed φ
  /-- The product cells meet the triples (`fill_pads`). -/
  product : ProductHolds T (pc.read he x)
  /-- The operands are the honest assignment's. -/
  ops : M.ops p (Lv.view x) = M.ops p z

/-- **The simulator of the batch masked reduction**: it sends uniform values (`valueFamily`).
`NeZero w`, `NeZero D`: parameter conditions.

Running time: it writes its coins and the challenges into the transcript, linear in the batch
transcript. This running time is argued here, not proved in Lean. -/
def maskedReductionSim [NeZero w] [NeZero D] (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k Rel.Cell) (Lv : Level K ι V) :
    (maskedReduction dom he Rel Pub M pc Lv).Sim where
  SimCoins := FreePads K w D n k
  sim _ ch v := (valueFamily he v).transcript ch

/-- **The honest batch masked reduction.** The honest input is a logical assignment on whose
operands the relation holds; the prover draws free pads and runs the honest skip on the operands,
pads added (`maskedFamily`). It is simulated by `maskedReductionSim`; the simulation is
`maskedFamily_identDistrib`. `NeZero w`, `NeZero D`: parameter conditions. -/
def maskedReductionHonest [NeZero w] [NeZero D] {Q : Relation K k D} (hX : Rel.Computes Q)
    (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k Rel.Cell) (Lv : Level K ι V) :
    (maskedReduction dom he Rel Pub M pc Lv).Honest Lv.view (V → K)
      (fun p z => Holds Q (M.ops p z)) (maskedReductionSim dom he Rel M pc Lv) where
  Pads := FreePads K w D n k
  prover p z φ := maskedFamily dom he Rel (M.ops p z) φ
  Commits p z φ x := Commits dom he Rel.toPadTriples M pc Lv p z φ x
  complete p z hb φ x hx ch := by
    set ops := M.ops p z
    have hm := messages_phaseFamily he (fun _ => CausalTranscript.empty _) ch
      (mask_honestMono_skipCausal dom hX ops (φ.pads Rel))
      (mask_honestMono_roundCausal dom hX ops (φ.pads Rel))
      (mask_honestMono_terminalCausal dom hX ops (φ.pads Rel))
    have hmask : ∀ t, mask (φ.pads Rel) t = mask (pc.read he x) t := fun t => by
      obtain ⟨h1, h2, h3⟩ := Transcript.mk.inj hx.pads
      simp only [mask, FreePads.pads]
      rw [← h1, ← h2, ← h3]
    refine (outHolds_iff dom he Rel M pc Lv p _ x).mpr ⟨hx.product, ?_⟩
    rw [hx.ops]
    change Deferred Rel dom ops _
      (messages he ((maskedFamily dom he Rel ops φ).transcript ch)) _
    rw [maskedFamily, hm, SkipRelation.honestT_eq hX, hmask]
    exact masked_completeness hX dom hb hx.product _
  identDistrib p z ch := maskedFamily_identDistrib dom he Rel hX (M.ops p z) ch

end MaskedReduction

/-! ### Several relations sharing one `γ` -/

section Merged

open GKR.Schedule (one oneValue)

variable {ι C V : Type} {e D w n k np : ℕ} (dom : SkipPoints K w D)
  (he : (D - 1) * (w - 1) = e) (Rs : Fin np → MonoRelation K k D) [Fintype C] [Encodable C]
  (L : PadLayout (MonoRelation.mergeShape Rs) C) {Pub : Type}

/-- **The merged relation's computations at `γ`**: the merged shape does not depend on `γ`
(`MonoRelation.merge_toMonoShape`), so one layout serves every `γ` (the C++ lays the pads out at
`γ = 1`, `BatchKernel::skip_`). -/
def mergedRel (γ : K) : SkipRelation K k D := (MonoRelation.merge Rs γ).toSkip L

theorem mergedRel_computes (γ : K) :
    (mergedRel Rs L γ).Computes (MonoRelation.merge Rs γ).toRelation :=
  (MonoRelation.merge Rs γ).toSkip_computes L

/-- The `γ` event's degree. -/
theorem mergeEvent_deg {ι' : Type} (Qs : Fin np → MvPolynomial (Fin k) K) (x : ι' → Fin k → K) :
    (mergeEvent Qs x).deg = np - 1 := by
  unfold mergeEvent
  split <;> rfl

/-- The instances of operands, as `FieldSkip.mergeEvent` reads them. -/
def instances (ops : Operands K w n k) : Fin (2 ^ n) × Fin w → Fin k → K := fun t => ops t.1 t.2

/-- **The merged relation holds** exactly when the merged polynomial vanishes on every instance. -/
theorem holds_merge_iff (ops : Operands K w n k) (γ : K) :
    Holds (MonoRelation.merge Rs γ).toRelation ops ↔
      ∀ t, MvPolynomial.eval (instances ops t) (Sumcheck.FieldSkip.merge (fun p => (Rs p).poly) γ) = 0 := by
  rw [MonoRelation.holds_toRelation_iff]
  simp only [instances, ← MonoRelation.eval_merge_poly, Prod.forall]

/-- **Every part holds** exactly when every part's polynomial vanishes on every instance. -/
theorem holds_parts_iff (ops : Operands K w n k) :
    (∀ p, Holds (Rs p).toRelation ops) ↔
      ∀ p t, MvPolynomial.eval (instances ops t) (Rs p).poly = 0 := by
  simp only [MonoRelation.holds_toRelation_iff, instances, MonoRelation.eval_poly, Prod.forall]

variable [Fintype ι] [Fintype K] [DecidableEq K] (Pub)

/-- **The merged batch as a masked reduction** (`batch.h`, `BatchKernel::reduce` with several relations):
`γ` (after the label `gordiehowe.field-batch.gamma`), then the batch phase of the merged relation
`Σ_p γ^p Q_p` at that `γ`: its terminal row and products on the cells and its opening claim. -/
def mergedMaskedReduction (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k C) (Lv : Level K ι V) :
    FieldProof.MaskedReduction K ι Pub (ι → K) id V 1 where
  n := _
  spec := one .V_to_P K ++ spec K e D n k
  Lin := Unit
  linear _ tr _ := terminalRow dom he (mergedRel Rs L (oneValue tr.left)) pc (challenges tr.right)
    (messages he tr.right)
  Q := C
  products := pc.products L.toPadTriples
  claims p tr _ := openingClaim dom M pc Lv p (challenges tr.right)
    (messages he tr.right)

/-- **The merged batch's claim reads what the adjoint reads and the pads.** -/
theorem readsOnly_mergedMaskedReduction [DecidableEq V] (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k C) (Lv : Level K ι V) {T : V → Prop}
    (hM : ∀ p s r u, (M.adjoint p s r u).ReadsOnly T) (hT : ∀ i, T (Lv.cell i)) :
    (mergedMaskedReduction dom he Rs L Pub M pc Lv).ReadsOnly fun _ => T := fun p tr _ =>
  readsOnly_openingClaim dom M pc Lv hM hT p _ _

variable {Pub}

/-- **The relation the merged batch proves** on the cells at public input `p`: every part on the
operands of the logical assignment, and the pads' products. -/
structure MergedSat (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k C) (Lv : Level K ι V)
    (p : Pub) (x : ι → K) : Prop where
  /-- Every part on the operands. -/
  holds : ∀ q, Holds (Rs q).toRelation (M.ops p (Lv.view x))
  /-- The pads' products. -/
  product : ProductHolds L.toPadTriples (pc.read he x)

/-- The merged masked reduction's output is the batch masked reduction's at the merged relation at `γ`. -/
theorem mergedOutHolds_iff (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k C)
    (Lv : Level K ι V) (p : Pub)
    (tr : (mergedMaskedReduction dom he Rs L Pub M pc Lv).spec.Transcript
      (Fin.last (mergedMaskedReduction dom he Rs L Pub M pc Lv).n)) (x : ι → K) :
    (mergedMaskedReduction dom he Rs L Pub M pc Lv).OutHolds Lv.view p tr x ↔
      (maskedReduction dom he (mergedRel Rs L (oneValue tr.left)) Pub M pc Lv).OutHolds Lv.view p tr.right x :=
  ⟨fun h => ⟨h.rows, h.claims⟩, fun h => ⟨h.rows, h.claims⟩⟩

/-- **The `γ` step as a claim reduction**: from every part on the operands to the merged relation at
`γ`, with the merging event (`FieldSkip.mergeEvent`, degree `np − 1`) at `γ`. -/
noncomputable def gammaReduction {Ctx : Type} (ops : Ctx → Operands K w n k) (A : Ctx → Prop) :
    ClaimReduction (one .V_to_P K) Ctx (fun _ => ((np - 1 : ℕ) : ℝ≥0) / Fintype.card K) :=
  ChallengeEventReduction.reduction (one .V_to_P K)
    (fun _ c _ γ => (mergeEvent (fun q => (Rs q).poly) (instances (ops c))).BadAt γ)
    (fun c => (∀ q, Holds (Rs q).toRelation (ops c)) ∧ A c)
    (fun c tr => Holds (MonoRelation.merge Rs (oneValue tr)).toRelation (ops c) ∧ A c)
    (fun _ => ((np - 1 : ℕ) : ℝ≥0) / Fintype.card K)
    (fun c _ _ => by
      have h := ChallengeEvent.card_filter_badAt_le
        (mergeEvent (fun q => (Rs q).poly) (instances (ops c)))
      rw [mergeEvent_deg] at h
      exact h)
    (fun c tr h => by
      rcases merge_sound _ _ ((holds_merge_iff Rs (ops c) _).mp h.1) with hall | hbad
      · exact Or.inl ⟨(holds_parts_iff Rs (ops c)).mpr hall, h.2⟩
      · exact Or.inr ⟨⟨0, rfl⟩, Nat.one_pos, hbad⟩)

/-- **The batch phase of the merged relation at the drawn `γ`** as a claim reduction, after the
`γ` step: from the merged relation at `γ` on the operands and the pads' products to the batch masked
reduction's output at `γ`. -/
noncomputable def mergedPhaseReduction [NeZero D] (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k C) (Lv : Level K ι V) :
    ClaimReduction (spec K e D n k)
      (AppendContext (FieldProof.MaskedRowReduction.Instance Pub (ι → K)) (one .V_to_P K))
      (error K e D n k GKR.Schedule.empty w) :=
  reduction he (fun c => (MonoRelation.merge Rs (oneValue c.transcript)).toRelation) dom
    (fun c => M.ops c.ctx.pub (Lv.view c.ctx.wit)) (fun c => pc.readMsg he c.ctx.wit)
    (fun c => ProductHolds L.toPadTriples (pc.read he c.ctx.wit))
    (fun c tr => (maskedReduction dom he (mergedRel Rs L (oneValue c.transcript)) Pub M pc Lv).OutHolds
      Lv.view c.ctx.pub tr c.ctx.wit)
    fun c _ h => by
      have h' := accepts_of_outHolds dom he (mergedRel_computes Rs L (oneValue c.transcript)) h
      exact ⟨h'.1, h'.2⟩

theorem mergedPhaseReduction_claim [NeZero D] (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k C) (Lv : Level K ι V)
    (c : AppendContext (FieldProof.MaskedRowReduction.Instance Pub (ι → K)) (one .V_to_P K)) :
    (mergedPhaseReduction dom he Rs L M pc Lv).claim c ↔
      Holds (MonoRelation.merge Rs (oneValue c.transcript)).toRelation
        (M.ops c.ctx.pub (Lv.view c.ctx.wit)) ∧ ProductHolds L.toPadTriples (pc.read he c.ctx.wit) :=
  Iff.rfl

/-- **Soundness of the merged batch's masked reduction**: the `γ` step (error `(np − 1)/|K|`), then the
batch phase of the merged relation at `γ` with its errors (`n/|K|`, `D(w − 1)/|K|`, `(D + 1)/|K|`
per round, `1/|K|`), from every part on the operands and the pads' products. -/
noncomputable def mergedMaskedReductionSound [NeZero D] (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k C) (Lv : Level K ι V) :
    (mergedMaskedReduction dom he Rs L Pub M pc Lv).Sound Lv.view
      (fun p x => MergedSat dom he Rs L M pc Lv p x)
      (ProtocolSpec.appendError (fun _ => ((np - 1 : ℕ) : ℝ≥0) / Fintype.card K)
        (error K e D n k GKR.Schedule.empty w)) where
  reduction :=
    (gammaReduction Rs (fun c : FieldProof.MaskedRowReduction.Instance Pub (ι → K) => M.ops c.pub (Lv.view c.wit))
        (fun c => ProductHolds L.toPadTriples (pc.read he c.wit))).seq
      (mergedPhaseReduction dom he Rs L M pc Lv)
      fun c tr h => (mergedPhaseReduction_claim dom he Rs L M pc Lv ⟨c, tr⟩).mp h
  claim_iff _ _ := ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.holds, h.product⟩⟩
  claimOut_iff p x tr := (mergedOutHolds_iff dom he Rs L M pc Lv p tr x).symm

omit [Field K] [DecidableEq K] in
/-- **The merged batch's total error**: `(np − 1)/|K|` for `γ` and the batch phase's. -/
theorem mergedError_sum (w : ℕ) :
    ∑ i, ProtocolSpec.appendError (P₁ := one .V_to_P K)
        (fun _ => ((np - 1 : ℕ) : ℝ≥0) / Fintype.card K)
        (error K e D n k GKR.Schedule.empty w) i =
      ((np - 1 : ℕ) : ℝ≥0) / Fintype.card K + ((n : ℝ≥0) / Fintype.card K +
        ((D * (w - 1) : ℕ) : ℝ≥0) / Fintype.card K + ((D + 1 : ℕ) : ℝ≥0) * n / Fintype.card K +
          1 / Fintype.card K) := by
  rw [ProtocolSpec.sum_appendError, error_sum]
  congr 1
  rw [Fintype.sum_equiv (GKR.Schedule.verifierIndex K) _
    (fun _ => ((np - 1 : ℕ) : ℝ≥0) / Fintype.card K) fun _ => rfl]
  simp

/-- **The honest merged batch phase**: `γ`, then the honest masked batch phase of the merged
relation at `γ`. -/
def mergedFamily (ops : Operands K w n k) (φ : FreePads K w D n k) :
    CausalTranscript (one .V_to_P K ++ spec K e D n k) :=
  (CausalTranscript.oneChallenge K).append fun t =>
    maskedFamily dom he (mergedRel Rs L (oneValue t)) ops φ

/-- **The simulator of the merged batch masked reduction**: it copies `γ`, then sends uniform
values. `NeZero w`, `NeZero D`: parameter conditions.

Running time: it writes its coins and the challenges into the transcript, linear in the batch
transcript. This running time is argued here, not proved in Lean. -/
def mergedMaskedReductionSim [NeZero w] [NeZero D] (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k C) (Lv : Level K ι V) :
    (mergedMaskedReduction dom he Rs L Pub M pc Lv).Sim where
  SimCoins := FreePads K w D n k
  sim _ ch v := ((CausalTranscript.oneChallenge K).append fun _ => valueFamily he v).transcript ch

/-- **The honest merged batch masked reduction.** The honest input is a logical assignment on whose
operands every part holds; the prover takes `γ`, then runs the honest skip of the merged relation
at `γ` (`mergedFamily`). It is simulated by `mergedMaskedReductionSim`. `NeZero w`, `NeZero D`:
parameter conditions. -/
def mergedMaskedReductionHonest [NeZero w] [NeZero D] (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k C) (Lv : Level K ι V) :
    (mergedMaskedReduction dom he Rs L Pub M pc Lv).Honest Lv.view (V → K)
      (fun p z => ∀ q, Holds (Rs q).toRelation (M.ops p z))
      (mergedMaskedReductionSim dom he Rs L M pc Lv) where
  Pads := FreePads K w D n k
  prover p z φ := mergedFamily dom he Rs L (M.ops p z) φ
  Commits p z φ x := Commits dom he L.toPadTriples M pc Lv p z φ x
  complete p z hb φ x hx ch := by
    refine (mergedOutHolds_iff dom he Rs L M pc Lv p _ x).mpr ?_
    have hl := CausalTranscript.append_left (CausalTranscript.oneChallenge K) (fun t =>
      maskedFamily dom he (mergedRel Rs L (oneValue t)) (M.ops p z) φ) ch
    have hr := CausalTranscript.append_right (CausalTranscript.oneChallenge K) (fun t =>
      maskedFamily dom he (mergedRel Rs L (oneValue t)) (M.ops p z) φ) ch
    simp only [mergedFamily]
    erw [hr, hl]
    have hm : Holds (MonoRelation.merge Rs (oneValue ((CausalTranscript.oneChallenge K).transcript
        ch.left))).toRelation (M.ops p z) :=
      (holds_merge_iff Rs _ _).mpr fun t => merge_complete _ _
        ((holds_parts_iff Rs _).mp hb) _ t
    exact (maskedReductionHonest dom he (mergedRel Rs L _) (mergedRel_computes Rs L _) M pc Lv).complete
      p z hm φ x hx ch.right
  identDistrib p z ch :=
    (maskedFamily_identDistrib dom he (mergedRel Rs L (oneValue
      ((CausalTranscript.oneChallenge K).transcript ch.left))) (mergedRel_computes Rs L _)
      (M.ops p z) ch.right).comp
      (ProtocolSpec.Transcript.join ((CausalTranscript.oneChallenge K).transcript ch.left))

end Merged

/-! ### The uniform simulator -/

section Uniform

open GKR.Schedule (one)
open HashCircuit.Skip (alt altFamily oneMsg oneChal)

/-- The message types of the alternating rounds are finite. -/
instance alt_typeFintype {M C : Type} [Fintype M] [Fintype C] :
    (k : ℕ) → ∀ i, Fintype ((alt M C k).Type i)
  | 0 => GKR.Schedule.empty_typeFintype
  | k + 1 =>
    letI := alt_typeFintype (M := M) (C := C) k
    inferInstanceAs (∀ i, Fintype ((one .P_to_V M ++ (one .V_to_P C ++ alt M C k)).Type i))

/-- The message types of the alternating rounds are nonempty. -/
instance alt_typeNonempty {M C : Type} [Nonempty M] [Nonempty C] :
    (k : ℕ) → ∀ i, Nonempty ((alt M C k).Type i)
  | 0 => GKR.Schedule.empty_typeNonempty
  | k + 1 =>
    haveI := alt_typeNonempty (M := M) (C := C) k
    inferInstanceAs (∀ i, Nonempty ((one .P_to_V M ++ (one .V_to_P C ++ alt M C k)).Type i))

/-- The messages of `k + 1` alternating rounds: the first message, and the later ones. -/
def altValuesEquiv {M : Type} (k : ℕ) : (Fin (k + 1) → M) ≃ M × (Unit × (Fin k → M)) where
  toFun v := (v 0, ((), fun j => v j.succ))
  invFun x := Fin.cons x.1 x.2.2
  left_inv v := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  right_inv x := by
    obtain ⟨a, ⟨⟩, t⟩ := x
    rfl

/-- **Alternating rounds sending fixed messages** form a value family whose value is the messages:
the challenges and the messages give the transcript, and back. -/
theorem altFamily_const_bijective {M C : Type} [Zero C] : (k : ℕ) →
    CausalTranscript.ValuesBijective fun v : Fin k → M => altFamily (C := C) k fun _ j => v j
  | 0 => (CausalTranscript.valuesBijective_empty _).comp_equiv (Equiv.ofUnique _ _)
  | k + 1 => ((CausalTranscript.valuesBijective_oneMessage M).append
      ((CausalTranscript.valuesBijective_oneChallenge C).append
        (altFamily_const_bijective k))).comp_equiv (altValuesEquiv k)

variable {e D w n k : ℕ}

/-- The message types of the batch phase followed by `R` are finite when those of `R` are. -/
instance phase_typeFintype [Fintype K] {mR : ℕ} {R : ProtocolSpec mR}
    [∀ i, Fintype (R.Type i)] : ∀ i, Fintype ((phase K e D n k R).Type i) :=
  @ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype
    (@ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype
      (@ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype
        (@ProtocolSpec.appendTypeFintype _ _ _ _ (alt_typeFintype n)
          (@ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype
            (@ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype inferInstance)))))

/-- The message types of the batch phase followed by `R` are nonempty when those of `R` are. -/
instance phase_typeNonempty {mR : ℕ} {R : ProtocolSpec mR} [∀ i, Nonempty (R.Type i)] :
    ∀ i, Nonempty ((phase K e D n k R).Type i) :=
  haveI : Nonempty K := ⟨0⟩
  @ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
    (@ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
      (@ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
        (@ProtocolSpec.appendTypeNonempty _ _ _ _ (alt_typeNonempty n)
          (@ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
            (@ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
              inferInstance)))))

/-- The message types of the batch phase are finite. -/
instance spec_typeFintype [Fintype K] : ∀ i, Fintype ((spec K e D n k).Type i) :=
  phase_typeFintype (R := GKR.Schedule.empty)

/-- The message types of the batch phase are nonempty. -/
instance spec_typeNonempty : ∀ i, Nonempty ((spec K e D n k).Type i) :=
  phase_typeNonempty (R := GKR.Schedule.empty)

/-- The values of the batch phase in the order it sends them: nothing for `ρ`, the skip values,
nothing for `r`, the round coefficients, the terminal claims, nothing for `u`. -/
def phaseValuesEquiv (he : (D - 1) * (w - 1) = e) :
    FreePads K w D n k ≃ Unit × ((Fin e → K) × (Unit × ((Fin n → Fin D → K) ×
      ((Fin k → K) × (Unit × Unit))))) where
  toFun v := ((), (fun i => v.skip (Fin.cast he.symm i), ((), (v.rounds, (v.terminal, ((), ()))))))
  invFun x := ⟨fun i => x.2.1 (Fin.cast he i), x.2.2.2.1, x.2.2.2.2.1⟩
  left_inv v := rfl
  right_inv x := by
    obtain ⟨⟨⟩, s, ⟨⟩, r, t, ⟨⟩, ⟨⟩⟩ := x
    rfl

/-- **The batch value family is bijective**: the simulated batch transcript, as a function of the
challenges and the sent values, is a bijection onto the full transcripts. -/
theorem valueFamily_bijective (he : (D - 1) * (w - 1) = e) :
    CausalTranscript.ValuesBijective (valueFamily (K := K) (n := n) (k := k) he) :=
  ((CausalTranscript.valuesBijective_oneChallenge (Fin n → K)).append
    ((CausalTranscript.valuesBijective_oneMessage (Fin e → K)).append
      ((CausalTranscript.valuesBijective_oneChallenge K).append
        ((altFamily_const_bijective (C := K) n).append
          ((CausalTranscript.valuesBijective_oneMessage (Fin k → K)).append
            ((CausalTranscript.valuesBijective_oneChallenge (Fin k → K)).append
              (CausalTranscript.valuesBijective_empty _))))))).comp_equiv (phaseValuesEquiv he)

variable {ι V Pub : Type} [Fintype ι] [Fintype K] [DecidableEq K] (dom : SkipPoints K w D)
  (he : (D - 1) * (w - 1) = e)

/-- The batch masked reduction's simulator is a bijection onto the full transcripts. -/
theorem maskedReductionHonest_simBijective [NeZero w] [NeZero D] {Rel : SkipRelation K k D}
    {Q : Relation K k D} (hX : Rel.Computes Q) (M : OperandMap dom Pub V n k)
    (pc : PadCells ι e D n k Rel.Cell) (Lv : Level K ι V) :
    (maskedReductionHonest dom he Rel hX M pc Lv).SimBijective := fun _ =>
  valueFamily_bijective (K := K) (n := n) (k := k) he

/-- The merged batch masked reduction's simulator is a bijection onto the full transcripts: it copies `γ`,
then sends its coins. -/
theorem mergedMaskedReductionHonest_simBijective [NeZero w] [NeZero D] {C : Type} [Fintype C] [Encodable C]
    {np : ℕ} (Rs : Fin np → MonoRelation K k D) (L : PadLayout (MonoRelation.mergeShape Rs) C)
    (M : OperandMap dom Pub V n k) (pc : PadCells ι e D n k C) (Lv : Level K ι V) :
    (mergedMaskedReductionHonest dom he Rs L M pc Lv).SimBijective := fun _ =>
  (valueFamily_bijective (K := K) (n := n) (k := k) he).oneChallenge_append

end Uniform

end GordieHowe.BatchedZerocheck
