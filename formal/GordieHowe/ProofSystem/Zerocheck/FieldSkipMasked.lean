-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.FieldSkipMono

@[expose] public section

/-!
# The masked skip zerocheck at any degree, for any relation with pad products

The masking of the C++ batch driver (`lib/gordiehowe/compiler/field_skip.h`, `MaskedFieldSkip`) for
a relation of degree at most `D`, stated once for every way of writing the relation and its pad
products down.

* **A relation with its pad products** (`SkipRelation K k D`): the relation's polynomial
  (`FieldSkip.Relation`, for the events), its value by field operations (`eval`), the product
  cells (`Cell`), each one quadratic triple of a terminal pad or a product cell and a terminal pad
  (`left`, `right`; `pad_quadratic`), their honest values (`fill`, `fill_pads`), the pad term of
  the terminal check as an affine form on the terminal pads and product cells (`padForm`,
  `terminal_expr`: `Q(m − P) = Q(m) + padForm m` under the triples), and the honest round
  messages by field operations (`honestRounds`, `MaskedFieldSkip::round_sums`). Instance: a
  relation given as monomials with a `PadLayout` (`MonoRelation.toSkip`, the C++
  `FieldRelation`).
* **The pads** (`Pads`, `MaskedFieldSkip::Layout`): one per message coordinate (the
  `(D − 1)(w − 1)` skip values, `D` per round, the `k` terminal claims) and the product cells,
  which the commitment checks as quadratic triples (`ProductHolds`).
* **Masking** (`MaskedFieldSkip::prove`, `mask(v)`: `v += pads[pad++]`): the prover sends
  `m = x + P`; the verifier reads the unmasked value as `m − P` (`message(x, at)`) (`unmask`). The
  running claim is affine in the messages (`EqFactoredDeg.claims_add`), so the terminal row is the
  claim from the sent values minus the claim from the pads, and the terminal identity
  `claim = eq(ρ, s) · Q(m − P)` expands into `Q(m)` and the pad term.
* **Soundness** (`masked_soundness`): the deferred equations and the products give
  `FieldSkip.Accepts` on the unmasked transcript (`deferred_iff`), so `FieldSkip.soundness`'s
  events, each evaluated on the unmasked transcript. **Completeness** (`masked_completeness`,
  `masked_completeness_free`): the honest transcript sent masked passes every deferred equation;
  the honest product cells are `fill` of the free pads.
-/

namespace GordieHowe.Sumcheck.FieldSkip

/-- **The product cells of a masked skip** (`field_skip.h`, `pad_quadratic`): the cells, each one
quadratic triple whose first factor is a terminal pad or a product cell (`left`) and whose second
is a terminal pad (`right`). -/
structure PadTriples (k : ℕ) where
  /-- The product cells. -/
  Cell : Type
  [fintype : Fintype Cell]
  /-- The product cells' encoding, which numbers them (`Encodable.fintypeEquivFin`). -/
  [encodable : Encodable Cell]
  /-- Each product cell's first factor: a terminal pad or a product cell. -/
  left : Cell → Fin k ⊕ Cell
  /-- Each product cell's second factor: a terminal pad. -/
  right : Cell → Fin k

attribute [instance] PadTriples.fintype PadTriples.encodable

/-- **A batched relation's computations** (`field_skip.h`, `MaskedFieldSkip`): what the masked skip
computes from a relation of degree at most `D` on `k` operands, all by field operations: the
product cells, the relation's value (`FieldRelation::eval`), the honest product cells
(`fill_pads`), the pad term of the terminal check as an affine form on the terminal pads and product
cells (`terminal_expr`), and the honest round messages (`round_sums`). That they are those of a
polynomial relation `Q` is `Computes`. -/
structure SkipRelation (K : Type) [Field K] (k D : ℕ) extends PadTriples k where
  /-- The relation's value. -/
  eval : (Fin k → K) → K
  /-- The honest product cells of terminal pads. -/
  fill : (Fin k → K) → Cell → K
  /-- The pad term of the terminal check. -/
  padForm : (Fin k → K) → AffineForm K (Fin k ⊕ Cell)
  /-- The honest round messages. -/
  honestRounds : ∀ {w n : ℕ}, Operands K w n k → SkipPoints K w D → (Fin n → K) → K →
    (Fin n → K) → Fin n → Fin D → K

/-- **The computations are a relation's**: the value is `Q`'s, the honest product cells meet the
triples, under the triples `Q(m − P) = Q(m) + padForm m`, and the honest round messages are
`EqFactoredDeg.honest`'s for `Q`. -/
structure SkipRelation.Computes {K : Type} [Field K] {k D : ℕ} (X : SkipRelation K k D)
    (Q : Relation K k D) : Prop where
  /-- The value is the polynomial's. -/
  eval_eq : ∀ x, MvPolynomial.eval x Q.Q = X.eval x
  /-- The honest product cells meet the triples. -/
  fill_triples : ∀ P c, Sum.elim P (X.fill P) (X.left c) * P (X.right c) = X.fill P c
  /-- Under the triples, `Q(m − P) = Q(m) + padForm m`. -/
  eval_sub : ∀ (P : Fin k → K) (Pr : X.Cell → K),
    (∀ c, Sum.elim P Pr (X.left c) * P (X.right c) = Pr c) →
      ∀ m, X.eval (m - P) = X.eval m + (X.padForm m).eval (Sum.elim P Pr)
  /-- The honest round messages are `EqFactoredDeg.honest`'s. -/
  honestRounds_eq : ∀ {w n : ℕ} (ops : Operands K w n k) (dom : SkipPoints K w D)
    (ρ : Fin n → K) (r : K) (s : Fin n → K),
    X.honestRounds ops dom ρ r s = EqFactoredDeg.honest ρ (residualMle Q ops dom r) s

namespace SkipRelation

variable {K : Type} [Field K] {k D w n : ℕ} (X : SkipRelation K k D) {Q : Relation K k D}

/-- **The honest transcript by field operations** (`MaskedFieldSkip::prove`): the skip values
`Σ_r eq(ρ, r) Q(Σ_z L_z(p) ops(r, z))`, the round messages (`honestRounds`) and the operands'
multilinear extensions at `(s, r)` (`opEvalDec`). Equal to `FieldSkip.honest` (`honestT_eq`). -/
def honestT (ops : Operands K w n k) (dom : SkipPoints K w D) (ch : Challenges K n k) :
    Transcript K w D n k where
  skip i := ∑ r : Fin (2 ^ n), PackedClaim.eqPt ch.rho r *
    X.eval (fun j => dom.interpEval (fun z => ops r z j) (dom.point (Sum.inr i)))
  rounds := X.honestRounds ops dom ch.rho ch.r ch.s
  terminal j := opEvalDec ops dom j ch.s ch.r

theorem honestT_eq {X : SkipRelation K k D} (hX : X.Computes Q) (ops : Operands K w n k)
    (dom : SkipPoints K w D) (ch : Challenges K n k) :
    X.honestT ops dom ch = honest Q ops dom ch := by
  simp only [honestT, honest, hX.honestRounds_eq, opEvalDec_eq, zeroEval, hX.eval_eq]
  rfl

/-- The relation vanishes on zero operands. -/
theorem eval_zero {X : SkipRelation K k D} (hX : X.Computes Q) : X.eval 0 = 0 := by
  rw [← hX.eval_eq]
  exact Q.eval_zero_Q

/-- **The batch holds** exactly when the relation's value vanishes on every instance. -/
theorem holds_iff {X : SkipRelation K k D} (hX : X.Computes Q) (ops : Operands K w n k) :
    Holds Q ops ↔ ∀ r z, X.eval (ops r z) = 0 := by
  simp only [Holds, residual, hX.eval_eq]

end SkipRelation

/-! ### The instances -/

/-- The triples of a pad layout. -/
abbrev PadLayout.toPadTriples {k : ℕ} {C : Type} [Fintype C] [Encodable C] {S : MonoShape k}
    (L : PadLayout S C) :
    PadTriples k :=
  ⟨C, L.left, L.right⟩

namespace MonoRelation

variable {K : Type} [Field K] {k D : ℕ} {C : Type} [Fintype C] [Encodable C]
  (R : MonoRelation K k D)
  (L : PadLayout R.toMonoShape C)

/-- **The pad term as an affine form** (`terminal_expr`): each monomial's choices of pads
(`Fin (2^d)`, the C++ masks, through `finFunctionFinEquiv`), each choice's coefficient times the
coordinate holding its pads. -/
def padForm (m : Fin k → K) : AffineForm K (Fin k ⊕ C) :=
  AffineForm.sumFin fun i : Fin R.nm => R.coeff i • AffineForm.sumFin fun mask : Fin (2 ^ R.deg i) =>
    choiceTerm (finFunctionFinEquiv.symm mask) (fun t => m (R.ops i t)) 1 •
      AffineForm.var (L.cell i (finFunctionFinEquiv.symm mask))

/-- A choice term is linear in its value. -/
theorem choiceTerm_eq_mul {d : ℕ} (x : Fin d → Fin 2) (a : Fin d → K) (v : K) :
    choiceTerm x a v = choiceTerm x a 1 * v := by
  unfold choiceTerm
  split_ifs <;> ring

omit [Fintype C] [Encodable C] in
theorem eval_padForm (m : Fin k → K) (read : Fin k ⊕ C → K) :
    (R.padForm L m).eval read = R.padTerm L m read := by
  simp only [padForm, padTerm, AffineForm.eval_sumFin, AffineForm.eval_smul, AffineForm.eval_var]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  refine Fintype.sum_equiv finFunctionFinEquiv.symm _ _ fun mask => ?_
  rw [choiceTerm_eq_mul _ _ (read _)]

/-- **A relation as monomials with its pad products** (`FieldRelation`, `pad_monomials`): the
masked skip's relation of the C++ batch driver. -/
abbrev toSkip : SkipRelation K k D where
  toPadTriples := L.toPadTriples
  eval := R.eval
  fill := L.fill
  padForm := R.padForm L
  honestRounds ops dom ρ r s := honestRoundsMono R ops dom ρ r s

/-- The monomials' computations are the relation's. -/
theorem toSkip_computes : (R.toSkip L).Computes R.toRelation where
  eval_eq := R.eval_toRelation
  fill_triples := L.triplesHold_fill
  eval_sub P Pr h m :=
    (R.eval_sub_eq L h m).trans (congrArg (R.eval m + ·) (R.eval_padForm L m (Sum.elim P Pr)).symm)
  honestRounds_eq ops dom ρ r s := honestRoundsMono_eq R ops dom ρ r s

/-- **A relation of any degree with the C++'s product chains** (`MaskedFieldSkip`: `products =
pad_monomials()`, one `pad_quadratic` triple per product): `toSkip` at `MonoShape.chainLayout`.
Every statement about a `SkipRelation` that `Computes` its relation applies at any `D`:
soundness (`masked_soundness`), completeness (`masked_completeness_free`), and, for the batch
stage, `GordieHowe.BatchedZerocheck.maskedReductionSound`, `maskedReductionHonest` and `maskedFamily_identDistrib`
(zero knowledge: uniform sent values). -/
abbrev chainSkip : SkipRelation K k D := R.toSkip R.chainLayout

/-- The product chains' computations are the relation's. -/
theorem chainSkip_computes : R.chainSkip.Computes R.toRelation := R.toSkip_computes _

end MonoRelation

end GordieHowe.Sumcheck.FieldSkip

namespace GordieHowe.Sumcheck.FieldSkipMasked

open FieldSkip

variable {K : Type} [Field K] {w D n k : ℕ} {C : Type}

/-- **The committed pads of a masked skip** (`MaskedFieldSkip::Layout`): one per skip value, `D`
per round, one per terminal claim, and the product cells `C`. -/
structure Pads (K : Type) (w D n k : ℕ) (C : Type) where
  /-- The pads of the skip values. -/
  skip : Fin ((D - 1) * (w - 1)) → K
  /-- The pads of each round's `D` coefficients. -/
  rounds : Fin n → Fin D → K
  /-- The pads of the terminal claims. -/
  terminal : Fin k → K
  /-- The product cells. -/
  product : C → K

/-- **The pads' quadratic constraints** (`pad_quadratic`): the triples on the terminal pads and
the product cells. -/
def ProductHolds (T : PadTriples k) (π : Pads K w D n k T.Cell) : Prop :=
  ∀ c, Sum.elim π.terminal π.product (T.left c) * π.terminal (T.right c) = π.product c

variable (X : SkipRelation K k D) {Q : Relation K k D}

/-- **The unmasked transcript** `sent − pad` (`MaskedFieldSkip::message`). -/
def unmask (π : Pads K w D n k C) (tr : Transcript K w D n k) : Transcript K w D n k where
  skip := tr.skip - π.skip
  rounds := tr.rounds - π.rounds
  terminal := tr.terminal - π.terminal

/-- **The transcript an honest prover sends** for unmasked messages `tr`: `tr + pad`
(`MaskedFieldSkip::prove`, `mask`). -/
def mask (π : Pads K w D n k C) (tr : Transcript K w D n k) : Transcript K w D n k where
  skip := tr.skip + π.skip
  rounds := tr.rounds + π.rounds
  terminal := tr.terminal + π.terminal

theorem unmask_mask (π : Pads K w D n k C) (tr : Transcript K w D n k) :
    unmask π (mask π tr) = tr := by
  cases tr
  simp [unmask, mask]

theorem skipClaim_sub (dom : SkipPoints K w D) (x y : Fin ((D - 1) * (w - 1)) → K) (r : K) :
    dom.skipClaim (x - y) r = dom.skipClaim x r - dom.skipClaim y r := by
  simp [SkipPoints.skipClaim, sub_mul, Finset.sum_sub_distrib]

/-- The verifier's running claim at `sent − pad`: the claim from the sent values minus the claim
from the pads (`EqFactoredDeg.claims_add`). -/
theorem claims_unmask (dom : SkipPoints K w D) (ch : Challenges K n k) (π : Pads K w D n k C)
    (tr : Transcript K w D n k) (i : Fin (n + 1)) :
    EqFactoredDeg.claims (dom.skipClaim (unmask π tr).skip ch.r) ch.rho (unmask π tr).rounds ch.s i =
      EqFactoredDeg.claims (dom.skipClaim tr.skip ch.r) ch.rho tr.rounds ch.s i -
        EqFactoredDeg.claims (dom.skipClaim π.skip ch.r) ch.rho π.rounds ch.s i := by
  have h := EqFactoredDeg.claims_add (dom.skipClaim (unmask π tr).skip ch.r)
    (dom.skipClaim π.skip ch.r) ch.rho (unmask π tr).rounds π.rounds ch.s i
  have hs : dom.skipClaim (unmask π tr).skip ch.r + dom.skipClaim π.skip ch.r =
      dom.skipClaim tr.skip ch.r := by
    simp only [unmask, skipClaim_sub, sub_add_cancel]
  have hr : (unmask π tr).rounds + π.rounds = tr.rounds := by
    simp only [unmask, sub_add_cancel]
  rw [hs, hr] at h
  rw [h, add_sub_cancel_right]

/-- The terminal identity at `sent − pad`, with the pads' products read from the product cells
(`terminal_expr`). -/
theorem terminalValue_unmask {X : SkipRelation K k D} (hX : X.Computes Q) (ch : Challenges K n k)
    {π : Pads K w D n k X.Cell} (hπ : ProductHolds X.toPadTriples π) (tr : Transcript K w D n k) :
    terminalValue Q ch.rho ch.s (unmask π tr).terminal =
      EqPolynomial.eqProd ch.rho ch.s *
        (X.eval tr.terminal + (X.padForm tr.terminal).eval (Sum.elim π.terminal π.product)) := by
  simp only [terminalValue, unmask, hX.eval_eq, hX.eval_sub π.terminal π.product hπ]

/-- **The deferred equations of the masked verifier** in the C++ row form (`rows_of`: the terminal
row, the claim from the sent values and the pads equal to `eq(ρ, s) · Q(m − P)` expanded; and
`opening_row`). -/
structure Deferred (dom : SkipPoints K w D) (ops : Operands K w n k) (ch : Challenges K n k)
    (tr : Transcript K w D n k) (π : Pads K w D n k X.Cell) : Prop where
  /-- The terminal row. -/
  terminal : EqFactoredDeg.claims (dom.skipClaim tr.skip ch.r) ch.rho tr.rounds ch.s (Fin.last n) -
      EqFactoredDeg.claims (dom.skipClaim π.skip ch.r) ch.rho π.rounds ch.s (Fin.last n) =
    EqPolynomial.eqProd ch.rho ch.s *
      (X.eval tr.terminal + (X.padForm tr.terminal).eval (Sum.elim π.terminal π.product))
  /-- The opening row. -/
  opening : batch ch.u tr.terminal - batch ch.u π.terminal =
    batch ch.u (trueTerminal ops dom ch.s ch.r)

/-- Under the products, the deferred equations on the sent transcript are exactly the unmasked
verifier's checks on `sent − pad`. -/
theorem deferred_iff {X : SkipRelation K k D} (hX : X.Computes Q) (dom : SkipPoints K w D)
    (ops : Operands K w n k) {ch : Challenges K n k}
    {tr : Transcript K w D n k} {π : Pads K w D n k X.Cell} (hπ : ProductHolds X.toPadTriples π) :
    Deferred X dom ops ch tr π ↔ Accepts Q ops dom ch (unmask π tr) := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · rw [claims_unmask, terminalValue_unmask hX ch hπ, h.terminal]
    · change batch ch.u (tr.terminal - π.terminal) = _
      rw [FieldSkipPads.batch_sub, h.opening]
  · intro h
    refine ⟨?_, ?_⟩
    · rw [← claims_unmask, h.sumcheck, terminalValue_unmask hX ch hπ]
    · rw [← FieldSkipPads.batch_sub]
      exact h.opening

/-- **Soundness of the masked verifier**: its deferred equations and the products give the batch
or one of `FieldSkip.soundness`'s events, each evaluated on the unmasked transcript `sent − pad`.
`hπ` is the commitment's quadratic constraints on the pads; `NeZero D` a parameter condition. -/
theorem masked_soundness [NeZero D] {X : SkipRelation K k D} (hX : X.Computes Q)
    (dom : SkipPoints K w D) (ops : Operands K w n k)
    {ch : Challenges K n k} {tr : Transcript K w D n k} {π : Pads K w D n k X.Cell}
    (hπ : ProductHolds X.toPadTriples π) (h : Deferred X dom ops ch tr π) :
    Holds Q ops ∨ (rhoEvent Q ops).BadAt ch.rho ∨
      (rEvent Q ops dom ch.rho (unmask π tr).skip).BadAt ch.r ∨
      (∃ i, (roundEvent Q ops dom ch.rho ch.r (unmask π tr).skip (unmask π tr).rounds
        ch.s i).BadAt (ch.s i)) ∨
      (uEvent ops dom ch.s ch.r (unmask π tr).terminal).BadAt ch.u :=
  soundness Q ops dom ((deferred_iff hX dom ops hπ).mp h)

/-- **Completeness of the masked verifier**: a batch that holds, pads meeting the products, and
the honest transcript sent masked pass every deferred equation for every challenge. -/
theorem masked_completeness [NeZero w] [NeZero D] {X : SkipRelation K k D} (hX : X.Computes Q)
    (dom : SkipPoints K w D) {ops : Operands K w n k}
    (h : Holds Q ops) {π : Pads K w D n k X.Cell} (hπ : ProductHolds X.toPadTriples π)
    (ch : Challenges K n k) :
    Deferred X dom ops ch (mask π (honest Q ops dom ch)) π := by
  rw [deferred_iff hX dom ops hπ, unmask_mask]
  exact completeness Q ops dom h ch

/-! ### Free pads -/

/-- **The pads the honest prover draws**: one per sent coordinate. The product cells are derived
(`FreePads.pads`, `fill_pads`). -/
structure FreePads (K : Type) (w D n k : ℕ) where
  /-- The skip pads. -/
  skip : Fin ((D - 1) * (w - 1)) → K
  /-- The round pads. -/
  rounds : Fin n → Fin D → K
  /-- The terminal pads. -/
  terminal : Fin k → K

namespace FreePads

/-- The free pads as a triple, for their group and finite-type structure. -/
def equivProd {K : Type} : FreePads K w D n k ≃
    (Fin ((D - 1) * (w - 1)) → K) × (Fin n → Fin D → K) × (Fin k → K) where
  toFun φ := (φ.skip, φ.rounds, φ.terminal)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance {K : Type} [Fintype K] : Fintype (FreePads K w D n k) :=
  Fintype.ofEquiv _ equivProd.symm

instance {K : Type} [Nonempty K] : Nonempty (FreePads K w D n k) := equivProd.nonempty

instance : AddCommGroup (FreePads K w D n k) := equivProd.addCommGroup

@[simp] theorem add_skip (φ ψ : FreePads K w D n k) : (φ + ψ).skip = φ.skip + ψ.skip := rfl
@[simp] theorem add_rounds (φ ψ : FreePads K w D n k) :
    (φ + ψ).rounds = φ.rounds + ψ.rounds := rfl
@[simp] theorem add_terminal (φ ψ : FreePads K w D n k) :
    (φ + ψ).terminal = φ.terminal + ψ.terminal := rfl

variable (X : SkipRelation K k D) {Q : Relation K k D}

/-- **The committed pads** of free pads: the free pads, and the product cells at their honest
values (`SkipRelation.fill`, `fill_pads`). -/
def pads (φ : FreePads K w D n k) : Pads K w D n k X.Cell :=
  ⟨φ.skip, φ.rounds, φ.terminal, X.fill φ.terminal⟩

/-- The committed pads of free pads meet the products. -/
theorem productHolds {X : SkipRelation K k D} {Q : Relation K k D} (hX : X.Computes Q)
    (φ : FreePads K w D n k) : ProductHolds X.toPadTriples (φ.pads X) :=
  hX.fill_triples φ.terminal

end FreePads

/-- The sent coordinates of a transcript, in the shape of the free pads. -/
def revealed (tr : Transcript K w D n k) : FreePads K w D n k := ⟨tr.skip, tr.rounds, tr.terminal⟩

/-- The transcript whose sent coordinates are `v`. -/
def ofRevealed (v : FreePads K w D n k) : Transcript K w D n k := ⟨v.skip, v.rounds, v.terminal⟩

/-- The transcript sent at the committed pads of free pads `φ` has the honest values plus `φ`. -/
theorem mask_eq_ofRevealed (tr : Transcript K w D n k) (φ : FreePads K w D n k) :
    mask (φ.pads X) tr = ofRevealed (revealed tr + φ) := rfl

/-- **Completeness at free pads.** -/
theorem masked_completeness_free [NeZero w] [NeZero D] {X : SkipRelation K k D}
    (hX : X.Computes Q) (dom : SkipPoints K w D)
    {ops : Operands K w n k} (h : Holds Q ops) (φ : FreePads K w D n k)
    (ch : Challenges K n k) :
    Deferred X dom ops ch (mask (φ.pads X) (honest Q ops dom ch)) (φ.pads X) :=
  masked_completeness hX dom h (FreePads.productHolds hX φ) ch

end GordieHowe.Sumcheck.FieldSkipMasked
