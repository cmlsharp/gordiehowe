-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.IOP.ClaimReduction
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim
public import GordieHowe.Foundations.Algebra.QuadraticSystem
public import GordieHowe.Foundations.Algebra.AffineForm
public import Mathlib.Algebra.MvPolynomial.Degrees

@[expose] public section

/-!
# Polynomial representation of masked GKR transcript checks

This models `ConstraintBuilder::first`, `next`, `finalize`, and `setup_lqc` in
`lib/zk/zk_common.h`. Masked values are unmasked by adding their committed pads.
Each layer starts at the preceding layer's two claims (zero at layer zero),
reconstructs p(1) from the preceding claim and p(0), and interpolates the three
values with the verifier's supplied coefficients. The final claim equals the
wiring factor times the product of the two unmasked next claims.

The linear finalization equation uses a committed product pad; the accompanying
quadratic equation binds it to the product of the two claim pads. The polynomial
representation and equivalence are proved (`system_holds_iff`, `valueExpr_eval`).
`GKR.CircuitFlatten` computes the challenge and wiring fields from a source circuit;
`GKR.SourceReduction` constructs the corresponding statistical reduction, and
`GordieHowe.GKR.LayeredCircuit.maskedReduction` presents it as a masked reduction.
-/

namespace GordieHowe.GKR.Transcript
open IOP

open MvPolynomial

variable {F ι PadIdx : Type} [Field F]

/-- A finite affine expression used by the generic constraint builder. -/
inductive Affine (F ι : Type)
  | constant : F → Affine F ι
  | variable : ι → Affine F ι
  | add : Affine F ι → Affine F ι → Affine F ι
  | sub : Affine F ι → Affine F ι → Affine F ι
  | scale : F → Affine F ι → Affine F ι

namespace Affine

def eval (w : ι → F) : Affine F ι → F
  | .constant x => x
  | .variable i => w i
  | .add p q => eval w p + eval w q
  | .sub p q => eval w p - eval w q
  | .scale x p => x * eval w p

noncomputable def polynomial : Affine F ι → MvPolynomial ι F
  | .constant x => C x
  | .variable i => X i
  | .add p q => polynomial p + polynomial q
  | .sub p q => polynomial p - polynomial q
  | .scale x p => C x * polynomial p

/-- The expression as an affine form (computable): the verifier's row. Its polynomial is
`polynomial` (`toMvPolynomial_form`). -/
def form : Affine F ι → AffineForm F ι
  | .constant x => .ofConst x
  | .variable i => .var i
  | .add p q => form p + form q
  | .sub p q => form p - form q
  | .scale x p => x • form p

@[simp] theorem toMvPolynomial_form (p : Affine F ι) : p.form.toMvPolynomial = p.polynomial := by
  induction p <;> simp_all [form, polynomial]

@[simp] theorem eval_form (w : ι → F) (p : Affine F ι) : p.form.eval w = p.eval w := by
  induction p <;> simp_all [form, eval]

theorem polynomial_eval (w : ι → F) (p : Affine F ι) :
    MvPolynomial.eval w p.polynomial = p.eval w := by
  induction p <;> simp_all [polynomial, eval]

theorem polynomial_degree (p : Affine F ι) : p.polynomial.totalDegree ≤ 1 := by
  induction p with
  | constant => simp [polynomial]
  | «variable» => simp [polynomial]
  | add p q hp hq => exact (totalDegree_add _ _).trans (max_le hp hq)
  | sub p q hp hq => exact (totalDegree_sub _ _).trans (max_le hp hq)
  | scale c p hp => exact (totalDegree_mul _ _).trans (by simpa using hp)

end Affine

/-- Fixed pad allocation. The two polynomial coordinates represent p(0), p(η),
where η is the field's third interpolation node (not necessarily the cast of 2);
the three claim coordinates represent left, right, and their product. -/
structure Layout (PadIdx : Type) (L : ℕ) where
  rounds : Fin (L + 1) → ℕ
  polyPad : (l : Fin (L + 1)) → Fin (rounds l) → Fin 2 → PadIdx
  claimPad : Fin (L + 1) → Fin 3 → PadIdx

/-- Public transcript and verifier-derived interpolation and wiring coefficients.
The layout fixes the number of layers and rounds before challenges are drawn. -/
structure _root_.GordieHowe.GKR.Transcript (F PadIdx : Type) (L : ℕ) (layout : Layout PadIdx L) where
  alpha : Fin (L + 1) → F
  lag : (l : Fin (L + 1)) → Fin (layout.rounds l) → Fin 3 → F
  hp : (l : Fin (L + 1)) → Fin (layout.rounds l) → Fin 2 → F
  wc : Fin (L + 1) → Fin 2 → F
  eqq : Fin (L + 1) → F
  inputAlpha : F

variable {L : ℕ} (layout : Layout PadIdx L) (tr : Transcript F PadIdx L layout)

def unmasked (p : PadIdx → F) (l : Fin (L + 1)) (h : Fin 2) : F :=
  tr.wc l h + p (layout.claimPad l ⟨h.val, by omega⟩)

def start (p : PadIdx → F) (l : Fin (L + 1)) : F :=
  if h : l.val = 0 then 0 else
    let prev : Fin (L + 1) := ⟨l.val - 1, by omega⟩
    unmasked layout tr p prev 0 + tr.alpha l * unmasked layout tr p prev 1

def step (p : PadIdx → F) (l : Fin (L + 1)) (claim : F)
    (r : Fin (layout.rounds l)) : F :=
  let p0 := tr.hp l r 0 + p (layout.polyPad l r 0)
  let p2 := tr.hp l r 1 + p (layout.polyPad l r 1)
  tr.lag l r 1 * (claim - p0) + tr.lag l r 0 * p0 + tr.lag l r 2 * p2

/-- Reconstruct p(1)=previous−p(0), then evaluate the quadratic polynomial using
its three interpolation coefficients, in the verifier's round order. -/
def claim (p : PadIdx → F) (l : Fin (L + 1)) : F :=
  (List.finRange (layout.rounds l)).foldl (step layout tr p l) (start layout tr p l)

/-- Unmasked GKR recurrence and binding of the auxiliary product pad. -/
def PadOK (p : PadIdx → F) : Prop :=
  ∀ l, p (layout.claimPad l 0) * p (layout.claimPad l 1) = p (layout.claimPad l 2) ∧
    claim layout tr p l = tr.eqq l * unmasked layout tr p l 0 * unmasked layout tr p l 1

/-- Terminal input claim, including its two committed masking pads. -/
def value (p : PadIdx → F) : F :=
  unmasked layout tr p (Fin.last L) 0 +
    tr.inputAlpha * unmasked layout tr p (Fin.last L) 1

variable (coord : PadIdx → ι)

def unmaskedExpr (l : Fin (L + 1)) (h : Fin 2) : Affine F ι :=
  .add (.constant (tr.wc l h)) (.variable (coord (layout.claimPad l ⟨h.val, by omega⟩)))

def startExpr (l : Fin (L + 1)) : Affine F ι :=
  if h : l.val = 0 then .constant 0 else
    let prev : Fin (L + 1) := ⟨l.val - 1, by omega⟩
    .add (unmaskedExpr layout tr coord prev 0)
      (.scale (tr.alpha l) (unmaskedExpr layout tr coord prev 1))

def stepExpr (l : Fin (L + 1)) (acc : Affine F ι)
    (r : Fin (layout.rounds l)) : Affine F ι :=
  let p0 := Affine.add (.constant (tr.hp l r 0)) (.variable (coord (layout.polyPad l r 0)))
  let p2 := Affine.add (.constant (tr.hp l r 1)) (.variable (coord (layout.polyPad l r 1)))
  .add (.add (.scale (tr.lag l r 1) (.sub acc p0)) (.scale (tr.lag l r 0) p0))
    (.scale (tr.lag l r 2) p2)

def claimExpr (l : Fin (L + 1)) : Affine F ι :=
  (List.finRange (layout.rounds l)).foldl (stepExpr layout tr coord l)
    (startExpr layout tr coord l)

theorem unmaskedExpr_eval (w : ι → F) (l : Fin (L + 1)) (h : Fin 2) :
    (unmaskedExpr layout tr coord l h).eval w = unmasked layout tr (w ∘ coord) l h := rfl

theorem startExpr_eval (w : ι → F) (l : Fin (L + 1)) :
    (startExpr layout tr coord l).eval w = start layout tr (w ∘ coord) l := by
  unfold startExpr start
  split <;> rfl

theorem stepExpr_eval (w : ι → F) (l : Fin (L + 1)) (acc : Affine F ι)
    (r : Fin (layout.rounds l)) :
    (stepExpr layout tr coord l acc r).eval w = step layout tr (w ∘ coord) l (acc.eval w) r := rfl

theorem fold_stepExpr_eval (w : ι → F) (l : Fin (L + 1))
    (rs : List (Fin (layout.rounds l))) (acc : Affine F ι) :
    (rs.foldl (stepExpr layout tr coord l) acc).eval w =
      rs.foldl (step layout tr (w ∘ coord) l) (acc.eval w) := by
  induction rs generalizing acc with
  | nil => rfl
  | cons r rs ih => simpa only [List.foldl_cons, stepExpr_eval] using ih (stepExpr layout tr coord l acc r)

theorem claimExpr_eval (w : ι → F) (l : Fin (L + 1)) :
    (claimExpr layout tr coord l).eval w = claim layout tr (w ∘ coord) l := by
  rw [claimExpr, fold_stepExpr_eval, startExpr_eval]
  rfl

/-- `finalize` uses a linear row: the quadratic product of pads is represented
by the separately constrained third claim pad. -/
def finalExpr (l : Fin (L + 1)) : Affine F ι :=
  .sub (claimExpr layout tr coord l)
    (.scale (tr.eqq l)
      (.add (.add (.add (.constant (tr.wc l 0 * tr.wc l 1))
        (.scale (tr.wc l 1) (.variable (coord (layout.claimPad l 0)))))
        (.scale (tr.wc l 0) (.variable (coord (layout.claimPad l 1)))))
        (.variable (coord (layout.claimPad l 2)))))

noncomputable def productPolynomial (l : Fin (L + 1)) : MvPolynomial ι F :=
  X (coord (layout.claimPad l 0)) * X (coord (layout.claimPad l 1)) -
    X (coord (layout.claimPad l 2))

theorem productPolynomial_degree (l : Fin (L + 1)) :
    (productPolynomial layout coord l (F := F)).totalDegree ≤ 2 := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_mul _ _).trans (by simp)
  · simp

noncomputable def system : QuadraticSystem F ι where
  Eq := Fin (L + 1) ⊕ Fin (L + 1)
  polynomial := Sum.elim (fun l => (finalExpr layout tr coord l).polynomial)
    (productPolynomial layout coord)
  degree := by
    rintro (l | l)
    · exact ((finalExpr layout tr coord l).polynomial_degree).trans (by decide)
    · exact productPolynomial_degree layout coord l

theorem finalExpr_eval_iff (w : ι → F) (l : Fin (L + 1))
    (hp : w (coord (layout.claimPad l 0)) * w (coord (layout.claimPad l 1)) =
      w (coord (layout.claimPad l 2))) :
    (finalExpr layout tr coord l).eval w = 0 ↔
      claim layout tr (w ∘ coord) l =
        tr.eqq l * unmasked layout tr (w ∘ coord) l 0 * unmasked layout tr (w ∘ coord) l 1 := by
  simp only [finalExpr, Affine.eval, claimExpr_eval, sub_eq_zero]
  simp only [unmasked, Function.comp_apply]
  change (claim layout tr (w ∘ coord) l = tr.eqq l *
    (tr.wc l 0 * tr.wc l 1 + tr.wc l 1 * w (coord (layout.claimPad l 0)) +
      tr.wc l 0 * w (coord (layout.claimPad l 1)) + w (coord (layout.claimPad l 2)))) ↔
    claim layout tr (w ∘ coord) l = tr.eqq l *
      (tr.wc l 0 + w (coord (layout.claimPad l 0))) *
      (tr.wc l 1 + w (coord (layout.claimPad l 1)))
  rw [← hp]
  ring_nf

theorem system_holds_iff (w : ι → F) :
    (system layout tr coord).Holds w ↔ PadOK layout tr (w ∘ coord) := by
  simp only [QuadraticSystem.Holds, system, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Affine.polynomial_eval, productPolynomial, map_sub, map_mul, eval_X, sub_eq_zero]
  constructor
  · rintro ⟨hfinal, hprod⟩ l
    exact ⟨hprod l, (finalExpr_eval_iff layout tr coord w l (hprod l)).mp (hfinal l)⟩
  · intro h
    exact ⟨fun l => (finalExpr_eval_iff layout tr coord w l (h l).1).mpr (h l).2,
      fun l => (h l).1⟩

def valueExpr : Affine F ι :=
  .add (unmaskedExpr layout tr coord (Fin.last L) 0)
    (.scale tr.inputAlpha (unmaskedExpr layout tr coord (Fin.last L) 1))

theorem valueExpr_eval (w : ι → F) :
    (valueExpr layout tr coord).eval w = value layout tr (w ∘ coord) := rfl

variable (F) in
/-- **The GKR interaction tied to the explicit masked-transcript recurrence**: the protocol
`spec` and the readouts of its full transcript, the two terminal input points `g0`, `g1` and the
flat masked transcript `transcript` the deferred rows read. This is the computational part,
following CHVY25 Figure 1, steps 4–6; its soundness for a relation, with its round errors, is
`Interaction.Sound`, kept separate so that the protocol and the rows of a concrete instance are
computable definitions (the split of `MaskedRowReduction` and `MaskedRowReduction.Sound`).
`GKR.SourceReduction.ofCircuit` constructs it from the typed no-copy schedule of a source
circuit; with an affine input readout it gives a masked reduction (`GKR.LayeredCircuit.maskedReduction`). -/
structure Interaction (PadIdx : Type) (d : ℕ) {L : ℕ} (layout : Layout PadIdx L) where
  /-- The number of moves. -/
  n : ℕ
  /-- The protocol. -/
  spec : ProtocolSpec n
  [fintype : ∀ i, Fintype (spec.Challenge i)]
  [decEq : ∀ i, DecidableEq (spec.Challenge i)]
  [nonempty : ∀ i, Nonempty (spec.Challenge i)]
  /-- The first terminal input point. -/
  g0 : spec.Transcript (Fin.last n) → Fin d → F
  /-- The second terminal input point. -/
  g1 : spec.Transcript (Fin.last n) → Fin d → F
  /-- The flat masked transcript the deferred rows read. -/
  transcript : spec.Transcript (Fin.last n) → Transcript F PadIdx L layout

attribute [instance] Interaction.fintype Interaction.decEq Interaction.nonempty

/-- **Soundness of a GKR interaction** with per-round errors `ε`: `reduction` reduces circuit
satisfaction `sat` on the input readout `input` (`claim_iff`) to the pad equations `PadOK` and the
terminal input claim on the committed pads `pads` (`claimOut_iff`), round by round. The interface
follows CHVY25 Figure 1, steps 4–6, and the layered-sumcheck argument in Theorem 4.1's proof. -/
structure Interaction.Sound {L : ℕ} {layout : Layout PadIdx L} {d : ℕ}
    (G : Interaction F PadIdx d layout) {Pub Wit : Type} (input : Pub → Wit → Fin (2 ^ d) → F)
    (pads : Wit → (PadIdx → F)) (sat : Pub → Wit → Prop) (ε : G.spec.ChallengeIdx → NNReal) where
  /-- The reduction from `sat` to the terminal claims. -/
  reduction : ClaimReduction G.spec (Pub × Wit) ε
  claim_iff : ∀ pub w, reduction.claim (pub, w) ↔ sat pub w
  claimOut_iff : ∀ pub w tr, reduction.claimOut (pub, w) tr ↔
    PadOK layout (G.transcript tr) (pads w) ∧
      ∑ x : Fin (2 ^ d),
        PackedClaim.claimCoeff (G.g0 tr) (G.g1 tr) (G.transcript tr).inputAlpha x * input pub w x =
          value layout (G.transcript tr) (pads w)

end GordieHowe.GKR.Transcript
