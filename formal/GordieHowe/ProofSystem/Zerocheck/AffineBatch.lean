-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.SkipBatchPhase
public import GordieHowe.ProofSystem.Zerocheck.SkipBatch
public import GordieHowe.ProofSystem.Zerocheck.BitSumcheckIP
public import GordieHowe.Headline
public import GordieHowe.ProofSystem.FieldProof.MaskedReduction
public import GordieHowe.Applications.Keccak.HashCircuit.Skip
public import GordieHowe.ProofSystem.Ligero.Routing
public import GordieHowe.Foundations.Algebra.AffineForm

@[expose] public section

/-!
# A batch on affine operands, at any degree

The batch stage (`GordieHowe/ProofSystem/Zerocheck/SkipBatch.lean`) at a relation of degree at most `D` given as
monomials (`FieldSkip.MonoRelation`, the C++ `FieldRelation`) with the C++'s product chains
(`MonoRelation.chainSkip`: one product cell per multiset of at least two operands dividing a
monomial, `field_skip.h`, `pad_monomials`), and an affine operand map (`OperandMap.affine`, the C++
`AffineOperandMap`): `N` instances, operand `j` of instance `t` the affine form `form p t j` on
logical coordinates `V`, read at the public input `p`. This is the batched relation of a compiled
program's domain (`compiler/compiled_domain.h`, `group_kernel`: one relation for the group, every
predicate's instances added to one `FieldViewMap`), whose operands are affine views of phase-0
committed cells (`compiler/batch_form.h`).

* **The batch** (`AffineBatch K Pub V`): the relation, the forms, the skip domain of width `w` and
  degree `D`, the rounds `n` with `N ≤ 2^n w`. It holds at `p` on an assignment `z` when the
  relation vanishes on every instance's operands (`Holds`); the stage's relation on the affine
  map's operands is the batch (`map_holds_iff`).
* **The pads** (`Pad`, `PadIdx`): `(D − 1)(w − 1)` skip pads, `D` per round, `k` terminal pads, one
  product cell per chain cell (`MaskedFieldSkip::Layout`; `card_pad`).
* **The masked reduction** (`ip`, at an embedding of the pads among the cells and a level): the batch stage's
  masked reduction; its soundness (`sound`) for the batch on the logical assignment and the pads' products,
  with the phase's errors; its honest prover (`honest`) on assignments where the batch holds, with the
  honest pad values (`padValue`) and the commitment condition (`commits_of`).
-/

namespace GordieHowe.BatchedZerocheck

open IOP Sumcheck.FieldSkip Sumcheck.FieldSkipMasked
open scoped NNReal

/-- **The index of a batch's pads** (`MaskedFieldSkip::Layout`): `e` skip values, `D` per round of
`n`, the `k` terminal claims, the product cells `C`. -/
inductive PadIdx (e D n k : ℕ) (C : Type)
  /-- The pad of skip value `i`. -/
  | skip (i : Fin e)
  /-- The pad of coefficient `d` of round `i`. -/
  | round (i : Fin n) (d : Fin D)
  /-- The pad of terminal claim `j`. -/
  | terminal (j : Fin k)
  /-- Product cell `c`. -/
  | product (c : C)

namespace PadIdx

variable {e D n k : ℕ} {C : Type}

/-- The pad index as blocks. -/
def equivSum : PadIdx e D n k C ≃ Fin e ⊕ ((Fin n × Fin D) ⊕ (Fin k ⊕ C)) where
  toFun
    | .skip i => .inl i
    | .round i d => .inr (.inl (i, d))
    | .terminal j => .inr (.inr (.inl j))
    | .product c => .inr (.inr (.inr c))
  invFun
    | .inl i => .skip i
    | .inr (.inl (i, d)) => .round i d
    | .inr (.inr (.inl j)) => .terminal j
    | .inr (.inr (.inr c)) => .product c
  left_inv p := by cases p <;> rfl
  right_inv x := by rcases x with i | ⟨i, d⟩ | j | c <;> rfl

instance [Fintype C] : Fintype (PadIdx e D n k C) := Fintype.ofEquiv _ equivSum.symm

instance [DecidableEq C] : DecidableEq (PadIdx e D n k C) := equivSum.decidableEq

/-- The pads are encoded as blocks (`equivSum`). -/
instance [Encodable C] : Encodable (PadIdx e D n k C) := Encodable.ofEquiv _ equivSum

end PadIdx

/-- **A batch on affine operands** with public inputs `Pub` and logical coordinates `V`: the
relation (`k` operands, degree at most `D`, as monomials), the form of operand `j` of instance
`t < N` at each public input, the skip domain of width `w` (`D(w − 1) + 1` points), the rounds `n`,
the instances fitting the rows (`fits`), a nonzero width (`width_ne`) and a nonzero degree
(`degree_ne`), all parameter conditions. -/
structure AffineBatch (K Pub V : Type) [Field K] where
  /-- The operands. -/
  k : ℕ
  /-- The degree. -/
  D : ℕ
  /-- The instances. -/
  N : ℕ
  /-- The skip width. -/
  w : ℕ
  /-- The sumcheck rounds. -/
  n : ℕ
  /-- The relation. -/
  rel : MonoRelation K k D
  /-- The form of operand `j` of instance `t`. -/
  form : Pub → Fin N → Fin k → AffineForm K V
  /-- The skip domain. -/
  dom : SkipPoints K w D
  /-- The instances fit the rows. -/
  fits : N ≤ 2 ^ n * w
  /-- The width is nonzero. -/
  width_ne : w ≠ 0
  /-- The degree is nonzero. -/
  degree_ne : D ≠ 0

namespace AffineBatch

variable {K Pub V : Type} [Field K] (B : AffineBatch K Pub V)

/-- The skip pads of the batch: `(D − 1)(w − 1)`. -/
abbrev e : ℕ := (B.D - 1) * (B.w - 1)

/-- The product cells of the batch (`pad_monomials`). -/
abbrev Cell : Type := B.rel.ChainCell

/-- **The number of product cells** (`pad_monomials`): the multisets of at least two operands
dividing a monomial. -/
abbrev m : ℕ := B.rel.padMonomials.card

theorem card_cell : Fintype.card B.Cell = B.m := Fintype.card_coe _

/-- The pads of the batch (`MaskedFieldSkip::Layout`). -/
abbrev Pad : Type := PadIdx B.e B.D B.n B.k B.Cell

/-- **The batch holds** at the public input `p` on an assignment `z`: the relation vanishes on
every instance's operands. -/
def Holds (p : Pub) (z : V → K) : Prop := ∀ t, B.rel.eval (fun j => (B.form p t j).eval z) = 0

/-- **The affine operand map** of the batch (`AffineOperandMap`). -/
def map : OperandMap B.dom Pub V B.n B.k := OperandMap.affine B.dom B.N B.form

/-- **The stage's relation on the affine map's operands is the batch** (`affine_holds_iff`: the
instances fit the rows, and the zero instances beyond `N` satisfy a relation with no constant
term). -/
theorem map_holds_iff (p : Pub) (z : V → K) :
    Sumcheck.FieldSkip.Holds B.rel.toRelation (B.map.ops p z) ↔ B.Holds p z :=
  affine_holds_iff B.dom B.rel.chainSkip_computes B.fits B.form p z

/-- **The batch's pad cells** at an embedding `e` of its pads. -/
def padCells {ι : Type} (e : B.Pad → ι) : BatchedZerocheck.PadCells ι B.e B.D B.n B.k B.Cell where
  skip i := e (.skip i)
  rounds i d := e (.round i d)
  terminal j := e (.terminal j)
  product c := e (.product c)

variable {ι : Type} [Fintype ι] [Fintype K] [DecidableEq K] (Pub)

/-- **The batch's masked reduction** at the pad embedding `e` and the level `Lv`: the batch stage's masked
reduction at the relation with the C++'s product chains, the affine operand map and the pad cells. -/
def ip (e : B.Pad → ι) (Lv : Level K ι V) : FieldProof.MaskedReduction K ι Pub (ι → K) id V 1 :=
  maskedReduction B.dom rfl B.rel.chainSkip Pub B.map (B.padCells e) Lv

/-- **The batch's claim reads what its forms read and the pads.** -/
theorem readsOnly_ip [DecidableEq V] (e : B.Pad → ι) (Lv : Level K ι V) {T : V → Prop}
    (h : ∀ p t j, (B.form p t j).ReadsOnly T) (hT : ∀ i, T (Lv.cell i)) :
    (B.ip Pub e Lv).ReadsOnly fun _ => T :=
  readsOnly_maskedReduction _ _ _ _ _ _ _ (readsOnly_affine_adjoint _ _ _ h) hT

variable {Pub}

/-- **The relation the batch's masked reduction proves** on the cells at the public input `p`: the batch on
the logical assignment, and the pads' products. -/
structure Sat (e : B.Pad → ι) (Lv : Level K ι V) (p : Pub) (x : ι → K) : Prop where
  /-- The batch on the logical assignment. -/
  holds : B.Holds p (Lv.view x)
  /-- The pads' products. -/
  product : ProductHolds B.rel.chainSkip.toPadTriples ((B.padCells e).read rfl x)

/-- The batch's round errors: the batch phase's at degree `D`. -/
noncomputable abbrev error : (spec K B.e B.D B.n B.k).ChallengeIdx → ℝ≥0 :=
  BatchedZerocheck.error K B.e B.D B.n B.k GKR.Schedule.empty B.w

omit [DecidableEq K] in
/-- **The batch's total error**: `n/|K|`, `D(w − 1)/|K|`, `(D + 1)n/|K|` and `1/|K|`. -/
theorem error_sum : ∑ i, B.error i = (B.n : ℝ≥0) / Fintype.card K +
    ((B.D * (B.w - 1) : ℕ) : ℝ≥0) / Fintype.card K +
      ((B.D + 1 : ℕ) : ℝ≥0) * B.n / Fintype.card K + 1 / Fintype.card K :=
  BatchedZerocheck.error_sum K _ B.D B.n B.k GKR.Schedule.empty B.w

/-- **Soundness of the batch's masked reduction**: the batch stage's (`BatchedZerocheck.maskedReductionSound`), from the
batch on the logical assignment and the pads' products, with the phase's errors. -/
noncomputable def sound (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.ip Pub e Lv).Sound Lv.view (B.Sat e Lv) B.error :=
  haveI : NeZero B.D := ⟨B.degree_ne⟩
  (maskedReductionSound B.dom rfl B.rel.chainSkip B.rel.chainSkip_computes B.map (B.padCells e) Lv).congr
    fun p _ => ⟨fun h => ⟨(B.map_holds_iff p _).mp h.holds, h.product⟩,
      fun h => ⟨(B.map_holds_iff p _).mpr h.holds, h.product⟩⟩

/-- **The honest pad values** of free pads (`fill_pads`): the free pads, and each product cell the
product of its multiset's terminal pads. -/
def padValue (φ : FreePads K B.w B.D B.n B.k) : B.Pad → K
  | .skip i => φ.skip i
  | .round i d => φ.rounds i d
  | .terminal j => φ.terminal j
  | .product c => B.rel.chainLayout.fill φ.terminal c

variable (Pub)

/-- **The simulator of the batch masked reduction**: the batch stage's
(`BatchedZerocheck.maskedReductionSim`).

Running time: `BatchedZerocheck.maskedReductionSim`'s, linear in the batch transcript.
This running time is argued here, not proved in Lean. -/
def sim (e : B.Pad → ι) (Lv : Level K ι V) : (B.ip Pub e Lv).Sim :=
  haveI : NeZero B.w := ⟨B.width_ne⟩
  haveI : NeZero B.D := ⟨B.degree_ne⟩
  maskedReductionSim B.dom rfl B.rel.chainSkip B.map (B.padCells e) Lv

/-- **The honest batch masked reduction**, on assignments where the batch holds: the batch stage's
(`BatchedZerocheck.maskedReductionHonest`) through `map_holds_iff`, simulated by `sim`.
Noncomputable only through the relation's polynomial, which the prover does not compute with. -/
noncomputable def honest (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.ip Pub e Lv).Honest Lv.view (V → K) (fun p z => B.Holds p z) (B.sim Pub e Lv) :=
  haveI : NeZero B.w := ⟨B.width_ne⟩
  haveI : NeZero B.D := ⟨B.degree_ne⟩
  (maskedReductionHonest B.dom rfl B.rel.chainSkip B.rel.chainSkip_computes B.map (B.padCells e) Lv).comap
    (fun _ z => z) fun p z h => (B.map_holds_iff p z).mpr h

variable {Pub}

/-- **Cells holding the honest pad values commit the honest assignment**: the pad cells hold the
free pads and the products, and the operands of the logical assignment are the honest
assignment's. -/
theorem commits_of (e : B.Pad → ι) (Lv : Level K ι V) (p : Pub) (z : V → K)
    (φ : FreePads K B.w B.D B.n B.k) (x : ι → K) (hz : B.map.ops p (Lv.view x) = B.map.ops p z)
    (hp : x ∘ e = B.padValue φ) : (B.honest Pub e Lv).Commits p z φ x := by
  have h : ∀ q, x (e q) = B.padValue φ q := fun q => congrFun hp q
  have hy : ∀ y : Fin B.k ⊕ B.Cell, Sum.elim (x ∘ (B.padCells e).terminal)
      (x ∘ (B.padCells e).product) y = Sum.elim φ.terminal (B.rel.chainLayout.fill φ.terminal) y :=
    fun y => by rcases y with j | c <;> exact h _
  refine ⟨?_, fun c => ?_, hz⟩
  · change Transcript.mk _ _ _ = Transcript.mk _ _ _
    congr 1
    · exact funext fun i => h (.skip _)
    · exact funext fun i => funext fun d => h (.round i d)
    · exact funext fun j => h (.terminal j)
  · change Sum.elim (x ∘ (B.padCells e).terminal) (x ∘ (B.padCells e).product)
        (B.rel.chainLayout.left c) * x ((B.padCells e).terminal (B.rel.chainLayout.right c)) =
      x ((B.padCells e).product c)
    rw [hy]
    change _ * x (e (.terminal _)) = x (e (.product c))
    rw [h, h]
    exact B.rel.chainLayout.triplesHold_fill φ.terminal c

/-! ### Zero knowledge with respect to the uniform simulator -/

/-- The message types of the batch's masked reduction are finite. -/
instance ip_typeFintype (e : B.Pad → ι) (Lv : Level K ι V) :
    ∀ i, Fintype ((B.ip Pub e Lv).spec.Type i) :=
  BatchedZerocheck.spec_typeFintype

/-- The message types of the batch's masked reduction are nonempty. -/
instance ip_typeNonempty (e : B.Pad → ι) (Lv : Level K ι V) :
    ∀ i, Nonempty ((B.ip Pub e Lv).spec.Type i) :=
  BatchedZerocheck.spec_typeNonempty

/-- The batch's simulator is a bijection onto the full transcripts. -/
theorem honest_simBijective (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.honest Pub e Lv).SimBijective :=
  haveI : NeZero B.w := ⟨B.width_ne⟩
  haveI : NeZero B.D := ⟨B.degree_ne⟩
  maskedReductionHonest_simBijective B.dom rfl B.rel.chainSkip_computes B.map (B.padCells e) Lv

/-- **Honest-verifier zero knowledge of the batch** with error `0` with respect to the uniform
simulator (paper `def:red-sec` (c)): at every public input and every logical assignment, the honest
transcript under uniform challenges and uniform free pads is a uniform full transcript. -/
@[headline]
theorem hvzk (e : B.Pad → ι) (Lv : Level K ι V) : (B.honest Pub e Lv).UniformHVZK :=
  (B.honest_simBijective e Lv).uniformHVZK

/-! ### The bit sumcheck -/

section BitSumcheck

variable [DecidableEq V] {m nw : ℕ}

variable (Pub) in
/-- **The batch's masked reduction with the bit sumcheck** (`MaskedReduction.bitSumcheck`) at the bit layout `L`:
the batch's masked reduction, then the masked sumcheck over the bit-index variables of its words, whose
output claim replaces the opening claim. -/
def bitIp (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    FieldProof.MaskedReduction K ι Pub (ι → K) id V 1 :=
  (B.ip Pub e Lv).bitSumcheck L Lv

omit [DecidableEq K] [DecidableEq V] in
variable (m) in
/-- **The errors of the batch with the bit sumcheck**: the batch phase's, then `2/|K|` per bit
round. -/
noncomputable abbrev bitError :
    (spec K B.e B.D B.n B.k ++ HashCircuit.Skip.alt (Fin 2 → K) K m).ChallengeIdx → ℝ≥0 :=
  FieldProof.MaskedReduction.bitSumcheckError (K := K) m B.error

omit [DecidableEq K] [DecidableEq V] in
/-- **The total error of the batch with the bit sumcheck**: the batch's, `n/|K|`,
`D(w − 1)/|K|`, `(D + 1)n/|K|` and `1/|K|`, plus `2m/|K|` for the `m` bit rounds. -/
theorem bitError_sum : ∑ i, B.bitError m i = (B.n : ℝ≥0) / Fintype.card K +
    ((B.D * (B.w - 1) : ℕ) : ℝ≥0) / Fintype.card K +
      ((B.D + 1 : ℕ) : ℝ≥0) * B.n / Fintype.card K + 1 / Fintype.card K +
        ((2 * m : ℕ) : ℝ≥0) / Fintype.card K := by
  rw [FieldProof.MaskedReduction.sum_bitSumcheckError, B.error_sum]

/-- **Soundness of the batch with the bit sumcheck**: the batch's relation (the batch on the
logical assignment and the pads' products), with the batch's errors and `2/|K|` per bit round. -/
noncomputable def bitSumcheckSound (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitIp Pub e Lv L).Sound Lv.view (B.Sat e Lv) (B.bitError m) :=
  (B.sound e Lv).bitSumcheck

variable (Pub) in
/-- **The simulator of the batch with the bit sumcheck**: the batch's simulator, then uniform values
(`MaskedReduction.Sim.bitSumcheck`).

Running time: the batch's simulator's and a copy of `2m` coins, linear in the transcript. This
running time is argued here, not proved in Lean. -/
def bitSim (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) : (B.bitIp Pub e Lv L).Sim :=
  FieldProof.MaskedReduction.Sim.bitSumcheck L (B.sim Pub e Lv)

variable (Pub) in
/-- **The honest batch with the bit sumcheck**, on assignments where the batch holds: the honest
batch, then the honest bit rounds at the assignment's bits (`MaskedReduction.Honest.bitSumcheck`),
simulated by `bitSim`. -/
noncomputable def bitHonest (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitIp Pub e Lv L).Honest Lv.view (V → K) (fun p z => B.Holds p z) (B.bitSim Pub e Lv L) :=
  (B.honest Pub e Lv).bitSumcheck L fun _ z => L.bits z

/-- **The cells commit the honest batch with the bit sumcheck** when they commit the honest batch,
the bit rounds' pads and the assignment's bits. -/
theorem bitCommits_of (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) (p : Pub)
    (z : V → K) (φ : FreePads K B.w B.D B.n B.k) (ψ : Fin m → Fin 2 → K) (x : ι → K)
    (hb : (B.honest Pub e Lv).Commits p z φ x) (hl : L.Commits Lv (L.bits z) ψ x) :
    (B.bitHonest Pub e Lv L).Commits p z (φ, ψ) x :=
  ⟨hb, hl⟩

/-- The message types of the batch's masked reduction with the bit sumcheck are finite. -/
instance bitIp_typeFintype (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    ∀ i, Fintype ((B.bitIp Pub e Lv L).spec.Type i) :=
  FieldProof.MaskedReduction.bitSumcheck_typeFintype (M := B.ip Pub e Lv)

/-- The message types of the batch's masked reduction with the bit sumcheck are nonempty. -/
instance bitIp_typeNonempty (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    ∀ i, Nonempty ((B.bitIp Pub e Lv L).spec.Type i) :=
  FieldProof.MaskedReduction.bitSumcheck_typeNonempty (M := B.ip Pub e Lv)

/-- The simulator of the batch with the bit sumcheck is a bijection onto the full transcripts. -/
theorem bitHonest_simBijective (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitHonest Pub e Lv L).SimBijective :=
  (B.honest_simBijective e Lv).bitSumcheck _

/-- **Honest-verifier zero knowledge of the batch with the bit sumcheck** with error `0` with
respect to the uniform simulator (paper `def:red-sec` (c)): at every public input and every
logical assignment, the honest transcript under uniform challenges, uniform free pads and uniform
bit-round pads is a uniform full transcript. -/
@[headline]
theorem bitHvzk (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitHonest Pub e Lv L).UniformHVZK :=
  (B.bitHonest_simBijective e Lv L).uniformHVZK

end BitSumcheck

end AffineBatch

end GordieHowe.BatchedZerocheck
