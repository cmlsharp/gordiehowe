-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.AffineBatch
public import GordieHowe.ProofSystem.RingSwitching.PackingRoute
public import GordieHowe.Headline

@[expose] public section

/-!
# A merged batch on affine operands

The batch stage's merged form (`GordieHowe.BatchedZerocheck.mergedMaskedReduction`; `batch.h`,
`FieldOperands::relation(gamma)`: `field_batch(name, tables, parts, width)` with several parts of
one instance count runs one zerocheck of `Σ_p γ^p Q_p` over the concatenated operands) on an affine
operand map (`OperandMap.affine`), as `AffineBatch` is the single relation's:

* **The batch** (`MergedAffineBatch K Pub V`): `np` relations of degree at most `D` on one operand
  vector of `k` operands (each part reads its own operands of the vector), the forms, the skip
  domain of width `w` and degree `D`, the rounds `n` with `N ≤ 2^n w`. It holds at `p` on `z` when
  every relation vanishes on every instance's operands (`Holds`, `map_holds_iff`).
* **The pads** (`Pad`): the batch's pad index (`PadIdx`) at the product cells of the merged shape's
  chains (`MonoRelation.mergeShape`, `MonoShape.chainLayout`), which do not depend on `γ`.
* **The masked reduction** (`ip`): `γ`, then the batch phase of `Σ_p γ^p Q_p`; its soundness (`sound`) with
  the errors `(np − 1)/|K|` at `γ` and the batch phase's (`error_sum`); its honest prover (`honest`)
  on assignments where every relation holds, with the honest pad values (`padValue`) and the
  commitment condition (`commits_of`).
* **A batch stage** (`BatchStage.merged`), as `BatchStage.one` is for `AffineBatch`.
-/

namespace GordieHowe.BatchedZerocheck

open IOP Sumcheck.FieldSkip Sumcheck.FieldSkipMasked
open scoped NNReal

/-- **A merged batch on affine operands** with public inputs `Pub` and logical coordinates `V`:
`np` relations (`k` operands, degree at most `D`, as monomials) on one operand vector, the form of
operand `j` of instance `t < N` at each public input, the skip domain of width `w`
(`D(w − 1) + 1` points), the rounds `n`, the instances fitting the rows (`fits`), a nonzero width
(`width_ne`) and a nonzero degree (`degree_ne`), all parameter conditions. -/
structure MergedAffineBatch (K Pub V : Type) [Field K] where
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
  /-- The relations. -/
  np : ℕ
  /-- Relation `q`. -/
  rels : Fin np → MonoRelation K k D
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

namespace MergedAffineBatch

variable {K Pub V : Type} [Field K] (B : MergedAffineBatch K Pub V)

/-- The skip pads of the batch: `(D − 1)(w − 1)`. -/
abbrev e : ℕ := (B.D - 1) * (B.w - 1)

/-- **The merged shape** of the relations (`MonoRelation.mergeShape`): their monomials in order,
the same at every `γ`. -/
abbrev shape : MonoShape B.k := MonoRelation.mergeShape B.rels

/-- The product cells of the batch (`pad_monomials` of the merged shape). -/
abbrev Cell : Type := B.shape.ChainCell

/-- **The product chains of the merged shape** (`MonoShape.chainLayout`). -/
abbrev layout : PadLayout B.shape B.Cell := B.shape.chainLayout fun _ => (B.rels _).deg_pos _

/-- The pads of the batch (`MaskedFieldSkip::Layout`). -/
abbrev Pad : Type := PadIdx B.e B.D B.n B.k B.Cell

/-- **The number of product cells** (`pad_monomials` of the merged shape). -/
abbrev m : ℕ := B.shape.padMonomials.card

theorem card_cell : Fintype.card B.Cell = B.m := Fintype.card_coe _

/-- **The batch holds** at the public input `p` on an assignment `z`: every relation vanishes on
every instance's operands. -/
def Holds (p : Pub) (z : V → K) : Prop :=
  ∀ q t, (B.rels q).eval (fun j => (B.form p t j).eval z) = 0

/-- **The affine operand map** of the batch (`AffineOperandMap`). -/
def map : OperandMap B.dom Pub V B.n B.k := OperandMap.affine B.dom B.N B.form

/-- **Every relation holds on the affine map's operands exactly when the batch holds**
(`affine_holds_iff` for each relation). -/
theorem map_holds_iff (p : Pub) (z : V → K) :
    (∀ q, Sumcheck.FieldSkip.Holds (B.rels q).toRelation (B.map.ops p z)) ↔ B.Holds p z :=
  forall_congr' fun q => affine_holds_iff B.dom (B.rels q).chainSkip_computes B.fits B.form p z

/-- **The batch's pad cells** at an embedding `e` of its pads. -/
def padCells {ι : Type} (e : B.Pad → ι) : BatchedZerocheck.PadCells ι B.e B.D B.n B.k B.Cell where
  skip i := e (.skip i)
  rounds i d := e (.round i d)
  terminal j := e (.terminal j)
  product c := e (.product c)

variable {ι : Type} [Fintype ι] [Fintype K] [DecidableEq K] (Pub)

/-- **The batch's masked reduction** at the pad embedding `e` and the level `Lv`: `γ`, then the batch phase
of the merged relation at `γ` (`mergedMaskedReduction`) on the affine operand map and the pad cells. -/
def ip (e : B.Pad → ι) (Lv : Level K ι V) : FieldProof.MaskedReduction K ι Pub (ι → K) id V 1 :=
  mergedMaskedReduction B.dom rfl B.rels B.layout Pub B.map (B.padCells e) Lv

/-- **The merged batch's claim reads what its forms read and the pads.** -/
theorem readsOnly_ip [DecidableEq V] (e : B.Pad → ι) (Lv : Level K ι V) {T : V → Prop}
    (h : ∀ p t j, (B.form p t j).ReadsOnly T) (hT : ∀ i, T (Lv.cell i)) :
    (B.ip Pub e Lv).ReadsOnly fun _ => T :=
  readsOnly_mergedMaskedReduction _ _ _ _ _ _ _ _ (readsOnly_affine_adjoint _ _ _ h) hT

variable {Pub}

/-- **The relation the batch's masked reduction proves** on the cells at the public input `p`: the batch on
the logical assignment, and the pads' products. -/
structure Sat (e : B.Pad → ι) (Lv : Level K ι V) (p : Pub) (x : ι → K) : Prop where
  /-- The batch on the logical assignment. -/
  holds : B.Holds p (Lv.view x)
  /-- The pads' products. -/
  product : ProductHolds B.layout.toPadTriples ((B.padCells e).read rfl x)

/-- The batch's round errors: `(np − 1)/|K|` at `γ`, then the batch phase's at degree `D`. -/
noncomputable abbrev error :
    (GKR.Schedule.one .V_to_P K ++ spec K B.e B.D B.n B.k).ChallengeIdx → ℝ≥0 :=
  ProtocolSpec.appendError (fun _ => ((B.np - 1 : ℕ) : ℝ≥0) / Fintype.card K)
    (BatchedZerocheck.error K B.e B.D B.n B.k GKR.Schedule.empty B.w)

omit [DecidableEq K] in
/-- **The batch's total error**: `(np − 1)/|K|`, then `n/|K|`, `D(w − 1)/|K|`, `(D + 1)n/|K|` and
`1/|K|`. -/
theorem error_sum : ∑ i, B.error i = ((B.np - 1 : ℕ) : ℝ≥0) / Fintype.card K +
    ((B.n : ℝ≥0) / Fintype.card K + ((B.D * (B.w - 1) : ℕ) : ℝ≥0) / Fintype.card K +
      ((B.D + 1 : ℕ) : ℝ≥0) * B.n / Fintype.card K + 1 / Fintype.card K) :=
  mergedError_sum (K := K) (e := B.e) (D := B.D) (n := B.n) (k := B.k) (np := B.np) B.w

/-- **Soundness of the batch's masked reduction**: the merged batch stage's
(`BatchedZerocheck.mergedMaskedReductionSound`: `merge_sound` at `γ`, then the batch phase), from the batch on the
logical assignment and the pads' products, with its errors. -/
noncomputable def sound (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.ip Pub e Lv).Sound Lv.view (B.Sat e Lv) B.error :=
  haveI : NeZero B.D := ⟨B.degree_ne⟩
  (mergedMaskedReductionSound B.dom rfl B.rels B.layout B.map (B.padCells e) Lv).congr
    fun p _ => ⟨fun h => ⟨(B.map_holds_iff p _).mp h.holds, h.product⟩,
      fun h => ⟨(B.map_holds_iff p _).mpr h.holds, h.product⟩⟩

/-- **The honest pad values** of free pads (`fill_pads`): the free pads, and each product cell the
product of its multiset's terminal pads. -/
def padValue (φ : FreePads K B.w B.D B.n B.k) : B.Pad → K
  | .skip i => φ.skip i
  | .round i d => φ.rounds i d
  | .terminal j => φ.terminal j
  | .product c => B.layout.fill φ.terminal c

variable (Pub)

/-- **The simulator of the merged masked reduction**: the merged batch stage's
(`BatchedZerocheck.mergedMaskedReductionSim`).

Running time: `BatchedZerocheck.mergedMaskedReductionSim`'s, linear in the batch transcript. This
running time is argued here, not proved in Lean. -/
def sim (e : B.Pad → ι) (Lv : Level K ι V) : (B.ip Pub e Lv).Sim :=
  haveI : NeZero B.w := ⟨B.width_ne⟩
  haveI : NeZero B.D := ⟨B.degree_ne⟩
  mergedMaskedReductionSim B.dom rfl B.rels B.layout B.map (B.padCells e) Lv

/-- **The honest merged masked reduction**, on assignments where the batch holds: the merged batch
stage's (`BatchedZerocheck.mergedMaskedReductionHonest`) through `map_holds_iff`, simulated by
`sim`. -/
noncomputable def honest (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.ip Pub e Lv).Honest Lv.view (V → K) (fun p z => B.Holds p z) (B.sim Pub e Lv) :=
  haveI : NeZero B.w := ⟨B.width_ne⟩
  haveI : NeZero B.D := ⟨B.degree_ne⟩
  (mergedMaskedReductionHonest B.dom rfl B.rels B.layout B.map (B.padCells e) Lv).comap
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
      (x ∘ (B.padCells e).product) y = Sum.elim φ.terminal (B.layout.fill φ.terminal) y :=
    fun y => by rcases y with j | c <;> exact h _
  refine ⟨?_, fun c => ?_, hz⟩
  · change Transcript.mk _ _ _ = Transcript.mk _ _ _
    congr 1
    · exact funext fun i => h (.skip _)
    · exact funext fun i => funext fun d => h (.round i d)
    · exact funext fun j => h (.terminal j)
  · change Sum.elim (x ∘ (B.padCells e).terminal) (x ∘ (B.padCells e).product)
        (B.layout.left c) * x ((B.padCells e).terminal (B.layout.right c)) =
      x ((B.padCells e).product c)
    rw [hy]
    change _ * x (e (.terminal _)) = x (e (.product c))
    rw [h, h]
    exact B.layout.triplesHold_fill φ.terminal c

/-! ### Zero knowledge with respect to the uniform simulator -/

/-- The message types of the batch's masked reduction are finite. -/
instance ip_typeFintype (e : B.Pad → ι) (Lv : Level K ι V) :
    ∀ i, Fintype ((B.ip Pub e Lv).spec.Type i) :=
  @ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype BatchedZerocheck.spec_typeFintype

/-- The message types of the batch's masked reduction are nonempty. -/
instance ip_typeNonempty (e : B.Pad → ι) (Lv : Level K ι V) :
    ∀ i, Nonempty ((B.ip Pub e Lv).spec.Type i) :=
  haveI : Nonempty K := ⟨0⟩
  @ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty BatchedZerocheck.spec_typeNonempty

/-- The batch's simulator is a bijection onto the full transcripts. -/
theorem honest_simBijective (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.honest Pub e Lv).SimBijective :=
  haveI : NeZero B.w := ⟨B.width_ne⟩
  haveI : NeZero B.D := ⟨B.degree_ne⟩
  mergedMaskedReductionHonest_simBijective B.dom rfl B.rels B.layout B.map (B.padCells e) Lv

/-- **Paper `lem:batch` (3)**: honest-verifier zero knowledge of the merged batch with error `0` with respect to the uniform
simulator (paper `def:red-sec` (c)): at every public input and every logical assignment, the honest
transcript under uniform challenges and uniform free pads is a uniform full transcript. -/
@[headline]
theorem hvzk (e : B.Pad → ι) (Lv : Level K ι V) : (B.honest Pub e Lv).UniformHVZK :=
  (B.honest_simBijective e Lv).uniformHVZK

/-! ### The bit sumcheck -/

section BitSumcheck

variable [DecidableEq V] {m nw : ℕ}

variable (Pub) in
/-- **The merged batch's masked reduction with the bit sumcheck** (`MaskedReduction.bitSumcheck`) at the bit
layout `L`: the merged batch's masked reduction, then the masked sumcheck over the bit-index variables of
its words, whose output claim replaces the opening claim. -/
def bitIp (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    FieldProof.MaskedReduction K ι Pub (ι → K) id V 1 :=
  (B.ip Pub e Lv).bitSumcheck L Lv

omit [DecidableEq K] [DecidableEq V] in
variable (m) in
/-- **The errors of the merged batch with the bit sumcheck**: the merged batch's, then `2/|K|`
per bit round. -/
noncomputable abbrev bitError :
    ((GKR.Schedule.one .V_to_P K ++ spec K B.e B.D B.n B.k) ++
      HashCircuit.Skip.alt (Fin 2 → K) K m).ChallengeIdx → ℝ≥0 :=
  FieldProof.MaskedReduction.bitSumcheckError (K := K) m B.error

omit [DecidableEq K] [DecidableEq V] in
/-- **The total error of the merged batch with the bit sumcheck**: `(np − 1)/|K|` for `γ`, the
batch phase's, plus `2m/|K|` for the `m` bit rounds. -/
theorem bitError_sum : ∑ i, B.bitError m i = ((B.np - 1 : ℕ) : ℝ≥0) / Fintype.card K +
    ((B.n : ℝ≥0) / Fintype.card K + ((B.D * (B.w - 1) : ℕ) : ℝ≥0) / Fintype.card K +
      ((B.D + 1 : ℕ) : ℝ≥0) * B.n / Fintype.card K + 1 / Fintype.card K) +
        ((2 * m : ℕ) : ℝ≥0) / Fintype.card K := by
  rw [FieldProof.MaskedReduction.sum_bitSumcheckError, B.error_sum]

/-- **Soundness of the merged batch with the bit sumcheck**: the merged batch's relation, with
the merged batch's errors and `2/|K|` per bit round. -/
noncomputable def bitSumcheckSound (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitIp Pub e Lv L).Sound Lv.view (B.Sat e Lv) (B.bitError m) :=
  (B.sound e Lv).bitSumcheck

variable (Pub) in
/-- **The simulator of the merged batch with the bit sumcheck**: the merged batch's simulator, then
uniform values (`MaskedReduction.Sim.bitSumcheck`).

Running time: the merged batch's simulator's and a copy of `2m` coins, linear in the transcript.
This running time is argued here, not proved in Lean. -/
def bitSim (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) : (B.bitIp Pub e Lv L).Sim :=
  FieldProof.MaskedReduction.Sim.bitSumcheck L (B.sim Pub e Lv)

variable (Pub) in
/-- **The honest merged batch with the bit sumcheck**, on assignments where the batch holds: the
honest merged batch, then the honest bit rounds at the assignment's bits, simulated by `bitSim`. -/
noncomputable def bitHonest (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitIp Pub e Lv L).Honest Lv.view (V → K) (fun p z => B.Holds p z) (B.bitSim Pub e Lv L) :=
  (B.honest Pub e Lv).bitSumcheck L fun _ z => L.bits z

/-- **The cells commit the honest merged batch with the bit sumcheck** when they commit the
honest merged batch, the bit rounds' pads and the assignment's bits. -/
theorem bitCommits_of (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) (p : Pub)
    (z : V → K) (φ : FreePads K B.w B.D B.n B.k) (ψ : Fin m → Fin 2 → K) (x : ι → K)
    (hb : (B.honest Pub e Lv).Commits p z φ x) (hl : L.Commits Lv (L.bits z) ψ x) :
    (B.bitHonest Pub e Lv L).Commits p z (φ, ψ) x :=
  ⟨hb, hl⟩

/-- The message types of the merged batch's masked reduction with the bit sumcheck are finite. -/
instance bitIp_typeFintype (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    ∀ i, Fintype ((B.bitIp Pub e Lv L).spec.Type i) :=
  FieldProof.MaskedReduction.bitSumcheck_typeFintype (M := B.ip Pub e Lv)

/-- The message types of the merged batch's masked reduction with the bit sumcheck are nonempty. -/
instance bitIp_typeNonempty (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    ∀ i, Nonempty ((B.bitIp Pub e Lv L).spec.Type i) :=
  FieldProof.MaskedReduction.bitSumcheck_typeNonempty (M := B.ip Pub e Lv)

/-- The simulator of the merged batch with the bit sumcheck is a bijection onto the full
transcripts. -/
theorem bitHonest_simBijective (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitHonest Pub e Lv L).SimBijective :=
  (B.honest_simBijective e Lv).bitSumcheck _

/-- **Honest-verifier zero knowledge of the merged batch with the bit sumcheck** with error `0`
with respect to the uniform simulator (paper `def:red-sec` (c)): at every public input and every
logical assignment, the honest transcript under uniform challenges, uniform free pads and uniform
bit-round pads is a uniform full transcript. -/
@[headline]
theorem bitHvzk (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitHonest Pub e Lv L).UniformHVZK :=
  (B.bitHonest_simBijective e Lv L).uniformHVZK

end BitSumcheck

end MergedAffineBatch

end GordieHowe.BatchedZerocheck
