-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.Language.Realizations.MemoryShuffleSubfield
public import GordieHowe.Foundations.Algebra.RecordPacking
public import GordieHowe.Language.Realizations.PermutationEvent

@[expose] public section

/-!
# ML-DSA: the SampleInBall memory-check lowering

Used by both ML-DSA configurations.

ML-DSA's SampleInBall shuffle (FIPS 204 Algorithm 29, lines 4-8) as GordieHowe checks it
(`lib/gordiehowe/examples/mldsa/sample_in_ball.h`, `sample_in_ball_shuffle`, an offline memory
check on `assert_permutation`, `permutation.h`): its source, its committed cells and checks, their
soundness and the honest cells. Reusable for every scheme with this shuffle (ML-DSA native and
emulated, the rings); its cells are ML-DSA's (selected positions of eight bits, `KH × KH` and
`KH × KH × KH` records over the selection field), so it belongs to the ML-DSA instances rather than
to the generic stack.

* **Source** (`SampleInBall.Shuffles`): the decoded challenge `chal` (the support and sign bits of
  each coefficient, H's `c_H`) is the ternary decoding of SampleInBall's shuffle of the selected
  positions `j_t` with the signs, once the positions are bytes at most `N - τ + t` and the signs
  are bits (`SampleInBall.Positioned`, the selection's conclusion and the bit checks).
* **Lowered** (`SampleInBall.Checks`, `sample_in_ball.h:348-388`): the committed cells
  `read_value`, `read_origin` (six bits per step), `c_enc`, `final_origin`, `unit`, `origin`; the
  rows `unit_t = 1 + (θ + 1) sign_t` and `origin_t = Σ_b e_b read_origin_{t,b}`; the comparator
  `read_origin_t < t + 1` (`.fresh`); the decoded challenge `chal = (c + (θ + 1)(c² + c), c² + c)`
  of `c_enc`; and the permutation of the records `(address, value, origin)`, packed at the fixed
  `κ` (`a + κ v + κ² o`, `RecordPacking.pack`), checked at `δ` (`h2c.sample.mem.delta`): reads
  `(j_t, read_value_t, origin_t)` then `(k, c_enc_k, final_origin_k)`, writes `(k, 0, 0)` for
  `k < N - τ`, then `(j_t, unit_t, t + 1)`, then `(N - τ + t, read_value_t, origin_t)`, in the
  C++ push order. The subfield cells lie in `E = GF(2^16)` (the packing tree's subfield).
* **Event** (`SampleInBall.bad`): `δ` is a root of the permutation event of the two packed
  lists (`PermutationEvent.permEvent`, degree `N + τ`, `SampleInBall.bad_deg`); bound
  `(N + τ) / |KH|` at `δ`'s phase.
* **Soundness** (`SampleInBall.shuffles_or_bad`): equal products give equal packed multisets; the
  packing is injective on `E³` (`SampleInBall.packT_injOn`, from `RecordPacking.pack_injOn`), so the
  record triples agree as multisets; the offline-memory argument
  (`MemoryShuffle.wit_cEnc_eq_shuffle`) then gives `c_enc` as the encoded shuffle, and the
  decoding gives the source. The C++'s packing at a constant replaces the second
  challenge `δ_enc` (`permutation.h:34-37`).
* **Honest prover** (`SampleInBall.honestCells`, `SampleInBall.checks_honestCells`): the honest
  trace of `MemoryShuffle` (`SampleInBall.honestTrace`, `MemoryShuffle.honestWit`), whose record
  triples agree (`MemoryShuffle.honestWit_key`); no completeness event.
-/

namespace GordieHowe
open IOP RealizedProgram.ProofSystem.PhaseLayout
open scoped NNReal ENNReal

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {A KH : Type} [Field KH] [DecidableEq KH]

/-- **A SampleInBall memory check** over `N` cells and `τ` steps, read from source assignments `A`:
the selection field (its subfield `E` and its embedding basis `e`, `of_scalar`; `SelectionField`),
`θ` of order `3` in `E` (cells hold `0`, `1`, `θ`), the record packing constant `κ` with its
injectivity on `E³`, the selected positions (eight bits per step), the signs and the decoded
challenge, the phase `k` of `δ` with its decoding `delta`, and the parameter conditions of the
`MemoryShuffle` argument (`τ ≤ N ≤ 256`, `τ < 64`: addresses are bytes, origins six bits). -/
structure MLDSA44.SampleInBall (L : RealizedProgram.ProofSystem.PhaseLayout K) (A KH : Type) [Field KH] where
  /-- The number of cells. -/
  N : ℕ
  /-- The number of steps. -/
  τ : ℕ
  /-- The selection field's degree bound (unused here; `SelectionField`'s parameter). -/
  S : ℕ
  /-- The selection field: the subfield `E` and the embedding basis. -/
  field : SelectionField KH S
  /-- `θ`, with `θ² + θ + 1 = 0`. -/
  Θ : MemoryShuffle.Theta KH
  θ_mem : Θ.θ ∈ field.E
  /-- The record packing constant. -/
  κ : KH
  /-- The packing at `κ` is injective on records of elements of `E`. -/
  packing : ∀ a b : Fin 3 → KH, (∀ i, a i ∈ field.E) → (∀ i, b i ∈ field.E) →
    RecordPacking.pack κ a = RecordPacking.pack κ b → a = b
  /-- The selected position of step `t`, eight bits. -/
  positions : A → Fin τ → BitWires KH 8
  /-- The sign of step `t`. -/
  signs : A → Fin τ → KH
  /-- The decoded challenge: the support and sign bits of coefficient `k`. -/
  chal : A → Fin N → KH × KH
  /-- The phase of `δ`. -/
  k : Fin K
  /-- `δ` from the challenge of phase `k`. -/
  delta : L.Ch k → KH
  τ_le : τ ≤ N
  N_le : N ≤ 256
  τ_lt : τ < 64

namespace MLDSA44.SampleInBall

variable (M : SampleInBall L A KH)

/-- The packing of a record `(a, v, o)`: `a + κ v + κ² o`. -/
def pack3 (a v o : KH) : KH := RecordPacking.pack M.κ ![a, v, o]

/-- The packing of a record triple. -/
def packT (t : KH × KH × KH) : KH := M.pack3 t.1 t.2.1 t.2.2

/-- The embedding of eight position bits. -/
def addr (bits : BitWires KH 8) : KH := M.field.embedBits (by decide) bits

/-- The embedding of six origin bits. -/
def originOf (bits : BitWires KH 6) : KH := M.field.embedBits (by decide) bits

/-- **Checked positions** (on the data: `τ` positions of eight bits and `τ` signs over `N` cells):
the positions are bits and at most `N - τ + t` (the rising selection's conclusion), and the signs
are bits. -/
structure Positioned (N : ℕ) {τ : ℕ} (positions : Fin τ → BitWires KH 8) (signs : Fin τ → KH) :
    Prop where
  bits : ∀ t, Bits.AllBool (positions t)
  le : ∀ t : Fin τ, Bits.natOfBits (positions t) ≤ N - τ + t
  signBool : ∀ t, signs t = 0 ∨ signs t = 1

/-- The signs as Booleans. -/
-- spec-side
def signBoolsOf {τ : ℕ} (signs : Fin τ → KH) (t : Fin τ) : Bool := decide (signs t = 1)

/-- **The shuffle** (on the data): SampleInBall's final array on the positions and signs, over the
integers (`MemoryShuffle.shuffle`). -/
-- spec-side
def shuffleOf (N : ℕ) {τ : ℕ} (positions : Fin τ → BitWires KH 8) (signs : Fin τ → KH) :
    Fin N → ℤ :=
  MemoryShuffle.shuffle N τ (fun t => Bits.natOfBits (positions t)) (signBoolsOf signs)

/-- **The shuffle's decoding** (on the data): on checked positions, the decoded challenge is the
ternary decoding of the shuffle. -/
def ShufflesOf (Θ : MemoryShuffle.Theta KH) (N : ℕ) {τ : ℕ} (positions : Fin τ → BitWires KH 8)
    (signs : Fin τ → KH) (chal : Fin N → KH × KH) : Prop :=
  Positioned N positions signs → ∀ k, chal k =
    MemoryShuffle.decodeTernary Θ (MemoryShuffle.encode Θ (shuffleOf N positions signs k))

/-- The signs as Booleans. -/
-- spec-side
def signBools (a : A) (t : Fin M.τ) : Bool := signBoolsOf (M.signs a) t

/-- **The shuffle** on a source assignment. -/
-- spec-side
def shuffle (a : A) : Fin M.N → ℤ := shuffleOf M.N (M.positions a) (M.signs a)

/-- **The source constraint**: on checked positions, the decoded challenge is the ternary
decoding of the shuffle. -/
def Shuffles (a : A) : Prop := ShufflesOf M.Θ M.N (M.positions a) (M.signs a) (M.chal a)

/-- **The lowered assignment**: the source assignment and the memory check's committed cells. -/
structure Lowered where
  /-- The source assignment. -/
  base : A
  /-- The value read at each step. -/
  readValue : Fin M.τ → KH
  /-- The origin read at each step, six bits. -/
  readOrigin : Fin M.τ → BitWires KH 6
  /-- The final cells. -/
  cEnc : Fin M.N → KH
  /-- The final origins. -/
  finalOrigin : Fin M.N → KH
  /-- The unit written at each step. -/
  unit : Fin M.τ → KH
  /-- The read origin as a subfield value. -/
  origin : Fin M.τ → KH

/-- **The read records**, packed, in the C++ push order (`sample_in_ball.h:366,369`): per step
`(j_t, read_value_t, origin_t)`, then per cell `(k, c_enc_k, final_origin_k)`. -/
def readsPacked (b : M.Lowered) : List KH :=
  (List.finRange M.τ).map (fun t : Fin M.τ => M.pack3 (M.addr (M.positions b.base t)) (b.readValue t)
      (b.origin t))
    ++ (List.finRange M.N).map fun k : Fin M.N => M.pack3 (M.field.embed (k : ℕ)) (b.cEnc k)
      (b.finalOrigin k)

/-- **The write records**, packed, in the C++ push order (`sample_in_ball.h:364-368`): the
initial cells `(k, 0, 0)` for `k < N - τ`, then per step `(j_t, unit_t, t + 1)`, then per step
`(N - τ + t, read_value_t, origin_t)`. -/
def writesPacked (b : M.Lowered) : List KH :=
  (List.range (M.N - M.τ)).map (fun k => M.pack3 (M.field.embed k) 0 0)
    ++ (List.finRange M.τ).map (fun t : Fin M.τ => M.pack3 (M.addr (M.positions b.base t)) (b.unit t)
      (M.field.embed ((t : ℕ) + 1)))
    ++ (List.finRange M.τ).map fun t : Fin M.τ => M.pack3 (M.field.embed (M.N - M.τ + (t : ℕ)))
      (b.readValue t) (b.origin t)

/-- **The memory check's constraints** at `δ`: the origin bits, the subfield cells, the unit and
origin rows, the comparator, the decoded challenge and the permutation. -/
structure Checks (b : M.Lowered) (δ : KH) : Prop where
  originBits : ∀ t, Bits.AllBool (b.readOrigin t)
  readValue_mem : ∀ t, b.readValue t ∈ M.field.E
  cEnc_mem : ∀ k, b.cEnc k ∈ M.field.E
  finalOrigin_mem : ∀ k, b.finalOrigin k ∈ M.field.E
  unitRow : ∀ t, b.unit t = MemoryShuffle.unit M.Θ (M.signs b.base t)
  originRow : ∀ t, b.origin t = M.originOf (b.readOrigin t)
  fresh : ∀ t : Fin M.τ, Bits.ltConst (b.readOrigin t) ((t : ℕ) + 1) = 1
  decode : ∀ k, M.chal b.base k = MemoryShuffle.decodeTernary M.Θ (b.cEnc k)
  perm : ((M.readsPacked b).map fun x => δ - x).prod = ((M.writesPacked b).map fun x => δ - x).prod

variable {Stmt : Type}

/-! #### The bridge to the memory argument of `MemoryShuffle` -/

/-- **The `MemoryShuffle` witness** of a lowered assignment (`MemoryShuffle.Wit`). -/
def toWit (b : M.Lowered) : MemoryShuffle.Wit KH M.N M.τ :=
  ⟨M.positions b.base, M.signs b.base, fun t => ⟨b.readValue t, b.readOrigin t⟩, b.cEnc,
    b.finalOrigin⟩

/-- The read records are the `MemoryShuffle` read triples, packed. -/
theorem readsPacked_eq (b : M.Lowered) (horigin : ∀ t, b.origin t = M.originOf (b.readOrigin t)) :
    M.readsPacked b = (MemoryShuffle.readsTriples M.field (M.toWit b)).map M.packT := by
  simp only [readsPacked, MemoryShuffle.readsTriples, List.map_append, List.map_map]
  congr 1
  refine List.map_congr_left fun t _ => ?_
  simp only [Function.comp, packT, horigin t]
  rfl

/-- The write records are the `MemoryShuffle` write triples, packed, up to order. -/
theorem writesPacked_eq (b : M.Lowered) (hunit : ∀ t, b.unit t = MemoryShuffle.unit M.Θ (M.signs b.base t))
    (horigin : ∀ t, b.origin t = M.originOf (b.readOrigin t)) :
    (↑(M.writesPacked b) : Multiset KH) =
      ↑((MemoryShuffle.writesTriples M.field M.Θ (M.toWit b)).map M.packT) := by
  rw [MemoryShuffle.writesTriples, List.map_append, List.map_flatMap, writesPacked]
  simp only [List.map_cons, List.map_nil, List.map_map]
  rw [← Multiset.coe_add, ← Multiset.coe_add, ← Multiset.coe_add, MemoryShuffle.multiset_flatMap_pair,
    add_assoc]
  congr 2
  · refine congrArg _ (List.map_congr_left fun t _ => ?_)
    simp only [packT, hunit t]
    rfl
  · refine congrArg _ (List.map_congr_left fun t _ => ?_)
    simp only [packT, horigin t]
    rfl

/-- The embedding of Boolean bits lies in `E`. -/
theorem embedBits_mem {m : ℕ} (hm : m ≤ 16) {v : BitWires KH m} (hv : Bits.AllBool v) :
    M.field.embedBits hm v ∈ M.field.E :=
  M.field.E.sum_mem fun i _ => M.field.E.mul_mem (by
    rcases hv i with h | h <;> rw [h]
    exacts [M.field.E.zero_mem, M.field.E.one_mem]) (M.field.e_mem _)

/-- The components of every `MemoryShuffle` record triple lie in `E`. -/
theorem triples_mem {b : M.Lowered} {δ : KH} (h : M.Checks b δ)
    (hp : Positioned M.N (M.positions b.base) (M.signs b.base)) :
    ∀ x ∈ MemoryShuffle.writesTriples M.field M.Θ (M.toWit b) ++
        MemoryShuffle.readsTriples M.field (M.toWit b),
      x.1 ∈ M.field.E ∧ x.2.1 ∈ M.field.E ∧ x.2.2 ∈ M.field.E := by
  intro x hx
  simp only [MemoryShuffle.writesTriples, MemoryShuffle.readsTriples, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with (⟨k, -, rfl⟩ | ⟨t, -, rfl | rfl⟩) | (⟨t, -, rfl⟩ | ⟨k, -, rfl⟩)
  · exact ⟨M.field.embed_mem _, M.field.E.zero_mem, M.field.E.zero_mem⟩
  · refine ⟨M.embedBits_mem _ (hp.bits t), MemoryShuffle.unit_mem M.Θ M.θ_mem ?_,
      M.field.embed_mem _⟩
    rcases hp.signBool t with h0 | h1
    · change M.signs b.base t ∈ _
      rw [h0]
      exact M.field.E.zero_mem
    · change M.signs b.base t ∈ _
      rw [h1]
      exact M.field.E.one_mem
  · exact ⟨M.field.embed_mem _, h.readValue_mem t, M.embedBits_mem _ (h.originBits t)⟩
  · exact ⟨M.embedBits_mem _ (hp.bits t), h.readValue_mem t, M.embedBits_mem _ (h.originBits t)⟩
  · exact ⟨M.field.embed_mem _, h.cEnc_mem k, h.finalOrigin_mem k⟩

omit [DecidableEq KH] in
/-- The packing of triples is injective on triples of elements of `E`. -/
theorem packT_injOn : Set.InjOn M.packT
    {x | x.1 ∈ M.field.E ∧ x.2.1 ∈ M.field.E ∧ x.2.2 ∈ M.field.E} := by
  rintro ⟨a, v, o⟩ ⟨ha, hv, ho⟩ ⟨a', v', o'⟩ ⟨ha', hv', ho'⟩ h
  have hmem : ∀ (x y z : KH), x ∈ M.field.E → y ∈ M.field.E → z ∈ M.field.E →
      ∀ i, (![x, y, z] : Fin 3 → KH) i ∈ M.field.E := fun x y z hx hy hz i => by
    fin_cases i
    exacts [hx, hy, hz]
  have he := M.packing _ _ (hmem a v o ha hv ho) (hmem a' v' o' ha' hv' ho') h
  have h0 := congrFun he 0
  have h1 := congrFun he 1
  have h2 := congrFun he 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  simp only [Matrix.vecHead, Matrix.vecTail, Function.comp, Fin.succ_zero_eq_one,
    Matrix.cons_val_one, Matrix.cons_val_zero] at h2
  rw [h0, h1, h2]

/-- The origin check of the `MemoryShuffle` witness, from the bits and the comparator. -/
theorem originsOk {b : M.Lowered} {δ : KH} (h : M.Checks b δ) : MemoryShuffle.OriginsOk (M.toWit b) := by
  refine ⟨h.originBits, fun t => ?_⟩
  have hf := h.fresh t
  rw [Bits.ltConst_eq (h.originBits t) (by have := t.isLt; have := M.τ_lt; omega)] at hf
  by_contra hcon
  change ¬ Bits.natOfBits (b.readOrigin t) < (t : ℕ) + 1 at hcon
  rw [ite_eq_right_iff.mpr (fun h => absurd h hcon)] at hf
  exact absurd hf (by norm_num)

/-- **The permutation event** of the packed records (`PermutationEvent.permEvent`). -/
noncomputable def bad (b : M.Lowered) : ChallengeEvent KH :=
  PermutationEvent.permEvent (M.readsPacked b) (M.writesPacked b)

/-- The permutation event has degree `N + τ`. -/
theorem bad_deg (b : M.Lowered) : (M.bad b).deg = M.N + M.τ := by
  change max (M.readsPacked b).length (M.writesPacked b).length = _
  simp only [readsPacked, writesPacked, List.length_append, List.length_map, List.length_finRange,
    List.length_range]
  have := M.τ_le
  omega

/-- **Soundness of the memory check**: the checks at `δ` give the source constraint, or `δ` is a
root of the permutation event. -/
theorem shuffles_or_bad [CharP KH 2] {b : M.Lowered} {δ : KH} (h : M.Checks b δ) :
    M.Shuffles b.base ∨ (M.bad b).BadAt δ := by
  rcases PermutationEvent.multiset_eq_or_badAt h.perm with hms | hbad
  · left
    intro hp k
    have hR := M.readsPacked_eq b h.originRow
    have hW := M.writesPacked_eq b h.unitRow h.originRow
    have hmap : Multiset.map M.packT ↑(MemoryShuffle.writesTriples M.field M.Θ (M.toWit b)) =
        Multiset.map M.packT ↑(MemoryShuffle.readsTriples M.field (M.toWit b)) := by
      rw [Multiset.map_coe, Multiset.map_coe, ← hW, ← hms, hR]
    have hkey := Multiset.eq_of_map_eq_of_injOn (M.packT_injOn.mono fun x hx => ?_) hmap
    · have hposLt : ∀ t : Fin M.τ, Bits.natOfBits ((M.toWit b).positions t) < M.N := fun t => by
        have := hp.le t
        have := t.isLt
        have := M.τ_le
        change Bits.natOfBits (M.positions b.base t) < M.N
        omega
      have hc := (MemoryShuffle.wit_cEnc_eq_shuffle M.τ_le M.N_le M.τ_lt hp.le hp.bits hp.signBool
        (M.originsOk h) hkey hposLt (k : ℕ) k.isLt).1
      rw [h.decode k]
      exact congrArg _ hc
    · rcases hx with hx | hx
      · exact M.triples_mem h hp x (List.mem_append_left _ (Multiset.mem_coe.mp hx))
      · exact M.triples_mem h hp x (List.mem_append_right _ (Multiset.mem_coe.mp hx))
  · exact Or.inr hbad

/-! #### The honest prover -/

/-- **The honest source**: checked positions, and the decoded challenge the ternary decoding of
the shuffle. -/
structure HonestShuffles (a : A) : Prop where
  positioned : Positioned M.N (M.positions a) (M.signs a)
  chal : ∀ k, M.chal a k = MemoryShuffle.decodeTernary M.Θ (MemoryShuffle.encode M.Θ (M.shuffle a k))

/-- **The `MemoryShuffle` honest trace** of a source assignment (`MemoryShuffle.honestWit`): the
shuffle run on the positions and signs, carrying origins. -/
-- spec-side
def honestTrace (a : A) : MemoryShuffle.Wit KH M.N M.τ :=
  MemoryShuffle.honestWit M.field M.Θ (fun t => Bits.natOfBits (M.positions a t)) (M.signBools a)

/-- **The honest cells** (`sample_in_ball.h:298-346`, the oblivious memory trace): the
`MemoryShuffle` honest trace's reads, final cells and origins, the units of the signs and the
reads' origins embedded. -/
-- spec-side
def honestCells (a : A) : M.Lowered :=
  ⟨a, fun t => ((M.honestTrace a).read t).value, fun t => ((M.honestTrace a).read t).origin,
    (M.honestTrace a).cEnc, (M.honestTrace a).finalOrigin,
    fun t => MemoryShuffle.unit M.Θ (M.signs a t),
    fun t => M.originOf ((M.honestTrace a).read t).origin⟩

/-- On checked positions, the `MemoryShuffle` witness of the honest cells is the honest trace. -/
theorem toWit_honestCells {a : A} (hp : Positioned M.N (M.positions a) (M.signs a)) :
    M.toWit (M.honestCells a) = M.honestTrace a := by
  have hpos : M.positions a = fun t (b : Fin 8) => Bits.constBit (Bits.natOfBits (M.positions a t)) b :=
    funext fun t => funext fun b => (Bits.constBit_natOfBits (hp.bits t) b).symm
  have hsg : M.signs a = fun t => if M.signBools a t then 1 else 0 := funext fun t => by
    rcases hp.signBool t with h0 | h1
    · simp [signBools, signBoolsOf, h0]
    · simp [signBools, signBoolsOf, h1]
  change MemoryShuffle.Wit.mk _ _ _ _ _ = MemoryShuffle.Wit.mk _ _ _ _ _
  congr 1

/-- **The honest cells pass the checks** at every `δ`. -/
theorem checks_honestCells [CharP KH 2] {a : A} (h : M.HonestShuffles a) (δ : KH) :
    M.Checks (M.honestCells a) δ := by
  have hp := h.positioned
  have hposle : ∀ t : Fin M.τ, Bits.natOfBits (M.positions a t) ≤ M.N - M.τ + t := hp.le
  have hor : MemoryShuffle.OriginsOk (M.honestTrace a) :=
    MemoryShuffle.honestWit_originsOk M.field M.Θ M.τ_le M.N_le M.τ_lt hposle
  refine ⟨fun t b => Bits.constBit_bool _ _,
    fun t => MemoryShuffle.honestWit_read_value_mem M.field M.Θ _ _ M.θ_mem t,
    fun k => MemoryShuffle.honestWit_cEnc_mem M.field M.Θ _ _ M.θ_mem k,
    fun k => MemoryShuffle.honestWit_finalOrigin_mem M.field M.Θ _ _ k,
    fun t => rfl, fun t => rfl, fun t => ?_, fun k => ?_, ?_⟩
  · change Bits.ltConst ((M.honestTrace a).read t).origin ((t : ℕ) + 1) = 1
    rw [Bits.ltConst_eq (hor.bool t) (by have := t.isLt; have := M.τ_lt; omega),
      ite_eq_left_iff.mpr (fun hn => absurd (hor.lt t) hn)]
  · change M.chal a k = _
    rw [h.chal k]
    change _ = MemoryShuffle.decodeTernary M.Θ ((MemoryShuffle.memoryTrace (N := M.N) M.Θ _ _).2.1 k)
    rw [MemoryShuffle.memoryTrace_cell_eq_shuffle]
    rfl
  · refine PermutationEvent.prod_eq_of_multiset_eq ?_ δ
    have hkey := MemoryShuffle.honestWit_key M.field M.Θ M.τ_le M.N_le M.τ_lt hposle
      (signs := M.signBools a)
    have hR := M.readsPacked_eq (M.honestCells a) fun _ => rfl
    have hW := M.writesPacked_eq (M.honestCells a) (fun _ => rfl) fun _ => rfl
    rw [toWit_honestCells M hp] at hR hW
    rw [hR, hW, ← Multiset.map_coe, ← Multiset.map_coe]
    exact congrArg _ hkey.symm

end MLDSA44.SampleInBall

end GordieHowe
