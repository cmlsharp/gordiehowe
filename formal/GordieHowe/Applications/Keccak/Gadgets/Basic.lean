-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Gadgets.Bits
public import GordieHowe.Applications.Keccak.Gadgets.Shake256Spec

@[expose] public section

/-!
# The Keccak-f[1600] gadget (`lib/circuits/tests/sha3/sha3_circuit.h`)

A transcription of Longfellow's `Sha3Circuit::keccak_f_1600` with a block
witness. The sponge built on it is `GordieHowe/Applications/Keccak/Gadgets/Shake256.lean`. The gadget is
generic over two construction parameters:

* the slicing: the rounds of each permutation after which the state is
  committed as advice and checked (`sha3_slice_at`, `sha3_slicing.h`);
* the packing of each state check: lane bits are grouped into slices, each
  slice is packed into one field element by public weights, and the packed
  values are compared (`sha3_vassert_eq`, `Logic::as_scalar`; the flagship uses
  four 16-bit slices over the 16-bit subfield of `GF(2^128)`).

Bits are field elements asserted Boolean where they are committed
(`LogicCircuit::input` asserts `assert_is_bit`). The logic backend's affine
bit representation is compiler infrastructure; the gadget uses the values it
denotes: `bnot a = 1 − a`, `and` is multiplication, `bxor a b = a + b − 2ab`
(equal to `a + b` in characteristic two, `Bits.bxor_eq`).

State indexing follows the C++: `A x y` is lane `(x, y)`, stored by the
vendored reference at index `x + 5y`; lane bit `z` has weight `2^z`.
-/

namespace GordieHowe.Keccak

open GordieHowe.Bits

variable {K : Type*} [Field K] [DecidableEq K]

/-- A Keccak state as bit wires: lane `(x, y)`, bit `z`. -/
abbrev State (K : Type*) := Fin 5 → Fin 5 → BitWires K 64

/-- `Logic::vrotl`: bit `i` moves to `(i + b) mod 64` (`logic.h:905-911`). -/
def rotl (v : BitWires K 64) (b : ℕ) : BitWires K 64 := fun z => v (z - Fin.ofNat 64 b)

/-- Bitwise xor of two lanes. -/
def lxor (u v : BitWires K 64) : BitWires K 64 := fun z => bxor (u z) (v z)

/-- The constant lane with the bits of `c` (`of_scalar`, `vbit<64>`). -/
def constLane (c : ℕ) : BitWires K 64 := fun z => constBit c z

/-- `theta` (`sha3_circuit.h:75-112`), with the C++ split `C = C0 ⊕ C1` and
`D = D0 ⊕ D1`, `D1` applied first. -/
def theta (A : State K) : State K :=
  let C0 : Fin 5 → BitWires K 64 := fun x => lxor (lxor (A x 2) (A x 3)) (lxor (A x 0) (A x 1))
  let C1 : Fin 5 → BitWires K 64 := fun x => A x 4
  let D0 : Fin 5 → BitWires K 64 := fun x => lxor (C0 (x + 4)) (rotl (C0 (x + 1)) 1)
  let D1 : Fin 5 → BitWires K 64 := fun x => lxor (C1 (x + 4)) (rotl (C1 (x + 1)) 1)
  fun x y => lxor (lxor (A x y) (D1 x)) (D0 x)

/-- `sha3_rotc` (`sha3_round_constants.cc`). -/
def rotc : Fin 24 → ℕ :=
  ![1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44]

/-- `sha3_rc` (`sha3_round_constants.cc`). -/
def rc : Fin 24 → ℕ :=
  ![0x0000000000000001, 0x0000000000008082, 0x800000000000808A, 0x8000000080008000,
    0x000000000000808B, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008A, 0x0000000000000088, 0x0000000080008009, 0x000000008000000A,
    0x000000008000808B, 0x800000000000008B, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800A, 0x800000008000000A,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008]

/-- `rho` (`sha3_circuit.h:114-123`): starting at `(1, 0)`, step `t` rotates
lane `(x, y)` by `rotc t` and moves to `(y, 2x + 3y)`. -/
def rho (A : State K) : State K :=
  ((List.finRange 24).foldl
    (fun (acc : State K × Fin 5 × Fin 5) t =>
      let (B, x, y) := acc
      (Function.update B x (Function.update (B x) y (rotl (B x y) (rotc t))), y, 2 * x + 3 * y))
    (A, 1, 0)).1

/-- `pi` (`sha3_circuit.h:125-132`). -/
def pi (A : State K) : State K := fun x y => A (x + 3 * y) x

/-- `chi` (`sha3_circuit.h:134-142`): `A1[x] ⊕ (A1[x+2] ∧ ¬A1[x+1])`. -/
def chi (A : State K) : State K :=
  fun x y => lxor (A x y) (fun z => A (x + 2) y z * bnot (A (x + 1) y z))

/-- `iota` (`sha3_circuit.h:144-147`). -/
def iota (r : Fin 24) (A : State K) : State K :=
  Function.update A 0 (Function.update (A 0) 0 (lxor (A 0 0) (constLane (rc r))))

/-- One round, in the C++ order. -/
def round (r : Fin 24) (A : State K) : State K := iota r (chi (pi (rho (theta A))))

/-- The slicing: after which rounds the state is committed and checked. The
final round must be sliced: block chaining and the squeezed output read the
round-23 advice, so without it those reads are unconstrained wires (a
necessary condition). -/
structure Slicing where
  slice : Fin 24 → Bool
  final : slice 23 = true

/-- Advice for one permutation: a state for each sliced round (the C++
allocates wires only for those, `BlockWitness::input`). -/
abbrev BlockAdvice (K : Type*) (sl : Slicing) := {r : Fin 24 // sl.slice r = true} → State K

/-- The packing of a state check: lane bit `i` lies in slice `sliceOf i` with
weight `weight i`; each slice is compared as one packed field element. The
field fact `injective`: Boolean lanes with equal packed slices are equal (for
`GF(2^128)` with 16-bit slices, independence of the subfield basis). -/
structure Packing (K : Type*) [Field K] where
  m : ℕ
  sliceOf : Fin 64 → Fin m
  weight : Fin 64 → K
  injective : ∀ a b : Fin 64 → Bool,
    (∀ s, ∑ i ∈ Finset.univ.filter (sliceOf · = s), (if a i then weight i else 0) =
      ∑ i ∈ Finset.univ.filter (sliceOf · = s), (if b i then weight i else 0)) → a = b

/-- `sha3_vassert_eq`: the packed slices of two lanes agree. -/
def packedEq (pk : Packing K) (u v : BitWires K 64) : Bool :=
  (List.finRange pk.m).all fun s =>
    decide (∑ i ∈ Finset.univ.filter (pk.sliceOf · = s), u i * pk.weight i =
      ∑ i ∈ Finset.univ.filter (pk.sliceOf · = s), v i * pk.weight i)

/-- Booleanity of committed advice (`LogicCircuit::input`). -/
def adviceBool {sl : Slicing} (bw : BlockAdvice K sl) : Bool :=
  (List.finRange 24).all fun r =>
    if h : sl.slice r = true then
      (List.finRange 5).all fun x => (List.finRange 5).all fun y => (List.finRange 64).all
        fun z => decide (bw ⟨r, h⟩ x y z * (bw ⟨r, h⟩ x y z - 1) = 0)
    else true

/-- `keccak_f_1600` with a block witness (`sha3_circuit.h:183-201`): after each
sliced round the computed state is checked against the advice and replaced by
it. Returns the verdict; the state the sponge reads is the round-23 advice. -/
def permute (sl : Slicing) (pk : Packing K) (A : State K) (bw : BlockAdvice K sl) : Bool :=
  ((List.finRange 24).foldl
    (fun (acc : Bool × State K) r =>
      let B := round r acc.2
      if h : sl.slice r = true then
        (acc.1 && (List.finRange 5).all fun x => (List.finRange 5).all fun y =>
          packedEq pk (B x y) (bw ⟨r, h⟩ x y), bw ⟨r, h⟩)
      else (acc.1, B))
    (true, A)).1

/-- The round-23 advice state of a block witness. -/
def finalState {sl : Slicing} (bw : BlockAdvice K sl) : State K := bw ⟨23, sl.final⟩

/-- Lanes of a Boolean state, as the vendored reference stores them (index
`x + 5y`, bit `z` of weight `2^z`). -/
-- spec-side
def toLanes (A : State K) : Array UInt64 :=
  Array.ofFn fun i : Fin 25 =>
    (natOfBits (A ⟨i % 5, Nat.mod_lt _ (by decide)⟩ ⟨i / 5, by omega⟩)).toUInt64

/-! ### Boolean states

A state whose wires are `0` or `1` is `ofBits f` for a `BitState` `f`; each gadget step
maps `ofBits f` to `ofBits` of the corresponding step of `GordieHowe/Applications/Keccak/Gadgets/Bits.lean`. -/

/-- A Boolean as a field bit. -/
-- spec-side
def ofBool (b : Bool) : K := if b then 1 else 0

omit [DecidableEq K] in
theorem ofBool_injective : Function.Injective (ofBool : Bool → K) := by
  intro a b h
  cases a <;> cases b <;> simp_all [ofBool]

omit [DecidableEq K] in
theorem ofBool_bool (b : Bool) : (ofBool b : K) = 0 ∨ (ofBool b : K) = 1 := by
  cases b <;> simp [ofBool]

theorem eq_ofBool {a : K} (h : a = 0 ∨ a = 1) : a = ofBool (decide (a = 1)) := by
  rcases h with rfl | rfl <;> simp [ofBool]

omit [DecidableEq K] in
theorem bxor_ofBool (a b : Bool) : bxor (ofBool a : K) (ofBool b) = ofBool (a ^^ b) := by
  cases a <;> cases b <;> simp [ofBool, bxor, ← one_add_one_eq_two]

omit [DecidableEq K] in
theorem ofBool_mul_bnot (a b : Bool) : (ofBool a : K) * bnot (ofBool b) = ofBool (!b && a) := by
  cases a <;> cases b <;> simp [ofBool, bnot]

omit [DecidableEq K] in
theorem constBit_eq_ofBool (c i : ℕ) : (constBit c i : K) = ofBool (c.testBit i) := by
  simp [constBit, ofBool, Nat.testBit_eq_decide_div_mod_eq]

/-- The field state with the bits `f`. -/
-- spec-side
def ofBits (f : BitState) : State K := fun x y z => ofBool (f x y z)

omit [DecidableEq K] in
theorem ofBits_allBool (f : BitState) (x y : Fin 5) : AllBool (ofBits (K := K) f x y) :=
  fun z => ofBool_bool (f x y z)

theorem eq_ofBits {A : State K} (hA : ∀ x y, AllBool (A x y)) :
    A = ofBits fun x y z => decide (A x y z = 1) :=
  funext fun x => funext fun y => funext fun z => eq_ofBool (hA x y z)

omit [Field K] [DecidableEq K] in
theorem rotl_zero (v : BitWires K 64) : rotl v 0 = v := by
  funext z
  simp only [rotl]
  congr 1
  ext
  simp only [Fin.sub_def, Fin.val_ofNat]
  omega

omit [Field K] [DecidableEq K] in
theorem rotl_rotl (v : BitWires K 64) (a b : ℕ) : rotl (rotl v a) b = rotl v (a + b) := by
  funext z
  simp only [rotl]
  congr 1
  ext
  simp only [Fin.sub_def, Fin.val_ofNat]
  omega

omit [Field K] [DecidableEq K] in
/-- The `rho` traversal rotates each lane by its entry of the vendored table. -/
theorem rho_eq (A : State K) : rho A = fun x y => rotl (A x y) (rhoOffset x y) := by
  let lift : (Fin 5 → Fin 5 → ℕ) × Fin 5 × Fin 5 → State K × Fin 5 × Fin 5 :=
    fun s => (fun x y => rotl (A x y) (s.1 x y), s.2)
  let offsets := fun (s : (Fin 5 → Fin 5 → ℕ) × Fin 5 × Fin 5) (t : Fin 24) =>
    (Function.update s.1 s.2.1 (Function.update (s.1 s.2.1) s.2.2 (s.1 s.2.1 s.2.2 + rotc t)),
      s.2.2, 2 * s.2.1 + 3 * s.2.2)
  have hinit : ((A, 1, 0) : State K × Fin 5 × Fin 5) = lift (fun _ _ => 0, 1, 0) := by
    simp [lift, rotl_zero]
  have htable : ((List.finRange 24).foldl offsets (fun _ _ => 0, 1, 0)).1 = rhoOffset := by
    funext x y
    revert x y
    decide +kernel
  unfold rho
  rw [hinit, List.foldl_hom lift (g₁ := offsets)]
  · simp only [lift, htable]
  rintro ⟨T, x, y⟩ t
  refine Prod.ext (funext fun x' => funext fun y' => ?_) rfl
  by_cases hx : x' = x
  · subst hx
    by_cases hy : y' = y
    · subst hy
      simp [lift, offsets, rotl_rotl]
    · simp [lift, offsets, hy]
  · simp [lift, offsets, hx]

omit [DecidableEq K] in
theorem theta_ofBits (f : BitState) : theta (ofBits (K := K) f) = ofBits (thetaBits f) := by
  funext x y z
  have hcol (x : Fin 5) (z : Fin 64) :
      column f x z = (f x 2 z ^^ f x 3 z ^^ (f x 0 z ^^ f x 1 z) ^^ f x 4 z) := by
    simp only [column]
    cases f x 0 z <;> cases f x 1 z <;> cases f x 2 z <;> cases f x 3 z <;> cases f x 4 z <;> rfl
  have hmix : ∀ a p q r s : Bool, (a ^^ (p ^^ q) ^^ (r ^^ s)) = (a ^^ (r ^^ p ^^ (s ^^ q))) := by
    decide
  simp only [theta, ofBits, lxor, rotl, bxor_ofBool, thetaBits]
  rw [show Fin.ofNat 64 1 = 1 from rfl, hmix, hcol, hcol]

omit [DecidableEq K] in
theorem rho_ofBits (f : BitState) : rho (ofBits (K := K) f) = ofBits (rhoBits f) := by
  rw [rho_eq]
  rfl

omit [DecidableEq K] in
theorem pi_ofBits (f : BitState) : pi (ofBits (K := K) f) = ofBits (piBits f) := rfl

omit [DecidableEq K] in
theorem chi_ofBits (f : BitState) : chi (ofBits (K := K) f) = ofBits (chiBits f) := by
  funext x y z
  simp only [chi, ofBits, lxor, ofBool_mul_bnot, bxor_ofBool, chiBits]

omit [DecidableEq K] in
theorem iota_ofBits (r : Fin 24) (f : BitState) :
    iota r (ofBits (K := K) f) = ofBits (iotaBits (rc r) f) := by
  funext x y z
  by_cases h : x = 0 ∧ y = 0
  · obtain ⟨rfl, rfl⟩ := h
    simp [iota, ofBits, lxor, constLane, constBit_eq_ofBool, bxor_ofBool, iotaBits]
  · have hne : ¬(x = 0 ∧ y = 0) := h
    by_cases hx : x = 0
    · subst hx
      have hy : y ≠ 0 := fun hy => h ⟨rfl, hy⟩
      simp [iota, ofBits, iotaBits, hy]
    · simp [iota, ofBits, iotaBits, hx]

omit [DecidableEq K] in
theorem round_ofBits (r : Fin 24) (f : BitState) :
    round r (ofBits (K := K) f) = ofBits (roundBits (rc r) f) := by
  rw [round, theta_ofBits, rho_ofBits, pi_ofBits, chi_ofBits, iota_ofBits, roundBits]

theorem round_allBool {A : State K} (hA : ∀ x y, AllBool (A x y)) (r : Fin 24) (x y : Fin 5) :
    AllBool (round r A x y) := by
  rw [eq_ofBits hA, round_ofBits]
  exact ofBits_allBool _ x y

theorem rc_eq (r : Fin 24) : rc r = SLHDSA.Concrete.Keccak.roundConstants[r]!.toNat := by
  revert r
  decide

theorem size_toLanes (A : State K) : (toLanes A).size = 25 := Array.size_ofFn

theorem laneBit_toLanes (f : BitState) : laneBit (toLanes (ofBits (K := K) f)) = f := by
  funext x y z
  have hi : (x : ℕ) + 5 * y < 25 := by omega
  have hx : (⟨((x : ℕ) + 5 * y) % 5, Nat.mod_lt _ (by decide)⟩ : Fin 5) = x := by
    ext
    simp only
    omega
  have hy : (⟨((x : ℕ) + 5 * y) / 5, by omega⟩ : Fin 5) = y := by
    ext
    simp only
    omega
  have hbit := constBit_natOfBits (ofBits_allBool (K := K) f x y) z
  rw [constBit_eq_ofBool] at hbit
  simp only [laneBit, toLanes]
  rw [getElem!_pos _ _ (by simpa using hi), Array.getElem_ofFn]
  simp only [hx, hy]
  have htest : (natOfBits (ofBits (K := K) f x y)).testBit z = f x y z := ofBool_injective hbit
  rw [Nat.toUInt64, UInt64.toBitVec_ofNat', BitVec.getLsbD_ofNat, htest]
  simp

/-- One gadget round computes the vendored round on Boolean states. -/
theorem toLanes_round {A : State K} (hA : ∀ x y, Bits.AllBool (A x y)) (r : Fin 24) :
    toLanes (round r A) =
      SLHDSA.Concrete.Keccak.round (toLanes A) SLHDSA.Concrete.Keccak.roundConstants[r]! := by
  rw [eq_ofBits hA, round_ofBits]
  refine eq_of_laneBit_eq (size_toLanes _) (size_round _ _) ?_
  rw [laneBit_round, laneBit_toLanes, laneBit_toLanes, rc_eq]

end GordieHowe.Keccak
