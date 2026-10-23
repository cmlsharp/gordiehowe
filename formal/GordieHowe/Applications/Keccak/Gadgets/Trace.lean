-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.Units.Equiv
public import GordieHowe.Applications.Keccak.Gadgets.Shake256
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim

@[expose] public section

/-!
# The committed Keccak trace of the batched-Keccak H

The batched-Keccak H proves a batch of Keccak-f permutations by a committed trace of round
states, checked by one AND relation per state bit. This file states the deterministic
semantics of that trace: the round relation, the affine maps it is built from, the rounds of a
permutation (`PermRelation`), state maps (`StateMap`), and the honest rounds (`iterRounds`) and
honest sponge permutation inputs (`spongeStart`). The batch's state map and relation are
`GordieHowe.KeccakBatch`; packing, the univariate skip and the opening forms are later layers.

Source: `lib/sumcheck/keccak_skip_link.h` at `e5daf0a`. Conventions, with the lines they are
read from:

* Lanes. `Sha3Reference` stores lane `(x, y)` as `A[x][y]` (`sha3_reference.cc:32-79`),
  bit `z` of weight `2^z`; `xorin` fills lanes in the order `x + 5y`
  (`sha3_reference.cc:106-118`). The trace stores lane `(x, y)` at word index `5x + y`
  (`KeccakSkipTrace::save`), the transpose of the vendored order `x + 5y`. States here are
  functions of `(x, y, z)` (`Keccak.State`), so no flat index occurs in a statement except
  where a C++ formula is transcribed.
* Packed words. Lane bits `16c, …, 16c + 15` form packed word `c ∈ {0, …, 3}` (`zChunk`,
  `zBit`), bit `j` of the word weighted by basis element `β j` (`of_scalar(word >> 16c)`,
  which is `PackedClaim.pack`).
* Rounds. `theta, rho, pi, chi, iota` in that order (`KeccakSkipTrace::permute`), round
  `t` using `sha3_rc[t % 24]` (`sha3_round_constants.cc:24-33`, equal to `Keccak.rc`).
  Rotation offsets come from the `rho` traversal (`keccak_skip_link.h`,
  `sha3_reference.cc:48-56`); `Keccak.rho_eq` identifies the traversal with the table
  `rhoOffset`.
* Round relation. For each lane and bit, `a = ~B[x+1][y]`, `b = B[x+2][y]`,
  `c = next[x][y] ^ B[x][y] ^ (x = y = 0 ? rc : 0)` with `B = pi(rho(theta(S)))`
  (`KeccakSkipTrace::operands`); the relation is `a*b + c = 0`.
-/

namespace GordieHowe.KeccakTrace

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 Matrix

/-! ## The affine maps as matrices

A state bit is indexed by `Idx = (x, y, z)`. `theta`, `rho`, `pi` and the `chi` operand
shifts are `0/1` matrices over any commutative semiring, so their transposes are
`Matrix.transpose`. Over a field of characteristic two they are the Keccak gadget's
maps (`thetaMat_mulVec_flat`, `rhoMat_mulVec_flat`, `piMat_mulVec_flat`). -/

/-- A state bit: lane `(x, y)`, bit `z`. -/
abbrev Idx := Fin 5 × Fin 5 × Fin 64

/-- A state as a vector indexed by `Idx`. -/
def flat {R : Type*} (A : Fin 5 → Fin 5 → Fin 64 → R) : Idx → R := fun i => A i.1 i.2.1 i.2.2

theorem flat_add {R : Type*} [Add R] (A A' : Fin 5 → Fin 5 → Fin 64 → R) :
    flat (A + A') = flat A + flat A' := rfl

theorem flat_zero {R : Type*} [Zero R] : flat (0 : Fin 5 → Fin 5 → Fin 64 → R) = 0 := rfl

theorem flat_smul {S R : Type*} [SMul S R] (e : S) (A : Fin 5 → Fin 5 → Fin 64 → R) :
    flat (e • A) = e • flat A := rfl

section Matrices

variable {R : Type*} [CommSemiring R]

/-- The `0/1` matrix whose row `i` selects coordinate `σ i`. -/
def selMat (σ : Idx → Idx) : Matrix Idx Idx R := fun i j => if j = σ i then 1 else 0

theorem selMat_mulVec (σ : Idx → Idx) (v : Idx → R) (i : Idx) : (selMat σ *ᵥ v) i = v (σ i) := by
  simp [selMat, Matrix.mulVec, dotProduct]

/-- Row `(x, y, z)` sums the five lanes of column `x + dx` at bit `z - dz`. -/
def columnMat (dx : Fin 5) (dz : Fin 64) : Matrix Idx Idx R :=
  fun i j => if j.1 = i.1 + dx ∧ j.2.2 = i.2.2 - dz then 1 else 0

theorem columnMat_mulVec (dx : Fin 5) (dz : Fin 64) (v : Idx → R) (i : Idx) :
    (columnMat dx dz *ᵥ v) i = ∑ y, v (i.1 + dx, y, i.2.2 - dz) := by
  simp only [columnMat, Matrix.mulVec, dotProduct, ite_mul, one_mul, zero_mul,
    Fintype.sum_prod_type, ite_and]
  simp [Finset.sum_ite_irrel]

/-- `theta` (`sha3_reference.cc:33-45`): each bit plus the parities of columns `x + 4`
at bit `z` and `x + 1` at bit `z - 1`. -/
def thetaMat : Matrix Idx Idx R := 1 + columnMat 4 0 + columnMat 1 1

theorem thetaMat_mulVec (v : Idx → R) (i : Idx) :
    (thetaMat *ᵥ v) i = v i + ∑ y, v (i.1 + 4, y, i.2.2) + ∑ y, v (i.1 + 1, y, i.2.2 - 1) := by
  simp only [thetaMat, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply, columnMat_mulVec,
    sub_zero]

/-- `rho`: lane `(x, y)` rotated left by `rhoOffset x y`. -/
def rhoMat : Matrix Idx Idx R :=
  selMat fun i => (i.1, i.2.1, i.2.2 - Fin.ofNat 64 (rhoOffset i.1 i.2.1))

/-- `pi` (`sha3_reference.cc:59-65`): lane `(x, y)` is old lane `(x + 3y, x)`. -/
def piMat : Matrix Idx Idx R := selMat fun i => (i.1 + 3 * i.2.1, i.1, i.2.2)

/-- The `chi` operand shift: lane `(x, y)` reads lane `(x + dx, y)`. -/
def shiftMat (dx : Fin 5) : Matrix Idx Idx R := selMat fun i => (i.1 + dx, i.2.1, i.2.2)

theorem rhoMat_mulVec (v : Idx → R) (i : Idx) :
    (rhoMat *ᵥ v) i = v (i.1, i.2.1, i.2.2 - Fin.ofNat 64 (rhoOffset i.1 i.2.1)) :=
  selMat_mulVec _ v i

theorem piMat_mulVec (v : Idx → R) (i : Idx) : (piMat *ᵥ v) i = v (i.1 + 3 * i.2.1, i.1, i.2.2) :=
  selMat_mulVec _ v i

theorem shiftMat_mulVec (dx : Fin 5) (v : Idx → R) (i : Idx) :
    (shiftMat dx *ᵥ v) i = v (i.1 + dx, i.2.1, i.2.2) :=
  selMat_mulVec _ v i

/-- The `iota` constant of round `r`: the bits of `rc r` in lane `(0, 0)`. -/
def iotaVec (r : Fin 24) : Idx → R :=
  fun i => if i.1 = 0 ∧ i.2.1 = 0 ∧ (rc r).testBit i.2.2 then 1 else 0

/-- `B = pi (rho (theta S))`, the linear part of a round before `chi`. -/
def linB (S : Idx → R) : Idx → R := piMat *ᵥ (rhoMat *ᵥ (thetaMat *ᵥ S))

theorem linB_add (S S' : Idx → R) : linB (S + S') = linB S + linB S' := by
  simp only [linB, Matrix.mulVec_add]

theorem linB_smul (e : R) (S : Idx → R) : linB (e • S) = e • linB S := by
  simp only [linB, Matrix.mulVec_smul]

/-- `B = pi (rho (theta S))` at lane `(x, y)`: `theta S` at lane `(x + 3y, x)` rotated by
`rhoOffset (x + 3y) x`. -/
theorem linB_apply (S : Idx → R) (x y : Fin 5) (z : Fin 64) :
    linB S (x, y, z) =
      S (x + 3 * y, x, z - Fin.ofNat 64 (rhoOffset (x + 3 * y) x)) +
        ∑ Y, S (x + 3 * y + 4, Y, z - Fin.ofNat 64 (rhoOffset (x + 3 * y) x)) +
        ∑ Y, S (x + 3 * y + 1, Y, z - Fin.ofNat 64 (rhoOffset (x + 3 * y) x) - 1) := by
  simp only [linB, piMat_mulVec, rhoMat_mulVec, thetaMat_mulVec]

/-- The first `chi` operand, `a = 1 + B[x+1, y]` (`~b[(x + 1) % 5][y]`). -/
def opA (S : Idx → R) : Idx → R := fun i => 1 + (shiftMat 1 *ᵥ linB S) i

/-- The second `chi` operand, `b = B[x+2, y]`. -/
def opB (S : Idx → R) : Idx → R := shiftMat 2 *ᵥ linB S

/-- The third operand, `c = S'[x, y] + B[x, y] + iota[x, y]`, from the committed next
state `S'`. -/
def opC (r : Fin 24) (S S' : Idx → R) : Idx → R := S' + linB S + iotaVec r

end Matrices

/-! ## The round relation -/

variable {K : Type*} [Field K] [DecidableEq K]

/-- The round relation of round constant `r` between committed states `S` and `S'`
(`keccak_skip_link.h:39-55`): `a * b + c = 0` at every lane and bit. -/
def RoundRelation (r : Fin 24) (S S' : State K) : Prop :=
  ∀ i : Idx, opA (flat S) i * opB (flat S) i + opC r (flat S) (flat S') i = 0

section CharTwo

variable [CharP K 2]

omit [DecidableEq K] in
theorem thetaMat_mulVec_flat (A : State K) : thetaMat *ᵥ flat A = flat (Keccak.theta A) := by
  funext ⟨x, y, z⟩
  simp only [thetaMat_mulVec, flat, Keccak.theta, lxor, rotl, bxor_eq, Fin.sum_univ_five]
  rw [show Fin.ofNat 64 1 = 1 from rfl]
  ring

omit [DecidableEq K] [CharP K 2] in
theorem rhoMat_mulVec_flat (A : State K) : rhoMat *ᵥ flat A = flat (Keccak.rho A) := by
  funext ⟨x, y, z⟩
  rw [rhoMat_mulVec, rho_eq]
  rfl

omit [DecidableEq K] [CharP K 2] in
theorem piMat_mulVec_flat (A : State K) : piMat *ᵥ flat A = flat (Keccak.pi A) := by
  funext ⟨x, y, z⟩
  rw [piMat_mulVec]
  rfl

omit [CharP K 2] [DecidableEq K] in
theorem iotaVec_eq_ofBool (r : Fin 24) (i : Idx) :
    (iotaVec r i : K) = ofBool (decide (i.1 = 0 ∧ i.2.1 = 0) && (rc r).testBit i.2.2) := by
  unfold iotaVec ofBool
  by_cases h : i.1 = 0 ∧ i.2.1 = 0
  · simp [h]
  · rw [ite_eq_right_iff.mpr fun h' => absurd ⟨h'.1, h'.2.1⟩ h]
    simp [h]

omit [DecidableEq K] in
/-- On bits, `B` is the bit model's `pi (rho (theta f))`. -/
theorem linB_flat_ofBits (f : BitState) :
    linB (flat (ofBits (K := K) f)) = flat (ofBits (piBits (rhoBits (thetaBits f)))) := by
  rw [linB, thetaMat_mulVec_flat, theta_ofBits, rhoMat_mulVec_flat, rho_ofBits,
    piMat_mulVec_flat, pi_ofBits]

omit [DecidableEq K] in
/-- One bit of the relation: `(1 + p) q + (v + u + c) = 0` says that `v` is the `chi` and
`iota` output `u ⊕ (¬p ∧ q) ⊕ c`. -/
theorem chi_relation_iff (p q u c : Bool) (v : K) :
    (1 + ofBool p) * ofBool q + (v + ofBool u + ofBool c) = 0 ↔
      v = ofBool ((u ^^ (!p && q)) ^^ c) := by
  have hx : ∀ a b : Bool, (ofBool (a ^^ b) : K) = ofBool a + ofBool b := fun a b => by
    rw [← bxor_ofBool, bxor_eq]
  have hand : (ofBool (!p && q) : K) = (1 + ofBool p) * ofBool q := by
    rw [← ofBool_mul_bnot, bnot, CharTwo.sub_eq_add]
    ring
  rw [hx, hx, hand, show (1 + ofBool p) * ofBool q + (v + ofBool u + ofBool c) =
    v + ((1 + ofBool p) * ofBool q + ofBool u + ofBool c) by ring, add_eq_zero_iff_eq_neg,
    CharTwo.neg_eq]
  constructor <;> intro h <;> linear_combination h

/-- **The round relation is the round.** On a Boolean state `S`, the relation holds
exactly when `S'` is the Keccak round of `S`. Only `S` needs to be Boolean: the relation
determines `S'`. -/
theorem roundRelation_iff {r : Fin 24} {S S' : State K} (hS : ∀ x y, AllBool (S x y)) :
    RoundRelation r S S' ↔ S' = Keccak.round r S := by
  rw [eq_ofBits hS, round_ofBits]
  generalize (fun x y z => decide (S x y z = 1)) = f
  have key : ∀ x y z, (opA (flat (ofBits (K := K) f)) (x, y, z) * opB (flat (ofBits f)) (x, y, z) +
      opC r (flat (ofBits f)) (flat S') (x, y, z) = 0 ↔
        S' x y z = ofBits (roundBits (rc r) f) x y z) := by
    intro x y z
    simp only [opA, opB, opC, linB_flat_ofBits, shiftMat_mulVec, Pi.add_apply, flat, ofBits,
      iotaVec_eq_ofBool, roundBits, iotaBits, chiBits]
    exact chi_relation_iff _ _ _ _ _
  simp only [RoundRelation, Prod.forall, key, funext_iff]

/-! ## Rounds and permutations -/

/-- Round relations along a sequence of `n + 1` states, round `t` with constant `ri t`. -/
def Rounds {n : ℕ} (ri : Fin n → Fin 24) (S : Fin (n + 1) → State K) : Prop :=
  ∀ t : Fin n, RoundRelation (ri t) (S t.castSucc) (S t.succ)

/-- On a Boolean first state, the round relations hold exactly when each state is the
round output of the previous one. -/
theorem rounds_iff {n : ℕ} {ri : Fin n → Fin 24} {S : Fin (n + 1) → State K}
    (h0 : ∀ x y, AllBool (S 0 x y)) :
    Rounds ri S ↔ ∀ t, S t.succ = Keccak.round (ri t) (S t.castSucc) := by
  have hbool : (∀ t : Fin n, (∀ x y, AllBool (S t.castSucc x y)) →
      S t.succ = Keccak.round (ri t) (S t.castSucc)) → ∀ t x y, AllBool (S t x y) := by
    intro h t
    induction t using Fin.induction with
    | zero => exact h0
    | succ t ih =>
      rw [h t ih]
      exact round_allBool ih _
  constructor
  · intro h
    have hb := hbool fun t hb => (roundRelation_iff hb).mp (h t)
    exact fun t => (roundRelation_iff (hb _)).mp (h t)
  · intro h
    have hb := hbool fun t _ => h t
    exact fun t => (roundRelation_iff (hb _)).mpr (h t)

/-- The 24 round relations of one permutation, round `t` with constant `t`. -/
def PermRelation (S : Fin 25 → State K) : Prop := Rounds (n := 24) id S

/-- On a Boolean first state, a permutation's relations hold exactly when each state is
the round output of the previous one. -/
theorem permRelation_iff {S : Fin 25 → State K} (h0 : ∀ x y, AllBool (S 0 x y)) :
    PermRelation S ↔ ∀ t : Fin 24, S t.succ = Keccak.round t (S t.castSucc) :=
  rounds_iff h0

/-- A permutation's relations carry an encoding of `s` in the first state to an encoding
of the vendored `f1600 s` in the last. -/
theorem PermRelation.encodes {S : Fin 25 → State K} {s : Array UInt64} (h : PermRelation S)
    (h0 : Encodes (S 0) s) : Encodes (S (Fin.last 24)) (SLHDSA.Concrete.Keccak.f1600 s) := by
  have hr := (permRelation_iff h0.bool).mp h
  have key : ∀ i : Fin 25, Encodes (S i) ((List.range i).foldl
      (fun s r => SLHDSA.Concrete.Keccak.round s SLHDSA.Concrete.Keccak.roundConstants[r]!) s) := by
    intro i
    induction i using Fin.induction with
    | zero => exact h0
    | succ t ih =>
      rw [hr t, Fin.val_succ, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
      exact ih.round t
  exact key (Fin.last 24)

/-! ## State maps -/

/-- **A state map** of `rounds` rounds over `S` committed states: round `t` relates state
`inp t` to state `out t` (`KeccakSkipLink::build`, `keccak_skip_link.h` lines 179-180 and
196: the `input` of round `t` and state `t + 1`). -/
structure StateMap (rounds S : ℕ) where
  inp : Fin rounds → Fin S
  out : Fin rounds → Fin S

namespace StateMap

variable {rounds S : ℕ}

/-- The round relations along a state map, round `t` with constant `ri t`. -/
def Rounds (m : StateMap rounds S) (ri : Fin rounds → Fin 24) (states : Fin S → State K) :
    Prop :=
  ∀ t, RoundRelation (ri t) (states (m.inp t)) (states (m.out t))

end StateMap

variable {np a : ℕ}

/-- Round `t` of the trace uses round constant `t mod 24` (`sha3_rc[t % 24]`,
`keccak_skip_link.h` line 94). -/
def roundIndex (t : Fin (24 * np)) : Fin 24 := ⟨t % 24, Nat.mod_lt _ (by decide)⟩

/-- The chunk of lane bit `z`: `z / 16`. -/
def zChunk (z : Fin 64) : Fin 4 := ⟨z / 16, by omega⟩

/-- The position of lane bit `z` in its chunk: `z mod 16`. -/
def zBit (z : Fin 64) : Fin (2 ^ 4) := ⟨z % 16, by show _ < 16; omega⟩

/-! ## Honest traces -/

/-- `n` Keccak rounds from `A`, round `i` with constant `i mod 24`. -/
-- spec-side
def iterRounds (A : State K) : ℕ → State K
  | 0 => A
  | n + 1 => Keccak.round ⟨n % 24, Nat.mod_lt _ (by decide)⟩ (iterRounds A n)

omit [CharP K 2] in
theorem iterRounds_allBool {A : State K} (hA : ∀ x y, AllBool (A x y)) :
    ∀ n x y, AllBool (iterRounds A n x y)
  | 0 => hA
  | n + 1 => round_allBool (iterRounds_allBool hA n) _

/-- Twenty-four rounds carry an encoding of `s` to an encoding of `f1600 s`. -/
theorem encodes_iterRounds {A : State K} {s : Array UInt64} (h : Encodes A s) :
    Encodes (iterRounds A 24) (SLHDSA.Concrete.Keccak.f1600 s) := by
  have hS : PermRelation fun i : Fin 25 => iterRounds A i := by
    intro t
    refine (roundRelation_iff (iterRounds_allBool h.bool t)).mpr ?_
    show iterRounds A ((t : ℕ) + 1) = _
    rw [iterRounds]
    congr 1
    exact Fin.ext (Nat.mod_eq_of_lt t.isLt)
  exact hS.encodes h

/-- **The honest input of permutation `p`** of the sponge `sp` on `seed` (`KeccakSkipTrace::absorb`):
block `0` absorbed into the zero state; for `1 ≤ p ≤ len / rate`, block `p` absorbed into the
output of permutation `p − 1`; later, the output of permutation `p − 1`. -/
-- spec-side
def spongeStart (sp : SpongeSpec) {len : ℕ} (seed : Fin len → BitWires K 8) : ℕ → State K
  | 0 => xorinBlock sp (fun _ _ _ => 0) (paddedByte sp seed 0)
  | p + 1 => if p + 1 ≤ len / sp.rate then
      xorinBlock sp (iterRounds (spongeStart sp seed p) 24) (paddedByte sp seed (p + 1))
    else iterRounds (spongeStart sp seed p) 24

section SpongeTrace

variable {sp : SpongeSpec} {len : ℕ} {seed : Fin len → BitWires K 8}

omit [CharP K 2] in
theorem spongeStart_allBool (hseed : ∀ i, AllBool (seed i)) :
    ∀ p x y, AllBool (spongeStart sp seed p x y)
  | 0 => (encodes_zero.xorinBlock (paddedByte_allBool (sp := sp) hseed 0)).bool
  | p + 1 => by
    have ih := spongeStart_allBool hseed p
    unfold spongeStart
    split_ifs
    · exact (Encodes.xorinBlock ⟨iterRounds_allBool ih 24, rfl⟩ (paddedByte_allBool hseed _)).bool
    · exact iterRounds_allBool ih 24

end SpongeTrace

end CharTwo

end GordieHowe.KeccakTrace
