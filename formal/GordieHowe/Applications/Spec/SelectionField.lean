-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.LinearIndependent.Defs
public import GordieHowe.Language.Realizations.Bits
public import GordieHowe.Applications.Params

@[expose] public section

/-!
# Field data for selection and memory checks

The chosen `w` basis elements encode a bit vector by a linear combination.
Injectivity on `w`-bit integers and membership in the chosen subfield are
field obligations, independent of any witness or challenge. The width `w` defaults to
`falconSampleBits` (sixteen, Falcon's HashToPoint sample), so `SelectionField K S` is the
sixteen-bit field data.
-/

namespace GordieHowe

structure Falcon512.Route (K : Type*) where
  count_enc : K
  full : K

/-- The natural-number view of a fixed binary embedding of `w` bits. -/
def selectionEmbed {K : Type*} [Field K] {w : ℕ} (e : Fin w → K) (v : ℕ) : K :=
  ∑ i : Fin w, if v / 2 ^ (i : ℕ) % 2 = 1 then e i else 0

/-- The `GF(2)`-combination of a linearly independent family, with Boolean
coefficients, is injective: the same field fact `selectionEmbed_injOn` uses
for the bits of a natural number, stated directly for a Boolean-indexed
vector. A packing of `w` bits into a linearly independent basis (as slice
weights) is injective on Boolean advice by this lemma. -/
theorem boolSum_injective {K : Type*} [Field K] [Module (ZMod 2) K] {w : ℕ} {e : Fin w → K}
    (he : LinearIndependent (ZMod 2) e) :
    Function.Injective fun b : Fin w → Bool => ∑ i, if b i then e i else 0 := by
  intro a b hab
  have h := Fintype.linearIndependent_iffₛ.mp he (fun i => if a i then (1 : ZMod 2) else 0)
    (fun i => if b i then (1 : ZMod 2) else 0) (by
      simp only [ite_smul, one_smul, zero_smul]
      exact hab)
  funext i
  have hi := h i
  cases ha : a i <;> cases hb : b i <;> simp_all

/-- The embedding is injective on `w`-bit integers when the basis is linearly
independent over `GF(2)`: it is the `GF(2)`-combination with the bits as
coefficients. -/
theorem selectionEmbed_injOn {K : Type*} [Field K] [Module (ZMod 2) K] {w : ℕ} {e : Fin w → K}
    (he : LinearIndependent (ZMod 2) e) : Set.InjOn (selectionEmbed e) (Set.Iio (2 ^ w)) := by
  intro v hv u hu hvu
  have hbits : (fun i : Fin w => Bits.constBit (K := ZMod 2) v i) =
      fun i : Fin w => Bits.constBit u i := by
    refine funext (Fintype.linearIndependent_iffₛ.mp he _ _ ?_)
    simp only [Bits.constBit, ite_smul, one_smul, zero_smul]
    exact hvu
  rw [← Nat.mod_eq_of_lt (Set.mem_Iio.mp hv), ← Nat.mod_eq_of_lt (Set.mem_Iio.mp hu),
    ← Bits.natOfBits_constBit (K := ZMod 2), ← Bits.natOfBits_constBit (K := ZMod 2), hbits]

/-- Chosen field data for selecting among `S` samples of `w` bits (`w` defaults to
`falconSampleBits`). `e` replaces an arbitrary function on natural numbers:
the circuit computes its embedding by field additions and multiplications. -/
structure SelectionField (K : Type*) [Field K] (S : ℕ) (w : ℕ := falconSampleBits) where
  E : Subfield K
  X : K
  X_not_mem : X ∉ E
  e : Fin w → K
  e_mem : ∀ i, e i ∈ E
  embed_injOn : Set.InjOn (selectionEmbed e) (Set.Iio (2 ^ w))
  g : K
  g_mem : g ∈ E
  g_order : ∀ a b, a ≤ S → b ≤ S → g ^ a = g ^ b → a = b

namespace SelectionField

variable {K : Type*} [Field K] {S w : ℕ}

/-- Specification readout, also used to embed compile-time constants. -/
def embed (F : SelectionField K S w) (v : ℕ) : K := selectionEmbed F.e v

theorem embed_mem (F : SelectionField K S w) (v : ℕ) : F.embed v ∈ F.E := by
  unfold embed selectionEmbed
  apply F.E.sum_mem
  intro i _
  split_ifs
  · exact F.e_mem i
  · exact F.E.zero_mem

/-- Wire-level embedding in the selected binary basis. -/
def embedBits [DecidableEq K] (F : SelectionField K S w) {m : ℕ} (hm : m ≤ w)
    (bits : Fin m → K) : K :=
  ∑ i, bits i * F.e (Fin.castLE hm i)

/-- Boolean wire embedding agrees with the natural-number specification. -/
theorem embedBits_eq [DecidableEq K] (F : SelectionField K S w) {m : ℕ} (hm : m ≤ w)
    {bits : Fin m → K} (hb : Bits.AllBool bits) :
    F.embedBits hm bits = F.embed (Bits.natOfBits bits) := by
  unfold embedBits embed selectionEmbed
  apply Finset.sum_of_injOn (Fin.castLE hm)
  · intro a _ b _ h
    exact Fin.ext (congrArg (fun x : Fin w => x.val) h)
  · intro a _
    exact Finset.mem_univ _
  · intro i _ hi
    have hmi : m ≤ i := by
      by_contra h
      have hlt : (i : ℕ) < m := by omega
      exact hi ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩
    have hlt := (Bits.natOfBits_lt bits).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) hmi)
    simpa only [Bits.constBit, ite_mul, one_mul, zero_mul] using
      congrArg (fun x : K => x * F.e i) (Bits.constBit_eq_zero_of_lt (K := K) hlt)
  · intro i _
    have heq := Bits.constBit_natOfBits hb i
    change bits i * F.e (Fin.castLE hm i) = _
    rw [← heq]
    unfold Bits.constBit
    simp only [Fin.val_castLE]
    split_ifs <;> simp

/-- The same field data at a smaller degree bound `S' ≤ S`: distinct powers of `g` up to
`S` are distinct up to `S'`. -/
def ofLE (F : SelectionField K S w) {S' : ℕ} (h : S' ≤ S) : SelectionField K S' w :=
  { F with g_order := fun a b ha hb => F.g_order a b (ha.trans h) (hb.trans h) }

end SelectionField
end GordieHowe
