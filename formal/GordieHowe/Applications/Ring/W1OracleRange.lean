-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Split
public import GordieHowe.Applications.MLDSA.Signing.Ideal
public import GordieHowe.Foundations.ToMathlib.FintypeBytes
public import GordieHowe.Foundations.Probability.Probability
public import GordieHowe.Model.QROM.QueryBits

@[expose] public section

/-!
# The oracle range of the ML-DSA ring publishing `w₁`, and its uniform decodings

The oracle of the ring publishing `w₁` takes values in `w1Y I₁ k e`: bit strings of bytes indexed
by `I₁ ⊕ Fin (k + e)`. The bytes at `I₁` are the base signer's component, the bytes at
`Fin (k + e)` the proof system's component `XOut k e`; `w1Sp` is the additive split.

- `map_uniform_equiv`, `map_uniform_fst`, `map_uniform_restrict`: the uniform law pushed through an
  equivalence, a first projection, and a restriction of functions to the range of an embedding is
  uniform. `map_uniform_fst_split`: the first component of a split uniform value is uniform.
- `bitsByte`, `bytesOfBits`: 8 bits as a byte, `n` bytes of bits as `Bytes n`.
  `bytesOf ι`: the bytes read from the bits at the positions `ι j`;
  `map_uniform_bytesOf`: it is uniform. `w1Bytes ι`: the same decoding read through the first
  component of `w1Sp`; `map_uniform_w1Bytes`. Commitment hashes `CommitHashBytes p` are
  `Bytes (p.lambda / 4)`, so `w1Bytes` covers them.
- `probUniform_mem_of_map`, `card_bytes`, `muAns_probUniform_le`: a uniform 64-byte decoding hits a
  set `S` with probability at most `|S| / 2^512`.
- `exists_decode_of_card`: a type of `2^r` elements with `r ≤ 8|I₁|` is the uniform image of
  `BitStr I₁ (Fin 8)`. `exists_maskDecode` for the mask box when `2γ₁ = 2^g` and `2γ₁ < q`, and
  `exists_maskDecode44/65/87` at the three parameter sets.
-/

namespace GordieHowe.RingSignature.W1Range

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.IOP PMF
open GordieHowe.QROM (BitStr XOut)
open scoped ENNReal

/-! ### Uniform laws under equivalences, projections and restrictions -/

section Uniform

variable {A B C : Type} [Fintype A] [Fintype B] [Fintype C] [Nonempty A] [Nonempty B] [Nonempty C]

/-- The uniform law pushed through an equivalence is uniform. -/
theorem map_uniform_equiv (e : A ≃ B) : (uniformOfFintype A).map e = uniformOfFintype B := by
  ext b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [Fintype.card_congr e]
  · intro a ha
    simp only [ite_eq_right_iff]
    rintro rfl
    exact absurd (e.symm_apply_apply a).symm ha

/-- The first component of a uniform pair is uniform. -/
theorem map_uniform_fst : (uniformOfFintype (B × C)).map Prod.fst = uniformOfFintype B := by
  ext b
  rw [PMF.map_apply, tsum_fintype, Fintype.sum_prod_type, Finset.sum_eq_single b]
  · simp only [uniformOfFintype_apply, Fintype.card_prod, ite_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, Nat.cast_mul]
    have h0 : (Fintype.card C : ℝ≥0∞) ≠ 0 := by simp
    have ht : (Fintype.card C : ℝ≥0∞) ≠ ∞ := by simp
    rw [ENNReal.mul_inv (Or.inr ht) (Or.inr h0), mul_left_comm, ENNReal.mul_inv_cancel h0 ht,
      mul_one]
  · intro b' _ hb
    simp [Ne.symm hb]
  · simp

/-- Pushing the uniform law through two maps that each give the uniform law gives it. -/
theorem map_uniform_comp {f : A → B} {g : B → C} (hf : (uniformOfFintype A).map f =
    uniformOfFintype B) (hg : (uniformOfFintype B).map g = uniformOfFintype C) :
    (uniformOfFintype A).map (g ∘ f) = uniformOfFintype C := by
  rw [← PMF.map_comp, hf, hg]

/-- The restriction of a uniform function to the range of an embedding is uniform. -/
theorem map_uniform_restrict {I K V : Type} [Fintype I] [DecidableEq I] [Fintype K]
    [DecidableEq K] [Fintype V]
    [Nonempty V] (ι : K ↪ I) :
    (uniformOfFintype (I → V)).map (fun x k => x (ι k)) = uniformOfFintype (K → V) := by
  classical
  let r : {i // i ∈ Set.range ι} ≃ K := (Equiv.ofInjective ι ι.injective).symm
  let e : (I → V) ≃ (K → V) × ({i // i ∉ Set.range ι} → V) :=
    (Equiv.piEquivPiSubtypeProd (· ∈ Set.range ι) fun _ => V).trans
      (Equiv.prodCongr (Equiv.arrowCongr r (Equiv.refl V)) (Equiv.refl _))
  have hf : (fun (x : I → V) k => x (ι k)) = Prod.fst ∘ e := by
    funext x k
    simp [e, r, Equiv.arrowCongr_apply]
  rw [hf, ← PMF.map_comp, map_uniform_equiv, map_uniform_fst]

/-- The first component of a uniform value read through an additive split is uniform. -/
theorem map_uniform_fst_split {Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
    [Fintype Y] [Fintype Y₁] [Fintype Y₂] [Nonempty Y] [Nonempty Y₁] [Nonempty Y₂]
    (sp : OracleSplit Y Y₁ Y₂) :
    (uniformOfFintype Y).map (fun y => (sp y).1) = uniformOfFintype Y₁ :=
  map_uniform_comp (f := sp.toEquiv) (map_uniform_equiv _) map_uniform_fst

/-- A decoding that pushes the uniform law to the uniform law hits a set `S` with probability
`|S| / |B|`. -/
theorem probUniform_mem_of_map {f : A → B} (hf : (uniformOfFintype A).map f = uniformOfFintype B)
    (S : Finset B) : Pr[a ← A : f a ∈ S] = S.card / Fintype.card B := by
  classical
  have h : Pr[a ← A : f a ∈ S] = Pr[b ← B : b ∈ S] := by
    unfold probUniform
    rw [← hf, PMF.toOuterMeasure_map_apply]
    rfl
  rw [h, probUniform_eq_card_div]
  simp

end Uniform

/-! ### The oracle range and its split -/

/-- The range of the oracle of the ring publishing `w₁`: bytes of 8 bits indexed by the base
signer's positions `I₁` and the proof system's `k + e` positions. -/
abbrev w1Y (I₁ : Type) (k e : ℕ) := BitStr (I₁ ⊕ Fin (k + e)) (Fin 8)

/-- The split of `w1Y` into the bytes at `I₁` and the proof system's range `XOut k e`. -/
def w1Sp (I₁ : Type) (k e : ℕ) : OracleSplit (w1Y I₁ k e) (BitStr I₁ (Fin 8)) (XOut k e) :=
  { Equiv.sumArrowEquivProdArrow I₁ (Fin (k + e)) (Fin 8 → ZMod 2) with
    map_add' := fun _ _ => rfl }

/-! ### Byte decodings -/

/-- 8 bits as a byte (bit `b` has weight `2^b`). -/
def bitsByte : (Fin 8 → ZMod 2) ≃ UInt8 :=
  ((finFunctionFinEquiv : (Fin 8 → Fin 2) ≃ Fin (2 ^ 8)).trans (finCongr (by norm_num))).trans
    UInt8.equivFin.symm

/-- `n` bytes of bits as `Bytes n`. -/
def bytesOfBits (n : ℕ) : (Fin n → Fin 8 → ZMod 2) ≃ Bytes n :=
  ((Equiv.refl (Fin n)).arrowCongr bitsByte).trans (Vector.equivFun UInt8 n).symm

/-- The `n` bytes read from the bits at the positions `ι j`. -/
def bytesOf {I₁ : Type} {n : ℕ} (ι : Fin n ↪ I₁) (x : BitStr I₁ (Fin 8)) : Bytes n :=
  bytesOfBits n fun j => x (ι j)

/-- There are `2^(8n)` byte strings of length `n`. -/
theorem card_bytes (n : ℕ) : Fintype.card (Bytes n) = 2 ^ (8 * n) := by
  rw [Fintype.card_congr (Vector.equivFun _ _), Fintype.card_fun, Fintype.card_fin,
    Fintype.card_congr UInt8.equivFin, Fintype.card_fin, pow_mul]
  norm_num

variable {I₁ : Type} [Fintype I₁] [DecidableEq I₁]

/-- The byte decoding of a uniform bit string is uniform. -/
theorem map_uniform_bytesOf {n : ℕ} (ι : Fin n ↪ I₁) :
    (uniformOfFintype (BitStr I₁ (Fin 8))).map (bytesOf ι) = uniformOfFintype (Bytes n) :=
  map_uniform_comp (f := fun (x : BitStr I₁ (Fin 8)) j => x (ι j)) (g := bytesOfBits n)
    (map_uniform_restrict ι) (map_uniform_equiv _)

/-- The byte decoding of the first component of `w1Y`. -/
def w1Bytes {k e n : ℕ} (ι : Fin n ↪ I₁) (y : w1Y I₁ k e) : Bytes n :=
  bytesOf ι (w1Sp I₁ k e y).1

/-- The byte decoding of the first component of a uniform `w1Y` value is uniform. -/
theorem map_uniform_w1Bytes {k e n : ℕ} (ι : Fin n ↪ I₁) :
    (uniformOfFintype (w1Y I₁ k e)).map (w1Bytes ι) = uniformOfFintype (Bytes n) :=
  map_uniform_comp (f := fun y => (w1Sp I₁ k e y).1) (map_uniform_fst_split _)
    (map_uniform_bytesOf ι)

/-- **The message-representative decoding is collision-bounded**: it hits a set `S` of 64-byte
strings with probability at most `|S| / 2^512`. -/
theorem muAns_probUniform_le {k e : ℕ} (ι : Fin 64 ↪ I₁) (S : Finset (Bytes 64)) :
    Pr[y ← w1Y I₁ k e : w1Bytes ι y ∈ S] ≤ S.card / 2 ^ 512 := by
  rw [probUniform_mem_of_map (map_uniform_w1Bytes ι) S, card_bytes, Nat.cast_pow, Nat.cast_ofNat]

/-! ### Mask decodings -/

/-- **A type of `2^r` elements with `r ≤ 8|I₁|` is a uniform image of `BitStr I₁ (Fin 8)`**: read
`r` of the bits and apply an equivalence. -/
theorem exists_decode_of_card {T : Type} [Fintype T] [Nonempty T] {r : ℕ}
    (hT : Fintype.card T = 2 ^ r) (hr : r ≤ 8 * Fintype.card I₁) :
    ∃ d : BitStr I₁ (Fin 8) → T,
      (uniformOfFintype (BitStr I₁ (Fin 8))).map d = uniformOfFintype T := by
  let u : BitStr I₁ (Fin 8) ≃ (I₁ × Fin 8 → ZMod 2) := (Equiv.curry _ _ _).symm
  have hc : r ≤ Fintype.card (I₁ × Fin 8) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    omega
  let ι : Fin r ↪ I₁ × Fin 8 := (Fin.castLEEmb hc).trans (Fintype.equivFin _).symm.toEmbedding
  let v : (Fin r → ZMod 2) ≃ T := Fintype.equivOfCardEq (by simp [hT])
  exact ⟨(v ∘ fun x k => x (ι k)) ∘ u, map_uniform_comp (map_uniform_equiv u)
    (map_uniform_comp (map_uniform_restrict ι) (map_uniform_equiv v))⟩

/-- **A uniform mask decoding**: when `2γ₁ = 2^g` and `2γ₁ < q`, the mask box has
`2^(g · 256 · l)` elements, and it is the uniform image of `BitStr I₁ (Fin 8)` when
`g · 256 · l ≤ 8|I₁|`. -/
theorem exists_maskDecode {p : Params} [Nonempty (MaskBox p)] {g : ℕ}
    (hq : 2 * p.gamma1 < modulus) (hg : 2 * p.gamma1 = 2 ^ g)
    (hI : g * 256 * p.l ≤ 8 * Fintype.card I₁) :
    ∃ d : BitStr I₁ (Fin 8) → MaskBox p,
      (uniformOfFintype (BitStr I₁ (Fin 8))).map d = uniformOfFintype (MaskBox p) := by
  refine exists_decode_of_card (r := g * 256 * p.l) ?_ hI
  rw [card_maskBox hq, hg, ← pow_mul, ringDegree, mul_assoc]

/-- The uniform mask decoding at ML-DSA-44 (`2γ₁ = 2^18`, `l = 4`). -/
theorem exists_maskDecode44 (hI : 18432 ≤ 8 * Fintype.card I₁) :
    ∃ d : BitStr I₁ (Fin 8) → MaskBox _root_.MLDSA.mldsa44,
      (uniformOfFintype (BitStr I₁ (Fin 8))).map d = uniformOfFintype (MaskBox _root_.MLDSA.mldsa44) :=
  haveI : Nonempty (MaskBox _root_.MLDSA.mldsa44) := maskBox_nonempty (by decide)
  exists_maskDecode (g := 18) (by decide) (by decide) (le_trans (by decide) hI)

/-- The uniform mask decoding at ML-DSA-65 (`2γ₁ = 2^20`, `l = 5`). -/
theorem exists_maskDecode65 (hI : 25600 ≤ 8 * Fintype.card I₁) :
    ∃ d : BitStr I₁ (Fin 8) → MaskBox _root_.MLDSA.mldsa65,
      (uniformOfFintype (BitStr I₁ (Fin 8))).map d = uniformOfFintype (MaskBox _root_.MLDSA.mldsa65) :=
  haveI : Nonempty (MaskBox _root_.MLDSA.mldsa65) := maskBox_nonempty (by decide)
  exists_maskDecode (g := 20) (by decide) (by decide) (le_trans (by decide) hI)

/-- The uniform mask decoding at ML-DSA-87 (`2γ₁ = 2^20`, `l = 7`). -/
theorem exists_maskDecode87 (hI : 35840 ≤ 8 * Fintype.card I₁) :
    ∃ d : BitStr I₁ (Fin 8) → MaskBox _root_.MLDSA.mldsa87,
      (uniformOfFintype (BitStr I₁ (Fin 8))).map d = uniformOfFintype (MaskBox _root_.MLDSA.mldsa87) :=
  haveI : Nonempty (MaskBox _root_.MLDSA.mldsa87) := maskBox_nonempty (by decide)
  exists_maskDecode (g := 20) (by decide) (by decide) (le_trans (by decide) hI)

end GordieHowe.RingSignature.W1Range
