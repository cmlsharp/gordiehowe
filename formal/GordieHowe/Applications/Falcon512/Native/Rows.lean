-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Rows.NativeLinear
public import GordieHowe.Applications.Spec.Rq

@[expose] public section

/-!
# Falcon-512 native signature rows

The native Falcon A circuit (`signature_relation` in `lib/gordiehowe/examples/falcon/falcon_native.h`,
benchmarked by `FalconNative.DISABLED_Bench`) commits `c` as `16` bits per coefficient, `s₁` and
`s₂`, and checks `s₁ − Σ_b 2^b·c_b + h * s₂ = 0` in `F[X]/(X^n + 1)` as one group of `native_linear`
rows (`NativeLinear`), with `h` the public key in coefficient form. The field has characteristic
`q = 12289`, so the rows are the Falcon ring relation itself: no bias, quotient or integer lifting.
`establish` pulls an accepted row system back to `Rq n`, given that `s₁` and `s₂` are casts of
naturals (the conclusion of the native norm gadget, `NativeNorm.sound`) and that the `c` bits are
Boolean.

The weight on bit `b` is `2^b mod q`, which is `2^b` in characteristic `q`.
-/

namespace GordieHowe.Falcon512.Native.Rows

open GordieHowe.NativeLinear

variable {F : Type*} [Field F] {n : ℕ}

/-- The witness the rows read: `c` as bits (bit `b` of coefficient `i` at `16i + b`),
`s₂`, `s₁`. -/
abbrev Wit (F : Type*) (n : ℕ) := (Fin (falconSampleBits * n) → F) × (Fin n → F) × (Fin n → F)

def cBits : Wit F n →ₗ[F] (Fin (falconSampleBits * n) → F) := LinearMap.fst F _ _
def s₂ : Wit F n →ₗ[F] (Fin n → F) := (LinearMap.fst F _ _).comp (LinearMap.snd F _ _)
def s₁ : Wit F n →ₗ[F] (Fin n → F) := (LinearMap.snd F _ _).comp (LinearMap.snd F _ _)

/-- Coefficient `i` of `c` from its bits, `Σ_b 2^b·c[16i + b]`. -/
def cCoeff (i : Fin n) : Wit F n →ₗ[F] F :=
  ∑ b : Fin falconSampleBits, ((2 : F) ^ (b : ℕ)) •
    ((LinearMap.proj ⟨falconSampleBits * i + b, by simp only [falconSampleBits]; omega⟩ :
      (Fin (falconSampleBits * n) → F) →ₗ[F] F).comp cBits)

/-- The public key's coefficients, as field elements. -/
def keyVec (h : _root_.Falcon.Rq n) (i : Fin n) : F := ((Falcon512.coeff h i).val : F)

/-- The three terms of the single group: `+s₁`, `−c`, `+h * s₂`. -/
def terms (h : _root_.Falcon.Rq n) : List (Term F (Wit F n) n 1) :=
  [⟨0, fun i => (LinearMap.proj i).comp s₁, 1, none⟩,
   ⟨0, cCoeff, -1, none⟩,
   ⟨0, fun i => (LinearMap.proj i).comp s₂, 1, some (.coeffs (keyVec h))⟩]

/-- The native signature rows for the public key `h`. -/
def rows (h : _root_.Falcon.Rq n) : Fin (1 * n) → Row F (Wit F n) := NativeLinear.rows (terms h)

/-- The raw samples as naturals, read from Boolean bits. -/
-- spec-side
def cNat [DecidableEq F] (W : Wit F n) (i : Fin n) : ℕ :=
  Bits.natOfBits fun b : Fin falconSampleBits =>
    cBits W ⟨falconSampleBits * i + b, by simp only [falconSampleBits]; omega⟩

/-- Reading `c`'s bits recovers `cCoeff`'s value under Booleanity. -/
theorem cNat_cast [DecidableEq F] (W : Wit F n) (hbits : Bits.AllBool (cBits W)) (i : Fin n) :
    (cNat W i : F) = cCoeff i W := by
  simp only [cNat, Bits.natOfBits, Nat.cast_sum, cCoeff, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, LinearMap.comp_apply, LinearMap.proj_apply, Nat.cast_ite, Nat.cast_pow,
    Nat.cast_ofNat]
  apply Finset.sum_congr rfl
  intro b _
  rcases hbits ⟨falconSampleBits * i + b, by simp only [falconSampleBits]; omega⟩ with hb | hb <;>
    simp [hb]

/-- Every row of the single group holds: coefficient `k` of `s₁ − c + h * s₂` is `0`. -/
theorem rows_hold_eq (h : _root_.Falcon.Rq n) (W : Wit F n) (hrows : rowsHold (rows h) W)
    (k : Fin n) :
    s₁ W k - cCoeff k W + LatticeCrypto.negacyclicConvCoeff (keyVec h) (s₂ W) k = 0 := by
  have hr := hrows (finProdFinEquiv ((0 : Fin 1), k))
  unfold Row.holds rows NativeLinear.rows at hr
  rw [Equiv.symm_apply_apply] at hr
  dsimp only at hr
  have hfilt : (terms (F := F) h).filter (fun t => t.row = (0 : Fin 1)) = terms h :=
    List.filter_eq_self.mpr fun t _ => by simp [Fin.eq_zero t.row]
  rw [hfilt, List.sum_linearMap_apply, List.map_map] at hr
  unfold terms at hr
  have hj : ∀ j : Fin n,
      LatticeCrypto.negacyclicConvCoeff (keyVec h) (Pi.single j 1) k * s₂ W j
        = s₂ W j * LatticeCrypto.negacyclicConvCoeff (keyVec h) (Pi.single j 1) k :=
    fun j => _root_.mul_comm _ _
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Function.comp_apply, Term.coeff, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearMap.proj_apply, one_smul, smul_eq_mul, neg_one_mul,
    LinearMap.sum_apply, hj] at hr
  rw [← DFT.negacyclicConvCoeff_eq_sum_mul_single (keyVec h) (fun j => s₂ W j) k] at hr
  linear_combination hr

/-- **Pullback of accepted native rows to the Falcon ring.** If the rows hold, the `c`
bits are Boolean (circuit Booleanity), and `s₁`, `s₂` are casts of the
naturals `x₁`, `x₂` (the gadget theorem `NativeNorm.sound`), then `c − s₂·h = s₁` in `Rq n` with
coefficients reduced mod `q`. `CharP F 12289` is a fact about the field. -/
theorem establish [DecidableEq F] [CharP F 12289] {h : _root_.Falcon.Rq n} {W : Wit F n} {x₁ x₂ : Fin n → ℕ}
    (hrows : rowsHold (rows h) W) (hbits : Bits.AllBool (cBits W))
    (hx₁ : ∀ i, (x₁ i : F) = s₁ W i) (hx₂ : ∀ i, (x₂ i : F) = s₂ W i) :
    Falcon512.ofCoeff (fun i => (cNat W i : _root_.Falcon.Coeff)) -
        Falcon512.ofCoeff (fun i => (x₂ i : _root_.Falcon.Coeff)) * h =
      Falcon512.ofCoeff (fun i => (x₁ i : _root_.Falcon.Coeff)) := by
  have hcp : CharP F _root_.Falcon.modulus := by unfold _root_.Falcon.modulus; infer_instance
  set φ : _root_.Falcon.Coeff →+* F := ZMod.castHom (dvd_refl _root_.Falcon.modulus) F with hφ
  have hφkey : ∀ i : Fin n, φ (Falcon512.coeff h i) = keyVec h i := by
    intro i
    rw [hφ, ZMod.castHom_apply, ZMod.cast_eq_val]
    rfl
  have hinj : Function.Injective φ := ZMod.castHom_injective F
  rw [Falcon512.mul_comm]
  apply LatticeCrypto.PolyBackend.ext_coeff (backend := _root_.Falcon.polyBackend n)
  intro k
  change Falcon512.coeff
      (Falcon512.ofCoeff (fun i => (cNat W i : _root_.Falcon.Coeff)) -
        h * Falcon512.ofCoeff (fun i => (x₂ i : _root_.Falcon.Coeff))) k
      = Falcon512.coeff (Falcon512.ofCoeff (fun i => (x₁ i : _root_.Falcon.Coeff))) k
  rw [Falcon512.coeff_ofCoeff]
  apply hinj
  have hlhs : Falcon512.coeff
      (Falcon512.ofCoeff (fun i => (cNat W i : _root_.Falcon.Coeff)) - h *
        Falcon512.ofCoeff (fun i => (x₂ i : _root_.Falcon.Coeff))) k
      = (cNat W k : _root_.Falcon.Coeff) -
        LatticeCrypto.negacyclicConvCoeff (Falcon512.coeff h) (fun i => (x₂ i : _root_.Falcon.Coeff)) k := by
    unfold Falcon512.coeff
    rw [LatticeCrypto.NegacyclicRing.coeff_sub (Falcon.coeffRing n)]
    change Falcon512.coeff (Falcon512.ofCoeff fun i => (cNat W i : _root_.Falcon.Coeff)) k -
        Falcon512.coeff (h * Falcon512.ofCoeff fun i => (x₂ i : _root_.Falcon.Coeff)) k =
      (cNat W k : _root_.Falcon.Coeff) -
        LatticeCrypto.negacyclicConvCoeff (Falcon512.coeff h)
          (fun i => (x₂ i : _root_.Falcon.Coeff)) k
    rw [Falcon512.coeff_ofCoeff, Falcon512.coeff_mul, Falcon512.coeff_ofCoeff]
  rw [hlhs, map_sub, DFT.negacyclicConvCoeff_map]
  simp only [map_natCast]
  have hkey : ⇑φ ∘ Falcon512.coeff h = keyVec (F := F) h := funext hφkey
  have hx2' : ⇑φ ∘ (fun j => (x₂ j : _root_.Falcon.Coeff)) = s₂ W :=
    funext fun j => (map_natCast φ (x₂ j)).trans (hx₂ j)
  rw [hkey, hx2']
  have hcNat : (cNat W k : F) = cCoeff k W := cNat_cast W hbits k
  have hrow := rows_hold_eq h W hrows k
  rw [← hcNat, ← hx₁ k] at hrow
  linear_combination -hrow

end GordieHowe.Falcon512.Native.Rows
