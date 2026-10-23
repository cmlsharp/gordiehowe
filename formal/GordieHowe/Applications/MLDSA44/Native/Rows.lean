-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Rows.NativeLinear
public import GordieHowe.Applications.MLDSA44.Spec.Basic
public import GordieHowe.Language.Realizations.Bits
import all LatticeCrypto.MLDSA.Concrete.NTT

@[expose] public section

/-!
# ML-DSA-44 native signature rows

The native ML-DSA A circuit (`signature_relation` in `lib/gordiehowe/examples/mldsa/mldsa_native.h`,
benchmarked by `MLDSANative.DISABLED_Bench`) commits `w′`, `z` and the challenge crossing bits
`sup`, `sgn`, and checks

`w′_i − Σ_j A_ij * z_j + 2^d·(t1_i * sup) − 2^(d+1)·(t1_i * sgn) = 0`

in `F[X]/(X^256 + 1)` as `K = 4` groups of `native_linear` rows (`NativeLinear`). The C++ states
it as one affine row per coefficient, with `Â` in NTT form through `PolyMatVec` and `t1` in
coefficient form through `PolyBroadcast`. For each `i` the row group has the terms

* `term(i, w′_i, 1)`;
* `term(i, z_j, −1, Â_ij, PublicForm::kNtt)` for each `j`;
* `term(i, sup, of_scalar(1 << d), t1_i)` and `term(i, sgn, −of_scalar(2 << d), t1_i)`, both in
  coefficient form.

The field has characteristic `q = 8380417`, so the rows are the ring relation itself: no
quotient or integer lifting. The two challenge terms together are `−c * (2^d·t1_i)` with
`c = sup − 2·sgn`.

The verifier supplies `Â = ExpandA(ρ)` as NTT spectra and `t1` as coefficients, each coefficient
`x` as `of_scalar(x)`, which is `embed x`. The row polynomial denoted by `Â_ij` is
`A_ij = NTT⁻¹(Â_ij)`; the NTT-form data is its spectrum in bit-reversed order at `ψ = ζ = 1753`.

`row_eval` pulls rows back to `R_q`: with Boolean `sup`, `sgn` and `w′`, `z` the images of
coefficients `xw`, `xz`, row `(i, k)` is the image of coefficient `k` of
`xw_i − computeWApprox(Â, c, z, t1)_i`, FIPS 204 Algorithm 8 line 9 for the vendored primitives.
`rows_hold_of_eq` is the converse, for completeness.

The witness bundles the four operands. Their commitment order does not enter the rows.
-/

namespace GordieHowe.MLDSA44.Native.Rows

open GordieHowe.NativeLinear

/-- ML-DSA-44's vendored concrete primitives. -/
abbrev prims : _root_.MLDSA.Primitives _root_.MLDSA.mldsa44 :=
  _root_.MLDSA.Concrete.concretePrimitives _root_.MLDSA.mldsa44

/-- An ML-DSA-44 public key `(ρ, t₁)`. -/
abbrev PublicKey : Type := _root_.MLDSA.PublicKey _root_.MLDSA.mldsa44 prims

/-- `K = 4`, the rows of `A`, as the vendored parameter record states it. -/
abbrev nRows : ℕ := _root_.MLDSA.mldsa44.k

/-- `L = 4`, the columns of `A`. -/
abbrev nCols : ℕ := _root_.MLDSA.mldsa44.l

/-- `N = 256`, the ring degree. -/
abbrev deg : ℕ := _root_.MLDSA.ringDegree

variable {F : Type*} [Field F]

/-! ### Witness and terms -/

/-- The witness the rows read: `w′` (`K` polynomials), `z` (`L` polynomials), and the
challenge crossing bits `sup` and `sgn`. -/
abbrev Wit (F : Type*) :=
  (Fin nRows → Fin deg → F) × (Fin nCols → Fin deg → F) × (Fin deg → F) × (Fin deg → F)

def wApprox : Wit F →ₗ[F] (Fin nRows → Fin deg → F) := LinearMap.fst F _ _
def z : Wit F →ₗ[F] (Fin nCols → Fin deg → F) := (LinearMap.fst F _ _).comp (LinearMap.snd F _ _)
def sup : Wit F →ₗ[F] (Fin deg → F) :=
  (LinearMap.fst F _ _).comp ((LinearMap.snd F _ _).comp (LinearMap.snd F _ _))
def sgn : Wit F →ₗ[F] (Fin deg → F) :=
  (LinearMap.snd F _ _).comp ((LinearMap.snd F _ _).comp (LinearMap.snd F _ _))

variable [CharP F _root_.MLDSA.modulus]

/-- `Z_q → F`. On a canonical representative `x` this is the C++ `of_scalar(x)`. -/
def embed : _root_.MLDSA.Coeff →+* F := ZMod.castHom (dvd_refl _) F

theorem embed_injective : Function.Injective (embed (F := F)) := ZMod.castHom_injective F

/-- `Â = ExpandA(ρ)`, the verifier's NTT-domain matrix (`MLDSA44.expandAFull`, FIPS 204
Algorithm 32). At a key whose `ExpandA` finishes within the byte budget it is the matrix the
verifier computes, `MLDSA44.expandABounded` (`MLDSA44.expandABounded_eq_expandAFull`). -/
noncomputable def aHat (pk : PublicKey) :
    _root_.MLDSA.TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l :=
  MLDSA44.expandAFull _root_.MLDSA.mldsa44 pk.rho

/-- `A_ij = NTT⁻¹(Â_ij)`, the coefficient polynomial the NTT-form data denotes. -/
noncomputable def aEntry (pk : PublicKey) (i : Fin nRows) (j : Fin nCols) : _root_.MLDSA.Rq :=
  _root_.MLDSA.Concrete.invNTT (((aHat pk).get i).get j)

/-- The NTT-form data the verifier reads for `Â_ij`. -/
noncomputable def aHatData (pk : PublicKey) (i : Fin nRows) (j : Fin nCols) (k : Fin deg) : F :=
  embed ((((aHat pk).get i).get j).coeffs.get k)

/-- The coefficients of `A_ij` in `F`. -/
noncomputable def aData (pk : PublicKey) (i : Fin nRows) (j : Fin nCols) (k : Fin deg) : F := embed ((aEntry pk i j).get k)

/-- The coefficients of `t1_i` in `F`. -/
def t1Data (pk : PublicKey) (i : Fin nRows) (k : Fin deg) : F := embed ((pk.t1.get i).get k)

/-- Group `i`'s terms in the C++ order: `+w′_i`, `−Â_ij * z_j` for each `j`,
`+2^d·t1_i * sup`, `−2^(d+1)·t1_i * sgn`. -/
noncomputable def groupTerms (pk : PublicKey) (i : Fin nRows) : List (Term F (Wit F) deg nRows) :=
  ⟨i, fun k => (LinearMap.proj k).comp ((LinearMap.proj i).comp wApprox), 1, none⟩ ::
    ((List.finRange nCols).map fun j =>
      ⟨i, fun k => (LinearMap.proj k).comp ((LinearMap.proj j).comp z), -1,
        some (.ntt (aHatData pk i j) (aData pk i j))⟩) ++
    [⟨i, fun k => (LinearMap.proj k).comp sup, 2 ^ _root_.MLDSA.droppedBits,
        some (.coeffs (t1Data pk i))⟩,
     ⟨i, fun k => (LinearMap.proj k).comp sgn, -(2 * 2 ^ _root_.MLDSA.droppedBits),
        some (.coeffs (t1Data pk i))⟩]

/-- All `4` groups. -/
noncomputable def terms (pk : PublicKey) : List (Term F (Wit F) deg nRows) :=
  (List.finRange nRows).flatMap (groupTerms pk)

/-- The native signature rows for the public key `pk`. -/
noncomputable def rows (pk : PublicKey) : Fin (nRows * deg) → Row F (Wit F) := NativeLinear.rows (terms pk)

theorem groupTerms_row (pk : PublicKey) (i : Fin nRows) :
    ∀ t ∈ groupTerms (F := F) pk i, t.row = i := by
  intro t ht
  simp only [groupTerms, List.cons_append, List.mem_cons, List.mem_append, List.mem_map,
    List.mem_finRange, true_and, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | ⟨j, rfl⟩ | rfl | rfl <;> rfl

/-! ### Pullback to `R_q` -/

variable [DecidableEq F]

/-- A Boolean wire as a coefficient. -/
-- spec-side
def bitCoeff (v : F) : _root_.MLDSA.Coeff := if v = 1 then 1 else 0

omit [DecidableEq F] in
theorem embed_bitCoeff [DecidableEq F] {v : F} (hv : v = 0 ∨ v = 1) : embed (bitCoeff v) = v := by
  unfold bitCoeff
  rcases hv with rfl | rfl <;> simp

/-- The challenge polynomial `c = sup − 2·sgn`, read from the crossing bits. -/
-- spec-side
def cPoly (W : Wit F) : _root_.MLDSA.Rq :=
  MLDSA44.ofCoeff fun k => bitCoeff (sup W k) - 2 * bitCoeff (sgn W k)

/-- **Row evaluation.** When `w′` and `z` are images of the coefficients `xw`, `xz` and the
crossing bits are Boolean, row `(i, k)` evaluates to the image of coefficient `k` of
`xw_i − computeWApprox(Â, c, z, t1)_i`. -/
theorem row_eval {pk : PublicKey} {W : Wit F} {xw : Fin nRows → Fin deg → _root_.MLDSA.Coeff}
    {xz : Fin nCols → Fin deg → _root_.MLDSA.Coeff}
    (hsup : Bits.AllBool (sup W)) (hsgn : Bits.AllBool (sgn W))
    (hw : ∀ i k, embed (xw i k) = wApprox W i k) (hz : ∀ j k, embed (xz j k) = z W j k)
    (i : Fin nRows) (k : Fin deg) :
    (rows (F := F) pk (finProdFinEquiv (i, k))).1 W =
      embed (xw i k - MLDSA44.coeff ((_root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 prims
        (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (aHat pk) (cPoly W)
        (Vector.ofFn fun j => MLDSA44.ofCoeff (xz j)) pk.t1).get i) k) := by
  rw [rows, terms, NativeLinear.rows_flatMap (groupTerms pk) (groupTerms_row pk) i k,
    MLDSA44.coeff_computeWApprox]
  simp only [groupTerms, List.cons_append, List.map_cons, List.map_append, List.map_map,
    List.sum_cons, List.sum_append, List.map_nil, List.sum_nil, add_zero, LinearMap.add_apply,
    ← Fin.sum_univ_def, LinearMap.sum_apply, Function.comp_apply, LinearMap.smul_apply,
    Term.coeff, one_smul, smul_eq_mul, LinearMap.comp_apply,
    LinearMap.proj_apply, DFT.sum_single_mul, neg_one_mul, Finset.sum_neg_distrib]
  rw [map_sub, map_sub, map_sum, ← hw i k]
  simp only [DFT.negacyclicConvCoeff_map]
  have hA : ∀ j : Fin nCols, ⇑embed ∘ MLDSA44.coeff (_root_.MLDSA.Concrete.concreteNTTRingOps.fromHat
      (((aHat pk).get i).get j)) = aData (F := F) pk i j := fun j => rfl
  have hZ : ∀ j : Fin nCols, ⇑embed ∘ MLDSA44.coeff ((Vector.ofFn fun j => MLDSA44.ofCoeff (xz j)).get j) =
      fun k => z W j k := by
    intro j
    funext k
    simp only [Function.comp_apply, Vector.get_ofFn, MLDSA44.coeff_ofCoeff, hz]
  have hC : ⇑embed ∘ MLDSA44.coeff (cPoly W) = fun k => sup W k - 2 * sgn W k := by
    funext k
    simp only [Function.comp_apply, cPoly, MLDSA44.coeff_ofCoeff, map_sub, map_mul, map_ofNat,
      embed_bitCoeff (hsup k), embed_bitCoeff (hsgn k)]
  have hT : (⇑embed ∘ fun k' => (2 ^ _root_.MLDSA.droppedBits : _root_.MLDSA.Coeff) *
      MLDSA44.coeff (pk.t1.get i) k') = fun k' => 2 ^ _root_.MLDSA.droppedBits * t1Data (F := F) pk i k' := by
    funext k'
    simp only [Function.comp_apply, map_mul, map_pow, map_ofNat]
    rfl
  simp only [hA, hZ, hC, hT, DFT.negacyclicConvCoeff_ternary,
    Falcon512.negacyclicConvCoeff_comm (fun k => sup W k),
    Falcon512.negacyclicConvCoeff_comm (fun k => sgn W k)]
  ring

/-- **Converse, for completeness.** If `w′` and `z` are the images of `xw`, `xz`, the crossing
bits are Boolean, and `xw = computeWApprox(Â, c, z, t1)`, every row holds. -/
theorem rows_hold_of_eq {pk : PublicKey} {W : Wit F} {xw : Fin nRows → Fin deg → _root_.MLDSA.Coeff}
    {xz : Fin nCols → Fin deg → _root_.MLDSA.Coeff}
    (hsup : Bits.AllBool (sup W)) (hsgn : Bits.AllBool (sgn W))
    (hw : ∀ i k, embed (xw i k) = wApprox W i k) (hz : ∀ j k, embed (xz j k) = z W j k)
    (heq : (Vector.ofFn fun i => MLDSA44.ofCoeff (xw i)) =
      _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 prims
        (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (aHat pk) (cPoly W)
        (Vector.ofFn fun j => MLDSA44.ofCoeff (xz j)) pk.t1) :
    rowsHold (rows pk) W := by
  intro r
  obtain ⟨⟨i, k⟩, rfl⟩ := finProdFinEquiv.surjective r
  unfold Row.holds
  rw [row_eval hsup hsgn hw hz, ← heq, Vector.get_ofFn, MLDSA44.coeff_ofCoeff, sub_self, map_zero]
  rfl

end GordieHowe.MLDSA44.Native.Rows
