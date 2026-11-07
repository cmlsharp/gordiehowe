-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Interp
public import GordieHowe.Applications.MLDSA44.Frontend.QField
public import GordieHowe.Applications.MLDSA44.Frontend.Key
public import GordieHowe.Applications.MLDSA44.Circuits.NativeAlgebra
public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.Library.Cross
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.NTTMul

@[expose] public section

/-!
# GordieHowe frontend: the signature relation of the native ML-DSA-44 ring programs

The native ML-DSA-44 ring programs (`spectral_relation` in
`lib/gordiehowe/examples/rings/mldsa_ring_native.h`) commit the selected member's key part:
`member.a_hat` (`4 × 4 × 256` entries of the prime subfield `GF(p^1)` of domain `A`, the matrix
`Â = ExpandA(ρ)` in FIPS 204's NTT order) and `member.t1` (`4 × 256`, the spectra
`NTT(2^d · t1_i)`). The signature relation is four spectral rows, the source predicates
`signature.relation.0 … 3` (predicates `1 … 4`): for each row `i` and frequency `k < 256`,

  `NTT(w_i)_k − (Σ_j â_ijk · NTT(z_j)_k − t̂_ik · NTT(support − 2 · sign)_k) = 0`

over the program's scheme-order transform `ntt 256 1753 scheme` (FIPS 204's NTT, Algorithm 41,
`GordieHowe.MLDSA44.KeyNTT.ofFin_ntt`), with `z` transformed once (shared expression `32`) and
the challenge's support and sign bits read off `challenge.c` (shared expressions `34`, `35`).

Contents:

* **The program facts** (`MldsaRingRelation`): the value numbering, the four rows' bodies and
  shared expressions (`rowLhs`), the zero constant, the challenge's Boolean check, `norm.z`, the
  prime-typed source values `member.a_hat`, `member.t1`, `signature.w`. Each program decides
  them (`GordieHoweCerts/Applications/MLDSA44/Ring/Native/{ROMParams,QROMParams}/Frontend/RelationFacts.lean`).
* **The readers** (`wVals`, `wOf`, `zVals`, `zOf`, `cBits`, `cPoly`, `aHatVals`, `t1HatVals`):
  the shapes of the proof-of-possession frontend's (`GordieHowe.MLDSA44.wOf`,
  `zOf`, `cPolyA`) at the ring program's values.
* **The algebra in `ZMod q`** (`eq_of_ntt_rows`): a polynomial whose NTT is
  `Σ_j â_j ⊙ NTT(z_j) − t̂ ⊙ NTT(c)` with `t̂ = NTT(T)` is `Σ_j NTT⁻¹(â_j) z_j − c T`.
* **The field rows in `ZMod q`** (`row_coord0`): the constant coordinate of row `i`, an
  `F_q`-linear map, where the committed `â` and `t̂` are casts of naturals.
* **The theorem** (`algebra_eq_of_cast`, `algebra_eq`): wherever the source program holds, at
  every `Â` and `t1` whose entries the committed `â` and `t̂` read (casts of their naturals below
  `q`, or their integer readings), `w = computeWApprox(Â, c, z, t1)` (FIPS 204 Algorithm 8,
  line 9), with `c`, `z`, `w` the program's readings. `algebra_eq` takes the key's `Â`
  (`Native.Rows.aHat pk`) and `t1`.
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.RealizedProgram (Expr IndexMap)

/-! ## The relation rows -/

/-- **Row `i`'s slice** of a `4 × 256` value: coordinates `256 i, …, 256 i + 255`. -/
def rowSlice (i : ℕ) : IndexMap := [(i * 256, 1, 256)]

/-- **Row `i`'s block** of the `4 × 4 × 256` matrix: coordinates `1024 i, …, 1024 i + 1023`. -/
def blockSlice (i : ℕ) : IndexMap := [(i * 1024, 1, 1024)]

/-- **The scheme-order transform of `256` coordinates at `ψ = 1753`** (FIPS 204's NTT). -/
def nttS (E : Expr) : Expr := .apply (.ntt 256 1753 .scheme) E

/-- **Column `j` of row `i`'s product** `â_ij ⊙ NTT(z_j)`, row `i`'s block at the shared
expression `ra`, the transformed `z` at the shared expression `32`. -/
def azTerm (ra j : ℕ) : Expr :=
  .mul (.reindex (rowSlice j) (.reindex (blockSlice 0) (.ref ra)))
    (.reindex (rowSlice j) (.reindex (blockSlice 0) (.ref 32)))

/-- **Row `i`'s challenge term** `t̂_i ⊙ NTT(support − 2 · sign)`, row `i`'s `t̂` at the shared
expression `rt`, the support and sign at the shared expressions `34`, `35` (`8380415 = −2`). -/
def ctTerm (rt : ℕ) : Expr :=
  .mul (.reindex (rowSlice 0) (.reindex (rowSlice 0) (.ref rt)))
    (.reindex (rowSlice 0) (.reindex (rowSlice 0)
      (nttS (.add (.ref 34) (.scale (.const 8380415) (.ref 35))))))

/-- **The left side of row `i`** (`signature.relation.i`): `NTT(w_i) − (Σ_j â_ij ⊙ NTT(z_j) −
t̂_i ⊙ NTT(c))`, `8380416 = −1`, row `i`'s `w`, `â`, `t̂` at the shared expressions `rw`, `ra`,
`rt`. -/
def rowLhs (rw ra rt : ℕ) : Expr :=
  .add (nttS (.ref rw)) (.scale (.const 8380416)
    (.add (.add (.add (.add (azTerm ra 0) (azTerm ra 1)) (azTerm ra 2)) (azTerm ra 3))
      (.scale (.const 8380416) (ctTerm rt))))

/-- The shared expression of row `i`'s `w` (`30, 36, 39, 42`). -/
def refW (i : ℕ) : ℕ := if i = 0 then 30 else 33 + 3 * i

/-- The shared expression of row `i`'s block of `â` (`31, 37, 40, 43`). -/
def refA (i : ℕ) : ℕ := if i = 0 then 31 else 34 + 3 * i

/-- The shared expression of row `i`'s `t̂` (`33, 38, 41, 44`). -/
def refT (i : ℕ) : ℕ := if i = 0 then 33 else 35 + 3 * i

/-- **The program facts of a native ML-DSA-44 ring program's signature relation**: the value
numbering (`member.a_hat`, `member.t1`, `z`, `challenge.c`, `signature.w`, `norm.z.offset`) and
predicate numbering (`challenge.c.boolean`, `norm.z`), the four rows `signature.relation.0 … 3`
(predicates `1 … 4`, `rowLhs` against the zero constant `2`) and their shared expressions, the
Boolean check of the challenge bits, `norm.z`, and the prime-typed source values. Each program
decides them. -/
class MldsaRingRelation (program : RealizedProgram) where
  /-- `member.a_hat`. -/
  aHat : ℕ
  /-- `member.t1`. -/
  t1 : ℕ
  /-- `z`. -/
  z : ℕ
  /-- `challenge.c`. -/
  c : ℕ
  /-- `signature.w`. -/
  w : ℕ
  /-- `norm.z.offset`. -/
  zOff : ℕ
  /-- `challenge.c.boolean`. -/
  cPred : ℕ
  /-- `norm.z`. -/
  normPred : ℕ
  /-- Domain `0` has field `0`. -/
  domainField0 : program.domainField 0 = 0
  /-- Shared expressions refer only to earlier ones. -/
  refsOrdered : program.RefsOrdered
  /-- The program has the shared expressions `0 … 44`. -/
  refsLt : 44 < program.exprs.length
  /-- `signature.relation.i` is row `i`. -/
  rows : ∀ i : Fin 4, ∃ t, (program.predicate ((i : ℕ) + 1)).body =
    .equal 0 (rowLhs (refW i) (refA i) (refT i)) (.leaf 2) t
  /-- Each row has `256` coordinates. -/
  rowLen : ∀ i : Fin 4, program.exprLen (rowLhs (refW i) (refA i) (refT i)) = 256
  /-- Row `i`'s `w`. -/
  exprW : ∀ i : Fin 4, program.expr (refW i) = .reindex (rowSlice i) (.leaf w)
  /-- Row `i`'s block of `â`. -/
  exprA : ∀ i : Fin 4, program.expr (refA i) = .reindex (blockSlice i) (.leaf aHat)
  /-- Row `i`'s `t̂`. -/
  exprT : ∀ i : Fin 4, program.expr (refT i) = .reindex (rowSlice i) (.leaf t1)
  /-- The transformed `z`. -/
  exprZ : program.expr 32 = .apply (.batched 4 (.ntt 256 1753 .scheme)) (.leaf z)
  /-- The challenge's supports. -/
  exprS : program.expr 34 = .reindex [(0, 2, 256)] (.leaf c)
  /-- The challenge's signs. -/
  exprG : program.expr 35 = .reindex [(1, 2, 256)] (.leaf c)
  /-- The zero constant `2` of `256` coordinates, of field `0`. -/
  const2 : program.isConstant 2 = true ∧ program.valueField 2 = 0 ∧
    program.constEntries 2 = List.replicate 256 0
  /-- The rows, the challenge's Boolean check and `norm.z` are source predicates. -/
  inSource : ∀ p ∈ [1, 2, 3, 4, cPred, normPred],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- `challenge.c.boolean` checks the challenge bits. -/
  cBool : (program.predicate cPred).body.boolCheck? = some ⟨0, c⟩
  /-- `norm.z`: `z + 130993` is a natural below `261987`. -/
  norm : ∃ t, (program.predicate normPred).body =
    .mem 0 [.add (.leaf z) (.leaf zOff)] (.range 261987) t
  /-- `norm.z.offset` is the constant `130993` of field `0`. -/
  offConst : program.isConstant zOff = true ∧ program.valueField zOff = 0 ∧
    program.constEntries zOff = List.replicate 1024 130993
  /-- `member.a_hat`, `member.t1` and `signature.w` are prime-typed source values of field `0`. -/
  primeVals : ∀ v ∈ [aHat, t1, w], v < program.values.length ∧ program.IsSourceValue v ∧
    (program.value v).typeSource = .node ∧ (program.value v).type = .sub "GF(p^1)" ∧
    program.valueField v = 0
  /-- The sizes of the values read. -/
  sizes : (program.value aHat).size = 4096 ∧ (program.value t1).size = 1024 ∧
    (program.value w).size = 1024 ∧ (program.value z).size = 1024 ∧
    (program.value c).size = 512

/-! ## Polynomial algebra in `ZMod q` -/

section Algebra

/-- **Coefficient `k` of the NTT** as an additive map (`NTTEval.ntt_get`: the value at
`ζ^(2·brv8(k)+1)`). -/
noncomputable def nttCoeffHom (k : Fin _root_.MLDSA.ringDegree) :
    _root_.MLDSA.Rq →+ _root_.MLDSA.Coeff where
  toFun f := (_root_.MLDSA.Concrete.ntt f).coeffs.get k
  map_zero' := by
    rw [MLDSA44.NTTEval.ntt_get]
    refine Finset.sum_eq_zero fun j _ => ?_
    erw [_root_.MLDSA.Concrete.Rq.get_zero j, zero_mul]
  map_add' f g := by
    rw [MLDSA44.NTTEval.ntt_get, MLDSA44.NTTEval.ntt_get, MLDSA44.NTTEval.ntt_get,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    erw [_root_.MLDSA.Concrete.Rq.get_add f g j, add_mul]

theorem nttCoeffHom_apply (k : Fin _root_.MLDSA.ringDegree) (f : _root_.MLDSA.Rq) :
    nttCoeffHom k f = (_root_.MLDSA.Concrete.ntt f).coeffs.get k := by
  simp only [nttCoeffHom, AddMonoidHom.coe_mk, ZeroHom.coe_mk]

/-- **Two NTT-domain polynomials with the same coefficients are equal.** -/
theorem tq_ext {a b : _root_.MLDSA.Tq}
    (h : ∀ k : Fin _root_.MLDSA.ringDegree, a.coeffs.get k = b.coeffs.get k) : a = b := by
  apply LatticeCrypto.TransformPoly.ext
  apply Vector.ext
  intro k hk
  exact h ⟨k, hk⟩

/-- **A polynomial row from its spectrum**: if the NTT of `W` is
`Σ_j â_j ⊙ NTT(z_j) − NTT(T) ⊙ NTT(c)` coefficientwise, then `W = Σ_j NTT⁻¹(â_j) z_j − c T`. -/
theorem eq_of_ntt_rows {W c T : _root_.MLDSA.Rq} {aRow : Vector _root_.MLDSA.Tq _root_.MLDSA.mldsa44.l}
    {z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l}
    (h : ∀ k : Fin _root_.MLDSA.ringDegree, (_root_.MLDSA.Concrete.ntt W).coeffs.get k =
      ∑ j : Fin _root_.MLDSA.mldsa44.l, (aRow.get j).coeffs.get k *
          (_root_.MLDSA.Concrete.ntt (z.get j)).coeffs.get k -
        (_root_.MLDSA.Concrete.ntt T).coeffs.get k * (_root_.MLDSA.Concrete.ntt c).coeffs.get k) :
    W = ∑ j : Fin _root_.MLDSA.mldsa44.l, _root_.MLDSA.Concrete.invNTT (aRow.get j) * z.get j -
      c * T := by
  generalize hR : ∑ j : Fin _root_.MLDSA.mldsa44.l,
    _root_.MLDSA.Concrete.invNTT (aRow.get j) * z.get j - c * T = R
  have key : _root_.MLDSA.Concrete.ntt W = _root_.MLDSA.Concrete.ntt R := by
    refine tq_ext fun k => ?_
    rw [h k, ← hR, ← nttCoeffHom_apply k (∑ j : Fin _root_.MLDSA.mldsa44.l,
      _root_.MLDSA.Concrete.invNTT (aRow.get j) * z.get j - c * T)]
    erw [map_sub, map_sum]
    simp only [nttCoeffHom_apply, ntt_mul_get, _root_.MLDSA.Concrete.ntt_invNTT]
    ring
  rw [← _root_.MLDSA.Concrete.invNTT_ntt W, key, _root_.MLDSA.Concrete.invNTT_ntt]

/-- **NTT coefficients of a polynomial** read through the program's scheme-order transform at
`ζ` (`KeyNTT.ofFin_ntt`), at any coefficient function agreeing with the polynomial below `256`. -/
theorem nttScheme_eq_ntt (f : _root_.MLDSA.Rq) {x : ℕ → _root_.MLDSA.Coeff}
    (hx : ∀ t (ht : t < 256), x t = f.get ⟨t, ht⟩) (k : Fin _root_.MLDSA.ringDegree) :
    RealizedProgram.Ops.nttScheme 256 _root_.MLDSA.zeta x k =
      (_root_.MLDSA.Concrete.ntt f).coeffs.get k := by
  have h := congrFun (MLDSA44.KeyNTT.ofFin_ntt f) k
  erw [RealizedProgram.Ops.ofFin_of_lt _ k.isLt] at h
  rw [h]
  unfold RealizedProgram.Ops.nttScheme
  split_ifs
  · exact RealizedProgram.NamedOp.nttNatural_congr (fun t ht => by
      rw [RealizedProgram.Ops.ofFin_of_lt _ ht]; exact hx t ht) _
  · rfl

end Algebra

/-! ## The readers -/

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaRingRelation program] {F0 FH : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "vA" => MldsaRingRelation.aHat program

set_option hygiene false in
local notation "vT" => MldsaRingRelation.t1 program

set_option hygiene false in
local notation "vZ" => MldsaRingRelation.z program

set_option hygiene false in
local notation "vC" => MldsaRingRelation.c program

set_option hygiene false in
local notation "vW" => MldsaRingRelation.w program

/-- **`w`** (`signature.w`, `4 × 256` of domain `A`), read in field `0`. -/
def wVals (rd : program.Valuation interp) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) : (interp 0).K :=
  program.evalE rd 0 (.leaf vW) ((i : ℕ) * 256 + k)

/-- **The extracted `w`**: each coefficient lifted below `q` (`NativeAlgebraCircuit.coeffRep`). -/
def wOf (rd : program.Valuation interp) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.k :=
  Vector.ofFn fun i => MLDSA44.ofCoeff fun k => NativeAlgebraCircuit.coeffRep (wVals rd i k)

/-- **`z`** (`4 × 256` of domain `A`), read in field `0`. -/
def zVals (rd : program.Valuation interp) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) : (interp 0).K :=
  program.evalE rd 0 (.leaf vZ) ((j : ℕ) * 256 + k)

/-- **The extracted `z`**: each coefficient lifted below `q`. -/
def zOf (rd : program.Valuation interp) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l :=
  Vector.ofFn fun j => MLDSA44.ofCoeff fun k => NativeAlgebraCircuit.coeffRep (zVals rd j k)

/-- **The challenge bits** (`challenge.c`, `256 × 2` bits of domain `A`: the support of
coefficient `k` at `2 k`, its sign at `2 k + 1`). -/
def cBits (rd : program.Valuation interp) (k : Fin _root_.MLDSA.ringDegree) (s : Fin 2) :
    (interp 0).K :=
  program.evalE rd 0 (.leaf vC) (2 * k + s)

/-- **The challenge polynomial**: `support − 2 · sign` of the challenge bits
(`Native.Rows.bitCoeff`). -/
def cPoly (rd : program.Valuation interp) : _root_.MLDSA.Rq :=
  MLDSA44.ofCoeff fun k =>
    Native.Rows.bitCoeff (cBits rd k 0) - 2 * Native.Rows.bitCoeff (cBits rd k 1)

/-- **The committed `â`** at row `i`, column `j`, frequency `k`: coordinate `(4 i + j) · 256 + k`
of `member.a_hat`, read in field `0`. -/
def aHatVals (rd : program.Valuation interp) (i j : Fin 4) (k : Fin 256) : (interp 0).K :=
  program.evalE rd 0 (.leaf vA) (((i : ℕ) * 4 + j) * 256 + k)

/-- **The committed `t̂`** at row `i`, frequency `k`: coordinate `256 i + k` of `member.t1`, read
in field `0`. -/
def t1HatVals (rd : program.Valuation interp) (i : Fin 4) (k : Fin 256) : (interp 0).K :=
  program.evalE rd 0 (.leaf vT) ((i : ℕ) * 256 + k)

/-- The extracted `w`'s coefficients. -/
theorem coeff_wOf (rd : program.Valuation interp) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) :
    MLDSA44.coeff ((wOf rd).get i) k = NativeAlgebraCircuit.coeffRep (wVals rd i k) := by
  unfold wOf
  erw [Vector.get_ofFn, MLDSA44.coeff_ofCoeff]

/-- The extracted `z`'s coefficients. -/
theorem coeff_zOf (rd : program.Valuation interp) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) :
    MLDSA44.coeff ((zOf rd).get j) k = NativeAlgebraCircuit.coeffRep (zVals rd j k) := by
  unfold zOf
  erw [Vector.get_ofFn, MLDSA44.coeff_ofCoeff]

/-- The challenge polynomial's coefficients. -/
theorem coeff_cPoly (rd : program.Valuation interp) (k : Fin _root_.MLDSA.ringDegree) :
    MLDSA44.coeff (cPoly rd) k =
      Native.Rows.bitCoeff (cBits rd k 0) - 2 * Native.Rows.bitCoeff (cBits rd k 1) := by
  unfold cPoly
  rw [MLDSA44.coeff_ofCoeff]

/-! ## The rows in the field -/

section Field

variable [QField F0]

/-- `q − 1` decodes to `−1`. -/
theorem decode_m1 : (interp 0).decode 8380416 = -1 := by
  rw [show (interp 0).decode 8380416 = ((8380416 : ℕ) : (interp 0).K) from
    QField.decode_lt (F0 := F0) _ (by norm_num), eq_neg_iff_add_eq_zero,
    show ((8380416 : ℕ) : (interp 0).K) + 1 = ((8380417 : ℕ) : (interp 0).K) by push_cast; ring]
  exact CharP.cast_eq_zero _ 8380417

/-- `q − 2` decodes to `−2`. -/
theorem decode_m2 : (interp 0).decode 8380415 = -2 := by
  rw [show (interp 0).decode 8380415 = ((8380415 : ℕ) : (interp 0).K) from
    QField.decode_lt (F0 := F0) _ (by norm_num), eq_neg_iff_add_eq_zero,
    show ((8380415 : ℕ) : (interp 0).K) + 2 = ((8380417 : ℕ) : (interp 0).K) by push_cast; ring]
  exact CharP.cast_eq_zero _ 8380417

/-- `ψ = 1753` decodes to its cast. -/
theorem decode_psi : (interp 0).decode 1753 = ((1753 : ℕ) : (interp 0).K) :=
  QField.decode_lt (F0 := F0) _ (by norm_num)

/-- **The scheme-order transform of `256` coordinates** at coordinate `k < 256`. -/
theorem evalE_nttS (rd : program.Valuation interp) (E : Expr) {k : ℕ} (hk : k < 256) :
    program.evalE rd 0 (nttS E) k =
      RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753) (program.evalE rd 0 E) k := by
  rw [nttS, RealizedProgram.evalE_apply]
  simp only [RealizedProgram.NamedOp.apply, RealizedProgram.NamedOp.block,
    RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, Nat.mod_eq_of_lt hk,
    Nat.div_eq_of_lt hk, zero_mul, zero_add]

/-- **A shared expression of the relation** reads its definition. -/
theorem evalE_ref' (rd : program.Valuation interp) {r : ℕ} (hr : r ≤ 44) :
    program.evalE rd 0 (.ref r) = program.evalE rd 0 (program.expr r) :=
  RealizedProgram.evalE_ref MldsaRingRelation.refsOrdered rd 0
    (by have := MldsaRingRelation.refsLt (program := program); omega)

theorem refW_le (i : Fin 4) : refW i ≤ 44 := by
  have := i.isLt; unfold refW; split_ifs <;> omega

theorem refA_le (i : Fin 4) : refA i ≤ 44 := by
  have := i.isLt; unfold refA; split_ifs <;> omega

theorem refT_le (i : Fin 4) : refT i ≤ 44 := by
  have := i.isLt; unfold refT; split_ifs <;> omega

/-- **Row `i`'s `w`** at coordinate `t < 256`. -/
theorem evalE_refW (rd : program.Valuation interp) (i : Fin 4) {t : ℕ} (ht : t < 256) :
    program.evalE rd 0 (.ref (refW i)) t = program.evalE rd 0 (.leaf vW) ((i : ℕ) * 256 + t) := by
  rw [evalE_ref' rd (refW_le i), MldsaRingRelation.exprW i, RealizedProgram.evalE_reindex, rowSlice,
    RealizedProgram.IndexMap.entry_step_one ht]

/-- **Row `i`'s `t̂`** at coordinate `t < 256`. -/
theorem evalE_refT (rd : program.Valuation interp) (i : Fin 4) {t : ℕ} (ht : t < 256) :
    program.evalE rd 0 (.ref (refT i)) t = program.evalE rd 0 (.leaf vT) ((i : ℕ) * 256 + t) := by
  rw [evalE_ref' rd (refT_le i), MldsaRingRelation.exprT i, RealizedProgram.evalE_reindex, rowSlice,
    RealizedProgram.IndexMap.entry_step_one ht]

/-- **Row `i`'s block of `â`** at coordinate `t < 1024`. -/
theorem evalE_refA (rd : program.Valuation interp) (i : Fin 4) {t : ℕ} (ht : t < 1024) :
    program.evalE rd 0 (.ref (refA i)) t = program.evalE rd 0 (.leaf vA) ((i : ℕ) * 1024 + t) := by
  rw [evalE_ref' rd (refA_le i), MldsaRingRelation.exprA i, RealizedProgram.evalE_reindex,
    blockSlice, RealizedProgram.IndexMap.entry_step_one ht]

/-- **The transformed `z`** at coordinate `256 j + k`: the transform of `z_j` at `k`. -/
theorem evalE_ref32 (rd : program.Valuation interp) {j k : ℕ} (hj : j < 4) (hk : k < 256) :
    program.evalE rd 0 (.ref 32) (j * 256 + k) =
      RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753)
        (fun t => program.evalE rd 0 (.leaf vZ) (j * 256 + t)) k := by
  have hlt : j * 256 + k < 1024 := by omega
  have hdiv : (j * 256 + k) / 256 = j := by omega
  have hmod : (j * 256 + k) % 256 = k := by omega
  rw [evalE_ref' rd (by norm_num), MldsaRingRelation.exprZ, RealizedProgram.evalE_apply]
  simp only [RealizedProgram.NamedOp.apply, RealizedProgram.NamedOp.block,
    RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, Nat.mod_eq_of_lt (show
      j * 256 + k < 4 * 256 by omega), Nat.div_eq_of_lt (show j * 256 + k < 4 * 256 by omega),
    zero_mul, zero_add, if_pos (show j * 256 + k < 4 * 256 by omega), hdiv, hmod]

/-- **The challenge term's operand** at coordinate `t < 256`: `support − 2 · sign`. -/
theorem evalE_chal (rd : program.Valuation interp) {t : ℕ} (ht : t < 256) :
    program.evalE rd 0 (.add (.ref 34) (.scale (.const 8380415) (.ref 35))) t =
      program.evalE rd 0 (.leaf vC) (2 * t) - 2 * program.evalE rd 0 (.leaf vC) (2 * t + 1) := by
  rw [RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, decode_m2,
    evalE_ref' rd (by norm_num), evalE_ref' rd (by norm_num), MldsaRingRelation.exprS,
    MldsaRingRelation.exprG, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_single ht, RealizedProgram.IndexMap.entry_single ht]
  have h1 : (((0 : ℕ) : ℤ) + (2 : ℤ) * (t : ℤ)).toNat = 2 * t := by omega
  have h2 : (((1 : ℕ) : ℤ) + (2 : ℤ) * (t : ℤ)).toNat = 2 * t + 1 := by omega
  rw [h1, h2]
  ring

/-- **Row `i`'s left side** at frequency `k < 256`: `NTT(w_i)_k − (Σ_j â_ijk · NTT(z_j)_k −
t̂_ik · NTT(support − 2 · sign)_k)`. -/
theorem evalE_rowLhs (rd : program.Valuation interp) (i : Fin 4) {k : ℕ} (hk : k < 256) :
    program.evalE rd 0 (rowLhs (refW i) (refA i) (refT i)) k =
      RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753)
          (fun t => program.evalE rd 0 (.leaf vW) ((i : ℕ) * 256 + t)) k -
        ((∑ j : Fin 4, program.evalE rd 0 (.leaf vA) ((i : ℕ) * 1024 + ((j : ℕ) * 256 + k)) *
            RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753)
              (fun t => program.evalE rd 0 (.leaf vZ) ((j : ℕ) * 256 + t)) k) -
          program.evalE rd 0 (.leaf vT) ((i : ℕ) * 256 + k) *
            RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753)
              (fun t => program.evalE rd 0 (.leaf vC) (2 * t) -
                2 * program.evalE rd 0 (.leaf vC) (2 * t + 1)) k) := by
  have hcol : ∀ j : ℕ, j < 4 → program.evalE rd 0 (azTerm (refA i) j) k =
      program.evalE rd 0 (.leaf vA) ((i : ℕ) * 1024 + (j * 256 + k)) *
        RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753)
          (fun t => program.evalE rd 0 (.leaf vZ) (j * 256 + t)) k := fun j hj => by
    have hjk : j * 256 + k < 1024 := by omega
    rw [azTerm, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex,
      RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
      rowSlice, blockSlice, RealizedProgram.IndexMap.entry_step_one hk,
      RealizedProgram.IndexMap.entry_step_one hjk, zero_mul, zero_add, evalE_refA rd i hjk,
      evalE_ref32 rd hj hk]
  rw [rowLhs, RealizedProgram.evalE_add, evalE_nttS rd _ hk, RealizedProgram.evalE_scale_const,
    decode_m1, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_add,
    RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, decode_m1,
    hcol 0 (by norm_num), hcol 1 (by norm_num), hcol 2 (by norm_num), hcol 3 (by norm_num),
    ctTerm, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    rowSlice, RealizedProgram.IndexMap.entry_step_one hk, zero_mul, zero_add,
    RealizedProgram.IndexMap.entry_step_one hk, zero_add, evalE_refT rd i hk, evalE_nttS rd _ hk,
    RealizedProgram.nttScheme_congr (fun t ht => evalE_refW rd i ht),
    RealizedProgram.nttScheme_congr (fun t ht => evalE_chal rd ht), Fin.sum_univ_four]
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  norm_num
  ring

/-- The zero constant `2` reads `0` in field `0`. -/
theorem evalE_leaf2 (e : program.Env interp) {k : ℕ} (hk : k < 256) :
    program.evalE (program.reader e) 0 (.leaf 2) k = 0 := by
  obtain ⟨c2, f2, e2⟩ := MldsaRingRelation.const2 (program := program)
  rw [RealizedProgram.evalE_leaf_of_isConstant e c2, RealizedProgram.constRead_of_valueField f2, e2,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hk, Option.getD_some]
  erw [QField.decode_lt (F0 := F0) _ (by norm_num)]
  rw [Nat.cast_zero]

/-- **Row `i` in the field** (`signature.relation.i`, wherever it holds): at frequency `k < 256`,
`NTT(w_i)_k = Σ_j â_ijk · NTT(z_j)_k − t̂_ik · NTT(support − 2 · sign)_k`. -/
theorem row_field {e : program.Env interp} (i : Fin 4)
    (h : program.HoldsAt e (program.predicate ((i : ℕ) + 1)).body) {k : ℕ} (hk : k < 256) :
    RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753)
        (fun t => program.evalE (program.reader e) 0 (.leaf vW) ((i : ℕ) * 256 + t)) k =
      (∑ j : Fin 4, program.evalE (program.reader e) 0 (.leaf vA) ((i : ℕ) * 1024 + ((j : ℕ) * 256 + k)) *
          RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753)
            (fun t => program.evalE (program.reader e) 0 (.leaf vZ) ((j : ℕ) * 256 + t)) k) -
        program.evalE (program.reader e) 0 (.leaf vT) ((i : ℕ) * 256 + k) *
          RealizedProgram.Ops.nttScheme 256 ((interp 0).decode 1753)
            (fun t => program.evalE (program.reader e) 0 (.leaf vC) (2 * t) -
              2 * program.evalE (program.reader e) 0 (.leaf vC) (2 * t + 1)) k := by
  obtain ⟨t, hb⟩ := MldsaRingRelation.rows (program := program) i
  rw [hb] at h
  have hx := h k (by rw [MldsaRingRelation.rowLen i]; exact hk)
  unfold RealizedProgram.evalWith at hx
  rw [MldsaRingRelation.domainField0 (program := program)] at hx
  rw [evalE_leaf2 e hk, evalE_rowLhs _ i hk] at hx
  exact sub_eq_zero.1 hx

/-! ## The constant coordinate -/

instance instFactPrime_ringRel : Fact (Nat.Prime 8380417) := instFactPrimeMlDsaQ

instance charP_ringRel : CharP (interp 0).K _root_.MLDSA.modulus := QField.charP

set_option hygiene false in
/-- **The constant coordinate of domain `A`'s field** as an additive map to `F_q`. -/
local notation "coord0" => (QField.coord0 (F0 := F0))

set_option hygiene false in
/-- **The prime field `F_q` in domain `A`'s field.** -/
local notation "φq" => (ZMod.castHom (dvd_refl _root_.MLDSA.modulus) (interp 0).K :
  _root_.MLDSA.Coeff →+* (interp 0).K)

theorem φq_apply (z : _root_.MLDSA.Coeff) : φq z = ((z.val : ℕ) : (interp 0).K) := by
  change (ZMod.cast z : (interp 0).K) = _
  rw [ZMod.cast_eq_val]

/-- **The constant coordinate is `F_q`-linear.** -/
theorem coord0_mul_φq (y : (interp 0).K) (z : _root_.MLDSA.Coeff) :
    coord0 (y * φq z) = coord0 y * z := by
  rw [mul_comm, φq_apply, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]

/-- The constant coordinate of an integer's cast. -/
theorem coord0_intCast (n : ℤ) : coord0 (n : (interp 0).K) = n := by
  rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
  · rw [Int.cast_natCast, Int.cast_natCast, QField.coord0_natCast]
  · rw [Int.cast_neg, Int.cast_natCast, map_neg, QField.coord0_natCast, Int.cast_neg,
      Int.cast_natCast]

/-- **The transform commutes with the constant coordinate** at `ψ = 1753`. -/
theorem coord0_nttScheme (x : ℕ → (interp 0).K) (m : ℕ) :
    coord0 (RealizedProgram.Ops.nttScheme 256 ((1753 : ℕ) : (interp 0).K) x m) =
      RealizedProgram.Ops.nttScheme 256 _root_.MLDSA.zeta (fun t => coord0 (x t)) m := by
  by_cases hm : m < 256
  · rw [RealizedProgram.Ops.nttScheme_apply (k := 8) (by norm_num) _ _ hm,
      RealizedProgram.Ops.nttScheme_apply (k := 8) (by norm_num) _ _ hm, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hψ : ((1753 : ℕ) : (interp 0).K) = φq _root_.MLDSA.zeta := by
      rw [show _root_.MLDSA.zeta = ((1753 : ℕ) : _root_.MLDSA.Coeff) from rfl, map_natCast]
    rw [hψ, ← map_pow, coord0_mul_φq]
  · unfold RealizedProgram.Ops.nttScheme
    rw [if_neg hm, if_neg hm, map_zero]

/-- **A cast of a natural is `φq` of its cast.** -/
theorem natCast_eq_φq (n : ℕ) : ((n : ℕ) : (interp 0).K) = φq (n : _root_.MLDSA.Coeff) :=
  (map_natCast φq n).symm

/-- **Row `i` in `ZMod q`**: the constant coordinate of `row_field`, where the committed `â` and
`t̂` of row `i` are the casts of `a i j k` and `tHat i k`. -/
theorem row_coord0 {e : program.Env interp} (i : Fin 4)
    (h : program.HoldsAt e (program.predicate ((i : ℕ) + 1)).body)
    {a : Fin 4 → Fin 4 → Fin 256 → ℕ} {tHat : Fin 4 → Fin 256 → ℕ}
    (hA : ∀ j k, aHatVals (program.reader e) i j k = ((a i j k : ℕ) : (interp 0).K))
    (hT : ∀ k, t1HatVals (program.reader e) i k = ((tHat i k : ℕ) : (interp 0).K))
    (k : Fin 256) :
    RealizedProgram.Ops.nttScheme 256 _root_.MLDSA.zeta
        (fun t => coord0 (program.evalE (program.reader e) 0 (.leaf vW) ((i : ℕ) * 256 + t))) k =
      (∑ j : Fin 4, ((a i j k : ℕ) : _root_.MLDSA.Coeff) *
          RealizedProgram.Ops.nttScheme 256 _root_.MLDSA.zeta
            (fun t => coord0 (program.evalE (program.reader e) 0 (.leaf vZ) ((j : ℕ) * 256 + t))) k) -
        ((tHat i k : ℕ) : _root_.MLDSA.Coeff) *
          RealizedProgram.Ops.nttScheme 256 _root_.MLDSA.zeta
            (fun t => coord0 (program.evalE (program.reader e) 0 (.leaf vC) (2 * t)) -
              2 * coord0 (program.evalE (program.reader e) 0 (.leaf vC) (2 * t + 1))) k := by
  have hr := row_field i h k.isLt
  rw [decode_psi] at hr
  have hA' : ∀ j : Fin 4, program.evalE (program.reader e) 0 (.leaf vA)
      ((i : ℕ) * 1024 + ((j : ℕ) * 256 + k)) = φq ((a i j k : ℕ) : _root_.MLDSA.Coeff) := fun j => by
    have hidx : ((i : ℕ) * 4 + j) * 256 + k = (i : ℕ) * 1024 + ((j : ℕ) * 256 + k) := by ring
    rw [← natCast_eq_φq, ← hA j k, aHatVals, hidx]
  have hT' : program.evalE (program.reader e) 0 (.leaf vT) ((i : ℕ) * 256 + k) =
      φq ((tHat i k : ℕ) : _root_.MLDSA.Coeff) := by
    rw [← natCast_eq_φq, ← hT k, t1HatVals]
  rw [Finset.sum_congr rfl fun j _ => by rw [hA' j], hT'] at hr
  have hc := congrArg coord0 hr
  rw [coord0_nttScheme, map_sub, map_sum, mul_comm (φq _), coord0_mul_φq, coord0_nttScheme] at hc
  rw [hc]
  have hC : (fun t => coord0 (program.evalE (program.reader e) 0 (.leaf vC) (2 * t) -
      2 * program.evalE (program.reader e) 0 (.leaf vC) (2 * t + 1))) =
      fun t => coord0 (program.evalE (program.reader e) 0 (.leaf vC) (2 * t)) -
          2 * coord0 (program.evalE (program.reader e) 0 (.leaf vC) (2 * t + 1)) := by
    have h2 : ∀ x y : (interp 0).K, coord0 (x - 2 * y) = coord0 x - 2 * coord0 y := by
      intro x y
      rw [map_sub, two_mul y, map_add, two_mul]
    exact funext fun t => h2 _ _
  rw [hC, mul_comm _ ((tHat i k : ℕ) : _root_.MLDSA.Coeff)]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (φq _), coord0_mul_φq, coord0_nttScheme, mul_comm]


/-! ## The source program's readings -/

/-- **A row holds** where the source program holds (`signature.relation.i`). -/
theorem holds_row {e : program.Env interp} (hs : program.SourceSatAt e) (i : Fin 4) :
    program.HoldsAt e (program.predicate ((i : ℕ) + 1)).body := by
  have hp : (i : ℕ) + 1 ∈ [1, 2, 3, 4, MldsaRingRelation.cPred program,
      MldsaRingRelation.normPred program] := by
    have := i.isLt
    interval_cases (i : ℕ) <;> simp
  obtain ⟨hlt, hsrc⟩ := MldsaRingRelation.inSource _ hp
  exact hs.preds _ (RealizedProgram.predicate_mem hlt) hsrc

/-- **A source predicate of the relation holds** where the source program holds. -/
theorem holds_of_mem {e : program.Env interp} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [1, 2, 3, 4, MldsaRingRelation.cPred program, MldsaRingRelation.normPred program]) :
    program.HoldsAt e (program.predicate p).body := by
  obtain ⟨hlt, hsrc⟩ := MldsaRingRelation.inSource _ hp
  exact hs.preds _ (RealizedProgram.predicate_mem hlt) hsrc

/-- **A node element read in an equal field identifier** stays in the node. -/
theorem castElt_mem_node {I : RealizedProgram.Interp} {a b : ℕ} (h : a = b) {s : String}
    {x : (I a).K} (hx : x ∈ (I a).node s) : (RealizedProgram.castElt x : (I b).K) ∈ (I b).node s := by
  subst h
  rwa [RealizedProgram.castElt_self]

/-- **A prime-typed source value is in the prime subfield** where the source program holds
(`member.a_hat`, `member.t1`, `signature.w`). -/
theorem prime_of_mem {e : program.Env interp} (hs : program.SourceSatAt e) {v : ℕ}
    (hv : v ∈ [vA, vT, vW]) {i : ℕ} (hi : i < (program.value v).size) :
    program.evalE (program.reader e) 0 (.leaf v) i ∈ (interp 0).node "GF(p^1)" := by
  obtain ⟨hvl, hsrc, hts, hty, hf⟩ := MldsaRingRelation.primeVals v hv
  have hmem := hs.types v hvl hsrc hts i hi
  rw [hty] at hmem
  exact castElt_mem_node hf hmem

/-- **A prime-typed reading is the cast of its integer reading.** -/
theorem natCast_toNat_of_mem {e : program.Env interp} (hs : program.SourceSatAt e) {v : ℕ}
    (hv : v ∈ [vA, vT, vW]) {i : ℕ} (hi : i < (program.value v).size) :
    (((interp 0).toNat (program.evalE (program.reader e) 0 (.leaf v) i) : ℕ) : (interp 0).K) =
      program.evalE (program.reader e) 0 (.leaf v) i :=
  QField.natCast_toNat _ (prime_of_mem hs hv hi)

/-- **`w` is the cast of an integer** at every coordinate (`signature.w` is prime-typed). -/
theorem w_int {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    ∃ n : ℤ, (n : (interp 0).K) = program.evalE (program.reader e) 0 (.leaf vW) m :=
  ⟨_, by
    rw [Int.cast_natCast]
    exact natCast_toNat_of_mem hs (v := vW) (by simp)
      (by rw [(MldsaRingRelation.sizes (program := program)).2.2.1]; exact hm)⟩

/-- **`z` is the cast of an integer** at every coordinate: `norm.z` puts `z + 130993` below
`261987`. -/
theorem z_int {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 1024) :
    ∃ n : ℤ, (n : (interp 0).K) = program.evalE (program.reader e) 0 (.leaf vZ) m := by
  obtain ⟨t, hb⟩ := MldsaRingRelation.norm (program := program)
  have h := holds_of_mem hs (p := MldsaRingRelation.normPred program) (by simp)
  rw [hb] at h
  have hlen : m < program.exprLen (.add (.leaf vZ) (.leaf (MldsaRingRelation.zOff program))) := by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf,
      (MldsaRingRelation.sizes (program := program)).2.2.2.1]
    exact hm
  obtain ⟨k, -, hk⟩ : ∃ k : ℕ, k < 261987 ∧ program.evalWith (program.reader e) 0
      (.add (.leaf vZ) (.leaf (MldsaRingRelation.zOff program))) m = k :=
    h m hlen _ (List.mem_singleton_self _)
  unfold RealizedProgram.evalWith at hk
  rw [MldsaRingRelation.domainField0 (program := program), RealizedProgram.evalE_add] at hk
  obtain ⟨c0, f0, e0⟩ := MldsaRingRelation.offConst (program := program)
  rw [RealizedProgram.evalE_leaf_of_isConstant e c0, RealizedProgram.constRead_of_valueField f0, e0,
    List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hm, Option.getD_some] at hk
  erw [QField.decode_lt (F0 := F0) _ (by norm_num)] at hk
  refine ⟨(k : ℤ) - 130993, ?_⟩
  push_cast
  rw [← hk]
  ring

/-- **The challenge bits are bits** (`challenge.c.boolean`). -/
theorem c_bool {e : program.Env interp} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 512) :
    program.evalE (program.reader e) 0 (.leaf vC) m = 0 ∨
      program.evalE (program.reader e) 0 (.leaf vC) m = 1 := by
  have h := RealizedProgram.bool_of_boolCheck MldsaRingRelation.cBool
    (holds_of_mem hs (p := MldsaRingRelation.cPred program) (by simp))
    (i := m) (by rw [(MldsaRingRelation.sizes (program := program)).2.2.2.2]; exact hm)
  rwa [MldsaRingRelation.domainField0 (program := program)] at h

/-- **The constant coordinate of a bit** is its coefficient. -/
theorem coord0_bool {x : (interp 0).K} (hx : x = 0 ∨ x = 1) :
    coord0 x = Native.Rows.bitCoeff x := by
  unfold Native.Rows.bitCoeff
  rcases hx with rfl | rfl
  · rw [map_zero, if_neg zero_ne_one]
  · rw [if_pos rfl, show (1 : (interp 0).K) = ((1 : ℕ) : (interp 0).K) from Nat.cast_one.symm,
      QField.coord0_natCast, Nat.cast_one]

/-- **The constant coordinate of an integer's cast** is its lift below `q`. -/
theorem coord0_eq_coeffRep {x : (interp 0).K} (hx : ∃ n : ℤ, (n : (interp 0).K) = x) :
    coord0 x = NativeAlgebraCircuit.coeffRep x := by
  obtain ⟨n, rfl⟩ := hx
  rw [coord0_intCast, NativeAlgebraCircuit.coeffRep_eq_intCast rfl]

/-! ## The theorem -/

/-- **`w = computeWApprox(Â, c, z, t1)`** wherever the source program holds, at every `Â` and
`t1` whose entries the committed values read: `member.a_hat` holds the casts of the naturals
below `q` of `Â`'s spectra, `member.t1` those of `NTT(2^d · t1_i)` (FIPS 204 Algorithm 8,
line 9, with the program's challenge polynomial, `z` and `w`). -/
theorem algebra_eq_of_cast {e : program.Env interp} (hs : program.SourceSatAt e)
    {aHat : _root_.MLDSA.TqMatrix _root_.MLDSA.mldsa44.k _root_.MLDSA.mldsa44.l}
    {t1 : Vector Native.Rows.prims.Power2High _root_.MLDSA.mldsa44.k}
    (hA : ∀ i j k, aHatVals (program.reader e) i j k =
      ((((aHat.get i).get j).coeffs.get k).val : (interp 0).K))
    (hT : ∀ i k, t1HatVals (program.reader e) i k =
      (((_root_.MLDSA.Concrete.ntt (Native.Rows.prims.power2RoundShift (t1.get i))).coeffs.get k).val :
        (interp 0).K)) :
    wOf (program.reader e) = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) aHat (cPoly (program.reader e))
      (zOf (program.reader e)) t1 := by
  have key : ∀ i : Fin _root_.MLDSA.mldsa44.k, (wOf (program.reader e)).get i =
      (_root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
        (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) aHat (cPoly (program.reader e))
        (zOf (program.reader e)) t1).get i := fun i => by
    rw [MLDSA44.computeWApprox_get]
    simp only [fromHat_eq]
    refine eq_of_ntt_rows fun k => ?_
    have hr := row_coord0 (a := fun i j k => (((aHat.get i).get j).coeffs.get k).val)
      (tHat := fun i k => ((_root_.MLDSA.Concrete.ntt
        (Native.Rows.prims.power2RoundShift (t1.get i))).coeffs.get k).val)
      i (holds_row hs i) (hA i) (hT i) k
    simp only [ZMod.natCast_zmod_val] at hr
    have hW : RealizedProgram.Ops.nttScheme 256 _root_.MLDSA.zeta (fun t => coord0
        (program.evalE (program.reader e) 0 (.leaf vW) ((i : ℕ) * 256 + t))) k =
        (_root_.MLDSA.Concrete.ntt ((wOf (program.reader e)).get i)).coeffs.get k := by
      refine nttScheme_eq_ntt _ (fun t ht => ?_) k
      have hi4 : (i : ℕ) < 4 := i.isLt
      rw [coord0_eq_coeffRep (w_int hs (by omega)), ← MLDSA44.coeff_apply, coeff_wOf]
      rfl
    have hZ : ∀ j : Fin 4, RealizedProgram.Ops.nttScheme 256 _root_.MLDSA.zeta (fun t => coord0
        (program.evalE (program.reader e) 0 (.leaf vZ) ((j : ℕ) * 256 + t))) k =
        (_root_.MLDSA.Concrete.ntt ((zOf (program.reader e)).get j)).coeffs.get k := fun j => by
      refine nttScheme_eq_ntt _ (fun t ht => ?_) k
      have hj4 : (j : ℕ) < 4 := j.isLt
      rw [coord0_eq_coeffRep (z_int hs (by omega)), ← MLDSA44.coeff_apply]
      exact (coeff_zOf (program.reader e) j ⟨t, ht⟩).symm
    have hC : RealizedProgram.Ops.nttScheme 256 _root_.MLDSA.zeta (fun t =>
        coord0 (program.evalE (program.reader e) 0 (.leaf vC) (2 * t)) -
          2 * coord0 (program.evalE (program.reader e) 0 (.leaf vC) (2 * t + 1))) k =
        (_root_.MLDSA.Concrete.ntt (cPoly (program.reader e))).coeffs.get k := by
      refine nttScheme_eq_ntt _ (fun t ht => ?_) k
      rw [coord0_bool (c_bool hs (by omega)), coord0_bool (c_bool hs (by omega))]
      rw [← MLDSA44.coeff_apply, coeff_cPoly]
      rfl
    rw [hW, hC] at hr
    simp only [hZ] at hr
    rw [hr]
    congr 1
  apply Vector.ext
  intro i hi
  simpa [Vector.get_eq_getElem] using key ⟨i, hi⟩

/-- **`w = computeWApprox(Â, c, z, t1)` at a key** wherever the source program holds, at every
public key whose `Â = ExpandA(ρ)` (`Native.Rows.aHat`, FIPS 204's NTT order) and
`NTT(2^d · t1_i)` the committed `member.a_hat` and `member.t1` hold, read as naturals
(`FieldInterp.toNat`, the integer reading; both values are prime-typed, so a reading is the cast
of its integer reading). -/
theorem algebra_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    {pk : Native.Rows.PublicKey}
    (hA : ∀ i j k, (interp 0).toNat (aHatVals (program.reader e) i j k) =
      ((((Native.Rows.aHat pk).get i).get j).coeffs.get k).val)
    (hT : ∀ i k, (interp 0).toNat (t1HatVals (program.reader e) i k) =
      ((_root_.MLDSA.Concrete.ntt (Native.Rows.prims.power2RoundShift (pk.t1.get i))).coeffs.get k).val) :
    wOf (program.reader e) = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk)
      (cPoly (program.reader e)) (zOf (program.reader e)) pk.t1 := by
  refine algebra_eq_of_cast hs (fun i j k => ?_) (fun i k => ?_)
  · rw [← hA i j k]
    exact (natCast_toNat_of_mem hs (v := vA) (by simp) (by
      rw [(MldsaRingRelation.sizes (program := program)).1]
      have := i.isLt; have := j.isLt; have := k.isLt; omega)).symm
  · rw [← hT i k]
    exact (natCast_toNat_of_mem hs (v := vT) (by simp) (by
      rw [(MldsaRingRelation.sizes (program := program)).2.1]
      have := i.isLt; have := k.isLt; omega)).symm

end Field

end GordieHowe.MLDSA44.Ring.Native
