-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Emulated.Rows
public import GordieHowe.Language.RealizedProgram.PrimeField
public import GordieHowe.Foundations.Fields.Goldilocks
public import GordieHowe.Applications.Spec.Rq
public import GordieHowe.Foundations.Fields.GoldilocksRoot512
public import GordieHowe.Language.Library.Cross
public import GordieHowe.Language.Library.Eval
public import GordieHowe.Language.Library.EvalPoint
public import GordieHowe.Language.Realizations.RealizeMac
public import GordieHowe.Language.Realizations.RealizeInteger
public import GordieHowe.Applications.MLDSA44.Ring.Frontend.RandomPoint

@[expose] public section

/-!
# GordieHowe frontend: the signature relation of the ML-DSA-44 ring carriers

The ML-DSA-44 ring carriers (`MLDSA44.Ring.Carrier.ROMParams`, `MLDSA44.Ring.Carrier.QROMParams`;
`carrier_relation` in `lib/gordiehowe/examples/rings/mldsa_ring_carrier.h`) check ML-DSA's
verification equation `w′ = A z − c · 2^d t1` in domain `A` over a Goldilocks extension (of
characteristic `p = 2^64 − 2^32 + 1`). The selected member's key enters as carrier spectra:
`member.a_hat` (value `56`) holds, at coordinate `(4 i + j) · 256 + m`, coordinate `m` of the
scheme-order negacyclic transform at `ψ = psi512` (`GordieHowe.psi512_isPrimitiveRoot`) of `A_ij`'s
coefficients, and `member.t1` (value `57`) at `256 i + m` that of `2^d t1_i`'s. The congruence
`w′_i ≡ Σ_j A_ij ⊛ z_j − 2^d t1_i ⊛ c (mod q)` is committed over the integers: the quotient
`signature.relation.q` (value `65`, `q′ < 2^36`) at the offset `qlo = −134137327`, and the high
halves `signature.Q` (value `66`, `4 × 255`) of the products by `X^256 + 1`. Each row is one
identity over the field, checked at one challenge `r` (`signature.r`, value `67`, challenge `1`):
the source predicates `signature.relation.0 … 3` (predicates `1 … 4`, `rowLhs`),

  `E_i(r) + (r^256 + 1) Q_i(r) + ⟨t̂_i, λ(r)⟩ c(r) − Σ_j ⟨â_ij, λ(r)⟩ z_j(r) = 0`,

`E_i = w′_i − q q′_i − q qlo` (the constant `−q qlo`, value `2`), coefficient vectors read against
the powers `r^t` (`signature.relation.0.public0`, value `533`) and spectra against the weights
`λ(r) = 256⁻¹ · Ntt_{ψ⁻¹}(1, r, …, r^255)` in scheme order (`signature.lambda`, value `535`,
`Ops.eval_inverseNtt`), `c = support − 2 · sign` read off the challenge bits (value `63`).

The rows are the ML-DSA rings' (`GordieHowe/Applications/MLDSA44/Ring/Frontend/RandomPoint.lean`,
`MldsaRandomPoint`) at the carrier's transform data (`ψ = psi512`, characteristic `p`) and the
first vector `E_i` above. This file proves the relation's meaning, generic in the program at the
program facts `MldsaCarrierRelation` (decided per program):

* **The rows at `r`** are the shared layer's (`rowPoly`, `relEvent`, `evalE_rowLhs`,
  `rowPoly_zero`), at the carrier's field facts (`instRandomPointField`) and its first vector
  (`eRow_eq`: `E_i = w′_i − q q′_i − q qlo`).
* **The readings** `wVals`, `zVals`, `cBits` of `w′` (value `64`), `z` (value `61`) and the
  challenge bits, and the extracted `wOf`, `zOf`, `cPoly` (the emulated proof of possession's, at
  the ring's values); the spectra (`SpectraOf pk rd`): the hypothesis that values `56` and `57`
  hold the scheme-order transforms of `Rows.aKeyOf pk` and `Rows.tKeyOf pk`.
* **The integer reading of a row** (`row_int`): where the source program holds and `r` is not in
  the event, a row's polynomial is `0`; split into its negacyclic part and a multiple of
  `X^256 + 1` (`Ops.polyOf_mul_polyOf`, `Ops.polyOf_eq_zero_of_add_mul`), its coefficients
  vanish in the field. At a key whose spectra values `56` and `57` hold, every coefficient is the
  cast of an integer (`Ops.intCast_sum_negCoef`): `w′`, `q′`, `z`, `c` and the keys are small
  integers' casts, and the integer `w′ − q (q′ + qlo) − (Σ_j A_ij ⊛ z_j − t_i ⊛ c)` lies below `p` in
  absolute value, so it is `0` (`sig_dvd`: `q` divides `w′ − (Σ_j A_ij ⊛ z_j − t_i ⊛ c)`).
* **The congruence** (`congruent_carrier`): where the source program holds and `r` is not in the
  event, at a key whose spectra values `56` and `57` hold,
  `Rows.Congruent (Rows.aKeyOf pk) (Rows.tKeyOf pk)` at the readings, and so
  `w′ = computeWApprox(Â, c, z, t1)` (`algebra_carrier`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open RealizedProgram

/-- `q` is prime (`instFactPrimeMlDsaQ`), so the coefficients form a field. -/
def factPrimeModulus : Fact (Nat.Prime _root_.MLDSA.modulus) := instFactPrimeMlDsaQ

attribute [local instance] factPrimeModulus

/-! ## The program facts -/

/-- **The program facts of an ML-DSA ring carrier's signature relation** (decided per program):
the random-point rows' (`MldsaRandomPoint`) at the carrier's numbering (`ids`: `member.a_hat`
`56`, `member.t1` `57`, `z` `61`, the challenge bits `63`, `w′` `64`, the high halves
`signature.Q` `66`, rows `signature.relation.0 … 3` predicates `1 … 4`, `signature.r` challenge
`1`) and transform data (`consts`: `ψ = psi512`, `256⁻¹`, `ψ⁻¹`, `−1`, `−2` modulo `p`), each row's
first vector `E_i = w′_i − q q′_i + (−q qlo)` (`rowE_eq`, at the quotient's shared expressions
`refRQ` and the constant `−q qlo`, value `2`); the challenge bits' type check (`13`); the ranges
`signature.w` (`17`, `w′` below `2^24`), `signature.relation.q` (`18`, `q′` (value `65`) below a
bound `B ≤ 2^36`: `645³` at the ROM parameters, `4096³` at the QROM ones) and `norm.z` (`19`,
`z + 130993` below `261987`), with the offset `norm.z.offset` (value `68`); and the sizes, fields
and kinds of the values read. -/
class MldsaCarrierRelation (program : RealizedProgram) extends MldsaRandomPoint program where
  /-- Row `i`'s quotient `q′`. -/
  refRQ : Fin 4 → ℕ
  /-- The numbering the carrier's readings name. -/
  ids : aHat = 56 ∧ t1 = 57 ∧ z = 61 ∧ c = 63 ∧ w = 64 ∧ q = 66 ∧ rel0 = 1 ∧ rChal = 1
  /-- The transform data: `ψ = psi512`, `256⁻¹`, `ψ⁻¹`, `−1` and `−2` modulo `p`. -/
  consts : psi = psi512 ∧ nInv = 18374686475393433601 ∧ psiInv = 4459017075746761332 ∧
    mOne = 18446744069414584320 ∧ mTwo = 18446744069414584319
  /-- Row `i`'s first vector `w′_i − q q′_i + (−q qlo)` (`18446744069406203904 = −q`). -/
  rowE_eq : ∀ i, rowE i = .add (.add (.ref (refW i))
    (.scale (.const 18446744069406203904) (.ref (refRQ i)))) (.reindex [(0, 0, 256)] (.leaf 2))
  /-- The quotient's shared expressions lie below `nRefs`. -/
  refRQLt : ∀ i, refRQ i < nRefs
  /-- Row `i`'s quotient. -/
  exprRQ : ∀ i : Fin 4, program.expr (refRQ i) = .reindex (rowSlice i) (.leaf 65)
  /-- The constant `−q qlo = 1124126735525359`, of field `0`. -/
  cqConst : program.isConstant 2 = true ∧ program.valueField 2 = 0 ∧
    program.constEntries 2 = [1124126735525359]
  /-- The challenge's Boolean check and the ranges are source predicates. -/
  inSource : ∀ p ∈ [13, 17, 18, 19],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- `challenge.c.boolean` checks the challenge bits. -/
  cBool : (program.predicate 13).body.boolCheck? = some ⟨0, 63⟩
  /-- `signature.w`: `w′` below `2^24`. -/
  wRange : ∃ r, (program.predicate 17).body = .mem 0 [.leaf 64] (.range 16777216) r
  /-- `signature.relation.q`: the quotient below a bound `B ≤ 2^36`. -/
  qRange : ∃ r B, (program.predicate 18).body = .mem 0 [.leaf 65] (.range B) r ∧ B ≤ 68719476736
  /-- `norm.z`: `z + 130993` below `261987`. -/
  zRange : ∃ r, (program.predicate 19).body = .mem 0 [.add (.leaf 61) (.leaf 68)] (.range 261987) r
  /-- `norm.z.offset` is the constant `130993`. -/
  offset : program.isConstant 68 = true ∧ program.valueField 68 = 0 ∧
    program.constEntries 68 = List.replicate 1024 130993
  /-- The sizes of `member.a_hat`, `member.t1`, `z`, the challenge bits, `w′`, the quotient and
  the high halves. -/
  sizes : (program.value 56).size = 4096 ∧ (program.value 57).size = 1024 ∧
    (program.value 61).size = 1024 ∧ (program.value 63).size = 512 ∧
    (program.value 64).size = 1024 ∧ (program.value 65).size = 1024 ∧
    (program.value 66).size = 1020
  /-- The quotient lies in field `0`. -/
  rqField : program.valueField 65 = 0
  /-- `z`, `w′` and the quotient are bound to their digits; the challenge bits are committed. -/
  kinds : (program.value 61).kind.isBound = true ∧ (program.value 64).kind.isBound = true ∧
    (program.value 65).kind.isBound = true ∧ (program.value 63).kind = .priv

section Ids

variable {program : RealizedProgram} [MldsaCarrierRelation program]

theorem aHat_eq : MldsaRandomPoint.aHat program = 56 := (MldsaCarrierRelation.ids (program := program)).1
theorem t1_eq : MldsaRandomPoint.t1 program = 57 := (MldsaCarrierRelation.ids (program := program)).2.1
theorem z_eq : MldsaRandomPoint.z program = 61 := (MldsaCarrierRelation.ids (program := program)).2.2.1
theorem c_eq : MldsaRandomPoint.c program = 63 :=
  (MldsaCarrierRelation.ids (program := program)).2.2.2.1
theorem w_eq : MldsaRandomPoint.w program = 64 :=
  (MldsaCarrierRelation.ids (program := program)).2.2.2.2.1
theorem q_eq : MldsaRandomPoint.q program = 66 :=
  (MldsaCarrierRelation.ids (program := program)).2.2.2.2.2.1
theorem rel0_eq : MldsaRandomPoint.rel0 program = 1 :=
  (MldsaCarrierRelation.ids (program := program)).2.2.2.2.2.2.1
theorem rChal_eq : MldsaRandomPoint.rChal program = 1 :=
  (MldsaCarrierRelation.ids (program := program)).2.2.2.2.2.2.2

/-- **The values the carrier reads are of field `0`**: `z`, the challenge bits, `w′`, the
quotient and the high halves. -/
theorem MldsaCarrierRelation.fields : ∀ v ∈ [61, 63, 64, 65, 66], program.valueField v = 0 := by
  intro v hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl
  · rw [← z_eq (program := program)]; exact MldsaRandomPoint.rowFields _ (by simp)
  · rw [← c_eq (program := program)]; exact MldsaRandomPoint.rowFields _ (by simp)
  · rw [← w_eq (program := program)]; exact MldsaRandomPoint.rowFields _ (by simp)
  · exact MldsaCarrierRelation.rqField
  · rw [← q_eq (program := program)]; exact MldsaRandomPoint.rowFields _ (by simp)

/-- **The challenge `r`** is the carrier's challenge `1`. -/
theorem rOf_eq {I : RealizedProgram.Interp} (e : program.Env I) : rOf e = castElt (e.chal 1 0) := by
  unfold rOf
  rw [rChal_eq]

end Ids

/-! ## The keys as integers -/

/-- **A key polynomial's coefficients as integers**, `0` past the degree. -/
def keyZ (key : Fin 256 → ℕ) (s : ℕ) : ℤ := if hs : s < 256 then (key ⟨s, hs⟩ : ℤ) else 0

/-- **A key polynomial cast into a field**, `0` past the degree. -/
abbrev keyPoly (K : Type*) [Field K] (key : Fin 256 → ℕ) : ℕ → K :=
  Ops.ofFin fun s : Fin 256 => ((key s : ℕ) : K)

/-- A key polynomial is the cast of its integers. -/
theorem keyPoly_eq_intCast (K : Type*) [Field K] (key : Fin 256 → ℕ) (s : ℕ) :
    keyPoly K key s = ((keyZ key s : ℤ) : K) := by
  simp only [keyPoly, Ops.ofFin, keyZ]
  split_ifs <;> simp

/-- **A key's negacyclic coefficients are small**: below `q` in absolute value. -/
theorem abs_negCoef_keyZ_le {key : Fin 256 → ℕ} (hkey : ∀ s, key s < Emulated.Rows.q) (j k : ℕ) :
    |Ops.negCoef 256 (keyZ key) j k| ≤ 8380416 := by
  rcases Ops.negCoef_signed 256 (keyZ key) j k with h | ⟨s, hs, h | h⟩
  · rw [h]; norm_num
  all_goals
    rw [h]
    have hk := hkey ⟨s, hs⟩
    change key ⟨s, hs⟩ < 8380417 at hk
    simp only [keyZ, dif_pos hs, abs_neg, Nat.abs_cast]
    exact_mod_cast Nat.le_of_lt_succ hk

/-- **A sum against a key's negacyclic row** is bounded by `256` times the key's and the operand's
bounds. -/
theorem abs_sum_negCoef_le {key : Fin 256 → ℕ} (hkey : ∀ s, key s < Emulated.Rows.q) {x : ℕ → ℤ}
    {B : ℤ} (hx : ∀ t < 256, |x t| ≤ B) (k : ℕ) :
    |∑ t : Fin 256, Ops.negCoef 256 (keyZ key) k t * x t| ≤ 256 * (8380416 * B) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hB : 0 ≤ B := (abs_nonneg _).trans (hx 0 (by norm_num))
  calc ∑ t : Fin 256, |Ops.negCoef 256 (keyZ key) k t * x t|
      ≤ ∑ _t : Fin 256, 8380416 * B := Finset.sum_le_sum fun t _ => by
        rw [abs_mul]
        exact mul_le_mul (abs_negCoef_keyZ_le hkey k t) (hx t t.isLt) (abs_nonneg _) (by norm_num)
    _ = 256 * (8380416 * B) := by simp

/-! ## The field of domain `A` -/

section Field

variable {I : RealizedProgram.Interp} [RealizedProgram.PrimeCastField (I 0) pGold]

theorem decode_lt0 {c : ℕ} (hc : c < pGold) : (I 0).decode c = (c : (I 0).K) :=
  RealizedProgram.PrimeCastField.decode_lt (p := pGold) c hc

theorem toNat_lt0 {k : ℕ} (hk : k < pGold) : (I 0).toNat (k : (I 0).K) = k :=
  RealizedProgram.PrimeCastField.toNat_natCast (p := pGold) k hk

/-- **The integer reading of a small integer's cast** is the integer. -/
theorem coefInt_small {z : ℤ} (hz : 2 * |z| < pGold) : (I 0).coefInt (z : (I 0).K) = z :=
  FieldInterp.coefInt_intCast (RealizedProgram.PrimeCastField.char_spec (p := pGold))
    (RealizedProgram.PrimeCastField.charP (p := pGold))
    (fun _ hk => toNat_lt0 hk) hz

theorem natCast_gold_sub {k : ℕ} (hk : k ≤ pGold) :
    (((pGold - k : ℕ) : ℕ) : (I 0).K) = -((k : ℕ) : (I 0).K) := by
  rw [Nat.cast_sub hk, CharP.cast_eq_zero, zero_sub]

/-- `p − 1` decodes to `−1`. -/
theorem decode_mOne0 : (I 0).decode 18446744069414584320 = -1 := by
  rw [decode_lt0 (by norm_num [pGold]), show (18446744069414584320 : ℕ) = pGold - 1 by
    norm_num [pGold], natCast_gold_sub (by norm_num [pGold]), Nat.cast_one]

/-- `p − 2` decodes to `−2`. -/
theorem decode_mTwo0 : (I 0).decode 18446744069414584319 = -2 := by
  rw [decode_lt0 (by norm_num [pGold]), show (18446744069414584319 : ℕ) = pGold - 2 by
    norm_num [pGold], natCast_gold_sub (by norm_num [pGold])]
  norm_num

/-- `p − q` decodes to `−q`. -/
theorem decode_mQ0 : (I 0).decode 18446744069406203904 = -((8380417 : ℕ) : (I 0).K) := by
  rw [decode_lt0 (by norm_num [pGold]), show (18446744069406203904 : ℕ) = pGold - 8380417 by
    norm_num [pGold], natCast_gold_sub (by norm_num [pGold])]

/-- `1` decodes to `1`. -/
theorem decode_one0 : (I 0).decode 1 = 1 := by
  rw [decode_lt0 (by norm_num [pGold]), Nat.cast_one]

/-- `0` decodes to `0`. -/
theorem decode_zero0 : (I 0).decode 0 = 0 := by
  rw [decode_lt0 (by norm_num [pGold]), Nat.cast_zero]

/-- `256⁻¹ = 18374686475393433601` in a field of characteristic `p`. -/
theorem decode_nInv0 : (I 0).decode 18374686475393433601 = ((256 : ℕ) : (I 0).K)⁻¹ := by
  rw [decode_lt0 (by norm_num [pGold])]
  exact Ops.natCast_eq_inv_of_mul_mod pGold (by norm_num [pGold])

/-- `ψ⁻¹ = 4459017075746761332` in a field of characteristic `p`. -/
theorem decode_psiInv0 : (I 0).decode 4459017075746761332 = ((I 0).decode psi512)⁻¹ :=
  RealizedProgram.decode_eq_inv_of_mul_mod pGold (decode_lt0 (by norm_num [pGold]))
    (decode_lt0 (by norm_num [pGold])) (by norm_num [pGold])

/-- **`ψ` is a primitive `512`-th root of unity** in domain `A`'s field. -/
theorem psi_isPrimitiveRoot0 : IsPrimitiveRoot ((I 0).decode psi512) (2 * 256) := by
  rw [decode_lt0 (by norm_num [pGold])]
  exact psi512_isPrimitiveRoot

/-- **The polynomial of a key's spectrum is the key**: the inverse transform at `ψ = psi512` of a
vector agreeing below `256` with the scheme-order transform of a key is the key's cast. -/
theorem inverseNtt_spectrum {x : ℕ → (I 0).K} {key : Fin 256 → ℕ}
    (hx : ∀ m < 256, x m = Ops.nttScheme 256 (psi512 : (I 0).K) (keyPoly (I 0).K key) m)
    {s : ℕ} (hs : s < 256) :
    Ops.inverseNtt 256 ((I 0).decode psi512) x s = ((keyZ key s : ℤ) : (I 0).K) := by
  rw [decode_lt0 (by norm_num [pGold]), Ops.inverseNtt_congr hx,
    Ops.inverseNtt_nttScheme (k := 8) (by norm_num) psi512_isPrimitiveRoot natCast_256_ne_zero _ hs,
    keyPoly_eq_intCast]

end Field

/-! ## The readings -/

section Readings

variable {program : RealizedProgram} {I : RealizedProgram.Interp}

/-- **`z`** (value `61`, `4 × 256`), in field `0`. -/
def zVals (rd : program.Valuation I) (j : Fin _root_.MLDSA.mldsa44.l)
    (k : Fin _root_.MLDSA.ringDegree) : (I 0).K :=
  program.evalE rd 0 (.leaf 61) ((j : ℕ) * 256 + k)

/-- **`w′`** (value `64`, `signature.w`, `4 × 256`), in field `0`. -/
def wVals (rd : program.Valuation I) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) : (I 0).K :=
  program.evalE rd 0 (.leaf 64) ((i : ℕ) * 256 + k)

/-- **The challenge bits** (value `63`, `challenge.c`, `256 × 2`: support, sign). -/
def cBits (rd : program.Valuation I) (k : Fin _root_.MLDSA.ringDegree) (s : Fin 2) : (I 0).K :=
  program.evalE rd 0 (.leaf 63) (2 * k + s)

/-- **The extracted `z`**: each coefficient the integer its element is (`FieldInterp.coefInt`),
modulo `q`. -/
def zOf (rd : program.Valuation I) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l :=
  Vector.ofFn fun j => MLDSA44.ofCoeff fun k => ((I 0).coefInt (zVals rd j k) : _root_.MLDSA.Coeff)

/-- **The extracted `w′`**: each coefficient the integer its element is, modulo `q`. -/
def wOf (rd : program.Valuation I) : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.k :=
  Vector.ofFn fun i => MLDSA44.ofCoeff fun k => ((I 0).coefInt (wVals rd i k) : _root_.MLDSA.Coeff)

/-- **The challenge polynomial**: `support − 2 · sign` of the challenge bits. -/
def cPoly (rd : program.Valuation I) : _root_.MLDSA.Rq :=
  MLDSA44.ofCoeff fun k =>
    Native.Rows.bitCoeff (cBits rd k 0) - 2 * Native.Rows.bitCoeff (cBits rd k 1)

/-- **The committed spectra are the transforms of `pk`'s keys**: `member.a_hat` (value `56`) holds,
at `(4 i + j) · 256 + m`, coordinate `m` of the scheme-order transform at `ψ = psi512` of `A_ij`'s
coefficients (`Rows.aKeyOf pk`, below `q`), and `member.t1` (value `57`) at `256 i + m` that of
`2^d t1_i`'s (`Rows.tKeyOf pk`). -/
structure SpectraOf (pk : Native.Rows.PublicKey) (rd : program.Valuation I) : Prop where
  /-- `member.a_hat` holds the transforms of `A`. -/
  a : ∀ (i j : Fin 4), ∀ m < 256, program.evalE rd 0 (.leaf 56) (((i : ℕ) * 4 + j) * 256 + m) =
    Ops.nttScheme 256 (psi512 : (I 0).K) (keyPoly (I 0).K (Emulated.Rows.aKeyOf pk i j)) m
  /-- `member.t1` holds the transforms of `2^d t1`. -/
  t : ∀ i : Fin 4, ∀ m < 256, program.evalE rd 0 (.leaf 57) ((i : ℕ) * 256 + m) =
    Ops.nttScheme 256 (psi512 : (I 0).K) (keyPoly (I 0).K (Emulated.Rows.tKeyOf pk i)) m

/-- **The naturals of `w′`** (its integer reading). -/
def wv (rd : program.Valuation I) (i : Fin 4) (k : Fin 256) : ℕ :=
  (program.intOf rd 64 ((i : ℕ) * 256 + k)).toNat

/-- **The shifted naturals of `z`** (`z + (γ₁ − β − 1)`). -/
def zv (rd : program.Valuation I) (j : Fin 4) (m : Fin 256) : ℕ :=
  (program.intOf rd 61 ((j : ℕ) * 256 + m) + 130993).toNat

/-- **The challenge polynomial's integers**: `support − 2 · sign` of the bits' integer readings. -/
def cInt (rd : program.Valuation I) (m : ℕ) : ℤ :=
  program.intOf rd 63 (2 * m) - 2 * program.intOf rd 63 (2 * m + 1)

end Readings

/-! ## The rows at the challenge -/

set_option linter.unusedSectionVars false

section Rows

variable {program : RealizedProgram} [MldsaCarrierRelation program] {I : RealizedProgram.Interp}
  [RealizedProgram.PrimeCastField (I 0) pGold]

/-- **The rows' field facts** in domain `A`'s field (`MldsaRandomPointField`): the carrier's
transform data (`MldsaCarrierRelation.consts`) decodes to `−1`, `−2`, `256⁻¹`, `ψ⁻¹` modulo `p`
at the primitive `512`-th root `ψ = psi512`. -/
instance instRandomPointField : MldsaRandomPointField program (I 0) where
  decode_one := decode_one0
  decode_zero := decode_zero0
  decode_mOne := by
    rw [(MldsaCarrierRelation.consts (program := program)).2.2.2.1]; exact decode_mOne0
  decode_mTwo := by
    rw [(MldsaCarrierRelation.consts (program := program)).2.2.2.2]; exact decode_mTwo0
  decode_nInv := by
    rw [(MldsaCarrierRelation.consts (program := program)).2.1]; exact decode_nInv0
  decode_psiInv := by
    rw [(MldsaCarrierRelation.consts (program := program)).2.2.1,
      (MldsaCarrierRelation.consts (program := program)).1]
    exact decode_psiInv0
  psi_isPrimitiveRoot := by
    rw [(MldsaCarrierRelation.consts (program := program)).1]; exact psi_isPrimitiveRoot0
  n_ne_zero := natCast_256_ne_zero

variable (e : program.Env I) (i : Fin 4)

/-- Row `i`'s quotient `q′` at `t`. -/
def rqRow (t : ℕ) : (I 0).K := program.evalE (program.reader e) 0 (.leaf 65) ((i : ℕ) * 256 + t)

variable {e i}

/-- **The constant `−q qlo`** reads `1124126735525359` at every coordinate of its broadcast. -/
theorem evalE_cq (e : program.Env I) {t : ℕ} (ht : t < 256) :
    program.evalE (program.reader e) 0 (.reindex [(0, 0, 256)] (.leaf 2)) t =
      ((1124126735525359 : ℕ) : (I 0).K) := by
  obtain ⟨hc, hf, he⟩ := MldsaCarrierRelation.cqConst (program := program)
  rw [evalE_reindex, IndexMap.entry_step_zero ht, evalE_leaf_of_isConstant e hc,
    constRead_of_valueField hf, he]
  exact decode_lt0 (by norm_num [pGold])

omit [RealizedProgram.PrimeCastField (I 0) pGold] in
theorem evalE_refRQ (rd : program.Valuation I) (i : Fin 4) {t : ℕ} (ht : t < 256) :
    program.evalE rd 0 (.ref (MldsaCarrierRelation.refRQ program i)) t =
      program.evalE rd 0 (.leaf 65) ((i : ℕ) * 256 + t) := by
  rw [evalE_ref' rd (MldsaCarrierRelation.refRQLt i), MldsaCarrierRelation.exprRQ i, evalE_reindex,
    rowSlice, IndexMap.entry_step_one ht]

/-- **Row `i`'s first vector** `E_i = w′_i − q q′_i + (−q qlo)` below `256`. -/
theorem eRow_eq (e : program.Env I) (i : Fin 4) {t : ℕ} (ht : t < 256) :
    eRow e i t = wRow e i t - ((8380417 : ℕ) : (I 0).K) * rqRow e i t +
      ((1124126735525359 : ℕ) : (I 0).K) := by
  unfold eRow
  rw [MldsaCarrierRelation.rowE_eq i, evalE_add, evalE_add, evalE_scale_const, decode_mQ0,
    evalE_refW _ i ht, evalE_refRQ _ i ht, evalE_cq e ht]
  unfold wRow rqRow
  ring

end Rows

/-! ## Soundness of the relation -/

section Sound

variable {program : RealizedProgram} [MldsaCarrierRelation program] {I : RealizedProgram.Interp}
  [RealizedProgram.PrimeCastField (I 0) pGold]

/-- **A predicate the relation reads holds** where the source program holds. -/
theorem holds_rel {e : program.Env I} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [13, 17, 18, 19]) : program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (predicate_mem (MldsaCarrierRelation.inSource p hp).1)
    (MldsaCarrierRelation.inSource p hp).2

/-- **A range membership of one record** gives a natural below the bound. -/
theorem natBelow_of_mem {rd : program.Valuation I} {n : ℕ} {r : Expr} {real : InRealization}
    (h : program.HoldsWith rd (.mem 0 [r] (.range n) real)) {i : ℕ} (hi : i < program.exprLen r) :
    ∃ k < n, program.evalE rd 0 r i = k := by
  have hw : ∃ k < n, program.evalE rd (program.domainField 0) r i = k :=
    h i hi r (List.mem_singleton_self r)
  have h0 := MldsaRandomPoint.domainField0 (program := program)
  revert hw
  generalize program.domainField 0 = D at h0 ⊢
  subst h0
  exact id

/-- **The integer reading of a bound value of field `0` whose element is a small integer's cast**
is the integer. -/
theorem intOf_of_boundInt {rd : program.Valuation I} {v i : ℕ}
    (hb : (program.value v).kind.isBound = true) (hf : program.valueField v = 0) {z : ℤ}
    (hz : 2 * |z| < pGold) (hv : program.evalE rd 0 (.leaf v) i = (z : (I 0).K)) :
    program.intOf rd v i = z := by
  obtain ⟨x, hx⟩ : ∃ x, (program.value v).kind = .bound x := by
    revert hb
    cases (program.value v).kind <;> simp [Kind.isBound]
  rw [intOf_of_bound _ hx]
  rw [evalE_leaf] at hv
  revert hv
  generalize rd v i = y
  generalize program.valueField v = a at hf y
  subst hf
  rw [castElt_self]
  intro hv
  rw [hv]
  exact coefInt_small hz

/-- **The integer reading of a committed value of field `0`** is its natural reading. -/
theorem intOf_of_priv (rd : program.Valuation I) {v i : ℕ} (hp : (program.value v).kind = .priv)
    (hf : program.valueField v = 0) :
    program.intOf rd v i = ((I 0).toNat (program.evalE rd 0 (.leaf v) i) : ℤ) := by
  unfold intOf
  rw [hp, evalE_leaf]
  simp only
  revert hf
  generalize rd v i = y
  generalize program.valueField v = a at y
  intro hf
  subst hf
  rw [castElt_self]

/-- **`signature.w` bounds `w′`** below `2^24`. -/
theorem w_range {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ n : ℕ, n < 16777216 ∧ program.evalE (program.reader e) 0 (.leaf 64) i = n := by
  have h := holds_rel hs (p := 17) (by simp)
  obtain ⟨_, hb⟩ := MldsaCarrierRelation.wRange (program := program)
  rw [hb] at h
  obtain ⟨n, hn, hv⟩ := natBelow_of_mem h
    (by rw [exprLen_leaf, (MldsaCarrierRelation.sizes (program := program)).2.2.2.2.1]; exact hi)
  exact ⟨n, hn, hv⟩

/-- **`signature.relation.q` bounds the quotient** below `2^36`. -/
theorem rq_range {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ n : ℕ, n < 68719476736 ∧ program.evalE (program.reader e) 0 (.leaf 65) i = n := by
  have h := holds_rel hs (p := 18) (by simp)
  obtain ⟨_, B, hb, hB⟩ := MldsaCarrierRelation.qRange (program := program)
  rw [hb] at h
  obtain ⟨n, hn, hv⟩ := natBelow_of_mem h
    (by rw [exprLen_leaf, (MldsaCarrierRelation.sizes (program := program)).2.2.2.2.2.1]; exact hi)
  exact ⟨n, lt_of_lt_of_le hn hB, hv⟩

/-- **`norm.z.offset`** reads `130993`. -/
theorem rd_offset (e : program.Env I) {i : ℕ} (hi : i < 1024) :
    program.evalE (program.reader e) 0 (.leaf 68) i = ((130993 : ℕ) : (I 0).K) := by
  obtain ⟨hc, hf, he⟩ := MldsaCarrierRelation.offset (program := program)
  rw [evalE_leaf_of_isConstant e hc, constRead_of_valueField hf, he, List.getD_eq_getElem?_getD,
    List.getElem?_replicate, if_pos hi, Option.getD_some, decode_lt0 (by norm_num [pGold])]

/-- **`norm.z` bounds `z`**: `z` is the cast of an integer in `[−130993, 130993]`. -/
theorem z_range {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ∃ z : ℤ, -130993 ≤ z ∧ z ≤ 130993 ∧ program.evalE (program.reader e) 0 (.leaf 61) i = z := by
  have h := holds_rel hs (p := 19) (by simp)
  obtain ⟨_, hb⟩ := MldsaCarrierRelation.zRange (program := program)
  rw [hb] at h
  obtain ⟨n, hn, hv⟩ := natBelow_of_mem h
    (by rw [exprLen_add, exprLen_leaf, (MldsaCarrierRelation.sizes (program := program)).2.2.1]
        exact hi)
  rw [evalE_add, rd_offset e hi] at hv
  refine ⟨(n : ℤ) - 130993, by omega, by omega, ?_⟩
  push_cast
  rw [← hv]
  push_cast
  ring

/-- **A natural reading of a bound value below `2^62`** is its integer reading's cast. -/
theorem intOf_of_natBelow {rd : program.Valuation I} {v i n : ℕ}
    (hb : (program.value v).kind.isBound = true) (hf : program.valueField v = 0)
    (hn : n < 2 ^ 62) (hv : program.evalE rd 0 (.leaf v) i = n) :
    program.intOf rd v i = n :=
  intOf_of_boundInt hb hf (by
    rw [abs_of_nonneg (by positivity)]
    norm_num [pGold]
    omega) (by rw [hv, Int.cast_natCast])

/-- **`w′`'s integer reading is a natural below `2^24`** and the integer of its element. -/
theorem intOf_w {e : program.Env I} (hs : program.SourceSatAt e) (i : Fin 4) (k : Fin 256) :
    program.intOf (program.reader e) 64 ((i : ℕ) * 256 + k) = wv (program.reader e) i k ∧
      program.intOf (program.reader e) 64 ((i : ℕ) * 256 + k) =
        (I 0).coefInt (wVals (program.reader e) i k) := by
  obtain ⟨n, hn, hv⟩ := w_range hs (show (i : ℕ) * 256 + k < 1024 by omega)
  have hsmall : 2 * |(n : ℤ)| < pGold := by
    rw [abs_of_nonneg (by positivity)]
    norm_num [pGold]
    omega
  have h : program.intOf (program.reader e) 64 ((i : ℕ) * 256 + k) = n :=
    intOf_of_natBelow (MldsaCarrierRelation.kinds (program := program)).2.1
      ((MldsaCarrierRelation.fields (program := program)) 64 (by simp)) (by omega) hv
  refine ⟨by rw [wv, h]; simp, ?_⟩
  unfold wVals
  rw [h, hv, show ((n : ℕ) : (I 0).K) = ((n : ℤ) : (I 0).K) from (Int.cast_natCast n).symm,
    coefInt_small hsmall]

/-- **`z`'s integer reading is its shifted natural less the shift** and the integer of its
element. -/
theorem intOf_z {e : program.Env I} (hs : program.SourceSatAt e) (j : Fin 4) (m : Fin 256) :
    program.intOf (program.reader e) 61 ((j : ℕ) * 256 + m) =
        Emulated.Rows.signedZ (zv (program.reader e)) j m ∧
      program.intOf (program.reader e) 61 ((j : ℕ) * 256 + m) =
        (I 0).coefInt (zVals (program.reader e) j m) := by
  obtain ⟨z, hlo, hhi, hv⟩ := z_range hs (show (j : ℕ) * 256 + m < 1024 by omega)
  have hsmall : 2 * |z| < pGold := by
    have ha : |z| ≤ 130993 := abs_le.mpr ⟨hlo, hhi⟩
    have hp : ((pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [pGold]
    rw [hp]
    linarith
  have h : program.intOf (program.reader e) 61 ((j : ℕ) * 256 + m) = z :=
    intOf_of_boundInt (MldsaCarrierRelation.kinds (program := program)).1
      ((MldsaCarrierRelation.fields (program := program)) 61 (by simp)) hsmall hv
  refine ⟨?_, ?_⟩
  · have hsh : ((mldsa44.normBound - 1 : ℕ) : ℤ) = 130993 := by decide
    simp only [Emulated.Rows.signedZ, Emulated.Rows.shift, zv, h, hsh]
    omega
  · unfold zVals
    rw [h, hv, coefInt_small hsmall]

/-- **The challenge bits are Boolean** where the source program holds. -/
theorem cBit_bool {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) 0 (.leaf 63) i = 0 ∨
      program.evalE (program.reader e) 0 (.leaf 63) i = 1 := by
  have h := bool_of_boolCheck MldsaCarrierRelation.cBool (holds_rel hs (p := 13) (by simp))
    (i := i) (by rw [(MldsaCarrierRelation.sizes (program := program)).2.2.2.1]; exact hi)
  rw [MldsaRandomPoint.domainField0] at h
  exact h

/-- **A challenge bit is its integer reading's cast**, and that reading is `0` or `1`. -/
theorem cBit_intOf {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) 0 (.leaf 63) i =
        ((program.intOf (program.reader e) 63 i : ℤ) : (I 0).K) ∧
      0 ≤ program.intOf (program.reader e) 63 i ∧ program.intOf (program.reader e) 63 i ≤ 1 := by
  rw [intOf_of_priv _ (MldsaCarrierRelation.kinds (program := program)).2.2.2
    ((MldsaCarrierRelation.fields (program := program)) 63 (by simp))]
  rcases cBit_bool hs hi with h | h <;> rw [h]
  · rw [show (0 : (I 0).K) = ((0 : ℕ) : (I 0).K) from Nat.cast_zero.symm,
      toNat_lt0 (by norm_num [pGold])]
    simp
  · rw [show (1 : (I 0).K) = ((1 : ℕ) : (I 0).K) from Nat.cast_one.symm,
      toNat_lt0 (by norm_num [pGold])]
    simp

/-- **Row `i` over the integers**: where the source program holds and `r` is not in the relation's
event, at a key whose spectra values `56` and `57` hold, coefficient `k` of row `i` is the integer
identity `w′ − q q′ + q · 134137327 + Σ_t (t_i)_{k,t} c_t − Σ_j Σ_t (A_ij)_{k,t} z_jt = 0`
(`(·)_{k,t}` the negacyclic coefficient rows, `Ops.negCoef`): its cast vanishes in the field
(`rowPoly_zero`, `Ops.polyOf_mul_polyOf`, `Ops.polyOf_eq_zero_of_add_mul`) and it lies below
`p` in absolute value. -/
theorem row_int {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (relEvent e).BadAt (rOf e)) {pk : Native.Rows.PublicKey}
    (hS : SpectraOf pk (program.reader e)) (i : Fin 4) {k : ℕ} (hk : k < 256) :
    program.intOf (program.reader e) 64 ((i : ℕ) * 256 + k) -
      8380417 * program.intOf (program.reader e) 65 ((i : ℕ) * 256 + k) + 1124126735525359 +
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t *
        cInt (program.reader e) t -
      ∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t) = 0 := by
  have hi4 := i.isLt
  -- the integer readings and their casts
  have hW : ∀ t < 256, wRow e i t = ((program.intOf (program.reader e) 64 ((i : ℕ) * 256 + t) : ℤ) : (I 0).K) ∧
      0 ≤ program.intOf (program.reader e) 64 ((i : ℕ) * 256 + t) ∧
      program.intOf (program.reader e) 64 ((i : ℕ) * 256 + t) < 16777216 := fun t ht => by
    obtain ⟨n, hn, hv⟩ := w_range hs (show (i : ℕ) * 256 + t < 1024 by omega)
    have h := intOf_of_natBelow (MldsaCarrierRelation.kinds (program := program)).2.1
      ((MldsaCarrierRelation.fields (program := program)) 64 (by simp)) (by omega) hv
    refine ⟨?_, by omega, by omega⟩
    unfold wRow
    rw [w_eq, h, hv, Int.cast_natCast]
  have hRQ : ∀ t < 256, rqRow e i t = ((program.intOf (program.reader e) 65 ((i : ℕ) * 256 + t) : ℤ) : (I 0).K) ∧
      0 ≤ program.intOf (program.reader e) 65 ((i : ℕ) * 256 + t) ∧
      program.intOf (program.reader e) 65 ((i : ℕ) * 256 + t) < 68719476736 := fun t ht => by
    obtain ⟨n, hn, hv⟩ := rq_range hs (show (i : ℕ) * 256 + t < 1024 by omega)
    have h := intOf_of_natBelow (MldsaCarrierRelation.kinds (program := program)).2.2.1
      ((MldsaCarrierRelation.fields (program := program)) 65 (by simp)) (by omega) hv
    refine ⟨?_, by omega, by omega⟩
    unfold rqRow
    rw [h, hv, Int.cast_natCast]
  have hZ : ∀ (j : Fin 4), ∀ t < 256,
      zRow e j t = ((program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t) : ℤ) : (I 0).K) ∧
      |program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t)| ≤ 130993 := fun j t ht => by
    have hj4 := j.isLt
    obtain ⟨z, hlo, hhi, hv⟩ := z_range hs (show (j : ℕ) * 256 + t < 1024 by omega)
    have h : program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t) = z :=
      intOf_of_boundInt (MldsaCarrierRelation.kinds (program := program)).1
        ((MldsaCarrierRelation.fields (program := program)) 61 (by simp)) (by
          have ha : |z| ≤ 130993 := abs_le.mpr ⟨hlo, hhi⟩
          have hp : ((pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [pGold]
          rw [hp]
          linarith) hv
    refine ⟨?_, by rw [h]; exact abs_le.mpr ⟨hlo, hhi⟩⟩
    unfold zRow
    rw [z_eq, h, hv]
  have hC : ∀ t < 256, cRow e t = ((cInt (program.reader e) t : ℤ) : (I 0).K) ∧ |cInt (program.reader e) t| ≤ 2 := fun t ht => by
    obtain ⟨h0, a0, b0⟩ := cBit_intOf hs (show 2 * t < 512 by omega)
    obtain ⟨h1, a1, b1⟩ := cBit_intOf hs (show 2 * t + 1 < 512 by omega)
    refine ⟨?_, ?_⟩
    · unfold cRow cInt
      rw [c_eq, h0, h1]
      push_cast
      ring
    · unfold cInt
      rw [abs_le]
      constructor <;> omega
  have hT : ∀ s < 256, Ops.inverseNtt 256 ((I 0).decode psi512) (tRow e i) s =
      ((keyZ (Emulated.Rows.tKeyOf pk i) s : ℤ) : (I 0).K) := fun s hs' =>
    inverseNtt_spectrum (fun m hm => by unfold tRow; rw [t1_eq]; exact hS.t i m hm) hs'
  have hA : ∀ (j : Fin 4), ∀ s < 256, Ops.inverseNtt 256 ((I 0).decode psi512) (aRow e i j) s =
      ((keyZ (Emulated.Rows.aKeyOf pk i j) s : ℤ) : (I 0).K) := fun j s hs' =>
    inverseNtt_spectrum (fun m hm => by
      unfold aRow
      rw [aHat_eq, show (i : ℕ) * 1024 + ((j : ℕ) * 256 + m) = ((i : ℕ) * 4 + j) * 256 + m by ring]
      exact hS.a i j m hm) hs'
  -- the row's polynomial, split
  set EZ : ℕ → ℤ := fun t => program.intOf (program.reader e) 64 ((i : ℕ) * 256 + t) -
    8380417 * program.intOf (program.reader e) 65 ((i : ℕ) * 256 + t) + 1124126735525359 with hEZ
  set TZ : ℕ → ℤ := keyZ (Emulated.Rows.tKeyOf pk i)
  set CZ : ℕ → ℤ := fun t => cInt (program.reader e) t
  set AZ : Fin 4 → ℕ → ℤ := fun j => keyZ (Emulated.Rows.aKeyOf pk i j)
  set ZZ : Fin 4 → ℕ → ℤ := fun j t => program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t)
  have hE : ∀ t < 256, eRow e i t = ((EZ t : ℤ) : (I 0).K) := fun t ht => by
    rw [eRow_eq e i ht, (hW t ht).1, (hRQ t ht).1, hEZ]
    push_cast
    ring
  have hmul : ∀ a b : ℕ → (I 0).K, Ops.polyOf 256 a * Ops.polyOf 256 b =
      Ops.polyOf 256 (Ops.negacyclic 256 a b) +
        (Polynomial.X ^ 256 + 1 : Polynomial (I 0).K) * Ops.polyOf 255 (Ops.high 256 a b) :=
    fun a b => Ops.polyOf_mul_polyOf (n := 256) (by norm_num) a b
  set Tf : ℕ → (I 0).K := fun s => ((TZ s : ℤ) : (I 0).K)
  set Cf : ℕ → (I 0).K := fun s => ((CZ s : ℤ) : (I 0).K)
  set Af : Fin 4 → ℕ → (I 0).K := fun j s => ((AZ j s : ℤ) : (I 0).K)
  set Zf : Fin 4 → ℕ → (I 0).K := fun j s => ((ZZ j s : ℤ) : (I 0).K)
  set L : ℕ → (I 0).K := fun s => ((EZ s : ℤ) : (I 0).K) + Ops.negacyclic 256 Tf Cf s -
    ∑ j : Fin 4, Ops.negacyclic 256 (Af j) (Zf j) s with hLdef
  have hsplit : rowPoly e i = Ops.polyOf 256 L + (Polynomial.X ^ 256 + 1 : Polynomial (I 0).K) *
      (Ops.polyOf 255 (qRow e i) + Ops.polyOf 255 (Ops.high 256 Tf Cf) -
        ∑ j : Fin 4, Ops.polyOf 255 (Ops.high 256 (Af j) (Zf j))) := by
    unfold rowPoly
    rw [(MldsaCarrierRelation.consts (program := program)).1, Ops.polyOf_congr hE,
      Ops.polyOf_congr hT, Ops.polyOf_congr (fun t ht => (hC t ht).1),
      Finset.sum_congr rfl fun j _ => by
        rw [Ops.polyOf_congr (hA j), Ops.polyOf_congr (fun t ht => (hZ j t ht).1)], hmul]
    simp only [hmul]
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hLdef,
      show (fun s => ((EZ s : ℤ) : (I 0).K) + Ops.negacyclic 256 Tf Cf s -
        ∑ j : Fin 4, Ops.negacyclic 256 (Af j) (Zf j) s) =
        (fun s => ((EZ s : ℤ) : (I 0).K)) + Ops.negacyclic 256 Tf Cf -
          (fun s => ∑ j : Fin 4, Ops.negacyclic 256 (Af j) (Zf j) s) from rfl,
      Ops.polyOf_sub, Ops.polyOf_add, Ops.polyOf_sum]
    ring
  have hz := rowPoly_zero hs hev i
  rw [hsplit] at hz
  have hL := Ops.eq_zero_of_polyOf_eq_zero (Ops.polyOf_eq_zero_of_add_mul (by norm_num) hz).1 hk
  -- the coefficient is an integer's cast
  have hcast : L k = ((EZ k + ∑ t : Fin 256, Ops.negCoef 256 TZ k t * CZ t -
      ∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (AZ j) k t * ZZ j t : ℤ) : (I 0).K) := by
    have hN : ∀ h x : ℕ → ℤ,
        Ops.negacyclic 256 (fun s => (h s : (I 0).K)) (fun s => (x s : (I 0).K)) k =
          ((∑ t : Fin 256, Ops.negCoef 256 h k t * x t : ℤ) : (I 0).K) := fun h x => by
      rw [Ops.negacyclic, Ops.ofFin_of_lt _ hk, Ops.intCast_sum_negCoef h x hk]
      rfl
    simp only [hLdef, Tf, Cf, Af, Zf, hN]
    push_cast
    ring
  rw [hcast] at hL
  have hdvd := (CharP.intCast_eq_zero_iff (I 0).K pGold _).1 hL
  -- the integer is below `p`
  have hbT := abs_le.mp (abs_sum_negCoef_le (B := 2) (fun s => KeyNTT.vals_lt _ s)
    (fun t ht => (hC t ht).2) k (key := Emulated.Rows.tKeyOf pk i))
  have hbA := fun j : Fin 4 => abs_le.mp (abs_sum_negCoef_le (B := 130993)
    (Emulated.Rows.aKeyOf_lt pk i j) (fun t ht => (hZ j t ht).2) k)
  obtain ⟨-, w0, w1⟩ := hW k hk
  obtain ⟨-, q0, q1⟩ := hRQ k hk
  have hX := Int.eq_zero_of_abs_lt_dvd hdvd (by
    rw [Fin.sum_univ_four]
    obtain ⟨a0, b0⟩ := hbA 0
    obtain ⟨a1, b1⟩ := hbA 1
    obtain ⟨a2, b2⟩ := hbA 2
    obtain ⟨a3, b3⟩ := hbA 3
    obtain ⟨a4, b4⟩ := hbT
    rw [abs_lt]
    simp only [hEZ, ZZ, AZ, TZ, CZ] at *
    have hp : ((pGold : ℕ) : ℤ) = 18446744069414584321 := by norm_num [pGold]
    rw [hp]
    constructor <;> omega)
  simp only [hEZ, ZZ, AZ, TZ, CZ] at hX
  linarith

/-- **The relation's sides differ by a multiple of `q`** where the source program holds and `r` is
not in the relation's event, at a key whose spectra values `56` and `57` hold (`row_int`: the
difference is `q (q′ + qlo)`). -/
theorem sig_dvd {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (relEvent e).BadAt (rOf e)) {pk : Native.Rows.PublicKey}
    (hS : SpectraOf pk (program.reader e)) (i : Fin 4) {k : ℕ} (hk : k < 256) :
    (8380417 : ℤ) ∣ program.intOf (program.reader e) 64 ((i : ℕ) * 256 + k) -
      (∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t) -
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t *
        cInt (program.reader e) t) := by
  have h := row_int hs hev hS i hk
  exact ⟨program.intOf (program.reader e) 65 ((i : ℕ) * 256 + k) - 134137327, by linarith⟩

/-- **The congruence of an ML-DSA ring carrier** (`Rows.Congruent` at the keys of `pk`):
`w′ ≡ Σ_j A_ij z_j − c t_i (mod q)` with `c = support − 2 · sign` and `t_i = 2^d t1_i`, where the
source program holds and `r` is not in the relation's event, at a key whose transforms the
committed spectra hold. -/
theorem congruent_carrier {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (relEvent e).BadAt (rOf e)) {pk : Native.Rows.PublicKey}
    (hS : SpectraOf pk (program.reader e)) :
    Emulated.Rows.Congruent (Emulated.Rows.aKeyOf pk) (Emulated.Rows.tKeyOf pk)
      (zv (program.reader e)) (wv (program.reader e)) (fun m => cInt (program.reader e) m) :=
  fun i k => by
  have hd := sig_dvd hs hev hS i k.isLt
  have h0 : ((program.intOf (program.reader e) 64 ((i : ℕ) * 256 + k) -
      (∑ j : Fin 4, ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t) -
      ∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t *
        cInt (program.reader e) t) : ℤ) : _root_.MLDSA.Coeff) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hd
  have hA : ∀ j : Fin 4,
      ((∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.aKeyOf pk i j)) k t *
        program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t) : ℤ) : _root_.MLDSA.Coeff) =
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin 256 => ((Emulated.Rows.aKeyOf pk i j m : ℕ) : _root_.MLDSA.Coeff))
        (fun m => ((Emulated.Rows.signedZ (zv (program.reader e)) j m : ℤ) : _root_.MLDSA.Coeff))
        k := by
    intro j
    refine (Ops.intCast_sum_negCoef (keyZ (Emulated.Rows.aKeyOf pk i j))
      (fun t => program.intOf (program.reader e) 61 ((j : ℕ) * 256 + t)) k.isLt).trans ?_
    congr 1
    · funext m
      simp only [keyZ, dif_pos (show (m : ℕ) < 256 from m.isLt), Int.cast_natCast]
      rfl
    · funext m
      rw [(intOf_z hs j m).1]
  have hT : ((∑ t : Fin 256, Ops.negCoef 256 (keyZ (Emulated.Rows.tKeyOf pk i)) k t *
        cInt (program.reader e) t : ℤ) : _root_.MLDSA.Coeff) =
      LatticeCrypto.negacyclicConvCoeff
        (fun m : Fin 256 => ((cInt (program.reader e) m : ℤ) : _root_.MLDSA.Coeff))
        (fun m => ((Emulated.Rows.tKeyOf pk i m : ℕ) : _root_.MLDSA.Coeff)) k := by
    refine (Ops.intCast_sum_negCoef (keyZ (Emulated.Rows.tKeyOf pk i))
      (fun t => cInt (program.reader e) t) k.isLt).trans ?_
    rw [Falcon512.negacyclicConvCoeff_comm]
    congr 1
    funext m
    simp only [keyZ, dif_pos (show (m : ℕ) < 256 from m.isLt), Int.cast_natCast]
    rfl
  have hW : ((program.intOf (program.reader e) 64 ((i : ℕ) * 256 + k) : ℤ) : _root_.MLDSA.Coeff) =
      ((wv (program.reader e) i k : ℕ) : _root_.MLDSA.Coeff) := by
    rw [(intOf_w hs i k).1, Int.cast_natCast]
  rw [Int.cast_sub, Int.cast_sub, Int.cast_sum, hW, hT] at h0
  simp only [hA] at h0
  show ((wv (program.reader e) i k : ℕ) : _root_.MLDSA.Coeff) = _
  exact sub_eq_zero.mp h0

/-- **A Boolean element of field `0` as a coefficient** is its integer reading. -/
theorem bitCoeff_eq_toNat {v : (I 0).K} (hv : v = 0 ∨ v = 1) :
    Native.Rows.bitCoeff v = ((I 0).toNat v : _root_.MLDSA.Coeff) := by
  rcases hv with rfl | rfl
  · rw [show (0 : (I 0).K) = ((0 : ℕ) : (I 0).K) from Nat.cast_zero.symm,
      toNat_lt0 (by norm_num [pGold])]
    unfold Native.Rows.bitCoeff
    simp
  · rw [show (1 : (I 0).K) = ((1 : ℕ) : (I 0).K) from Nat.cast_one.symm,
      toNat_lt0 (by norm_num [pGold])]
    unfold Native.Rows.bitCoeff
    simp

/-- **The challenge polynomial's coefficients** are `support − 2 · sign` of the challenge bits'
integer readings. -/
theorem coeff_cPoly {e : program.Env I} (hs : program.SourceSatAt e) :
    MLDSA44.coeff (cPoly (program.reader e)) = fun k : Fin _root_.MLDSA.ringDegree =>
      ((cInt (program.reader e) k : ℤ) : _root_.MLDSA.Coeff) := by
  funext k
  have hk : (k : ℕ) < 256 := k.isLt
  have hp := (MldsaCarrierRelation.kinds (program := program)).2.2.2
  have hf := (MldsaCarrierRelation.fields (program := program)) 63 (by simp)
  rw [cPoly, MLDSA44.coeff_ofCoeff, cInt, intOf_of_priv _ hp hf, intOf_of_priv _ hp hf]
  have h0 : cBits (program.reader e) k 0 = program.evalE (program.reader e) 0 (.leaf 63) (2 * k) :=
    by simp [cBits]
  have h1 : cBits (program.reader e) k 1 =
      program.evalE (program.reader e) 0 (.leaf 63) (2 * k + 1) := by simp [cBits]
  rw [h0, h1, bitCoeff_eq_toNat (cBit_bool hs (by omega)),
    bitCoeff_eq_toNat (cBit_bool hs (by omega))]
  push_cast
  rfl

/-- **The extracted `z` is the shifted naturals' `z`** (`Rows.zVec`). -/
theorem zOf_eq {e : program.Env I} (hs : program.SourceSatAt e) :
    zOf (program.reader e) = Emulated.Rows.zVec (zv (program.reader e)) := by
  apply Vector.ext
  intro j hj
  unfold zOf Emulated.Rows.zVec
  rw [Vector.getElem_ofFn, Vector.getElem_ofFn]
  refine congrArg MLDSA44.ofCoeff (funext fun m => ?_)
  exact congrArg (Int.cast : ℤ → _root_.MLDSA.Coeff)
    ((intOf_z hs ⟨j, hj⟩ m).2.symm.trans (intOf_z hs ⟨j, hj⟩ m).1)

/-- **`w′ = computeWApprox(Â, c, z, t1)`** for an ML-DSA ring carrier, where the source program
holds and `r` is not in the relation's event, at a key whose transforms the committed spectra hold
(`congruent_carrier`, `Rows.Congruent.computeWApprox`): the emulated proof of possession's
`algebra` at the ring's readings. -/
theorem algebra_carrier {e : program.Env I} (hs : program.SourceSatAt e)
    (hev : ¬ (relEvent e).BadAt (rOf e)) {pk : Native.Rows.PublicKey}
    (hS : SpectraOf pk (program.reader e)) :
    wOf (program.reader e) = _root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44 Native.Rows.prims
      (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps) (Native.Rows.aHat pk)
      (cPoly (program.reader e)) (zOf (program.reader e)) pk.t1 := by
  have hcong := congruent_carrier hs hev hS
  apply Vector.ext
  intro i hi
  have key : (wOf (program.reader e)).get ⟨i, hi⟩ = (_root_.MLDSA.computeWApprox
      _root_.MLDSA.mldsa44 Native.Rows.prims (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps)
      (Native.Rows.aHat pk) (cPoly (program.reader e)) (zOf (program.reader e)) pk.t1).get
        ⟨i, hi⟩ := by
    rw [← MLDSA44.ofCoeff_coeff (Vector.get (_root_.MLDSA.computeWApprox _root_.MLDSA.mldsa44
      Native.Rows.prims (nttOps := _root_.MLDSA.Concrete.concreteNTTRingOps)
      (Native.Rows.aHat pk) (cPoly (program.reader e)) (zOf (program.reader e)) pk.t1)
        ⟨i, hi⟩)]
    unfold wOf
    rw [Vector.get_ofFn]
    refine congrArg MLDSA44.ofCoeff (funext fun k => ?_)
    rw [MLDSA44.coeff_computeWApprox, coeff_cPoly hs, zOf_eq hs]
    have h := congrArg (Int.cast : ℤ → _root_.MLDSA.Coeff)
      ((intOf_w hs ⟨i, hi⟩ k).2.symm.trans (intOf_w hs ⟨i, hi⟩ k).1)
    rw [Int.cast_natCast] at h
    exact h.trans (hcong.computeWApprox ⟨i, hi⟩ k)
  simpa [Vector.get_eq_getElem] using key

end Sound

end GordieHowe.MLDSA44.Ring.Carrier
