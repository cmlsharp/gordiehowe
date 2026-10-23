-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Basic
public import GordieHowe.Generated.Falcon512.Native.ROMParams.Program
public import GordieHowe.Applications.Falcon512.Frontend.Key
public import GordieHowe.Language.Realizations.RealizeGrouped

@[expose] public section

/-!
# GordieHowe frontend: native Falcon, the algebra of domain `A`

Domain `A`'s obligation of the frontend (`GordieHowe.Falcon512.Native.ROMParams.AlgebraSound`) for a native Falcon
program, generic in the program and its fields at the program facts `FalconAAlg` (decided per
program) and domain `A`'s field facts (`GordieHowe.Falcon512.AField`): wherever the source program holds, the
hand-built native algebra (`GordieHowe.Falcon512.Native.AlgebraConstraints`, `GordieHowe.Falcon512.Native.AlgRequests`) holds at
the decoded key with the program's `c_A` and `s2`, at advice whose `s1` is the program's
`signature.s1`:

* **the norm and the encoding** (`NormSound`): the native norm's constraints, the encoding's
  Boolean checks and the requests at advice read off the program; each program discharges it with
  the generic norm (`FalconNorm`, `GordieHowe/Applications/Falcon512/Frontend/Norm.lean`, at domain `A`);
* **the signature rows** (`signatureRows`), from `signature.equation`'s constant coordinates, and
  the sample bits' Booleanity (`cA_bool`).
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program hiding program
open GordieHowe.Bits
open Emulated (PublicKey)

/-! ## The program facts of domain `A` -/

/-- **The program facts domain `A` reads beyond the norm** (each program instantiates them by
`decide` and `rfl`): `c_A` (`545`) and `s2` (`546`), the field-form signature equation (`pSig`) with
its body and operators, the values `s2` and `signature.s1` (`547`) prime-typed private source values
of field `1`, `c_A` of field `1`, no value bound to an expression, `statement.hhat` opaque. -/
class FalconAAlg (program : RealizedProgram) [FalconACore program] where
  /-- `crossing.c_A` is value `545`. -/
  cA_eq : FalconACore.cA program = 545
  /-- `s2` is value `546`. -/
  s2_eq : FalconACore.s2 program = 546
  /-- The field-form `signature.equation`. -/
  pSig : ℕ
  /-- The signature equation is a source predicate. -/
  inSource_sig : pSig < program.predicates.length ∧ program.inSource (program.predicate pSig) = true
  /-- The field-form `signature.equation`. -/
  sig : ∃ real, (program.predicate pSig).body = .mod 1 12289
    (.add (.leaf 547) (.apply (.negacyclicConv 544 (.ntt 10302)) (.leaf 546)))
    (.apply (.batched 512 (.fromDigits 16 2)) (.leaf 545)) real
  /-- `s2` and `signature.s1` have `512` coordinates. -/
  sizes_sig : (program.value 546).size = 512 ∧ (program.value 547).size = 512
  /-- `s2` and `signature.s1` are prime-typed private source values. -/
  primeA_sig : ∀ v ∈ [546, 547], v < program.values.length ∧
    program.IsSourceValue v ∧ (program.value v).typeSource = .node ∧
    (program.value v).type = .sub "GF(p^1)" ∧ program.valueField v = 1 ∧
    program.isConstant v = false
  /-- `c_A` is a non-constant value of field `1`. -/
  fields_cA : program.valueField 545 = 1 ∧ program.isConstant 545 = false
  /-- The program binds no value to an expression. -/
  noBound : ∀ v < program.values.length,
    (match (program.value v).kind with
      | .bound _ => false
      | _ => true) = true
  /-- `statement.hhat` is an opaque statement value of no argument. -/
  hhatKind : (program.value 544).kind = .pub (.opaque "statement.hhat" [])
  /-- The named operators of `signature.equation`. -/
  ops_sig : RealizedProgram.NamedOp.cols program (.negacyclicConv 544 (.ntt 10302)) = 512 ∧
    RealizedProgram.NamedOp.rows program (.negacyclicConv 544 (.ntt 10302)) = 512 ∧
    RealizedProgram.NamedOp.cols program (.batched 512 (.fromDigits 16 2)) = 8192 ∧
    RealizedProgram.NamedOp.rows program (.batched 512 (.fromDigits 16 2)) = 512

variable {program : RealizedProgram} {FH FA : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.falconInterpOf FH FA

variable [HField FH] [AField FA] [FalconHBase program] [FalconACore program] [FalconAAlg program]

instance : CharP (interp 1).K 12289 := AField.charQ (FA := FA)

/-! ## Reading the values of `A` -/

/-- **A value of domain `A`** read in `FA`. -/
def rdA (e : program.Env interp) (v i : ℕ) : (interp 1).K :=
  program.evalE (program.reader e) 1 (.leaf v) i

/-- **`s2` is value `546`** (`FalconAAlg.s2_eq`). -/
theorem s2Vals_eq (e : program.Env interp) (i : Fin falcon512.n) :
    s2Vals (program.reader e) i = rdA e 546 i := by
  unfold s2Vals rdA
  rw [FalconAAlg.s2_eq]

/-- **`c_A` is value `545`** (`FalconAAlg.cA_eq`). -/
theorem cABits_eq (e : program.Env interp) (j : Fin falcon512.n) :
    cABits e j = program.wordAt (program.reader e) 1 545 16 j := by
  unfold cABits
  rw [FalconAAlg.cA_eq]

/-- **The integer reading of a value** for `mod_q` (`RealizedProgram.intOf`). -/
abbrev ia (e : program.Env interp) (v i : ℕ) : ℤ :=
  program.intOf (program.reader e) v i

theorem cast_toNat_castElt {a : ℕ} (ha : a = 1) (x : (interp a).K)
    (hx : x ∈ (interp a).node "GF(p^1)") :
    (((interp a).toNat x : ℕ) : (interp 1).K) = (RealizedProgram.castElt x : (interp 1).K) := by
  subst ha
  rw [RealizedProgram.castElt_self]
  exact AField.natCast_toNat hx

variable (program) in
/-- **A private source value of `A` typed in the prime subfield by its node.** -/
def PrimeA (v : ℕ) : Prop :=
  v < program.values.length ∧ program.IsSourceValue v ∧ (program.value v).typeSource = .node ∧
    (program.value v).type = .sub "GF(p^1)" ∧ program.valueField v = 1 ∧
    program.isConstant v = false

/-- **No value of the program is bound** (`noBound`; a value past the table is the default). -/
theorem kind_ne_bound (v : ℕ) (x : RealizedProgram.Expr) : (program.value v).kind ≠ .bound x := by
  intro h
  by_cases hv : v < program.values.length
  · have := FalconAAlg.noBound (program := program) v hv
    rw [h] at this
    cases this
  · have hd : program.value v = default := by
      simp only [RealizedProgram.value, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega), Option.getD_none]
    rw [hd] at h
    cases h

/-- **The integer reading of a prime-typed value casts to the value** where the source program holds
(its node type, `SourceSatAt.types`). -/
theorem intOf_cast {e : program.Env interp} (hs : program.SourceSatAt e) {v : ℕ} (hv : PrimeA program v)
    {i : ℕ} (hi : i < (program.value v).size) : ((ia e v i : ℤ) : (interp 1).K) = rdA e v i := by
  obtain ⟨hvl, hsrc, hts, hty, hf, hc⟩ := hv
  have hmem := hs.types v hvl hsrc hts i hi
  rw [hty] at hmem
  have hint : program.intOf (program.reader e) v i =
      ((interp (program.valueField v)).toNat (program.reader e v i) : ℤ) := by
    unfold RealizedProgram.intOf
    unfold RealizedProgram.isConstant at hc
    split
    · rename_i es h
      rw [h] at hc
      cases hc
    · rename_i x h
      exact absurd h (kind_ne_bound _ x)
    · rfl
  rw [ia, hint, Int.cast_natCast]
  exact cast_toNat_castElt hf _ hmem

/-- **A source predicate holds** where the source program holds. -/
theorem holdsAt {e : program.Env interp} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p < program.predicates.length) (hsrc : program.inSource (program.predicate p) = true) :
    program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (RealizedProgram.predicate_mem hp) hsrc

/-- `s2` and `signature.s1` are prime-typed private source values. -/
theorem primeA {v : ℕ} (hv : v ∈ [546, 547]) : PrimeA program v :=
  FalconAAlg.primeA_sig v hv

/-! ## The advice -/

/-- **The integer reading of a value of `A`** as a natural. -/
def nA (e : program.Env interp) (v j : ℕ) : ℕ := (interp 1).toNat (rdA e v j)

/-- **The integer reading of a non-constant value of `A`** is its natural reading. -/
theorem ia_eq_nA (e : program.Env interp) {v : ℕ} (hf : program.valueField v = 1)
    (hc : program.isConstant v = false) (j : ℕ) : ia e v j = nA e v j := by
  have hint : program.intOf (program.reader e) v j =
      ((interp (program.valueField v)).toNat (program.reader e v j) : ℤ) := by
    unfold RealizedProgram.intOf
    unfold RealizedProgram.isConstant at hc
    split
    · rename_i es h
      rw [h] at hc
      cases hc
    · rename_i x h
      exact absurd h (kind_ne_bound _ x)
    · rfl
  rw [ia, hint, nA, rdA, RealizedProgram.evalE_leaf, RealizedProgram.toNat_castElt hf]

/-- **A prime-typed value of `A` is the cast of its natural reading.** -/
theorem nA_cast {e : program.Env interp} (hs : program.SourceSatAt e) {v : ℕ} (hv : PrimeA program v)
    {j : ℕ} (hj : j < (program.value v).size) : ((nA e v j : ℕ) : (interp 1).K) = rdA e v j := by
  have := intOf_cast hs hv hj
  rw [ia_eq_nA e hv.2.2.2.2.1 hv.2.2.2.2.2, Int.cast_natCast] at this
  exact this

/-! ## The norm and the encoding -/

/-- **Advice for the norm and the encoding at `e`**: native advice whose `s1` is
`signature.s1` (`547`), at which the native norm's constraints (`NativeNorm.Holds` at the norm's
inputs `s1 ‖ s2`), the encoding's Boolean checks and the requests hold. -/
def NormAdvice (e : program.Env interp) : Prop :=
  ∃ alg : Native.Committed (interp 1).K, (∀ i, alg.s1 i = rdA e 547 i) ∧
    NativeNorm.Holds (Native.normInputs (s2Vals (program.reader e)) alg) alg.norm ∧
    NativeEncoding.BitsHold alg.norm ∧ Native.AlgRequests alg

variable (program FH FA) in
/-- **The norm's obligation wherever the source program holds**, discharged per program by the
generic norm (`FalconNorm`). -/
def NormSound : Prop := ∀ e : program.Env interp, program.SourceSatAt e → NormAdvice e

/-! ## The signature equation

`signature.equation` is a `mod_q` (`q = 12289`) in the field form: its integer readings agree
modulo `q`. They read the values' constant coordinates, and the operators' matrix entries'
(`FieldInterp.coefInt`), so they are the equation of the constant coordinates (`coord0`, an
`F_q`-linear map): the statement's `statement.hhat` may have other coordinates, which the readings
ignore, as `keyOf` does. The key's polynomial is the inverse transform of the constant coordinates
of `statement.hhat` (`KeyNTT.inverseNtt_keyHat`), and `s₁`, `s₂` and `c_A` lie in the prime
subfield, so the equation of the constant coordinates is the signature rows. -/

/-- **The constant coordinate of `FA`** as an additive map to `F_q` (`AField.coord0`). -/
abbrev coord0 : (interp 1).K →+ ZMod 12289 := AField.coord0 (FA := FA)

/-- **The prime field `F_q` in `FA`.** -/
abbrev φq : ZMod 12289 →+* (interp 1).K := ZMod.castHom (dvd_refl 12289) _

theorem φq_apply (z : ZMod 12289) : (φq z : (interp 1).K) = ((z.val : ℕ) : (interp 1).K) := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

/-- The constant coordinate of a natural's cast. -/
theorem coord0_natCast (n : ℕ) : coord0 (n : (interp 1).K) = n :=
  AField.coord0_natCast n

/-- The constant coordinate of an element of `F_q`. -/
theorem coord0_φq (z : ZMod 12289) : coord0 (φq z : (interp 1).K) = z := by
  rw [φq_apply, coord0_natCast, ZMod.natCast_zmod_val]

/-- **The constant coordinate is `F_q`-linear.** -/
theorem coord0_φq_mul (z : ZMod 12289) (y : (interp 1).K) : coord0 (φq z * y) = z * coord0 y := by
  rw [φq_apply, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, ZMod.natCast_zmod_val]

/-- The integer reading of an element is the value of its constant coordinate. -/
theorem toNat_eq_val (x : (interp 1).K) : (interp 1).toNat x = (coord0 x).val :=
  AField.toNat_eq x

/-- **The centred integer reading casts to the constant coordinate.** -/
theorem coefInt_cast (x : (interp 1).K) :
    (((interp 1).coefInt x : ℤ) : ZMod 12289) = coord0 x := by
  unfold RealizedProgram.FieldInterp.coefInt RealizedProgram.FieldInterp.centered
  rw [toNat_eq_val]
  split_ifs
  · rw [Int.cast_natCast, ZMod.natCast_zmod_val]
  · rw [show (interp 1).spec.characteristic = 12289 from AField.spec_char, Int.cast_sub,
      Int.cast_natCast,
      Int.cast_natCast, ZMod.natCast_self, sub_zero, ZMod.natCast_zmod_val]

/-- An element whose integer reading casts back lies in `F_q`. -/
theorem φq_coord0 {x : (interp 1).K} (hx : (((interp 1).toNat x : ℕ) : (interp 1).K) = x) :
    φq (coord0 x) = x := by
  rw [φq_apply, ← toNat_eq_val, hx]

/-- **The inverse transform commutes with the constant coordinate** at `ψ = 10302`. -/
theorem coord0_inverseNtt (h : ℕ → (interp 1).K) (s : ℕ) :
    coord0 (RealizedProgram.Ops.inverseNtt 512 ((10302 : ℕ) : (interp 1).K) h s) =
      RealizedProgram.Ops.inverseNtt 512 KeyNTT.psi512 (fun m => coord0 (h m)) s := by
  have h512 : ((512 : ℕ) : (interp 1).K)⁻¹ = φq ((512 : ℕ) : ZMod 12289)⁻¹ := by
    rw [map_inv₀, map_natCast]
  have hψ : ((10302 : ℕ) : (interp 1).K)⁻¹ = φq KeyNTT.psi512⁻¹ := by
    rw [map_inv₀, show KeyNTT.psi512 = ((10302 : ℕ) : ZMod 12289) from
      (Nat.cast_ofNat).symm, map_natCast]
  unfold RealizedProgram.Ops.inverseNtt
  split_ifs with hs
  · rw [h512]
    rw [hψ]
    rw [coord0_φq_mul]
    rw [map_sum]
    have hterm : ∀ (y : (interp 1).K) (k : ℕ),
        coord0 (y * φq KeyNTT.psi512⁻¹ ^ k) = coord0 y * KeyNTT.psi512⁻¹ ^ k := by
      intro y k
      rw [← map_pow, _root_.mul_comm, coord0_φq_mul, _root_.mul_comm]
    simp only [hterm]
  · exact map_zero _

/-- The constant coordinate of a product with an element of `F_q`. -/
theorem coord0_mul_prime {x y : (interp 1).K} (hy : φq (coord0 y) = y) :
    coord0 (x * y) = coord0 x * coord0 y := by
  rw [← hy, _root_.mul_comm, coord0_φq_mul, coord0_φq, _root_.mul_comm]

/-- **The negacyclic convolution with a vector over `F_q` commutes with the constant
coordinate.** -/
theorem coord0_negacyclicConvCoeff {n : ℕ} (h y : Fin n → (interp 1).K)
    (hy : ∀ t, φq (coord0 (y t)) = y t) (k : Fin n) :
    coord0 (LatticeCrypto.negacyclicConvCoeff h y k) =
      LatticeCrypto.negacyclicConvCoeff (fun a => coord0 (h a)) (fun b => coord0 (y b)) k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  split_ifs
  · exact coord0_mul_prime (hy _)
  · rw [map_neg, coord0_mul_prime (hy _)]
  · exact map_zero _

/-- **The integer reading of a named operator on a value over `F_q`** casts, modulo `q`, to the
constant coordinate of the operator on the value (`NamedOp.block_eq_sum_unit`, `coefInt_cast`). -/
theorem applyInt_cast (e : program.Env interp) (op : RealizedProgram.NamedOp) {v : ℕ}
    (hf : program.valueField v = 1) (hc : program.isConstant v = false)
    (hprime : ∀ t < RealizedProgram.NamedOp.cols program op, φq (coord0 (rdA e v t)) = rdA e v t) {j : ℕ}
    (hj : j < RealizedProgram.NamedOp.rows program op) :
    ((RealizedProgram.NamedOp.applyInt program (program.domainField 1) (program.reader e) op
        (program.evalIntWith (program.reader e) 1 (.leaf v)) j : ℤ) : ZMod 12289) =
      coord0 (RealizedProgram.NamedOp.block program 1 (program.reader e) op (fun t => rdA e v t) j) := by
  unfold RealizedProgram.NamedOp.applyInt
  rw [Nat.mod_eq_of_lt hj, Nat.div_eq_of_lt hj, Nat.zero_mul]
  generalize hd : program.domainField 1 = d
  obtain rfl : d = 1 := by rw [← hd]; exact FalconACore.domainField1
  rw [RealizedProgram.NamedOp.block_eq_sum_unit program (program.reader e) op _ j, map_sum, Int.cast_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Int.cast_mul, coefInt_cast, Nat.zero_add, RealizedProgram.evalIntWith_leaf]
  change _ * ((ia e v t : ℤ) : ZMod 12289) = _
  rw [ia_eq_nA e hf hc, Int.cast_natCast, nA, toNat_eq_val, ZMod.natCast_zmod_val,
    coord0_mul_prime (hprime t t.isLt)]

set_option maxRecDepth 4096 in
/-- **The key's polynomial read by `signature.equation`**: the constant coordinates of the inverse
transform of `statement.hhat` are the key's coefficients, at a statement that decodes to `pk`. -/
theorem coord0_keyPoly {e : program.Env interp} {pk : PublicKey} (hpk : keyOf e.stmt = some pk)
    {a : ℕ} (ha : a < 512) :
    coord0 (RealizedProgram.Ops.inverseNtt 512 ((10302 : ℕ) : (interp 1).K)
      (fun s => (RealizedProgram.castElt (program.reader e 544 s) : (interp 1).K)) a) = Falcon512.coeff pk.h ⟨a, ha⟩ := by
  rw [coord0_inverseNtt]
  have hread : program.reader e 544 = e.stmt 544 :=
    RealizedProgram.reader_of_opaque_nil e (name := "statement.hhat") (FalconAAlg.hhatKind (program := program))
  rw [RealizedProgram.Ops.inverseNtt_congr
    (y := RealizedProgram.Ops.ofFin fun j : Fin 512 => (KeyNTT.keyHat pk j : ZMod 12289))
    (fun m hm => ?_), KeyNTT.inverseNtt_keyHat pk ha]
  rw [RealizedProgram.Ops.ofFin_of_lt _ hm, hread, ← toNat_hhat_of_keyOf hpk ⟨m, hm⟩]
  have h1 : program.valueField 544 = 1 := FalconACore.hhatField
  change coord0 (RealizedProgram.castElt (e.stmt 544 m) : (interp 1).K) =
    (((interp (program.valueField 544)).toNat (e.stmt 544 m) : ℕ) : ZMod 12289)
  rw [← RealizedProgram.toNat_castElt h1, toNat_eq_val, ZMod.natCast_zmod_val]

/-- **The samples' bits are bits** (`crossing.c_A.boolean`). -/
theorem cA_bool {e : program.Env interp} (hs : program.SourceSatAt e) {t : ℕ} (ht : t < 8192) :
    rdA e 545 t = 0 ∨ rdA e 545 t = 1 := by
  obtain ⟨pb, hpb, hbc, hsrcb⟩ := FalconACore.cABoolean (program := program)
  have hsz := (FalconACore.raw_facts (program := program)).2.2
  rw [FalconAAlg.cA_eq] at hbc hsz
  have hbool := hs.holdsAt_of_predByName hpb hsrcb
  have := RealizedProgram.bool_of_boolCheck hbc hbool (i := t)
    (by change t < (program.value 545).size; rw [hsz]; exact ht)
  rw [FalconACore.domainField1] at this
  exact this

theorem φq_coord0_bool {x : (interp 1).K} (hx : x = 0 ∨ x = 1) : φq (coord0 x) = x := by
  rcases hx with rfl | rfl
  · rw [map_zero, map_zero]
  · rw [show (1 : (interp 1).K) = ((1 : ℕ) : (interp 1).K) from Nat.cast_one.symm, coord0_natCast,
      map_natCast]

set_option maxRecDepth 4096 in
/-- **The signature rows hold** at the decoded key (`Native.SignatureRows`), from
`signature.equation`'s constant coordinates. -/
theorem signatureRows {e : program.Env interp} (hs : program.SourceSatAt e) {pk : PublicKey}
    (hpk : keyOf e.stmt = some pk) (alg : Native.Committed (interp 1).K)
    (hs1 : ∀ i, alg.s1 i = rdA e 547 i) :
    Native.SignatureRows pk.h (cABits e) (s2Vals (program.reader e)) alg := by
  intro i
  have hi := i.isLt
  change (i : ℕ) < 512 at hi
  obtain ⟨_, hbd⟩ := FalconAAlg.sig (program := program)
  have h := holdsAt hs (FalconAAlg.inSource_sig (program := program)).1
    (FalconAAlg.inSource_sig (program := program)).2
  rw [hbd] at h
  have hdvd := h i (by rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (FalconAAlg.sizes_sig (program := program)).2]; exact hi)
  have hZ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12289).2 hdvd
  rw [Int.cast_sub, sub_eq_zero, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_apply,
    RealizedProgram.evalIntWith_apply, Int.cast_add, RealizedProgram.evalIntWith_leaf] at hZ
  have h546 : ∀ t < 512, φq (coord0 (rdA e 546 t)) = rdA e 546 t := fun t ht =>
    φq_coord0 (nA_cast hs (primeA (program := program) (v := 546) (by simp)) (by rw [(FalconAAlg.sizes_sig (program := program)).1]; exact ht))
  have h547 : φq (coord0 (rdA e 547 i)) = rdA e 547 i :=
    φq_coord0 (nA_cast hs (primeA (program := program) (v := 547) (by simp)) (by rw [(FalconAAlg.sizes_sig (program := program)).2]; exact hi))
  have h545 : ∀ t < 8192, φq (coord0 (rdA e 545 t)) = rdA e 545 t := fun t ht =>
    φq_coord0_bool (cA_bool hs ht)
  obtain ⟨hcN, hrN, hcB, hrB⟩ := FalconAAlg.ops_sig (program := program)
  rw [applyInt_cast e _ (primeA (v := 546) (by simp)).2.2.2.2.1
      (primeA (v := 546) (by simp)).2.2.2.2.2
      (fun t ht => h546 t (hcN ▸ ht)) (hrN ▸ hi),
    applyInt_cast e _ (FalconAAlg.fields_cA (program := program)).1 (FalconAAlg.fields_cA (program := program)).2
      (fun t ht => h545 t (hcB ▸ ht)) (hrB ▸ hi)] at hZ
  change ((ia e 547 i : ℤ) : ZMod 12289) + _ = _ at hZ
  rw [ia_eq_nA e (primeA (v := 547) (by simp)).2.2.2.2.1 (primeA (v := 547) (by simp)).2.2.2.2.2,
    Int.cast_natCast, nA, toNat_eq_val,
    ZMod.natCast_zmod_val] at hZ
  have hsz : (program.value 544).size = 512 := FalconACore.hhatSize
  have hN : RealizedProgram.NamedOp.block program 1 (program.reader e) (.negacyclicConv 544 (.ntt 10302))
      (fun t => rdA e 546 t) i =
      LatticeCrypto.negacyclicConvCoeff
        (RealizedProgram.Ops.toFin 512 (RealizedProgram.Ops.inverseNtt 512 ((10302 : ℕ) : (interp 1).K)
          (fun s => (RealizedProgram.castElt (program.reader e 544 s) : (interp 1).K))))
        (RealizedProgram.Ops.toFin 512 fun t => rdA e 546 t) ⟨i, hi⟩ := by
    simp only [RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.formPoly, RealizedProgram.Ops.negacyclic]
    erw [AField.decode_eq (FA := FA) 10302]
    generalize (program.value 544).size = N at hsz ⊢
    subst hsz
    exact RealizedProgram.Ops.ofFin_of_lt (R := (interp 1).K) _ hi
  have hB : RealizedProgram.NamedOp.block program 1 (program.reader e) (.batched 512 (.fromDigits 16 2))
      (fun t => rdA e 545 t) i = ∑ l : Fin 16, ((2 ^ (l : ℕ) : ℕ) : (interp 1).K) *
        rdA e 545 (i * 16 + l) := by
    simp only [RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, RealizedProgram.Ops.fromDigits, Nat.mul_one,
      Nat.div_one, Nat.mod_one, ite_true, if_pos hi, Nat.cast_pow]
    simp only [AField.decode_eq]
  rw [hN, hB, coord0_negacyclicConvCoeff _ (RealizedProgram.Ops.toFin 512 fun t => rdA e 546 t)
    (fun t => h546 t t.isLt), map_sum] at hZ
  have hcA : ∀ l : Fin 16, coord0 (((2 ^ (l : ℕ) : ℕ) : (interp 1).K) * rdA e 545 (i * 16 + l)) =
      ((2 ^ (l : ℕ) : ℕ) : ZMod 12289) * coord0 (rdA e 545 (i * 16 + l)) := fun l => by
    rw [← map_natCast φq, coord0_φq_mul]
  simp only [hcA] at hZ
  have hφ := congrArg (φq (FH := FH) (FA := FA)) hZ
  rw [map_add, h547, DFT.negacyclicConvCoeff_map (φq (FH := FH) (FA := FA)), map_sum] at hφ
  simp only [map_mul, map_natCast, Function.comp_def] at hφ
  have hkey : ∀ a : Fin 512, φq (coord0 (RealizedProgram.Ops.toFin 512 (RealizedProgram.Ops.inverseNtt 512
      ((10302 : ℕ) : (interp 1).K) (fun s => (RealizedProgram.castElt (program.reader e 544 s) : (interp 1).K))) a)) =
      ((EmulatedAlgebraCircuit.keyCoeffs pk.h a : ℕ) : (interp 1).K) := fun a => by
    rw [φq_apply, RealizedProgram.Ops.toFin_apply, coord0_keyPoly hpk a.isLt]
    rfl
  have hfin : ∀ t : Fin 512, φq (coord0 (RealizedProgram.Ops.toFin 512 (fun t => rdA e 546 t) t)) =
      s2Vals (program.reader e) t := fun t => (h546 t t.isLt).trans (s2Vals_eq e t).symm
  simp only [hkey, hfin, fun l : Fin 16 => h545 (i * 16 + l) (by omega)] at hφ
  unfold Emulated.sampleValue
  simp only [cABits_eq]
  change ∑ b : Fin 16, (2 : (interp 1).K) ^ (b : ℕ) * rdA e 545 (i * 16 + b) - _ - alg.s1 i = 0
  rw [hs1 i]
  push_cast at hφ
  have hconv : LatticeCrypto.negacyclicConvCoeff (n := 512)
      (fun x => ((EmulatedAlgebraCircuit.keyCoeffs pk.h x : ℕ) : (interp 1).K))
      (fun x => s2Vals (program.reader e) x) ⟨i, hi⟩ =
      LatticeCrypto.negacyclicConvCoeff (fun j => ((EmulatedAlgebraCircuit.keyCoeffs pk.h j : ℕ) :
        (interp 1).K)) (s2Vals (program.reader e)) i := rfl
  rw [hconv] at hφ
  rw [sub_eq_zero, sub_eq_iff_eq_add]
  exact hφ.symm

/-! ## Domain `A`'s obligation -/

/-- **Domain `A`'s algebra** (`AlgebraConstraints`, `AlgRequests`): wherever the source program
holds and at every key its statement decodes to, the native algebra holds at the norm's advice
(`hN`): the sample bits are bits (`crossing.c_A.boolean`), the signature rows (`signatureRows`), the
native norm, the encoding's Boolean checks and the requests (`NormSound`). -/
theorem algebraNative (hN : NormSound program FH FA) {e : program.Env interp}
    (hs : program.SourceSatAt e) {pk : PublicKey}
    (hpk : keyOf e.stmt = some pk) : ∃ alg : Native.Committed (interp 1).K,
      Native.AlgebraConstraints pk.h (cABits e) (s2Vals (program.reader e)) alg ∧
        Native.AlgRequests alg := by
  obtain ⟨alg, hs1, hnorm, hbits, hreq⟩ := hN e hs
  refine ⟨alg, ⟨fun i b => ?_, signatureRows hs hpk alg hs1, hnorm, hbits⟩, hreq⟩
  have hi : (i : ℕ) < 512 := i.isLt
  have hb : (b : ℕ) < 16 := b.isLt
  rw [cABits_eq]
  exact cA_bool hs (by omega)

/-- **Domain `A`'s obligation of the frontend** (`AlgebraSound`): Falcon native's algebra at the
norm's advice (`algebraNative`) gives Falcon's algebraic verifier and the encoding bounds
(`Native.algebra_sound`). -/
theorem algebraSound (hN : NormSound program FH FA) :
    AlgebraSound (program := program) (FH := FH) (FA := FA) := by
  intro e hs pk hpk
  obtain ⟨alg, hcons, hreq⟩ := algebraNative hN hs hpk
  exact Native.algebra_sound hcons hreq

end GordieHowe.Falcon512.Native.ROMParams
