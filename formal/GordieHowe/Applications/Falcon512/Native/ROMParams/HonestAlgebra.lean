-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.HonestSelect
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Algebra
public import GordieHowe.Applications.Falcon512.NormHonest

@[expose] public section

/-!
# GordieHowe: the honest algebra of a native Falcon program

The honest values of domain `A` (`algVal`): the samples' bits `c_A`, and the honest naturals of the
norm and the encoding of the signature (`GordieHowe.Falcon512.Norm.NormIn` at the honest input, `hIn`: the
canonical `s1` and `s2`, the native norm's digits and carries); and domain A's predicates at the
source environment of these values: the norm's and the encoding's by the generic norm
(`norm_honest`, `GordieHowe.Falcon512.Norm.preds_honest`), the signature equations (both forms), `c_A`'s type check
and the crossing (here). Generic in the program (`FalconAHonest`: domain A's facts beyond the
frontend's and the norm's, decided per program) and the fields.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program hiding program
open GordieHowe.Bits
open Norm (FalconNorm FalconNormHonest NormIn NormVals)

/-- **The program facts of honest domain A** beyond the norm's (`FalconAAlg` and; each program
instantiates them by `decide`): the norm at domain and field `1` on the values `546 … 554`
(`FalconNorm`), the field-form signature equation (`pSigE`), `c_A`'s type check (`pCA`) and
`mac.equal` (`pMac`), with their bodies and the values' cells. -/
class FalconAHonest (program : RealizedProgram) [FalconACore program] [FalconNorm program]
    [FalconNormHonest program] extends FalconAAlg program where
  /-- The norm is at domain `1`. -/
  norm_dA : FalconNorm.dA program = 1
  /-- The norm is at field `1`. -/
  norm_fA : FalconNorm.fA program = 1
  /-- The norm's values are `546 … 554`. -/
  norm_ids : FalconNorm.s2 program = 546 ∧ FalconNorm.s1 program = 547 ∧ FalconNorm.a program = 548 ∧
    FalconNorm.sq program = 549 ∧ FalconNorm.cc program = 550 ∧ FalconNorm.nd program = 551 ∧
    FalconNorm.nc program = 552 ∧ FalconNorm.D program = 553 ∧ FalconNorm.Dc program = 554
  /-- The field-form signature equation. -/
  pSigE : ℕ
  /-- `c_A`'s type check. -/
  pCA : ℕ
  /-- `mac.equal`. -/
  pMac : ℕ
  /-- The values of `A` are checked committed values of field `1`. -/
  a_checks : ∀ v ∈ [545, 546, 547, 548, 549, 550, 551, 552, 553, 554],
    program.privCellB v = true ∧ program.valueField v = 1 ∧ program.isConstant v = false
  /-- `c_A` has `8192` coordinates. -/
  sizes_H : (program.value 545).size = 8192
  /-- The zero row constant `44`. -/
  const44 : program.isConstant 44 = true ∧ program.valueField 44 = 1 ∧
    program.constEntries 44 = List.replicate 512 0
  /-- The field-form signature equation. -/
  sigE_body : ∃ t, (program.predicate pSigE).body = .equal 1
    (.add (.add (.leaf 547) (.apply (.negacyclicConv 544 (.ntt 10302)) (.leaf 546)))
      (.scale (.const 12288) (.apply (.batched 512 (.fromDigits 16 2)) (.leaf 545))))
    (.leaf 44) t
  /-- The field-form signature equation's length. -/
  sigE_len : program.exprLen (.add (.add (.leaf 547) (.apply (.negacyclicConv 544 (.ntt 10302))
      (.leaf 546))) (.scale (.const 12288) (.apply (.batched 512 (.fromDigits 16 2))
        (.leaf 545)))) = 512
  /-- `c_A`'s type check. -/
  ca_body : ∃ t, (program.predicate pCA).body = .equal 1 (.mul (.leaf 545) (.leaf 545)) (.leaf 545) t
  /-- `mac.equal` crosses the raw view `540` and `c_A`. -/
  mac_body : ∃ o r, (program.predicate pMac).body = .cross 0 (.leaf 540) 1 (.leaf 545) o r ∧
    1 ≤ o.width
  /-- The crossing's fields. -/
  cross_fields : program.valueField 540 = 0 ∧ program.valueField 545 = 1

open FalconAHonest

set_option linter.unusedSectionVars false

/-- Constants decode to their casts in `F_q`. -/
theorem decode_A {FA : RealizedProgram.FieldInterp} [AField FA] (c : ℕ) : FA.decode c = (c : FA.K) :=
  AField.decode_eq c

variable {program : RealizedProgram} [FalconACore program] [FalconNorm program] [FalconNormHonest program]
  [FalconAHonest program] {FH FA : RealizedProgram.FieldInterp} [HField FH] [AField FA] [FalconHBase program]

set_option hygiene false in
local notation "interp" => RealizedProgram.falconInterpOf FH FA

section Naturals

variable {L : ℕ} (y : Falcon512.PoP.HonestInput L)

/-- **The signature the norm reads** at an honest input: the key, the samples and `s2`. -/
def hIn : NormIn := ⟨y.pk.h, y.samples, y.signature⟩

/-- **The honest signature is valid**: Falcon's algebraic verifier accepts and the encoding bounds
hold. -/
theorem hIn_valid {y : Falcon512.PoP.HonestInput L} (hy : y.Valid) : (hIn y).Valid :=
  ⟨hy.algebra, hy.encoding⟩

/-- **The honest natural of value `v` at coordinate `j`** of domain `A`: the samples' bits `c_A`
(`545`), and the norm's and the encoding's naturals of `hIn` (`s2` `546`, `s1` `547`, the norm's
digits and carries `548 … 554`); `0` elsewhere. -/
-- spec-side
noncomputable def hNat (program : RealizedProgram) [FalconNorm program] [FalconNormHonest program] {L : ℕ}
    (y : Falcon512.PoP.HonestInput L) (v j : ℕ) : ℕ :=
  if v = 545 then (if h : j < 8192 then y.samples ⟨j / 16, by have : falcon512.n = 512 := rfl; omega⟩ / 2 ^ (j % 16) % 2 else 0)
  else if v = 546 then (hIn y).nS2 j
  else if v = 547 then (hIn y).nS1 j
  else if v = 548 then (hIn y).nA j
  else if v = 549 then (hIn y).nSq j
  else if v = 550 then (hIn y).nCc j
  else if v = 551 then (hIn y).nNd j
  else if v = 552 then (hIn y).nNc j
  else if v = 553 then (hIn y).nD j
  else if v = 554 then (hIn y).nDc j
  else 0

variable {y}

theorem hNat_546 (j : ℕ) : hNat program y 546 j = (hIn y).nS2 j := by
  unfold hNat
  rw [if_neg (by norm_num), if_pos rfl]

theorem hNat_547 (j : ℕ) : hNat program y 547 j = (hIn y).nS1 j := by
  unfold hNat
  rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem nS1_hIn {j : ℕ} (hj : j < 512) : (hIn y).nS1 j =
    Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) y.pk.h y.samples y.signature ⟨j, hj⟩ := by
  unfold NormIn.nS1 hIn
  rw [dif_pos hj]

theorem nS2_hIn {j : ℕ} (hj : j < 512) : (hIn y).nS2 j =
    Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) y.signature ⟨j, hj⟩ := by
  unfold NormIn.nS2 hIn
  rw [dif_pos hj]

theorem hNat_548 (j : ℕ) : hNat program y 548 j = (hIn y).nA j := by
  unfold hNat
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem hNat_549 (j : ℕ) : hNat program y 549 j = (hIn y).nSq j := by
  unfold hNat
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem hNat_550 (j : ℕ) : hNat program y 550 j = (hIn y).nCc j := by
  unfold hNat
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem hNat_551 (j : ℕ) : hNat program y 551 j = (hIn y).nNd j := by
  unfold hNat
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem hNat_552 (j : ℕ) : hNat program y 552 j = (hIn y).nNc j := by
  unfold hNat
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem hNat_553 (j : ℕ) : hNat program y 553 j = (hIn y).nD j := by
  unfold hNat
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

theorem hNat_554 (j : ℕ) : hNat program y 554 j = (hIn y).nDc j := by
  unfold hNat
  rw [if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]

end Naturals

/-! ## Reading the honest values -/

section Reading

variable {val x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **A checked committed value of `A` reads a natural below `q`** at the source environment:
its reading and its integer reading. -/
theorem rdA_honest {v j n : ℕ} (hv : program.privCellB v = true) (hf : program.valueField v = 1)
    (hval : val v j = RealizedProgram.castElt (a := 1) ((n : ℕ) : (interp 1).K))
    (hj : j < (program.value v).size) :
    rdA (program.srcEnv interp x val c π) v j = (n : (interp 1).K) := by
  unfold rdA
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_srcEnv_of_privCellB x val c π hv hj, hval]
  exact RealizedProgram.castElt_castElt_of_eq hf.symm _

theorem ia_honest {v j n : ℕ} (hv : program.privCellB v = true) (hf : program.valueField v = 1)
    (hc : program.isConstant v = false)
    (hval : val v j = RealizedProgram.castElt (a := 1) ((n : ℕ) : (interp 1).K))
    (hj : j < (program.value v).size) (hn : n < 12289) :
    ia (program.srcEnv interp x val c π) v j = n := by
  rw [ia_eq_nA _ hf hc, nA, rdA_honest hv hf hval hj]
  exact congrArg Nat.cast (AField.toNat_natCast (FA := FA) hn)

end Reading

/-! ## The honest values of `A` -/

/-- **The values of `A` the norm, the signature and the encoding read.** -/
def NormValues (program : RealizedProgram) [FalconACore program] [FalconNorm program] [FalconNormHonest program]
    [FalconAHonest program] : List ℕ :=
  [545, 546, 547, 548, 549, 550, 551, 552, 553, 554]

/-- **The honest values of the norm and the signature**: the honest naturals (`hNat`) in `F_q^9`.

Running time: computing these values takes the honest residues (one negacyclic product), then a
constant number of digit operations per coefficient and batch. This running time is argued here, not
proved in Lean. -/
-- spec-side
noncomputable def algVal (program : RealizedProgram) [FalconACore program] [FalconNorm program]
    [FalconNormHonest program] [FalconAHonest program] {L : ℕ}
    (y : Falcon512.PoP.HonestInput L) (v j : ℕ) : (interp (program.valueField v)).K :=
  if v ∈ NormValues program then RealizedProgram.castElt (a := 1) ((hNat program y v j : ℕ) : (interp 1).K) else 0

theorem normValues_sub : NormValues program ⊆ [545, 546, 547, 548, 549, 550, 551, 552, 553, 554] := by
  intro v hv
  simp only [NormValues, List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
  omega

section HonestReading

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

theorem ia_algVal (h : ∀ v ∈ NormValues program, val v = algVal program y v) {v j : ℕ} (hv : v ∈ NormValues program)
    (hj : j < (program.value v).size) (hn : hNat program y v j < 12289) :
    ia (program.srcEnv interp x val c π) v j = hNat program y v j := by
  obtain ⟨h1, h2, h3⟩ := FalconAHonest.a_checks (program := program) v (normValues_sub hv)
  refine ia_honest h1 h2 h3 ?_ hj hn
  rw [h v hv]
  unfold algVal
  rw [if_pos hv]

theorem rdA_algVal (h : ∀ v ∈ NormValues program, val v = algVal program y v) {v j : ℕ} (hv : v ∈ NormValues program)
    (hj : j < (program.value v).size) :
    rdA (program.srcEnv interp x val c π) v j = (hNat program y v j : (interp 1).K) := by
  obtain ⟨h1, h2, -⟩ := FalconAHonest.a_checks (program := program) v (normValues_sub hv)
  refine rdA_honest h1 h2 ?_ hj
  rw [h v hv]
  unfold algVal
  rw [if_pos hv]

end HonestReading

/-! ## The norm and the encoding -/

section HonestNorm

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

/-- **A value of `NormValues` holds its honest natural** cast from field `1`. -/
theorem val_norm (h : ∀ v ∈ NormValues program, val v = algVal program y v) {v : ℕ}
    (hv : v ∈ NormValues program) (j : ℕ) :
    val v j = RealizedProgram.castElt (a := 1) ((hNat program y v j : ℕ) : (interp 1).K) := by
  rw [h v hv]
  unfold algVal
  rw [if_pos hv]

/-- **The honest values of the norm** (`Norm.NormVals` at `hIn`). -/
theorem normVals (h : ∀ v ∈ NormValues program, val v = algVal program y v) :
    NormVals val (hIn y) := by
  obtain ⟨i2, i1, ia', isq, icc, ind, inc, iD, iDc⟩ := FalconAHonest.norm_ids (program := program)
  have hf := FalconAHonest.norm_fA (program := program)
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_, fun j => ?_,
    fun j => ?_, fun j => ?_⟩
  · rw [i2, hf, val_norm h (by simp [NormValues]), hNat_546]
  · rw [i1, hf, val_norm h (by simp [NormValues]), hNat_547]
  · rw [ia', hf, val_norm h (by simp [NormValues]), hNat_548]
  · rw [isq, hf, val_norm h (by simp [NormValues]), hNat_549]
  · rw [icc, hf, val_norm h (by simp [NormValues]), hNat_550]
  · rw [ind, hf, val_norm h (by simp [NormValues]), hNat_551]
  · rw [inc, hf, val_norm h (by simp [NormValues]), hNat_552]
  · rw [iD, hf, val_norm h (by simp [NormValues]), hNat_553]
  · rw [iDc, hf, val_norm h (by simp [NormValues]), hNat_554]

/-- The norm's field reads `F_q`'s facts. -/
instance instFalconAFieldNorm : AField (interp (FalconNorm.fA program)) :=
  (FalconAHonest.norm_fA (program := program)).symm ▸ (inferInstance : AField (interp 1))

/-- **The norm's and the encoding's predicates hold on the honest values**
(`Norm.preds_honest` at `hIn`). -/
theorem norm_honest (hy : y.Valid) (h : ∀ v ∈ NormValues program, val v = algVal program y v) :
    ∀ q ∈ [FalconNorm.p0 program, FalconNorm.p0 program + 1, FalconNorm.p0 program + 2,
      FalconNorm.p0 program + 3, FalconNorm.p0 program + 4, FalconNorm.p0 program + 5,
      FalconNorm.p0 program + 6, FalconNorm.p0 program + 7, FalconNorm.p0 program + 8,
      FalconNorm.p0 program + 9, FalconNorm.pDc program, FalconNorm.pEncB program,
      FalconNorm.pRange program, FalconNorm.pRange program + 1, FalconNorm.pRange program + 2,
      FalconNorm.pRange program + 3, FalconNorm.pRange program + 4, FalconNorm.pRange program + 5,
      FalconNorm.pHigh program, FalconNorm.pSlack program],
      program.HoldsAt (program.srcEnv interp x val c π) (program.predicate q).body :=
  Norm.preds_honest (hIn_valid hy) (normVals h)

end HonestNorm

/-! ## The signature equation -/

/-- `q − 1` is `−1` in `F_q`. -/
theorem q_neg_one : ((12288 : ℕ) : (interp 1).K) = -1 := by
  have h0 : ((12289 : ℕ) : (interp 1).K) = 0 := CharP.cast_eq_zero _ 12289
  push_cast at h0 ⊢
  linear_combination h0


section Signature

set_option maxRecDepth 4096

/-- The key's operator block: the negacyclic product with the inverse transform of
`statement.hhat`. -/
theorem block_negacyclic (e : program.Env interp) (z : ℕ → (interp 1).K) {i : ℕ} (hi : i < 512) :
    RealizedProgram.NamedOp.block program 1 (program.reader e) (.negacyclicConv 544 (.ntt 10302)) z i =
      LatticeCrypto.negacyclicConvCoeff
        (RealizedProgram.Ops.toFin 512 (RealizedProgram.Ops.inverseNtt 512 ((10302 : ℕ) : (interp 1).K)
          (fun s => (RealizedProgram.castElt (program.reader e 544 s) : (interp 1).K))))
        (RealizedProgram.Ops.toFin 512 z) ⟨i, hi⟩ := by
  have hsz : (program.value 544).size = 512 := FalconACore.hhatSize
  simp only [RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.formPoly, RealizedProgram.Ops.negacyclic]
  generalize (program.value 544).size = n at hsz ⊢
  subst hsz
  try dsimp only
  simp only [AField.decode_eq]
  exact RealizedProgram.Ops.ofFin_of_lt (R := (interp 1).K) _ hi

/-- The samples' operator block: each sample from its `16` bits. -/
theorem block_fromDigits (e : program.Env interp) (z : ℕ → (interp 1).K) {i : ℕ} (hi : i < 512) :
    RealizedProgram.NamedOp.block program 1 (program.reader e) (.batched 512 (.fromDigits 16 2)) z i =
      ∑ l : Fin 16, ((2 ^ (l : ℕ) : ℕ) : (interp 1).K) * z (i * 16 + l) := by
  simp only [RealizedProgram.NamedOp.block, RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, RealizedProgram.Ops.fromDigits, Nat.mul_one,
    Nat.div_one, Nat.mod_one, ite_true, if_pos hi, Nat.cast_pow]
  try dsimp only
  simp only [AField.decode_eq]

end Signature

/-- **The bits of a sample in `F_q`**: `Σ_l 2^l bit_l(c) = c mod 2^16`. -/
theorem sum_bits_zmod (n : ℕ) :
    ∑ l : Fin 16, ((2 ^ (l : ℕ) : ℕ) : ZMod 12289) * ((n / 2 ^ (l : ℕ) % 2 : ℕ) : ZMod 12289) =
      ((n % 2 ^ 16 : ℕ) : ZMod 12289) := by
  rw [← Bits.natOfBits_constBit (K := ZMod 12289) (m := 16) n]
  unfold Bits.natOfBits Bits.constBit
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ (l : ℕ)) with h0 | h1
  · rw [h0]
    simp
  · rw [h1]
    simp

section HonestSignature

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

/-- **The honest signature rows in `F_q`**: `s₁ + h s₂ = c` (`honestSignature_eq`). -/
theorem sig_zmod (hy : y.Valid) (i : Fin 512) :
    ((Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) y.pk.h y.samples y.signature i : ℕ) :
        ZMod 12289) +
      LatticeCrypto.negacyclicConvCoeff (Rows.keyVec (F := ZMod 12289) y.pk.h)
        (fun b => ((Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) y.signature b : ℕ) :
          ZMod 12289)) i =
      ∑ l : Fin 16, ((2 ^ (l : ℕ) : ℕ) : ZMod 12289) *
        ((y.samples i / 2 ^ (l : ℕ) % 2 : ℕ) : ZMod 12289) := by
  rw [sum_bits_zmod, Nat.mod_eq_of_lt (Emulated.samples_lt hy i)]
  have := Falcon512.NativeAlgebraCircuit.Honest.honestSignature_eq (F := ZMod 12289) y.pk.h y.samples
    y.signature i
  rw [this]
  exact sub_add_cancel _ _

theorem rdA545 (h : ∀ v ∈ NormValues program, val v = algVal program y v) {j : ℕ} (hj : j < 8192) :
    rdA (program.srcEnv interp x val c π) 545 j =
      ((y.samples ⟨j / 16, by have : falcon512.n = 512 := rfl; omega⟩ / 2 ^ (j % 16) % 2 : ℕ) :
        (interp 1).K) := by
  rw [rdA_algVal h (by simp [NormValues]) (by
    have : (program.value 545).size = 8192 := FalconAHonest.sizes_H (program := program)
    rw [this]; exact hj)]
  unfold hNat
  simp only [ite_true, hj, ↓reduceDIte]

theorem rdA545_bool (h : ∀ v ∈ NormValues program, val v = algVal program y v) {j : ℕ} (hj : j < 8192) :
    rdA (program.srcEnv interp x val c π) 545 j = 0 ∨ rdA (program.srcEnv interp x val c π) 545 j = 1 := by
  rw [rdA545 h hj]
  rcases Nat.mod_two_eq_zero_or_one (y.samples ⟨j / 16, by have : falcon512.n = 512 := rfl; omega⟩ /
    2 ^ (j % 16)) with h0 | h1
  · left; rw [h0, Nat.cast_zero]
  · right; rw [h1, Nat.cast_one]

theorem rdA546 (h : ∀ v ∈ NormValues program, val v = algVal program y v) {t : ℕ} (ht : t < 512) :
    rdA (program.srcEnv interp x val c π) 546 t =
      ((Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) y.signature ⟨t, ht⟩ : ℕ) :
        (interp 1).K) := by
  rw [rdA_algVal h (by simp [NormValues]) (by rw [(FalconAAlg.sizes_sig (program := program)).1]; exact ht)]
  rw [hNat_546, nS2_hIn ht]

set_option maxRecDepth 4096 in
/-- **`signature.equation` (`mod_q`) holds** on the honest values at the honest key: modulo `q`,
`s₁ + h s₂ = c` (`sig_zmod`), read through the constant coordinates (`applyInt_cast`,
`coord0_keyPoly`). -/
theorem sig284_honest (hy : y.Valid) (hx : keyOf x = some y.pk)
    (h : ∀ v ∈ NormValues program, val v = algVal program y v) :
    program.HoldsAt (program.srcEnv interp x val c π) (program.predicate (FalconAAlg.pSig program)).body := by
  set e := program.srcEnv interp x val c π
  obtain ⟨_, hpb⟩ := FalconAAlg.sig (program := program)
  rw [hpb]
  intro i hi
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (FalconAAlg.sizes_sig (program := program)).2] at hi
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12289).1 ?_
  have h546 : ∀ t < 512, φq (coord0 (rdA e 546 t)) = rdA e 546 t := fun t ht => by
    rw [rdA546 h ht, coord0_natCast, map_natCast]
  have h545 : ∀ t < 8192, φq (coord0 (rdA e 545 t)) = rdA e 545 t := fun t ht =>
    φq_coord0_bool (rdA545_bool h ht)
  have hcN : RealizedProgram.NamedOp.cols program (.negacyclicConv 544 (.ntt 10302)) = 512 := (FalconAAlg.ops_sig (program := program)).1
  have hrN : RealizedProgram.NamedOp.rows program (.negacyclicConv 544 (.ntt 10302)) = 512 := (FalconAAlg.ops_sig (program := program)).2.1
  have hcB : RealizedProgram.NamedOp.cols program (.batched 512 (.fromDigits 16 2)) = 8192 := (FalconAAlg.ops_sig (program := program)).2.2.1
  have hrB : RealizedProgram.NamedOp.rows program (.batched 512 (.fromDigits 16 2)) = 512 := (FalconAAlg.ops_sig (program := program)).2.2.2
  rw [Int.cast_sub, sub_eq_zero, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_apply,
    RealizedProgram.evalIntWith_apply, Int.cast_add, RealizedProgram.evalIntWith_leaf,
    applyInt_cast e _ (FalconAHonest.a_checks (program := program) 546 (by simp)).2.1 (FalconAHonest.a_checks (program := program) 546 (by simp)).2.2
      (fun t ht => h546 t (hcN ▸ ht)) (hrN ▸ hi),
    applyInt_cast e _ (FalconAHonest.a_checks (program := program) 545 (by simp)).2.1 (FalconAHonest.a_checks (program := program) 545 (by simp)).2.2
      (fun t ht => h545 t (hcB ▸ ht)) (hrB ▸ hi),
    block_negacyclic e _ hi, block_fromDigits e _ hi,
    coord0_negacyclicConvCoeff _ (RealizedProgram.Ops.toFin 512 fun t => rdA e 546 t)
      (fun t => h546 t t.isLt), map_sum]
  change ((ia e 547 i : ℤ) : ZMod 12289) + _ = _
  have h547 : ia e 547 i =
      (Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) y.pk.h y.samples y.signature
        ⟨i, hi⟩ : ℕ) := by
    refine ia_algVal h (by simp [NormValues]) (by rw [(FalconAAlg.sizes_sig (program := program)).2]; exact hi) ?_ |>.trans ?_
    · rw [hNat_547, nS1_hIn hi]
      exact ZMod.val_lt _
    · rw [hNat_547, nS1_hIn hi]
  rw [h547, Int.cast_natCast]
  have hx' : keyOf e.stmt = some y.pk := hx
  have hkey1 : ∀ a : Fin 512, coord0 (RealizedProgram.Ops.toFin 512 (RealizedProgram.Ops.inverseNtt 512
      ((10302 : ℕ) : (interp 1).K) (fun s => (RealizedProgram.castElt (program.reader e 544 s) : (interp 1).K))) a) =
      Falcon512.coeff y.pk.h ⟨a, a.isLt⟩ := fun a => by
    rw [RealizedProgram.Ops.toFin_apply]
    exact coord0_keyPoly hx' a.isLt
  have hkey : (fun a : Fin 512 => coord0 (RealizedProgram.Ops.toFin 512 (RealizedProgram.Ops.inverseNtt 512
      ((10302 : ℕ) : (interp 1).K) (fun s => (RealizedProgram.castElt (program.reader e 544 s) : (interp 1).K))) a)) =
      Rows.keyVec (F := ZMod 12289) y.pk.h := by
    funext a
    rw [hkey1 a]
    unfold Rows.keyVec
    exact (ZMod.natCast_zmod_val _).symm
  have hs2 : (fun b : Fin 512 => coord0 (RealizedProgram.Ops.toFin 512 (fun t => rdA e 546 t) b)) =
      fun b => ((Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) y.signature b : ℕ) :
        ZMod 12289) := by
    funext b
    rw [RealizedProgram.Ops.toFin_apply, rdA546 h b.isLt, coord0_natCast]
    rfl
  rw [hkey, hs2]
  have hc : ∀ l : Fin 16, coord0 (((2 ^ (l : ℕ) : ℕ) : (interp 1).K) * rdA e 545 (i * 16 + l)) =
      ((2 ^ (l : ℕ) : ℕ) : ZMod 12289) *
        ((y.samples ⟨i, hi⟩ / 2 ^ (l : ℕ) % 2 : ℕ) : ZMod 12289) := fun l => by
    rw [rdA545 h (by omega), ← map_natCast φq, coord0_φq_mul, coord0_natCast]
    have e2 : (i * 16 + (l : ℕ)) % 16 = l := by omega
    have e3 : (i * 16 + (l : ℕ)) / 16 = i := by omega
    simp only [e2, e3]
  simp only [hc]
  exact sig_zmod hy ⟨i, hi⟩


set_option maxRecDepth 4096 in
/-- **The key's polynomial in `F_q^9`** at the honest statement: the inverse transform of
`statement.hhat` is the key's coefficients (`KeyNTT.inverseNtt_keyHat`, `map_inverseNtt`). -/
theorem keyF_honest (hx : x = stmtOf y.pk) (a : Fin 512) :
    RealizedProgram.Ops.toFin 512 (RealizedProgram.Ops.inverseNtt 512 ((10302 : ℕ) : (interp 1).K)
      (fun s => RealizedProgram.castElt (program.reader (program.srcEnv interp x val c π) 544 s))) a =
      Rows.keyVec (F := (interp 1).K) y.pk.h a := by
  have hread : program.reader (program.srcEnv interp x val c π) 544 = x 544 :=
    RealizedProgram.reader_of_opaque_nil _ (name := "statement.hhat") (FalconAAlg.hhatKind (program := program))
  rw [RealizedProgram.Ops.toFin_apply, hread]
  rw [RealizedProgram.Ops.inverseNtt_congr (y := fun m => φq (RealizedProgram.Ops.ofFin (fun j => (KeyNTT.keyHat y.pk j :
    ZMod 12289)) m)) (fun m hm => ?_)]
  · rw [show ((10302 : ℕ) : (interp 1).K) = φq KeyNTT.psi512 by
        rw [show KeyNTT.psi512 = ((10302 : ℕ) : ZMod 12289) from (Nat.cast_ofNat).symm,
          map_natCast],
      ← RealizedProgram.Ops.map_inverseNtt, KeyNTT.inverseNtt_keyHat y.pk a.isLt]
    unfold Rows.keyVec
    exact φq_apply _
  · rw [hx, stmtOf_hhat y.pk ⟨m, hm⟩, RealizedProgram.Ops.ofFin_of_lt _ hm, map_natCast]
    exact RealizedProgram.castElt_castElt_of_eq (FalconACore.hhatField (program := program)).symm _

end HonestSignature


/-- **The bits of a sample in a field**: `Σ_l 2^l bit_l(c) = c mod 2^16`. -/
theorem sum_bits_field {K : Type*} [Field K] [DecidableEq K] (n : ℕ) :
    ∑ l : Fin 16, (2 : K) ^ (l : ℕ) * ((n / 2 ^ (l : ℕ) % 2 : ℕ) : K) = ((n % 2 ^ 16 : ℕ) : K) := by
  rw [← Bits.natOfBits_constBit (K := K) (m := 16) n]
  unfold Bits.natOfBits Bits.constBit
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ (l : ℕ)) with h0 | h1
  · rw [h0]
    simp
  · rw [h1]
    simp

section HonestSignatureField

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

set_option maxRecDepth 4096 in
/-- **`signature.equation` (field form) holds** on the honest values at the honest statement:
`s₁ + h s₂ − c = 0` in `F_q^9` (`honestSignature_eq`, `keyF_honest`). -/
theorem sig265_honest (hy : y.Valid) (hx : x = stmtOf y.pk)
    (h : ∀ v ∈ NormValues program, val v = algVal program y v) :
    program.HoldsAt (program.srcEnv interp x val c π) (program.predicate (FalconAHonest.pSigE program)).body := by
  set e := program.srcEnv interp x val c π
  obtain ⟨_, hpb⟩ := FalconAHonest.sigE_body (program := program)
  rw [hpb]
  refine holdsWith_equal1_of fun i hi => ?_
  have hi' : i < 512 := by
    rw [FalconAHonest.sigE_len (program := program)] at hi; exact hi
  have hrN : RealizedProgram.NamedOp.rows program (.negacyclicConv 544 (.ntt 10302)) = 512 := (FalconAAlg.ops_sig (program := program)).2.1
  have hcN : RealizedProgram.NamedOp.cols program (.negacyclicConv 544 (.ntt 10302)) = 512 := (FalconAAlg.ops_sig (program := program)).1
  change program.evalE _ 1 (.add (.add (.leaf 547) (.apply (.negacyclicConv 544 (.ntt 10302))
      (.leaf 546))) (.scale (.const 12288) (.apply (.batched 512 (.fromDigits 16 2))
        (.leaf 545)))) i = program.evalE _ 1 (.leaf 44) i
  rw [RealizedProgram.evalE_leaf_of_isConstant _ (FalconAHonest.const44 (program := program)).1,
    RealizedProgram.constRead_of_valueField (FalconAHonest.const44 (program := program)).2.1,
    show (program.constEntries 44).getD i 0 = 0 by
      rw [(FalconAHonest.const44 (program := program)).2.2,
        List.getD_eq_getElem?_getD, List.getElem?_replicate]
      split <;> rfl,
    RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_apply_batched_fromDigits _ _ (by norm_num), RealizedProgram.evalE_apply]
  unfold RealizedProgram.NamedOp.apply
  rw [hrN, hcN, Nat.div_eq_of_lt hi', Nat.mod_eq_of_lt hi', Nat.zero_mul]
  simp only [Nat.zero_add]
  rw [block_negacyclic e _ hi']
  change rdA e 547 i + _ + _ = (interp 1).decode 0
  have h547 : rdA e 547 i = ((Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) y.pk.h y.samples
      y.signature ⟨i, hi'⟩ : ℕ) : (interp 1).K) := by
    rw [rdA_algVal h (by simp [NormValues]) (by rw [(FalconAAlg.sizes_sig (program := program)).2]; exact hi')]
    rw [hNat_547, nS1_hIn hi']
  have hkey : RealizedProgram.Ops.toFin 512 (RealizedProgram.Ops.inverseNtt 512 ((10302 : ℕ) : (interp 1).K)
      (fun s => (RealizedProgram.castElt (program.reader e 544 s) : (interp 1).K))) =
      Rows.keyVec (F := (interp 1).K) y.pk.h := funext (keyF_honest hx)
  have hs2 : RealizedProgram.Ops.toFin 512 (fun t => program.evalE (program.reader e) 1 (.leaf 546) t) =
      fun j : Fin 512 => ((Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) y.signature j : ℕ) :
        (interp 1).K) := by
    funext j
    rw [RealizedProgram.Ops.toFin_apply]
    exact rdA546 h j.isLt
  have hbits : ∑ l : Fin 16, (interp 1).decode 2 ^ (l : ℕ) *
      program.evalE (program.reader e) 1 (.leaf 545) (i * 16 + l) =
      ((y.samples ⟨i, hi'⟩ : ℕ) : (interp 1).K) := by
    rw [← Nat.mod_eq_of_lt (Emulated.samples_lt hy ⟨i, hi'⟩), ← sum_bits_field]
    refine Finset.sum_congr rfl fun l _ => ?_
    change (interp 1).decode 2 ^ (l : ℕ) * rdA e 545 (i * 16 + l) = _
    rw [rdA545 h (by omega), decode_A]
    have e2 : (i * 16 + (l : ℕ)) % 16 = l := by omega
    have e3 : (i * 16 + (l : ℕ)) / 16 = i := by omega
    simp only [e2, e3]
    push_cast
    rfl
  rw [h547, hkey, hs2, hbits, decode_A, decode_A, q_neg_one (FH := FH) (FA := FA)]
  have hsig := Falcon512.NativeAlgebraCircuit.Honest.honestSignature_eq (F := (interp 1).K) y.pk.h y.samples
    y.signature ⟨i, hi'⟩
  rw [hsig]
  push_cast
  ring_nf
  exact neg_add_cancel _

end HonestSignatureField

/-! ## The crossing -/

section HonestCrossing

variable [FalconHHonest program] [FalconHSelHonest program] [FalconHConsts program FH]
  [FalconSelField program FH FA]

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

/-- **The type check of `c_A` holds**: the honest sample bits are bits. -/
theorem cABool_honest (h : ∀ v ∈ NormValues program, val v = algVal program y v) :
    program.HoldsAt (program.srcEnv interp x val c π) (program.predicate (FalconAHonest.pCA program)).body := by
  obtain ⟨_, hcb⟩ := FalconAHonest.ca_body (program := program)
  rw [RealizedProgram.HoldsAt, hcb]
  refine holdsWith_equal1_of fun j hj => ?_
  have hsz : (program.value 545).size = 8192 := FalconAHonest.sizes_H (program := program)
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_leaf, hsz] at hj
  have key : rdA (program.srcEnv interp x val c π) 545 j * rdA (program.srcEnv interp x val c π) 545 j =
      rdA (program.srcEnv interp x val c π) 545 j := by
    rcases rdA545_bool h hj with h0 | h1
    · rw [h0, mul_zero]
    · rw [h1, mul_one]
  exact key

/-- **A constant's bit as a field element** is the cast of the bit. -/
theorem constBit_eq_cast {K : Type*} [Field K] (n b : ℕ) :
    Bits.constBit (K := K) n b = ((n / 2 ^ b % 2 : ℕ) : K) := by
  unfold Bits.constBit
  rcases Nat.mod_two_eq_zero_or_one (n / 2 ^ b) with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

/-- The raw view's bit `j mod 16` of sample `j / 16` (`hNat` at `c_A`). -/
theorem raw_honest (hsel : ∀ v ∈ [539, 541, 542], val v = selVal program FH FA y v) {j : ℕ} (hj : j < 8192) :
    program.evalE (program.reader (program.srcEnv interp x val c π)) 0 (.leaf 540) j =
      ((hNat program y 545 j : ℕ) : (interp 0).K) := by
  have := congrFun (selWord_honest (x := x) (c := c) (π := π) hsel ⟨j / 16, by omega⟩)
    ⟨j % 16, by omega⟩
  simp only [selWord, RealizedProgram.SelectShape.word, RealizedProgram.wordAt] at this
  rw [show (j / 16) * 16 + j % 16 = j by omega] at this
  have hsf := selField (program := program)
  revert this
  generalize RealizedProgram.SelectShape.field program selShape = f at hsf ⊢
  subst hsf
  intro this
  refine this.trans ?_
  rw [constBit_eq_cast]
  unfold hNat
  simp only [ite_true, hj, ↓reduceDIte]
  rfl

theorem hNat545_lt (j : ℕ) : hNat program y 545 j < 2 := by
  unfold hNat
  simp only [ite_true]
  split_ifs
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

set_option maxRecDepth 4096 in
/-- **`mac.equal` holds at the source environment** on the honest values: the raw view and `c_A`
are the same sample bits. -/
theorem cross_honest (hsel : ∀ v ∈ [539, 541, 542], val v = selVal program FH FA y v)
    (h : ∀ v ∈ NormValues program, val v = algVal program y v) :
    program.HoldsAt (program.srcEnv interp x val c π) (program.predicate (FalconAHonest.pMac program)).body := by
  obtain ⟨_, _, hmb, hwid⟩ := FalconAHonest.mac_body (program := program)
  rw [RealizedProgram.HoldsAt, hmb]
  have hsz : program.exprLen (.leaf 540) = 8192 := by
    rw [RealizedProgram.exprLen_leaf]; exact (FalconACore.raw_facts (program := program)).2.1
  have hf540' : program.valueField 540 = 0 := (FalconAHonest.cross_fields (program := program)).1
  have hf540 : program.valueField 540 = program.domainField 0 :=
    hf540'.trans (FalconHBase.domainField0 (program := program)).symm
  have hf545 : program.valueField 545 = program.domainField 1 :=
    (FalconAHonest.cross_fields (program := program)).2.trans
      (FalconACore.domainField1 (program := program)).symm
  have hbit : ∀ j < 8192, (interp (program.domainField 0)).toNat
      (program.evalWith (program.reader (program.srcEnv interp x val c π)) 0 (.leaf 540) j) =
      hNat program y 545 j := by
    intro j hj
    have h1 : (interp (program.domainField 0)).toNat
        (program.evalWith (program.reader (program.srcEnv interp x val c π)) 0 (.leaf 540) j) =
        (interp (program.valueField 540)).toNat (program.reader (program.srcEnv interp x val c π) 540 j) := by
      unfold RealizedProgram.evalWith
      rw [RealizedProgram.evalE_leaf]
      exact RealizedProgram.toNat_castElt_of_eq hf540 _
    have h2 : (interp 0).toNat
        (program.evalE (program.reader (program.srcEnv interp x val c π)) 0 (.leaf 540) j) =
        (interp (program.valueField 540)).toNat (program.reader (program.srcEnv interp x val c π) 540 j) := by
      rw [RealizedProgram.evalE_leaf]
      exact RealizedProgram.toNat_castElt_of_eq hf540' _
    rw [h1, ← h2, raw_honest hsel hj]
    rcases (show hNat program y 545 j = 0 ∨ hNat program y 545 j = 1 by have := hNat545_lt (program := program) (y := y) j; omega)
      with h0 | h0 <;> rw [h0]
    · rw [Nat.cast_zero]
      exact HField.toNat_zero (FH := FH)
    · rw [Nat.cast_one]
      exact HField.toNat_one (FH := FH)
  have hbitA : ∀ j < 8192, (interp (program.domainField 1)).toNat
      (program.evalWith (program.reader (program.srcEnv interp x val c π)) 1 (.leaf 545) j) =
      hNat program y 545 j := by
    intro j hj
    have h1 : (interp (program.domainField 1)).toNat
        (program.evalWith (program.reader (program.srcEnv interp x val c π)) 1 (.leaf 545) j) =
        (interp 1).toNat (rdA (program.srcEnv interp x val c π) 545 j) := by
      unfold rdA RealizedProgram.evalWith
      rw [RealizedProgram.evalE_leaf, RealizedProgram.evalE_leaf, RealizedProgram.toNat_castElt_of_eq hf545,
        RealizedProgram.toNat_castElt_of_eq (FalconAHonest.cross_fields (program := program)).2]
    rw [h1, rdA_algVal h (by simp [NormValues]) (by
      have : (program.value 545).size = 8192 := FalconAHonest.sizes_H (program := program)
      rw [this]; exact hj)]
    exact AField.toNat_natCast (FA := FA) (by have := hNat545_lt (program := program) (y := y) j; omega)
  simp only [RealizedProgram.HoldsWith]
  rw [hsz]
  refine ⟨fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [hbitA j hj]
    exact lt_of_lt_of_le (hNat545_lt (program := program) j)
      ((Nat.pow_le_pow_right (by norm_num) hwid).trans_eq' (by norm_num))
  · rw [hbit j hj, hbitA j hj]

end HonestCrossing

end GordieHowe.Falcon512.Native.ROMParams
