-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Frontend.Statement
public import GordieHowe.Applications.Falcon512.Emulated.Interp
public import GordieHowe.Applications.Falcon512.Emulated.System.Algebra
public import GordieHowe.Foundations.Algebra.PowModOrder
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity
public import GordieHowe.Language.Realizations.Derivation.TableKernel

@[expose] public section

/-!
# GordieHowe frontend: the Falcon ring carriers

The frontend of the theorem at the realized program for the Falcon ring carriers (`Falcon512.Ring.Carrier.ROMParams` and
`Falcon512.Ring.Carrier.QROMParams`, export `5d775ae1`: Falcon's arithmetic modulo `q` emulated over a
Goldilocks extension), generic in the program and its interpretation at the program facts
`FalconCarrierBase` (decided per program; the two programs agree on every value, shared
expression and predicate) and the field facts `GordieHowe.Falcon512.EField`:

* **The membership** is the Falcon rings' (`GordieHowe.Falcon512.Ring.FalconRingMember`, at the Goldilocks
  transform root `ψ = psiG`, a primitive `1024`-th root of unity, `psiG_isPrimitiveRoot`).
* **The signature equation** (`signature.equation`, the integer congruence
  `c − s1 ≡ h · s2 (mod q)` of the product form): its right side is the negacyclic product by the
  polynomial whose spectrum the committed spectrum holds. Without the membership's event the spectrum
  is the transform of the signer's key, so that polynomial is the key, whose coefficients are below
  `q` (`evalIntWith_carrierSigN`); the congruence is Falcon's (`Emulated.Rows.Congruent`).
* **The magnitudes, the norm and the encoding** (`magnitudes.s1`, `magnitudes.s2`, `norm.sum`, the
  ranges of `mag1`, `mag2`, `low2`, the budget and the norm, `encoding.high2`) are Falcon
  emulated's (`GordieHowe.Falcon512.Emulated.algebraSpec_of_congruent`), which gives the relation
  `GordieHowe.Falcon512.Ring.rel` at the extracted values (`mem_rel_of_source_carrier`).
* **Round-by-round knowledge soundness of `Π_P₀`** (`rbr_carrier`): `GordieHowe.RealizedProgram.rbr_of_events` at the
  membership's event, error `511/|F|` at `member.ring.gamma`.
-/


namespace GordieHowe.Falcon512.Ring

open GordieHowe.Bits IOP Emulated.Params
open scoped NNReal ENNReal

/-! ## The Goldilocks constants -/

/-- **The constant `−1`** of the Goldilocks fields: `p − 1`. -/
abbrev mOneG : ℕ := 18446744069414584320

/-- **The Goldilocks transform root** `ψ` of the carriers (`11353340290879379826`). -/
abbrev psiG : ℕ := 11353340290879379826

/-- **An emulated program's field** reads `p − 1` as `−1`. -/
instance (FA : RealizedProgram.FieldInterp) [EField FA] : RingField FA mOneG where
  decode_negOne := by
    rw [EField.decode_lt _ (by norm_num [pGold])]
    have h0 : ((pGold : ℕ) : FA.K) = 0 := CharP.cast_eq_zero _ pGold
    have : (mOneG : ℕ) + 1 = pGold := by norm_num [pGold]
    rw [← this] at h0
    push_cast at h0
    linear_combination h0
  decode_zero := by rw [EField.decode_lt _ (by norm_num [pGold]), Nat.cast_zero]
  decode_one := by rw [EField.decode_lt _ (by norm_num [pGold]), Nat.cast_one]
  toNat_zero := by
    have := EField.toNat_natCast (FA := FA) (k := 0) (by norm_num [pGold])
    rwa [Nat.cast_zero] at this
  toNat_one := by
    have := EField.toNat_natCast (FA := FA) (k := 1) (by norm_num [pGold])
    rwa [Nat.cast_one] at this

/-- `ψ ^ 512 = −1` modulo `p` (one `powMod` value). -/
theorem psiG_pow_zmod : (psiG : ZMod pGold) ^ 2 ^ 9 = -1 :=
  powMod_eq_neg_one_of_eq (by norm_num [pGold]) (by decide)

section Root

variable {K : Type*} [Field K] [CharP K pGold]

/-- `ψ ^ 512 = −1` in every field of characteristic `p`. -/
theorem psiG_pow : (psiG : K) ^ 512 = -1 := by
  have h := congrArg (ZMod.castHom (dvd_refl pGold) K) psiG_pow_zmod
  rw [map_pow, map_natCast, map_neg, map_one] at h
  simpa using h

/-- `ψ` is a primitive `1024`-th root of unity in every field of characteristic `p`. -/
theorem psiG_isPrimitiveRoot : IsPrimitiveRoot (psiG : K) (2 * 512) := by
  have h1 : (-1 : K) ≠ 1 := by
    intro h
    have h2 : ((2 : ℕ) : K) = 0 := by
      push_cast
      linear_combination -h
    rw [CharP.cast_eq_zero_iff K pGold] at h2
    norm_num [pGold] at h2
  have := IsPrimitiveRoot.of_pow_two_pow_eq_neg_one (n := 9) h1 (by simpa using psiG_pow (K := K))
  simpa using this

/-- `512` is nonzero in every field of characteristic `p`. -/
theorem natCast_512_ne_zero : ((512 : ℕ) : K) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff K pGold]
  norm_num [pGold]

end Root

/-- **A natural-order transform is the negacyclic spectrum** at any root. -/
theorem nttNatural_eq_negSpectrum' {K : Type*} [Field K] (ψ : K) (x : ℕ → K) (k : Fin 512) :
    RealizedProgram.Ops.nttNatural 512 ψ x k = DFT.negSpectrum ψ (fun j : Fin 512 => x j) k := by
  rw [RealizedProgram.Ops.nttNatural_apply 512 _ _ k.isLt, DFT.negSpectrum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.mul_comm]


/-! ## The integer reading of a negacyclic coefficient -/

section Coef

variable {FA : RealizedProgram.FieldInterp} [EField FA]

/-- **The constant coordinate of an integer's cast** is its cast. -/
theorem coord0_intCast (w : ℤ) : EField.coord0 (FA := FA) (w : FA.K) = (w : ZMod pGold) := by
  rcases w with n | n
  · rw [Int.ofNat_eq_natCast, Int.cast_natCast, Int.cast_natCast, EField.coord0_natCast]
  · rw [Int.cast_negSucc, Int.cast_negSucc, map_neg, EField.coord0_natCast]

/-- **The integer reading of a negacyclic coefficient** of entries whose integer readings are
naturals below `p/2` is the coefficient of those naturals: the integer reading reads the constant
coordinate, which is additive (`EField.coord0`). -/
theorem coefInt_negCoef_E (n : ℕ) {h : ℕ → FA.K} {z : ℕ → ℕ}
    (hz : ∀ s < n, FA.toNat (h s) = z s ∧ 2 * z s < pGold) (j k : ℕ) :
    FA.coefInt (RealizedProgram.Ops.negCoef n h j k) =
      RealizedProgram.Ops.negCoef n (fun s => (z s : ℤ)) j k := by
  set w := RealizedProgram.Ops.negCoef n (fun s => (z s : ℤ)) j k with hw
  have hsmall : 2 * |w| < (pGold : ℤ) := by
    rcases RealizedProgram.Ops.negCoef_signed n (fun s => (z s : ℤ)) j k with h0 | ⟨i, hi, h1 | h1⟩
    · rw [hw, h0]
      norm_num [pGold]
    · rw [hw, h1, abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast (hz i hi).2
    · rw [hw, h1, abs_neg, abs_of_nonneg (Int.natCast_nonneg _)]
      exact_mod_cast (hz i hi).2
  have hc : EField.coord0 (FA := FA) (RealizedProgram.Ops.negCoef n h j k) = (w : ZMod pGold) := by
    rw [RealizedProgram.Ops.negCoef_map, hw,
      show ((RealizedProgram.Ops.negCoef n (fun s => (z s : ℤ)) j k : ℤ) : ZMod pGold) =
        Int.castAddHom (ZMod pGold) (RealizedProgram.Ops.negCoef n (fun s => (z s : ℤ)) j k) from rfl,
      RealizedProgram.Ops.negCoef_map, RealizedProgram.Ops.negCoef_eq, RealizedProgram.Ops.negCoef_eq]
    have he : ∀ s < n, EField.coord0 (FA := FA) (h s) = (Int.castAddHom (ZMod pGold)) (z s : ℤ) := by
      intro s hs
      show _ = (((z s : ℤ)) : ZMod pGold)
      rw [Int.cast_natCast, ← (hz s hs).1, EField.toNat_eq, ZMod.natCast_zmod_val]
    split_ifs with h1 h2 h2
    · rw [he _ h1.2, he _ h2.2]
    · rw [he _ h1.2]
    · rw [he _ h2.2]
    · rfl
  have htn : ∀ k < pGold, FA.toNat (k : FA.K) = k := fun k hk => EField.toNat_natCast hk
  have h1 : FA.toNat (RealizedProgram.Ops.negCoef n h j k) = FA.toNat ((w : ℤ) : FA.K) := by
    rw [EField.toNat_eq, EField.toNat_eq, hc, coord0_intCast]
  have h2 := RealizedProgram.FieldInterp.coefInt_intCast EField.spec_char EField.charP htn hsmall
  unfold RealizedProgram.FieldInterp.coefInt at h2 ⊢
  rw [h1]
  exact h2

/-- **A negacyclic coefficient of `512` naturals is the single-sum convolution weight**
(`Emulated.Rows.convWeight`). -/
theorem negCoef_eq_convWeight (z : ℕ → ℕ) (i k : Fin 512) :
    RealizedProgram.Ops.negCoef 512 (fun s => (z s : ℤ)) i k =
      Emulated.Rows.convWeight ℤ (fun t : Fin 512 => z t) i k := by
  rw [RealizedProgram.Ops.negCoef_eq, Emulated.Rows.convWeight]
  have hi := i.isLt
  have hk := k.isLt
  by_cases hki : (k : ℕ) ≤ i
  · rw [dif_pos hki, if_pos ⟨hki, by omega⟩, if_neg (by omega), sub_zero]
  · rw [dif_neg hki, if_neg (by omega), if_pos ⟨by omega, by omega⟩, zero_sub,
      show (i : ℕ) + 512 - k = 512 + i - k by omega]

end Coef

/-! ## The program facts -/

/-- **The carriers' signature equation's left side** (`signature.equation`): `c − s1`. -/
def carrierSigP : RealizedProgram.Expr :=
  .add (.leaf 5) (.scale (.const mOneG) (.leaf 10))

/-- **The carriers' signature equation's right side** (`signature.equation`): the negacyclic
product of `s2` by the polynomial whose natural-order spectrum (at `ψ = psiG`) the committed
spectrum holds. -/
def carrierSigN : RealizedProgram.Expr :=
  .apply (.negacyclicConv 6 (.nttNatural psiG)) (.leaf 9)

/-- **A magnitude equation** `(mag − s)(mag − (q − s)) = 0` of the value `s` at the magnitude
`mag`. -/
def magLhs (mag s : ℕ) : RealizedProgram.Expr :=
  .mul (.add (.leaf mag) (.scale (.const mOneG) (.leaf s)))
    (.add (.leaf mag) (.scale (.const mOneG) (.add (.scale (.const mOneG) (.leaf s))
      (.reindex [(0, 0, 512)] (.leaf 2)))))

/-- **The norm's left side** (`norm.sum`): `squares − Σ mag1² − Σ mag2²`. -/
def normLhs : RealizedProgram.Expr :=
  .add (.add (.leaf 16) (.scale (.const mOneG) (.apply (.sum 512) (.mul (.leaf 12) (.leaf 12)))))
    (.scale (.const mOneG) (.apply (.sum 512) (.mul (.leaf 13) (.leaf 13))))

/-- **The encoding budget's expression**: `50176 − Σ mag2 + Σ low2`. -/
def budgetExpr : RealizedProgram.Expr :=
  .add (.add (.scale (.const mOneG) (.apply (.sum 512) (.leaf 13))) (.apply (.sum 512) (.leaf 14)))
    (.leaf 15)

/-- **The program facts of a Falcon ring carrier outside the membership** (decided per program):
the numbering (`statement.ring` `4`, `statement.c` `5`, `key.spectrum` `6`, `s2` `9`,
`signature.s1` `10`, the quotient `signature.equation.q` `11`, `magnitudes.mag1` `12`,
`magnitudes.mag2` `13`, `encoding.low2` `14`, the budget offset `15`, `norm.squares` `16`, `q` at
`2`, the zero row `3`); the signature equation (predicate `4`, the spectral product form with
quotient `11`), the magnitudes (`1`, `2`), the norm (`3`), the ranges (`10` … `15`) and
`encoding.high2` (`17`), source predicates; the constants; the fields, sizes and types of the
values read. -/
class FalconCarrierBase (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
    [FalconRingMember program] : Prop where
  /-- The numbering of the membership's values. -/
  ids : FalconRingMember.ring program = 4 ∧ FalconRingMember.chal program = 5 ∧
    FalconRingMember.spec program = 6 ∧ FalconRingMember.s2 program = 9 ∧
    FalconRingMember.mOne program = mOneG ∧ FalconRingMember.psi program = psiG ∧
    FalconRingMember.zero program = 1
  /-- `signature.equation`: `c − s1 ≡ h · s2 (mod q)` in the spectral product form, its quotient
  `11` from `−6291457`, at most `12570625`. -/
  sig : ∃ real, (program.predicate 4).body = .mod 0 12289 carrierSigP carrierSigN real ∧
    real.form = .spectralProduct ∧ real.quotient = some (.leaf 11) ∧
    real.quotientLo = -6291457 ∧ real.qmax = 12570625
  /-- `magnitudes.s1`. -/
  magS1 : ∃ t, (program.predicate 1).body = .equal 0 (magLhs 12 10) (.leaf 3) t
  /-- `magnitudes.s2`. -/
  magS2 : ∃ t, (program.predicate 2).body = .equal 0 (magLhs 13 9) (.leaf 3) t
  /-- `norm.sum`. -/
  normSum : ∃ t, (program.predicate 3).body = .equal 0 normLhs (.leaf 1) t
  /-- `magnitudes.mag1`. -/
  rMag1 : ∃ r, (program.predicate 10).body = .mem 0 [.leaf 12] (.range 6145) r
  /-- `magnitudes.mag2`. -/
  rMag2 : ∃ r, (program.predicate 11).body = .mem 0 [.leaf 13] (.range 2048) r
  /-- `encoding.low2`. -/
  rLow2 : ∃ r, (program.predicate 12).body = .mem 0 [.leaf 14] (.range 128) r
  /-- `encoding.budget`. -/
  rBudget : ∃ r, (program.predicate 13).body = .mem 0 [budgetExpr] (.range 50177) r
  /-- `norm.bound`. -/
  rNorm : ∃ r, (program.predicate 14).body = .mem 0 [.leaf 16] (.range 34034727) r
  /-- `signature.equation.q`. -/
  rQuot : ∃ r, (program.predicate 15).body = .mem 0 [.leaf 11] (.range 8589934592) r
  /-- `encoding.high2`, not in a product form. -/
  high2 : ∃ r, (program.predicate 17).body = .mod 0 128 (.leaf 13) (.leaf 14) r ∧
    r.form.isProduct = false
  /-- The predicates read are source predicates. -/
  inSource : ∀ p ∈ [1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 17],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- The constants: `q`, the zero row, the budget offset. -/
  consts : program.isConstant 2 = true ∧ (program.constEntries 2).getD 0 0 = 12289 ∧
    program.isConstant 3 = true ∧ program.constEntries 3 = List.replicate 512 0 ∧
    program.isConstant 15 = true ∧ (program.constEntries 15).getD 0 0 = 50176
  /-- The values read are of field `0`. -/
  fields : ∀ v ∈ [2, 3, 10, 11, 12, 13, 14, 15, 16], program.valueField v = 0
  /-- The sizes of the values read. -/
  sizes : (program.value 10).size = 512 ∧ (program.value 11).size = 512 ∧
    (program.value 12).size = 512 ∧ (program.value 13).size = 512 ∧
    (program.value 14).size = 512 ∧ (program.value 16).size = 1
  /-- `signature.s1`, `magnitudes.mag2` and `encoding.low2` are committed. -/
  privKinds : (program.value 10).kind = .priv ∧ (program.value 13).kind = .priv ∧
    (program.value 14).kind = .priv
  /-- The statement's checks bound the keys (value `4`) below `q`. -/
  ringCheck : ∃ m ∈ program.statement.checks,
    program.memberValue? m.member = some 4 ∧ m.entryBound? = some 12289
  /-- The statement's checks bound the challenge (value `5`) below `q`. -/
  chalCheck : ∃ m ∈ program.statement.checks,
    program.memberValue? m.member = some 5 ∧ m.entryBound? = some 12289

/-! ## Soundness -/

section Sound

open Emulated (PublicKey)
open Native (CoreWit)

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] {I : RealizedProgram.Interp} [EField (I 0)]

/-- **A carrier's field facts at its constant `−1`** (`p − 1`). -/
theorem ringField_carrier : RingField (I 0) (FalconRingMember.mOne program) := by
  rw [(FalconCarrierBase.ids (program := program)).2.2.2.2.1]
  infer_instance

attribute [local instance] ringField_carrier

/-- **A carrier predicate holds** where the source program holds. -/
theorem holdsAt_carrier {e : program.Env I} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 17]) :
    program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (RealizedProgram.predicate_mem (FalconCarrierBase.inSource p hp).1)
    (FalconCarrierBase.inSource p hp).2

/-- **A range membership of one record** of domain `0` gives a natural below the bound. -/
theorem natBelow_mem0 {e : program.Env I} {r : RealizedProgram.Expr} {n : ℕ} {real : RealizedProgram.InRealization}
    (h : program.HoldsAt e (.mem 0 [r] (.range n) real)) {i : ℕ} (hi : i < program.exprLen r) :
    ∃ k < n, program.evalE (program.reader e) 0 r i = (k : (I 0).K) := by
  have := h i hi
  obtain ⟨k, hk, hkv⟩ := this r (List.mem_singleton_self r)
  refine ⟨k, hk, ?_⟩
  unfold RealizedProgram.evalWith at hkv
  rw [FalconRingMember.domainField0 (program := program)] at hkv
  exact hkv

/-- **A value of domain `0`** read in field `0`. -/
abbrev rdC (e : program.Env I) (v i : ℕ) : (I 0).K :=
  program.evalE (program.reader e) 0 (.leaf v) i

/-- A constant of field `0` below `p` reads its cast. -/
theorem rdC_const {e : program.Env I} {v c i : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 0) (he : (program.constEntries v).getD i 0 = c)
    (hcp : c < pGold) : rdC e v i = (c : (I 0).K) := by
  unfold rdC
  rw [RealizedProgram.evalE_leaf_of_isConstant e hc, RealizedProgram.constRead_of_valueField hf, he,
    EField.decode_lt _ hcp]

theorem rdC_q (e : program.Env I) : rdC e 2 0 = (12289 : ℕ) := by
  obtain ⟨c2, e2, -⟩ := FalconCarrierBase.consts (program := program)
  exact rdC_const c2 ((FalconCarrierBase.fields (program := program)) 2 (by simp)) e2
    (by norm_num [pGold])

theorem rdC_off (e : program.Env I) : rdC e 15 0 = (50176 : ℕ) := by
  obtain ⟨-, -, -, -, c15, e15⟩ := FalconCarrierBase.consts (program := program)
  exact rdC_const c15 ((FalconCarrierBase.fields (program := program)) 15 (by simp)) e15
    (by norm_num [pGold])

theorem rdC_zeros (e : program.Env I) {i : ℕ} (hi : i < 512) : rdC e 3 i = 0 := by
  obtain ⟨-, -, c3, e3, -⟩ := FalconCarrierBase.consts (program := program)
  rw [rdC_const c3 ((FalconCarrierBase.fields (program := program)) 3 (by simp)) (c := 0)
    (by rw [e3, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]; rfl)
    (by norm_num [pGold]), Nat.cast_zero]

theorem decode_mOneG : (I 0).decode mOneG = -1 := RingField.decode_negOne

/-- **A magnitude equation's left side** at coordinate `i < 512`: `(mag − s)(mag − (q − s))`. -/
theorem evalE_magLhs (e : program.Env I) (mag v : ℕ) {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) 0 (magLhs mag v) i =
      (rdC e mag i - rdC e v i) * (rdC e mag i - ((12289 : ℕ) - rdC e v i)) := by
  have hq := rdC_q (program := program) e
  rw [magLhs, RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_scale_const, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_zero hi, decode_mOneG]
  unfold rdC at hq ⊢
  rw [hq]
  ring

/-- **The magnitude equations** (`magnitudes.s1`, `magnitudes.s2`): at every coordinate,
`(mag − s)(mag − (q − s)) = 0`. -/
theorem mag_eq {e : program.Env I} (hs : program.SourceSatAt e) {p mag v : ℕ}
    (hp : p ∈ [1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 17])
    (hb : ∃ t, (program.predicate p).body = .equal 0 (magLhs mag v) (.leaf 3) t)
    (hsz : (program.value mag).size = 512) {i : ℕ} (hi : i < 512) :
    (rdC e mag i - rdC e v i) * (rdC e mag i - ((12289 : ℕ) - rdC e v i)) = 0 := by
  obtain ⟨t, hbd⟩ := hb
  have h := holdsAt_carrier hs hp
  rw [hbd] at h
  have hx := holdsAt_equal0 h i (by
    rw [magLhs, RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, hsz]
    exact hi)
  rw [evalE_magLhs e mag v hi] at hx
  change _ = rdC e 3 i at hx
  rw [rdC_zeros e hi] at hx
  exact hx

/-- The zero constant `1` reads `0`. -/
theorem rdC_zero1 (e : program.Env I) :
    program.evalE (program.reader e) 0 (.leaf 1) 0 = 0 := by
  have h1 := evalE_zero (program := program) e
  rw [(FalconCarrierBase.ids (program := program)).2.2.2.2.2.2] at h1
  exact h1

/-- **The norm's left side**: `squares − Σ mag1² − Σ mag2²`. -/
theorem evalE_normLhs (e : program.Env I) :
    program.evalE (program.reader e) 0 normLhs 0 = rdC e 16 0 - ∑ i : Fin 512, rdC e 12 i * rdC e 12 i -
      ∑ i : Fin 512, rdC e 13 i * rdC e 13 i := by
  rw [normLhs, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_scale_const, RealizedProgram.evalE_apply_sum, RealizedProgram.evalE_apply_sum, decode_mOneG]
  simp only [Nat.zero_mul, Nat.zero_add, RealizedProgram.evalE_mul]
  unfold rdC
  ring

theorem exprLen_normLhs : program.exprLen normLhs = 1 := by
  rw [normLhs, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf,
    (FalconCarrierBase.sizes (program := program)).2.2.2.2.2]

/-- **The norm's equation** (`norm.sum`): `squares − Σ mag1² − Σ mag2² = 0`. -/
theorem norm_eq {e : program.Env I} (hs : program.SourceSatAt e) :
    rdC e 16 0 - ∑ i : Fin 512, rdC e 12 i * rdC e 12 i -
      ∑ i : Fin 512, rdC e 13 i * rdC e 13 i = 0 := by
  obtain ⟨t, hbd⟩ := FalconCarrierBase.normSum (program := program)
  have h := holdsAt_carrier hs (p := 3) (by simp)
  rw [hbd] at h
  have hx := holdsAt_equal0 h 0 (by rw [exprLen_normLhs]; norm_num)
  rw [rdC_zero1, evalE_normLhs] at hx
  exact hx

/-- **The statement's keys and challenge are below `q`** where the statement passes the checks. -/
theorem stmt_lt {x : program.Valuation I} (hok : program.StatementOk I x) :
    (∀ i < 32768, (I 0).toNat (ringEntry x i) < 12289) ∧
      ∀ i < 512, (I 0).toNat (chalEntry x i) < 12289 := by
  obtain ⟨h5, hc5, -, -, -, -, -⟩ := FalconCarrierBase.ids (program := program)
  obtain ⟨m, hm, hv, hq⟩ := FalconCarrierBase.ringCheck (program := program)
  obtain ⟨m', hm', hv', hq'⟩ := FalconCarrierBase.chalCheck (program := program)
  have H := hok m hm
  have H' := hok m' hm'
  unfold RealizedProgram.MemberHolds at H H'
  rw [hv, hq] at H
  rw [hv', hq'] at H'
  have hf5 : program.valueField 4 = 0 := by
    have := (FalconRingMember.fields (program := program)) (FalconRingMember.ring program) (by simp)
    rwa [h5] at this
  have hf6 : program.valueField 5 = 0 := by
    have := (FalconRingMember.fields (program := program)) (FalconRingMember.chal program) (by simp)
    rwa [hc5] at this
  have hs5 : (program.value 4).size = 32768 := by
    have := (FalconRingMember.sizes (program := program)).2.2.1
    rwa [h5] at this
  have hs6 : (program.value 5).size = 512 := by
    have := (FalconRingMember.sizes (program := program)).2.2.2.1
    rwa [hc5] at this
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · unfold ringEntry
    rw [h5, RealizedProgram.toNat_castElt hf5]
    exact H i (by rw [hs5]; exact hi)
  · unfold chalEntry
    rw [hc5, RealizedProgram.toNat_castElt hf6]
    exact H' i (by rw [hs6]; exact hi)

/-- **The coefficients of a ring key with entries below `q`** are the entries read as naturals. -/
theorem keyCoeffs_ringKey_of_lt {x : program.Valuation I} {r : ℕ}
    (h : ∀ j : Fin falcon512.n, (I 0).toNat (ringEntry x (r * 512 + j)) < 12289)
    (j : Fin falcon512.n) :
    EmulatedAlgebraCircuit.keyCoeffs (ringKey x r).h j = (I 0).toNat (ringEntry x (r * 512 + j)) := by
  simp only [ringKey, EmulatedAlgebraCircuit.keyCoeffs, Falcon512.coeff_ofCoeff, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (h j)

/-- **The centred reading of `p − 1`** is `−1`. -/
theorem centered_mOneG : (I 0).centered mOneG = -1 := by
  rw [RealizedProgram.FieldInterp.centered_eq, EField.spec_char]
  unfold RealizedProgram.centeredZ
  norm_num [pGold]

/-- **The signature equation has `512` coordinates.** -/
theorem exprLen_carrierSigP : program.exprLen carrierSigP = 512 := by
  obtain ⟨-, hc5, -⟩ := FalconCarrierBase.ids (program := program)
  have hs5 : (program.value 5).size = 512 := by
    have := (FalconRingMember.sizes (program := program)).2.2.2.1
    rwa [hc5] at this
  rw [carrierSigP, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, hs5]

/-- **The signature equation's left side on the integers**: `c − s1`, both read as naturals. -/
theorem evalIntWith_carrierSigP (e : program.Env I) (i : ℕ) :
    program.evalIntWith (program.reader e) 0 carrierSigP i =
      ((I 0).toNat (chalEntry e.stmt i) : ℤ) - ((I 0).toNat (rdC e 10 i) : ℤ) := by
  obtain ⟨-, hc5, -⟩ := FalconCarrierBase.ids (program := program)
  have hk5 : (program.value 5).kind = .pub (.opaque "statement.c" []) := by
    have := FalconRingMember.chalKind (program := program)
    rwa [hc5] at this
  have hf5 : program.valueField 5 = 0 := by
    have := (FalconRingMember.fields (program := program)) (FalconRingMember.chal program) (by simp)
    rwa [hc5] at this
  have hf10 := (FalconCarrierBase.fields (program := program)) 10 (by simp)
  have hk10 := (FalconCarrierBase.privKinds (program := program)).1
  rw [carrierSigP, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const,
    RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf,
    FalconRingMember.domainField0 (program := program), centered_mOneG]
  unfold RealizedProgram.intOf
  rw [hk5, hk10]
  simp only
  unfold chalEntry rdC
  rw [hc5, RealizedProgram.toNat_castElt hf5, RealizedProgram.evalE_leaf,
    RealizedProgram.toNat_castElt hf10, RealizedProgram.reader_of_opaque_nil e hk5]
  ring

/-- **The signature equation's right side on the integers**, at a polynomial whose spectrum the
committed spectrum holds with coefficients read as naturals `z` below `p/2`: the negacyclic
coefficients of `z` against `s2` read as naturals. -/
theorem evalIntWith_carrierSigN (e : program.Env I) {z : ℕ → ℕ}
    (hz : ∀ s < 512, (I 0).toNat
      (RealizedProgram.Ops.inverseNttNatural 512 (psiG : (I 0).K) (specOf e) s) = z s ∧ 2 * z s < pGold)
    {i : ℕ} (hi : i < 512) :
    program.evalIntWith (program.reader e) 0 carrierSigN i =
      ∑ k : Fin 512, RealizedProgram.Ops.negCoef 512 (fun s => (z s : ℤ)) i k *
        ((I 0).toNat (s2Of e k) : ℤ) := by
  obtain ⟨-, -, h6, h9, -, -, -⟩ := FalconCarrierBase.ids (program := program)
  have hs6 : (program.value 6).size = 512 := by
    have := (FalconRingMember.sizes (program := program)).2.1
    rwa [h6] at this
  have hf9 : program.valueField 9 = 0 := by
    have := (FalconRingMember.fields (program := program)) (FalconRingMember.s2 program) (by simp)
    rwa [h9] at this
  have hk9 : (program.value 9).kind = .priv := by
    have := (FalconRingMember.privKinds (program := program)).2.2
    rwa [h9] at this
  have hd := FalconRingMember.domainField0 (program := program)
  rw [carrierSigN, RealizedProgram.evalIntWith_apply,
    RealizedProgram.NamedOp.applyInt_negacyclicConv _ _ _ _ _ (by rw [hs6]; norm_num), hs6,
    Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
  simp only [Nat.zero_mul, Nat.zero_add]
  rw [hd]
  have hpoly : RealizedProgram.NamedOp.formPoly (I := I) 0 512
      (fun s => RealizedProgram.castElt (program.reader e 6 s)) (.nttNatural psiG) =
      RealizedProgram.Ops.inverseNttNatural 512 (psiG : (I 0).K) (specOf e) := by
    funext s
    show RealizedProgram.Ops.inverseNttNatural 512 ((I 0).decode psiG)
      (fun s => RealizedProgram.castElt (program.reader e 6 s)) s = _
    rw [EField.decode_lt _ (by norm_num [pGold])]
    unfold specOf
    rw [h6]
    rfl
  rw [hpoly]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coefInt_negCoef_E 512 hz, RealizedProgram.evalIntWith_leaf]
  unfold RealizedProgram.intOf s2Of
  rw [hk9, h9, RealizedProgram.evalE_leaf, RealizedProgram.toNat_castElt hf9]

/-- **The signature equation's sides differ by a multiple of `q`** where the source program holds
(`signature.equation`, the congruence of the product form). -/
theorem sig_dvd_carrier {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 512) :
    (12289 : ℤ) ∣ program.evalIntWith (program.reader e) 0 carrierSigP i -
      program.evalIntWith (program.reader e) 0 carrierSigN i := by
  obtain ⟨real, hb, -⟩ := FalconCarrierBase.sig (program := program)
  have h := holdsAt_carrier hs (p := 4) (by simp)
  rw [hb] at h
  exact_mod_cast h.1 i (by rw [exprLen_carrierSigP]; exact hi)

/-- **A leaf of domain `0` below a bound**, from its range. -/
theorem leaf_natBelow {e : program.Env I} (hs : program.SourceSatAt e) {p v n : ℕ}
    (hp : p ∈ [1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 17])
    (hb : ∃ r, (program.predicate p).body = .mem 0 [.leaf v] (.range n) r)
    {sz : ℕ} (hsz : (program.value v).size = sz) (i : Fin sz) :
    ∃ k < n, rdC e v i = (k : (I 0).K) := by
  obtain ⟨r, hbd⟩ := hb
  have h := holdsAt_carrier hs hp
  rw [hbd] at h
  exact natBelow_mem0 h (by rw [RealizedProgram.exprLen_leaf, hsz]; exact i.isLt)

/-- **The integer reading of a committed natural below `p`** is the natural. -/
theorem intOf_priv {e : program.Env I} {v i n : ℕ} (hk : (program.value v).kind = .priv)
    (hf : program.valueField v = 0) (hr : rdC e v i = (n : (I 0).K)) (hn : n < pGold) :
    program.intOf (program.reader e) v i = n := by
  unfold RealizedProgram.intOf
  rw [hk]
  unfold rdC at hr
  rw [RealizedProgram.evalE_leaf] at hr
  have h := congrArg (I 0).toNat hr
  rw [RealizedProgram.toNat_castElt hf, EField.toNat_natCast hn] at h
  simp only [h]

/-- **The signature congruence** where the source program holds without the membership's event:
the spectrum is the transform of the signer's key (`spec_eq_of_not_event`), so the kernel's
polynomial is the key, whose coefficients are below `q` (`stmt_lt`); the product form's congruence
on the integers (`sig_dvd_carrier`) is `c ≡ s1 + h · s2 (mod q)`. -/
theorem congruent_carrier {e : program.Env I} (hok : program.StatementOk I e.stmt)
    (hs : program.SourceSatAt e) (hev : ¬ ringEvent 0 e) {s1N s2N : Fin 512 → ℕ}
    (hs1 : ∀ i : Fin 512, rdC e 10 i = (s1N i : (I 0).K) ∧ s1N i ≤ 12289)
    (hs2 : ∀ i : Fin 512, s2Of e i = (s2N i : (I 0).K) ∧ s2N i ≤ 12289) :
    Emulated.Rows.Congruent q
      (EmulatedAlgebraCircuit.keyCoeffs (ringKey e.stmt (idxOf e)).h) (chalNat e.stmt) s1N s2N := by
  obtain ⟨-, -, -, -, -, hpsi, -⟩ := FalconCarrierBase.ids (program := program)
  obtain ⟨hring, hchal⟩ := stmt_lt (program := program) hok
  have hidx := idxOf_lt e (memberPreds_of_source hs)
  have hh : ∀ j : Fin 512, (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + j)) < 12289 :=
    fun j => hring _ (by have := j.isLt; omega)
  set z : ℕ → ℕ := fun s => (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + s)) with hzdef
  -- the kernel's polynomial is the signer's key
  have hspec := spec_eq_of_not_event (memberPreds_of_source hs) hev
  have hz : ∀ s < 512, (I 0).toNat
      (RealizedProgram.Ops.inverseNttNatural 512 (psiG : (I 0).K) (specOf e) s) = z s ∧
        2 * z s < pGold := by
    intro s hs'
    have hinv : RealizedProgram.Ops.inverseNttNatural 512 (psiG : (I 0).K) (specOf e) s =
        ringEntry e.stmt (idxOf e * 512 + s) := by
      rw [RealizedProgram.Ops.inverseNttNatural_congr (y := RealizedProgram.Ops.nttNatural 512
          (psiG : (I 0).K) (fun c => ringEntry e.stmt (idxOf e * 512 + c))) fun m hm => by
          rw [hspec ⟨m, hm⟩, keySpec, hpsi, EField.decode_lt _ (by norm_num [pGold])],
        RealizedProgram.Ops.inverseNttNatural_nttNatural (psiG_isPrimitiveRoot (K := (I 0).K))
          (natCast_512_ne_zero (K := (I 0).K)) _ hs']
    refine ⟨by rw [hinv], ?_⟩
    have := hh ⟨s, hs'⟩
    change (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + s)) < 12289 at this
    simp only [hzdef]
    norm_num [pGold]
    omega
  rw [show EmulatedAlgebraCircuit.keyCoeffs (ringKey e.stmt (idxOf e)).h =
      fun j : Fin falcon512.n => (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + j)) from
    funext (keyCoeffs_ringKey_of_lt hh)]
  suffices H : ∀ i : Fin 512, (((I 0).toNat (chalEntry e.stmt i) : ℕ) : ZMod 12289) =
      (s1N i : ZMod 12289) + LatticeCrypto.negacyclicConvCoeff
        (fun j : Fin 512 => (z j : ZMod 12289)) (fun j => (s2N j : ZMod 12289)) i from fun i => H i
  intro i
  have hd := sig_dvd_carrier hs i.isLt
  rw [evalIntWith_carrierSigP, evalIntWith_carrierSigN e hz i.isLt] at hd
  have hs1i : (I 0).toNat (rdC e 10 i) = s1N i := by
    rw [(hs1 i).1, EField.toNat_natCast (by have := (hs1 i).2; norm_num [pGold]; omega)]
  have hs2k : ∀ k : Fin 512, (I 0).toNat (s2Of e k) = s2N k := fun k => by
    rw [(hs2 k).1, EField.toNat_natCast (by have := (hs2 k).2; norm_num [pGold]; omega)]
  simp only [hs1i, hs2k] at hd
  have hsum : ∑ k : Fin 512, RealizedProgram.Ops.negCoef 512 (fun s => (z s : ℤ)) i k * (s2N k : ℤ) =
      LatticeCrypto.negacyclicConvCoeff (fun k : Fin 512 => ((z k : ℕ) : ℤ)) (fun k => (s2N k : ℤ)) i := by
    exact (Finset.sum_congr rfl fun k _ => by rw [negCoef_eq_convWeight z i k]).trans
      (Emulated.Rows.sum_convWeight_eq_negacyclicConvCoeff (fun t : Fin 512 => z t) _ i)
  rw [hsum] at hd
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12289).2 hd
  rw [Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast,
    Emulated.Rows.intCast_negacyclicConvCoeff (fun t : Fin 512 => z t) s2N i] at hc
  linear_combination hc

/-- **Soundness of a carrier's source program without the membership's event**: the signature
congruence (`congruent_carrier`) with the magnitudes, the norm and the encoding budget, by Falcon
emulated's `algebraSpec_of_congruent`, gives the relation. -/
theorem mem_rel_of_source_carrier {e : program.Env I} (hok : program.StatementOk I e.stmt)
    (hs : program.SourceSatAt e) (hev : ¬ ringEvent 0 e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  classical
  obtain ⟨-, -, -, h9, -, -, -⟩ := FalconCarrierBase.ids (program := program)
  obtain ⟨hz10, -, hz12, hz13, hz14, hz16⟩ := FalconCarrierBase.sizes (program := program)
  obtain ⟨-, hk13, hk14⟩ := FalconCarrierBase.privKinds (program := program)
  have hf : ∀ v ∈ [2, 3, 10, 11, 12, 13, 14, 15, 16], program.valueField v = 0 :=
    FalconCarrierBase.fields (program := program)
  -- the ranges
  choose mag1N hmag1N hmag1C using leaf_natBelow (e := e) hs (p := 10) (by simp)
    FalconCarrierBase.rMag1 hz12
  choose mag2N hmag2N hmag2C using leaf_natBelow (e := e) hs (p := 11) (by simp)
    FalconCarrierBase.rMag2 hz13
  choose low2N hlow2N hlow2C using leaf_natBelow (e := e) hs (p := 12) (by simp)
    FalconCarrierBase.rLow2 hz14
  obtain ⟨sq, hsqN, hsqC⟩ := leaf_natBelow (e := e) hs (p := 14) (by simp)
    FalconCarrierBase.rNorm hz16 ⟨0, by norm_num⟩
  -- the magnitudes
  have hm1 : ∀ i : Fin 512, (rdC e 12 i - rdC e 10 i) * (rdC e 12 i - ((12289 : ℕ) - rdC e 10 i)) = 0 :=
    fun i => mag_eq hs (p := 1) (by simp) FalconCarrierBase.magS1 hz12 i.isLt
  have hm2 : ∀ i : Fin 512, (rdC e 13 i - rdC e 9 i) * (rdC e 13 i - ((12289 : ℕ) - rdC e 9 i)) = 0 :=
    fun i => mag_eq hs (p := 2) (by simp) FalconCarrierBase.magS2 hz13 i.isLt
  have hs1R : ∀ i : Fin 512, Range.IsNatBelow (12289 + 1) (rdC e 10 i) := fun i =>
    EmulatedNorm.isNatBelow_of_centering ⟨mag1N i, by have := hmag1N i; omega, (hmag1C i).symm⟩ (hm1 i)
  have hs2R : ∀ i : Fin 512, Range.IsNatBelow (12289 + 1) (rdC e 9 i) := fun i =>
    EmulatedNorm.isNatBelow_of_centering ⟨mag2N i, by have := hmag2N i; omega, (hmag2C i).symm⟩ (hm2 i)
  choose s1N hs1N hs1C using hs1R
  choose s2N hs2N hs2C using hs2R
  have hs2Of : ∀ i : Fin 512, s2Of e i = (s2N i : (I 0).K) := fun i => by
    unfold s2Of
    rw [h9]
    exact (hs2C i).symm
  -- the signature congruence
  have hcong := congruent_carrier hok hs hev (s1N := s1N) (s2N := s2N)
    (fun i => ⟨(hs1C i).symm, Nat.le_of_lt_succ (hs1N i)⟩)
    (fun i => ⟨hs2Of i, Nat.le_of_lt_succ (hs2N i)⟩)
  have hidx := idxOf_lt e (memberPreds_of_source hs)
  -- the encoding budget
  have hlow : ∀ i : Fin 512, low2N i = mag2N i % 128 := by
    intro i
    obtain ⟨r, hbd, -⟩ := FalconCarrierBase.high2 (program := program)
    have h := holdsAt_carrier hs (p := 17) (by simp)
    rw [hbd] at h
    have hd := h.1 i (by rw [RealizedProgram.exprLen_leaf, hz13]; exact i.isLt)
    rw [RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf,
      intOf_priv hk13 (hf 13 (by simp)) (hmag2C i) (by have := hmag2N i; norm_num [pGold]; omega),
      intOf_priv hk14 (hf 14 (by simp)) (hlow2C i) (by have := hlow2N i; norm_num [pGold]; omega)] at hd
    obtain ⟨m, hm⟩ := hd
    have := hlow2N i
    omega
  have hbudget : ∑ i : Fin 512, mag2N i / 128 ≤ 392 := by
    obtain ⟨r, hbd⟩ := FalconCarrierBase.rBudget (program := program)
    have h := holdsAt_carrier hs (p := 13) (by simp)
    rw [hbd] at h
    obtain ⟨b, hb, hbv⟩ := natBelow_mem0 h (i := 0) (by
      rw [budgetExpr, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale,
        RealizedProgram.exprLen_apply]
      simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, RealizedProgram.exprLen_leaf, hz13])
    rw [budgetExpr, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
      RealizedProgram.evalE_apply_sum, RealizedProgram.evalE_apply_sum, decode_mOneG] at hbv
    change _ + rdC e 15 0 = _ at hbv
    rw [rdC_off] at hbv
    simp only [Nat.zero_mul, Nat.zero_add] at hbv
    change -1 * ∑ t : Fin 512, rdC e 13 t + ∑ t : Fin 512, rdC e 14 t + _ = _ at hbv
    simp only [hmag2C, hlow2C] at hbv
    have hcast : (((∑ t : Fin 512, low2N t) + 50176 : ℕ) : (I 0).K) =
        ((b + ∑ t : Fin 512, mag2N t : ℕ) : (I 0).K) := by
      push_cast
      linear_combination hbv
    have hl : ∑ t : Fin 512, low2N t ≤ 512 * 128 := by
      calc _ ≤ ∑ _t : Fin 512, 128 := Finset.sum_le_sum fun t _ => (hlow2N t).le
        _ = 512 * 128 := by simp
    have hm' : ∑ t : Fin 512, mag2N t ≤ 512 * 2048 := by
      calc _ ≤ ∑ _t : Fin 512, 2048 := Finset.sum_le_sum fun t _ => (hmag2N t).le
        _ = 512 * 2048 := by simp
    have hnat := IntLift.natCast_inj_of_lt (K := (I 0).K) (p := pGold)
      (by norm_num [pGold]; omega) (by norm_num [pGold]; omega) hcast
    have hsplit : ∑ t : Fin 512, mag2N t =
        ∑ t : Fin 512, low2N t + 128 * ∑ t : Fin 512, mag2N t / 128 := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hlow t]
      omega
    omega
  -- the algebra
  have hA := Emulated.algebraSpec_of_congruent (F := (I 0).K)
    (h := (ringKey e.stmt (idxOf e)).h) (c := chalNat e.stmt)
    (s1 := fun i => rdC e 10 i) (s2 := fun i => s2Of e i) (mag1 := fun i => rdC e 12 i)
    (mag2 := fun i => rdC e 13 i) (norm := rdC e 16 0) (s1N := s1N) (s2N := s2N) (mag2N := mag2N)
    (fun i => ⟨Nat.le_of_lt_succ (hs1N i), hs1C i⟩)
    (fun i => ⟨Nat.le_of_lt_succ (hs2N i), (hs2Of i).symm⟩)
    (fun i => ⟨mag1N i, hmag1N i, (hmag1C i).symm⟩)
    (fun i => ⟨hmag2N i, (hmag2C i).symm⟩)
    (fun i => hm1 i)
    (fun i => by
      have := hm2 i
      have h2 : s2Of e i = rdC e 9 i := by rw [hs2Of i]; exact hs2C i
      rw [h2]
      exact this)
    (norm_eq hs) ⟨sq, hsqN, hsqC.symm⟩ hbudget hcong
  refine ⟨by rw [proj_idx]; exact hidx, ?_, ?_⟩
  · show Falcon512.algebraOk falcon512 (ringKey e.stmt (proj e.stmt e.asg).idx).h _
      (proj e.stmt e.asg).s2.toRq
    rw [proj_idx, proj_s2]
    have h2 := Emulated.decodeS2Int_toRq (fun i : Fin falcon512.n => s2Of e i)
    erw [h2]
    exact hA.algebra
  · show Falcon512.EncodingBounds falcon512 (proj e.stmt e.asg).s2
    rw [proj_s2]
    exact hA.encoding

/-- **The relation from the source program without the event** (`RealizedProgram.rbr_of_events`'
`hsound`). -/
theorem sound_carrier :
    ∀ e : program.Env I, program.StatementOk I e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ ringEvent j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun _ hok hs hno => mem_rel_of_source_carrier hok hs
    (hno 0 ((FalconRingMember.isSourceChal_iff (program := program) 0).2 rfl))

/-- **Round-by-round knowledge soundness of `Π_P₀` for a Falcon ring carrier**
(`RealizedProgram.rbr_of_events`): the relation `rel`, the extractor `extractor`, the error `511/|F|` at
`member.ring.gamma` and `0` elsewhere (`ringEps`). -/
theorem rbr_carrier :
    rbrKnowledgeSoundness rel (program.sourceVerifier I) extractor
      (program.eventState I rel proj ringEvent ringEvent_use sound_carrier)
      (program.roundError I (ringEps I)) :=
  program.rbr_of_events I rel proj ringEvent (ringEps I) ringEvent_use ringEvent_bound sound_carrier

end Sound

end GordieHowe.Falcon512.Ring
