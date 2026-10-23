-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Frontend.Statement
public import GordieHowe.Applications.Falcon512.Emulated.Interp
public import GordieHowe.Applications.Falcon512.Emulated.System.Algebra
public import GordieHowe.Foundations.Algebra.PowModOrder
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity

@[expose] public section

/-!
# GordieHowe frontend: the Falcon ring carriers

The frontend of the theorem at the realized program for the Falcon ring carriers (`Falcon512.Ring.Carrier.ROMParams` and
`Falcon512.Ring.Carrier.QROMParams`, export `b65a4929`: Falcon's arithmetic modulo `q` emulated over a
Goldilocks extension), generic in the program and its interpretation at the program facts
`FalconCarrierBase` (decided per program; the two programs agree on every value, shared
expression and predicate) and the field facts `GordieHowe.Falcon512.EField`:

* **The membership** is the Falcon rings' (`GordieHowe.Falcon512.Ring.FalconRingMember`, at the Goldilocks
  transform root `ψ = psiG`, a primitive `1024`-th root of unity, `psiG_isPrimitiveRoot`).
* **The signature equation** (`sig_field`): without the membership's event the spectrum is the
  transform of the signer's key, and the transform is injective, so
  `c + bias − s1 − q · quot = h · s2` in the field; its projection onto the prime field
  (`primeProjE`, the constant coordinate) is the equation on the integer readings, whose sides stay
  below `p`, so `c ≡ s1 + h · s2 (mod q)` (`GordieHowe.Falcon512.Emulated.Rows.Congruent.of_field`).
* **The magnitudes, the norm and the encoding** (`magnitudes.s1`, `magnitudes.s2`, `norm.sum`, the
  ranges of `quot`, `mag1`, `mag2`, `low2`, the budget and the norm, `encoding.high2`) are Falcon
  emulated's (`GordieHowe.Falcon512.Emulated.algebraSpec_of_congruent`), which gives the relation
  `GordieHowe.Falcon512.Ring.rel` at the extracted values (`mem_rel_of_source`).
* **Round-by-round knowledge soundness of `Π_P₀`** (`rbr`): `GordieHowe.RealizedProgram.rbr_of_events` at the
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

/-! ## The projection onto the prime field -/

section Proj

variable {FA : RealizedProgram.FieldInterp} [EField FA]

/-- **The projection onto `F_p`**: `x ↦ (toNat x : K)`, additive. -/
noncomputable def primeProjE : FA.K →+ FA.K :=
  (EField.φp (FA := FA)).toAddMonoidHom.comp (EField.coord0 (FA := FA))

theorem primeProjE_apply (x : FA.K) : primeProjE x = ((FA.toNat x : ℕ) : FA.K) := by
  simp only [primeProjE, AddMonoidHom.coe_comp, Function.comp_apply,
    RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, EField.φp_apply,
    EField.toNat_eq]

theorem primeProjE_natCast (n : ℕ) : primeProjE (n : FA.K) = (n : FA.K) := by
  rw [primeProjE_apply, EField.toNat_eq, EField.coord0_natCast,
    ← EField.φp_apply, map_natCast]

theorem primeProjE_mul_natCast (a : FA.K) (n : ℕ) :
    primeProjE (a * (n : FA.K)) = primeProjE a * (n : FA.K) := by
  have hn : (n : FA.K) = EField.φp (n : ZMod pGold) := by simp
  rw [hn, _root_.mul_comm, primeProjE]
  simp only [AddMonoidHom.coe_comp, Function.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, EField.coord0_φp_mul, map_mul]
  ring

theorem primeProjE_negacyclic (h : Fin 512 → FA.K) (s : Fin 512 → ℕ) (k : Fin 512) :
    primeProjE (LatticeCrypto.negacyclicConvCoeff h (fun j => (s j : FA.K)) k) =
      LatticeCrypto.negacyclicConvCoeff (fun j => primeProjE (h j)) (fun j => (s j : FA.K)) k := by
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  split_ifs
  · exact primeProjE_mul_natCast _ _
  · rw [map_neg, primeProjE_mul_natCast]
  · exact map_zero _

end Proj

/-! ## The program facts -/

/-- **The carriers' signature equation's left side** (`signature.equation`):
`Ntt(c + bias − s1 − q · quot) − spectrum ⊙ Ntt(s2)`. -/
def carrierSigLhs : RealizedProgram.Expr :=
  .add (.apply (.ntt 512 psiG .natural) (.add (.add (.add (.leaf 6) (.reindex [(0, 0, 512)] (.leaf 2)))
      (.scale (.const mOneG) (.leaf 11))) (.scale (.const mOneG) (.scale (.const 12289) (.leaf 12)))))
    (.scale (.const mOneG) (.mul (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.leaf 7)))
      (.reindex [(0, 1, 512)] (.reindex [(0, 1, 512)] (.apply (.ntt 512 psiG .natural) (.leaf 10))))))

/-- **A magnitude equation** `(mag − s)(mag − (q − s)) = 0` of the value `s` at the magnitude
`mag`. -/
def magLhs (mag s : ℕ) : RealizedProgram.Expr :=
  .mul (.add (.leaf mag) (.scale (.const mOneG) (.leaf s)))
    (.add (.leaf mag) (.scale (.const mOneG) (.add (.scale (.const mOneG) (.leaf s))
      (.reindex [(0, 0, 512)] (.leaf 4)))))

/-- **The norm's left side** (`norm.sum`): `squares − Σ mag1² − Σ mag2²`. -/
def normLhs : RealizedProgram.Expr :=
  .add (.add (.leaf 17) (.scale (.const mOneG) (.apply (.sum 512) (.mul (.leaf 13) (.leaf 13)))))
    (.scale (.const mOneG) (.apply (.sum 512) (.mul (.leaf 14) (.leaf 14))))

/-- **The encoding budget's expression**: `50176 − Σ mag2 + Σ low2`. -/
def budgetExpr : RealizedProgram.Expr :=
  .add (.add (.scale (.const mOneG) (.apply (.sum 512) (.leaf 14))) (.apply (.sum 512) (.leaf 15)))
    (.leaf 16)

/-- **The program facts of a Falcon ring carrier outside the membership** (decided per program):
the numbering (`statement.ring` `5`, `statement.c` `6`, `key.spectrum` `7`, `s2` `10`,
`signature.s1` `11`, `signature.quot` `12`, `magnitudes.mag1` `13`, `magnitudes.mag2` `14`,
`encoding.low2` `15`, the budget offset `16`, `norm.squares` `17`, the bias `2`, the zero row `3`,
`q` at `4`); the signature equation (predicate `1`), the magnitudes (`2`, `3`), the norm (`4`), the
ranges (`10` … `15`) and `encoding.high2` (`17`), source predicates; the constants; the fields,
sizes and types of the values read. -/
class FalconCarrierBase (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
    [FalconRingMember program] : Prop where
  /-- The numbering of the membership's values. -/
  ids : FalconRingMember.ring program = 5 ∧ FalconRingMember.chal program = 6 ∧
    FalconRingMember.spec program = 7 ∧ FalconRingMember.s2 program = 10 ∧
    FalconRingMember.mOne program = mOneG ∧ FalconRingMember.psi program = psiG ∧
    FalconRingMember.zero program = 1
  /-- `signature.equation`. -/
  sig : ∃ t, (program.predicate 1).body = .equal 0 carrierSigLhs (.leaf 3) t
  /-- `magnitudes.s1`. -/
  magS1 : ∃ t, (program.predicate 2).body = .equal 0 (magLhs 13 11) (.leaf 3) t
  /-- `magnitudes.s2`. -/
  magS2 : ∃ t, (program.predicate 3).body = .equal 0 (magLhs 14 10) (.leaf 3) t
  /-- `norm.sum`. -/
  normSum : ∃ t, (program.predicate 4).body = .equal 0 normLhs (.leaf 1) t
  /-- `signature.quot`. -/
  rQuot : ∃ r, (program.predicate 10).body = .mem 0 [.leaf 12] (.range 8589934592) r
  /-- `magnitudes.mag1`. -/
  rMag1 : ∃ r, (program.predicate 11).body = .mem 0 [.leaf 13] (.range 6145) r
  /-- `magnitudes.mag2`. -/
  rMag2 : ∃ r, (program.predicate 12).body = .mem 0 [.leaf 14] (.range 2048) r
  /-- `encoding.low2`. -/
  rLow2 : ∃ r, (program.predicate 13).body = .mem 0 [.leaf 15] (.range 128) r
  /-- `encoding.budget`. -/
  rBudget : ∃ r, (program.predicate 14).body = .mem 0 [budgetExpr] (.range 50177) r
  /-- `norm.bound`. -/
  rNorm : ∃ r, (program.predicate 15).body = .mem 0 [.leaf 17] (.range 34034727) r
  /-- `encoding.high2`. -/
  high2 : ∃ r, (program.predicate 17).body = .mod 0 128 (.leaf 14) (.leaf 15) r
  /-- The predicates read are source predicates. -/
  inSource : ∀ p ∈ [1, 2, 3, 4, 10, 11, 12, 13, 14, 15, 17],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- The constants: the bias, the zero row, `q`, the budget offset. -/
  consts : program.isConstant 2 = true ∧ (program.constEntries 2).getD 0 0 = 77309435394 ∧
    program.isConstant 3 = true ∧ program.constEntries 3 = List.replicate 512 0 ∧
    program.isConstant 4 = true ∧ (program.constEntries 4).getD 0 0 = 12289 ∧
    program.isConstant 16 = true ∧ (program.constEntries 16).getD 0 0 = 50176
  /-- The values read are of field `0`. -/
  fields : ∀ v ∈ [2, 3, 4, 11, 12, 13, 14, 15, 16, 17], program.valueField v = 0
  /-- The sizes of the values read. -/
  sizes : (program.value 11).size = 512 ∧ (program.value 12).size = 512 ∧
    (program.value 13).size = 512 ∧ (program.value 14).size = 512 ∧
    (program.value 15).size = 512 ∧ (program.value 17).size = 1
  /-- `magnitudes.mag2` and `encoding.low2` are committed. -/
  privKinds : (program.value 14).kind = .priv ∧ (program.value 15).kind = .priv
  /-- The statement's checks bound the keys (value `5`) below `q`. -/
  ringCheck : ∃ m ∈ program.statement.checks,
    program.memberValue? m.member = some 5 ∧ m.entryBound? = some 12289
  /-- The statement's checks bound the challenge (value `6`) below `q`. -/
  chalCheck : ∃ m ∈ program.statement.checks,
    program.memberValue? m.member = some 6 ∧ m.entryBound? = some 12289

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

theorem rdC_q (e : program.Env I) : rdC e 4 0 = (12289 : ℕ) := by
  obtain ⟨-, -, -, -, c4, e4, -⟩ := FalconCarrierBase.consts (program := program)
  exact rdC_const c4 ((FalconCarrierBase.fields (program := program)) 4 (by simp)) e4
    (by norm_num [pGold])

theorem rdC_bias (e : program.Env I) : rdC e 2 0 = (77309435394 : ℕ) := by
  obtain ⟨c2, e2, -⟩ := FalconCarrierBase.consts (program := program)
  exact rdC_const c2 ((FalconCarrierBase.fields (program := program)) 2 (by simp)) e2
    (by norm_num [pGold])

theorem rdC_off (e : program.Env I) : rdC e 16 0 = (50176 : ℕ) := by
  obtain ⟨-, -, -, -, -, -, c16, e16⟩ := FalconCarrierBase.consts (program := program)
  exact rdC_const c16 ((FalconCarrierBase.fields (program := program)) 16 (by simp)) e16
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
    program.evalE (program.reader e) 0 normLhs 0 = rdC e 17 0 - ∑ i : Fin 512, rdC e 13 i * rdC e 13 i -
      ∑ i : Fin 512, rdC e 14 i * rdC e 14 i := by
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
    rdC e 17 0 - ∑ i : Fin 512, rdC e 13 i * rdC e 13 i -
      ∑ i : Fin 512, rdC e 14 i * rdC e 14 i = 0 := by
  obtain ⟨t, hbd⟩ := FalconCarrierBase.normSum (program := program)
  have h := holdsAt_carrier hs (p := 4) (by simp)
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
  have hf5 : program.valueField 5 = 0 := by
    have := (FalconRingMember.fields (program := program)) (FalconRingMember.ring program) (by simp)
    rwa [h5] at this
  have hf6 : program.valueField 6 = 0 := by
    have := (FalconRingMember.fields (program := program)) (FalconRingMember.chal program) (by simp)
    rwa [hc5] at this
  have hs5 : (program.value 5).size = 32768 := by
    have := (FalconRingMember.sizes (program := program)).2.2.1
    rwa [h5] at this
  have hs6 : (program.value 6).size = 512 := by
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

/-- **The carriers' signature equation's left side** at frequency `k < 512`:
`Ntt(c + bias − s1 − q · quot)_k − spectrum_k · Ntt(s2)_k`. -/
theorem evalE_carrierSigLhs (e : program.Env I) {k : ℕ} (hk : k < 512) :
    program.evalE (program.reader e) 0 carrierSigLhs k =
      RealizedProgram.Ops.nttNatural 512 (psiG : (I 0).K) (fun i => chalEntry e.stmt i + (77309435394 : ℕ) -
        rdC e 11 i - (12289 : ℕ) * rdC e 12 i) k -
        specOf e k * RealizedProgram.Ops.nttNatural 512 (psiG : (I 0).K) (s2Of e) k := by
  obtain ⟨-, hc6, h7, h10, -, -, -⟩ := FalconCarrierBase.ids (program := program)
  have hdec : (I 0).decode psiG = (psiG : (I 0).K) := EField.decode_lt _ (by norm_num [pGold])
  rw [carrierSigLhs, RealizedProgram.evalE_add, evalE_apply_ntt _ psiG _ hk,
    RealizedProgram.evalE_scale_const, decode_mOneG, RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_step_one hk, Nat.zero_add, RealizedProgram.IndexMap.entry_step_one hk, Nat.zero_add,
    evalE_apply_ntt _ psiG _ hk, hdec]
  have hc : RealizedProgram.Ops.nttNatural 512 (psiG : (I 0).K) (program.evalE (program.reader e) 0
      (.add (.add (.add (.leaf 6) (.reindex [(0, 0, 512)] (.leaf 2)))
        (.scale (.const mOneG) (.leaf 11))) (.scale (.const mOneG) (.scale (.const 12289) (.leaf 12)))))
      k = RealizedProgram.Ops.nttNatural 512 (psiG : (I 0).K) (fun i => chalEntry e.stmt i + (77309435394 : ℕ) -
        rdC e 11 i - (12289 : ℕ) * rdC e 12 i) k := by
    refine RealizedProgram.NamedOp.nttNatural_congr (fun i hi => ?_) k
    rw [RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
      RealizedProgram.evalE_scale_const, RealizedProgram.evalE_scale_const, decode_mOneG,
      EField.decode_lt _ (by norm_num [pGold]), RealizedProgram.evalE_reindex,
      RealizedProgram.IndexMap.entry_step_zero hi]
    change _ + rdC e 2 0 + _ + _ = _
    rw [rdC_bias, RealizedProgram.evalE_leaf,
      RealizedProgram.reader_of_opaque_nil e (hc6 ▸ FalconRingMember.chalKind (program := program))]
    unfold chalEntry rdC
    rw [hc6]
    ring
  rw [hc]
  unfold specOf s2Of
  rw [h7, h10]
  ring

theorem exprLen_carrierSigLhs : program.exprLen carrierSigLhs = 512 := by
  obtain ⟨-, hc6, -⟩ := FalconCarrierBase.ids (program := program)
  have hs6 : (program.value 6).size = 512 := by
    have := (FalconRingMember.sizes (program := program)).2.2.2.1
    rwa [hc6] at this
  rw [carrierSigLhs, RealizedProgram.exprLen_add, RealizedProgram.exprLen_apply, RealizedProgram.exprLen_add,
    RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, hs6]
  simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols]

/-- **The signature equation** (`signature.equation`): where the source program holds,
`Ntt(c + bias − s1 − q · quot)_k = spectrum_k · Ntt(s2)_k` at every frequency `k < 512`. -/
theorem sig_eq_carrier {e : program.Env I} (hs : program.SourceSatAt e) {k : ℕ} (hk : k < 512) :
    RealizedProgram.Ops.nttNatural 512 (psiG : (I 0).K) (fun i => chalEntry e.stmt i + (77309435394 : ℕ) -
        rdC e 11 i - (12289 : ℕ) * rdC e 12 i) k =
      specOf e k * RealizedProgram.Ops.nttNatural 512 (psiG : (I 0).K) (s2Of e) k := by
  obtain ⟨t, hb⟩ := FalconCarrierBase.sig (program := program)
  have h := holdsAt_carrier hs (p := 1) (by simp)
  rw [hb] at h
  have hx := holdsAt_equal0 h k (by rw [exprLen_carrierSigLhs]; exact hk)
  change _ = rdC e 3 k at hx
  rw [rdC_zeros e hk, evalE_carrierSigLhs e hk] at hx
  exact sub_eq_zero.1 hx

/-- **A coordinate of a leaf of domain `0` below a bound**, from its range. -/
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

/-- **Soundness of a carrier's source program without the membership's event**: the spectrum is
the transform of the signer's key (`spec_eq_of_not_event`), the signature equation is
`c + bias − s1 − q · quot = h · s2` in the field (`sig_eq_carrier`, the transform's injectivity),
whose projection onto `F_p` (`primeProjE`) is the integer congruence
(`Rows.Congruent.of_field`); with the magnitudes, the norm and the encoding budget,
Falcon emulated's `algebraSpec_of_congruent` gives the relation. -/
theorem mem_rel_of_source_carrier {e : program.Env I} (hok : program.StatementOk I e.stmt)
    (hs : program.SourceSatAt e) (hev : ¬ ringEvent 0 e) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  classical
  obtain ⟨h5, hc6, h7, h10, hm, hpsi, -⟩ := FalconCarrierBase.ids (program := program)
  obtain ⟨hz11, hz12, hz13, hz14, hz15, hz17⟩ := FalconCarrierBase.sizes (program := program)
  obtain ⟨hk14, hk15⟩ := FalconCarrierBase.privKinds (program := program)
  have hf : ∀ v ∈ [2, 3, 4, 11, 12, 13, 14, 15, 16, 17], program.valueField v = 0 :=
    FalconCarrierBase.fields (program := program)
  -- the ranges
  choose quotN hquotN hquotC using leaf_natBelow (e := e) hs (p := 10) (by simp)
    FalconCarrierBase.rQuot hz12
  choose mag1N hmag1N hmag1C using leaf_natBelow (e := e) hs (p := 11) (by simp)
    FalconCarrierBase.rMag1 hz13
  choose mag2N hmag2N hmag2C using leaf_natBelow (e := e) hs (p := 12) (by simp)
    FalconCarrierBase.rMag2 hz14
  choose low2N hlow2N hlow2C using leaf_natBelow (e := e) hs (p := 13) (by simp)
    FalconCarrierBase.rLow2 hz15
  obtain ⟨sq, hsqN, hsqC⟩ := leaf_natBelow (e := e) hs (p := 15) (by simp)
    FalconCarrierBase.rNorm hz17 ⟨0, by norm_num⟩
  -- the magnitudes
  have hm1 : ∀ i : Fin 512, (rdC e 13 i - rdC e 11 i) * (rdC e 13 i - ((12289 : ℕ) - rdC e 11 i)) = 0 :=
    fun i => mag_eq hs (p := 2) (by simp) FalconCarrierBase.magS1 hz13 i.isLt
  have hm2 : ∀ i : Fin 512, (rdC e 14 i - rdC e 10 i) * (rdC e 14 i - ((12289 : ℕ) - rdC e 10 i)) = 0 :=
    fun i => mag_eq hs (p := 3) (by simp) FalconCarrierBase.magS2 hz14 i.isLt
  have hs1R : ∀ i : Fin 512, Range.IsNatBelow (12289 + 1) (rdC e 11 i) := fun i =>
    EmulatedNorm.isNatBelow_of_centering ⟨mag1N i, by have := hmag1N i; omega, (hmag1C i).symm⟩ (hm1 i)
  have hs2R : ∀ i : Fin 512, Range.IsNatBelow (12289 + 1) (rdC e 10 i) := fun i =>
    EmulatedNorm.isNatBelow_of_centering ⟨mag2N i, by have := hmag2N i; omega, (hmag2C i).symm⟩ (hm2 i)
  choose s1N hs1N hs1C using hs1R
  choose s2N hs2N hs2C using hs2R
  have hs2Of : ∀ i : Fin 512, s2Of e i = (s2N i : (I 0).K) := fun i => by
    unfold s2Of
    rw [h10]
    exact (hs2C i).symm
  -- the signature equation in the field
  have hspec : ∀ k : Fin 512, specOf e k = keySpec e k := spec_eq_of_not_event hs hev
  have hfun : (fun i : Fin 512 => chalEntry e.stmt i + ((77309435394 : ℕ) : (I 0).K) -
      rdC e 11 i - ((12289 : ℕ) : (I 0).K) * rdC e 12 i) =
      LatticeCrypto.negacyclicConvCoeff (fun j : Fin 512 => ringEntry e.stmt (idxOf e * 512 + j))
        (fun j : Fin 512 => s2Of e j) := by
    apply DFT.negSpectrum_injective (psiG_isPrimitiveRoot (K := (I 0).K))
      (natCast_512_ne_zero (K := (I 0).K))
    rw [DFT.negSpectrum_negacyclicConvCoeff (psiG_pow (K := (I 0).K))]
    funext k
    have h := sig_eq_carrier hs k.isLt
    rw [hspec k, keySpec, hpsi, EField.decode_lt _ (by norm_num [pGold]),
      nttNatural_eq_negSpectrum', nttNatural_eq_negSpectrum', nttNatural_eq_negSpectrum'] at h
    exact h
  -- its projection onto the prime field
  have hproj : ∀ i : Fin 512, ((chalNat e.stmt i : ℕ) : (I 0).K) + ((77309435394 : ℕ) : (I 0).K) -
      (s1N i : (I 0).K) - (12289 : ℕ) * (quotN i : (I 0).K) =
      LatticeCrypto.negacyclicConvCoeff
        (fun j : Fin 512 => (((I 0).toNat (ringEntry e.stmt (idxOf e * 512 + j)) : ℕ) : (I 0).K))
        (fun j : Fin 512 => (s2N j : (I 0).K)) i := by
    intro i
    have h := congrArg (fun f => primeProjE (FA := I 0) (f i)) hfun
    simp only at h
    have hs2f : (fun j : Fin 512 => s2Of e j) = fun j : Fin 512 => (s2N j : (I 0).K) :=
      funext hs2Of
    rw [hs2f, primeProjE_negacyclic, ← hs1C i, hquotC i, map_sub, map_sub, map_add,
      primeProjE_natCast, primeProjE_natCast, ← Nat.cast_mul, primeProjE_natCast,
      primeProjE_apply] at h
    simp only [primeProjE_apply] at h
    unfold chalNat
    push_cast at h ⊢
    exact h
  -- the bounds
  obtain ⟨hring, hchal⟩ := stmt_lt (program := program) hok
  have hidx := idxOf_lt e hs
  have hh : ∀ j : Fin 512, (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + j)) < 12289 :=
    fun j => hring _ (by have := j.isLt; omega)
  have hcong : Emulated.Rows.Congruent q
      (EmulatedAlgebraCircuit.keyCoeffs (ringKey e.stmt (idxOf e)).h) (chalNat e.stmt) s1N s2N := by
    rw [show EmulatedAlgebraCircuit.keyCoeffs (ringKey e.stmt (idxOf e)).h =
      fun j : Fin 512 => (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + j)) from
      funext (keyCoeffs_ringKey_of_lt hh)]
    exact Emulated.Rows.Congruent.of_field (F := (I 0).K) (p := pGold) (D := 8589934592)
      hh (fun i => hchal i i.isLt) (fun i => Nat.le_of_lt_succ (hs1N i))
      (fun i => Nat.le_of_lt_succ (hs2N i)) hquotN (by norm_num)
      (by norm_num [pGold, falcon512, Falcon.Concrete.params512]) hproj
  -- the encoding budget
  have hlow : ∀ i : Fin 512, low2N i = mag2N i % 128 := by
    intro i
    obtain ⟨r, hbd⟩ := FalconCarrierBase.high2 (program := program)
    have h := holdsAt_carrier hs (p := 17) (by simp)
    rw [hbd] at h
    have hd := h i (by rw [RealizedProgram.exprLen_leaf, hz14]; exact i.isLt)
    rw [RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf,
      intOf_priv hk14 (hf 14 (by simp)) (hmag2C i) (by have := hmag2N i; norm_num [pGold]; omega),
      intOf_priv hk15 (hf 15 (by simp)) (hlow2C i) (by have := hlow2N i; norm_num [pGold]; omega)] at hd
    obtain ⟨m, hm⟩ := hd
    have := hlow2N i
    omega
  have hbudget : ∑ i : Fin 512, mag2N i / 128 ≤ 392 := by
    obtain ⟨r, hbd⟩ := FalconCarrierBase.rBudget (program := program)
    have h := holdsAt_carrier hs (p := 14) (by simp)
    rw [hbd] at h
    obtain ⟨b, hb, hbv⟩ := natBelow_mem0 h (i := 0) (by
      rw [budgetExpr, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale,
        RealizedProgram.exprLen_apply]
      simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, RealizedProgram.exprLen_leaf, hz14])
    rw [budgetExpr, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
      RealizedProgram.evalE_apply_sum, RealizedProgram.evalE_apply_sum, decode_mOneG] at hbv
    change _ + rdC e 16 0 = _ at hbv
    rw [rdC_off] at hbv
    simp only [Nat.zero_mul, Nat.zero_add] at hbv
    change -1 * ∑ t : Fin 512, rdC e 14 t + ∑ t : Fin 512, rdC e 15 t + _ = _ at hbv
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
    (s1 := fun i => rdC e 11 i) (s2 := fun i => s2Of e i) (mag1 := fun i => rdC e 13 i)
    (mag2 := fun i => rdC e 14 i) (norm := rdC e 17 0) (s1N := s1N) (s2N := s2N) (mag2N := mag2N)
    (fun i => ⟨Nat.le_of_lt_succ (hs1N i), hs1C i⟩)
    (fun i => ⟨Nat.le_of_lt_succ (hs2N i), (hs2Of i).symm⟩)
    (fun i => ⟨mag1N i, hmag1N i, (hmag1C i).symm⟩)
    (fun i => ⟨hmag2N i, (hmag2C i).symm⟩)
    (fun i => hm1 i)
    (fun i => by
      have := hm2 i
      have h2 : s2Of e i = rdC e 10 i := by rw [hs2Of i]; exact hs2C i
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
