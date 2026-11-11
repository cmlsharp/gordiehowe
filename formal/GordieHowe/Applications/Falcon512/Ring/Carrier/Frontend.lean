-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Frontend.Statement
public import GordieHowe.Applications.Falcon512.Emulated.Interp
public import GordieHowe.Applications.Falcon512.Emulated.System.Algebra
public import GordieHowe.Foundations.Algebra.PowModOrder
public import GordieHowe.Foundations.ToMathlib.RootsOfUnity
public import GordieHowe.Language.Realizations.Derivation.Rules
public import GordieHowe.Language.Realizations.Derivation.Events

@[expose] public section

/-!
# GordieHowe frontend: the Falcon ring carriers

The frontend of the theorem at the realized program for the Falcon ring carriers (`Falcon512.Ring.Carrier.ROMParams` and
`Falcon512.Ring.Carrier.QROMParams`: Falcon's arithmetic modulo `q` emulated over a
Goldilocks extension), generic in the program and its interpretation at the program facts
`FalconCarrierBase` (decided per program; the two programs agree on every value, shared
expression and predicate) and the field facts `GordieHowe.Falcon512.EField`:

* **The membership** is the Falcon rings' (`GordieHowe.Falcon512.Ring.FalconRingMember`, at the Goldilocks
  transform root `ψ = psiG`, a primitive `1024`-th root of unity, `psiG_isPrimitiveRoot`).
* **The signature equation** (`signature.equation`, `eOf_eqLeft`, `congruent_carrier`) is the
  Falcon rings' at a random point (`GordieHowe.Falcon512.Ring.FalconRandomPoint`, `sigPoly`,
  `sigEvent`, `eOf_eq_negacyclic`, in `GordieHowe/Applications/Falcon512/Ring/Frontend/Basic.lean`)
  at the carriers' transform data (`instRandomPointFieldCarrier`) and first vector: the program
  checks, at one challenge `r` (`signature.r`), `E = H · s2` in `F[X]/(X^512 + 1)` with
  `E = c − s1 − q · equation.q + q · 6291457` (`eqLeft`; the quotient `equation.q` below `2^33`)
  and a committed high half `Q`, the key `H` read through the interpolation weights
  `λ(r) = 512⁻¹ Ntt_{ψ⁻¹}(1, r, …, r^511)` (`GordieHowe/Language/Library/EvalPoint.lean`): the
  predicate is the polynomial `E − H · s2 + (X^512 + 1) Q` at `r`. Unless `r` is a root of it
  while it is nonzero (degree at most `1022`, Schwartz–Zippel) it is `0`, so
  (`Ops.polyOf_mul_polyOf`, `Ops.polyOf_eq_zero_of_add_mul`) `E_k` is the negacyclic coefficient
  `(H · s2)_k` in the field.
  Without the membership's event `H` is the signer's key, whose coefficients are below `q`; the
  constant coordinates (`EField.coord0`) read the coefficient equation on the integers modulo `p`,
  and its sides differ by less than `p`, so `c − s1 − h · s2 = q (equation.q − 6291457)`: the
  congruence is Falcon's (`Emulated.Rows.Congruent`).
* **The magnitudes, the norm and the encoding** (`magnitudes.s1`, `magnitudes.s2`, `norm.sum`, the
  ranges of `mag1`, `mag2`, `low2`, the budget and the norm, `encoding.high2`) are Falcon
  emulated's (`GordieHowe.Falcon512.Emulated.algebraSpec_of_congruent`), which gives the relation
  `GordieHowe.Falcon512.Ring.rel` at the extracted values (`mem_rel_of_source_carrier`).
* **Round-by-round knowledge soundness of `Π_P₀`** (`rbr_carrier`): `GordieHowe.RealizedProgram.rbr_of_events` at the
  membership's and the signature equation's events (`carrierEvent`), errors `511/|F|` at
  `member.ring.gamma` and `1022/|F|` at `signature.r` (`carrierEps`).
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

/-! ## The negacyclic coefficients -/

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

/-! ## The program facts -/

/-- **The constant `−q`** of the Goldilocks fields: `p − 12289`. -/
abbrev mQG : ℕ := 18446744069414572032

/-- **The signature equation's offset** `q · 6291457 = −q · qlo` (`Carrier.bias`): the quotient
`signature.equation.q` is committed from the lower end `qlo = −6291457`. -/
abbrev qloG : ℕ := 77315715073

/-- **A magnitude equation** `(mag − s)(mag − (q − s)) = 0` of the value `s` at the magnitude
`mag` (`q` the constant `3`). -/
def magLhs (mag s : ℕ) : RealizedProgram.Expr :=
  .mul (.add (.leaf mag) (.scale (.const mOneG) (.leaf s)))
    (.add (.leaf mag) (.scale (.const mOneG) (.add (.scale (.const mOneG) (.leaf s))
      (.reindex [(0, 0, 512)] (.leaf 3)))))

/-- **The norm's left side** (`norm.sum`): `squares − Σ mag1² − Σ mag2²`. -/
def normLhs : RealizedProgram.Expr :=
  .add (.add (.leaf 19) (.scale (.const mOneG) (.apply (.sum 512) (.mul (.leaf 15) (.leaf 15)))))
    (.scale (.const mOneG) (.apply (.sum 512) (.mul (.leaf 16) (.leaf 16))))

/-- **The encoding budget's expression**: `50176 − Σ mag2 + Σ low2`. -/
def budgetExpr : RealizedProgram.Expr :=
  .add (.add (.scale (.const mOneG) (.apply (.sum 512) (.leaf 16))) (.apply (.sum 512) (.leaf 17)))
    (.leaf 18)

/-- **The program facts of a Falcon ring carrier outside the membership** (decided per program):
the signature equation's at a random point (`FalconRandomPoint`) at the carriers' numbering
(`sigIds`: the high half `signature.Q` `13`, `signature.r`'s challenge `1`, `signature.equation`
predicate `1`), transform data (`invConsts`: `512⁻¹` and `ψ⁻¹` modulo `p`) and first vector
`E = c − s1 − q · equation.q + q · 6291457` (`sigE_eq`); the numbering (`statement.ring` `5`,
`statement.c` `6`, `key.spectrum` `7`, `s2` `10`, `signature.s1` `11`, the quotient
`signature.equation.q` `12`, `magnitudes.mag1` `15`, `magnitudes.mag2` `16`, `encoding.low2` `17`,
the budget offset `18`, `norm.squares` `19`; the constants `0` (`1`), the offset `q · 6291457`
(`2`), `q` (`3`), the zero row (`4`)); the magnitudes (predicates `2`, `3`), the norm (`4`), the
ranges (`10` … `15`) and `encoding.high2` (`17`), source predicates; the constants; the fields,
sizes and kinds of the values read; the statement's checks. -/
class FalconCarrierBase (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
    [FalconRingMember program] extends FalconRandomPoint program where
  /-- The numbering of the membership's values. -/
  ids : FalconRingMember.ring program = 5 ∧ FalconRingMember.chal program = 6 ∧
    FalconRingMember.spec program = 7 ∧ FalconRingMember.s2 program = 10 ∧
    FalconRingMember.mOne program = mOneG ∧ FalconRingMember.psi program = psiG ∧
    FalconRingMember.zero program = 1
  /-- The numbering of the signature equation's high half, challenge and predicate. -/
  sigIds : q = 13 ∧ rChal = 1 ∧ sigPred = 1
  /-- `512⁻¹` and `ψ⁻¹` modulo `p`. -/
  invConsts : nInv = 18410715272404008961 ∧ psiInv = 4295002282146690441
  /-- The first vector `c − s1 − q · equation.q + q · 6291457` (the constant `2`). -/
  sigE_eq : sigE = .add (.add (.add (.leaf 6) (.scale (.const mOneG) (.leaf 11)))
    (.scale (.const mQG) (.leaf 12))) (.reindex [(0, 0, 512)] (.leaf 2))
  /-- `magnitudes.s1`. -/
  magS1 : ∃ t, (program.predicate 2).body = .equal 0 (magLhs 15 11) (.leaf 4) t
  /-- `magnitudes.s2`. -/
  magS2 : ∃ t, (program.predicate 3).body = .equal 0 (magLhs 16 10) (.leaf 4) t
  /-- `norm.sum`. -/
  normSum : ∃ t, (program.predicate 4).body = .equal 0 normLhs (.leaf 1) t
  /-- `signature.equation.q`. -/
  rQuot : ∃ r, (program.predicate 10).body = .mem 0 [.leaf 12] (.range 8589934592) r
  /-- `magnitudes.mag1`. -/
  rMag1 : ∃ r, (program.predicate 11).body = .mem 0 [.leaf 15] (.range 6145) r
  /-- `magnitudes.mag2`. -/
  rMag2 : ∃ r, (program.predicate 12).body = .mem 0 [.leaf 16] (.range 2048) r
  /-- `encoding.low2`. -/
  rLow2 : ∃ r, (program.predicate 13).body = .mem 0 [.leaf 17] (.range 128) r
  /-- `encoding.budget`. -/
  rBudget : ∃ r, (program.predicate 14).body = .mem 0 [budgetExpr] (.range 50177) r
  /-- `norm.bound`. -/
  rNorm : ∃ r, (program.predicate 15).body = .mem 0 [.leaf 19] (.range 34034727) r
  /-- `encoding.high2`. -/
  high2 : ∃ r, (program.predicate 17).body = .mod 0 128 (.leaf 16) (.leaf 17) r
  /-- The predicates read beside the signature equation are source predicates. -/
  inSource : ∀ p ∈ [2, 3, 4, 10, 11, 12, 13, 14, 15, 17],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- The constants: `q`, the zero row, the budget offset. -/
  consts : program.isConstant 3 = true ∧ (program.constEntries 3).getD 0 0 = 12289 ∧
    program.isConstant 4 = true ∧ program.constEntries 4 = List.replicate 512 0 ∧
    program.isConstant 18 = true ∧ (program.constEntries 18).getD 0 0 = 50176
  /-- The signature equation's offset `q · 6291457`. -/
  qloConst : program.isConstant 2 = true ∧ (program.constEntries 2).getD 0 0 = qloG
  /-- The values read beside the signature equation's are of field `0`. -/
  fields : ∀ v ∈ [2, 3, 4, 11, 12, 15, 16, 17, 18, 19], program.valueField v = 0
  /-- The sizes of the values read. -/
  sizes : (program.value 11).size = 512 ∧ (program.value 12).size = 512 ∧
    (program.value 15).size = 512 ∧ (program.value 16).size = 512 ∧
    (program.value 17).size = 512 ∧ (program.value 19).size = 1
  /-- The sizes of the signature equation's other values: `Q`, `r^t`, `λ`, `r^512 + 1`. -/
  sigSizes : (program.value 13).size = 511 ∧ (program.value 22).size = 512 ∧
    (program.value 23).size = 512 ∧ (program.value 24).size = 1
  /-- `signature.s1`, `magnitudes.mag2` and `encoding.low2` are committed. -/
  privKinds : (program.value 11).kind = .priv ∧ (program.value 16).kind = .priv ∧
    (program.value 17).kind = .priv
  /-- `signature.equation.q` is bound to its digits. -/
  quotBound : ∃ x, (program.value 12).kind = .bound x
  /-- The statement's checks bound the keys (value `5`) below `q`. -/
  ringCheck : ∃ m ∈ program.statement.checks,
    program.memberValue? m.member = some 5 ∧ m.entryBound? = some 12289
  /-- The statement's checks bound the challenge (value `6`) below `q`. -/
  chalCheck : ∃ m ∈ program.statement.checks,
    program.memberValue? m.member = some 6 ∧ m.entryBound? = some 12289

section Ids

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program]

/-- **The carriers' challenges**: `member.ring.gamma` (`0`) and `signature.r` (`1`). -/
theorem isSourceChal_iff_carrier : ∀ j, program.IsSourceChal j ↔ j = 0 ∨ j = 1 := by
  intro j
  rw [FalconRandomPoint.isSourceChal_iff, (FalconCarrierBase.sigIds (program := program)).2.1]

/-- **`signature.Q`** (value `13`) is committed. -/
theorem qPriv_carrier : (program.value 13).kind = .priv := by
  rw [← (FalconCarrierBase.sigIds (program := program)).1]
  exact FalconRandomPoint.qPriv

/-- **The challenge `r`** is the carriers' challenge `1`. -/
theorem rOf_eqC {I : RealizedProgram.Interp} (e : program.Env I) :
    rOf e = RealizedProgram.castElt (e.chal 1 0) := by
  unfold rOf
  rw [(FalconCarrierBase.sigIds (program := program)).2.1]

end Ids

/-! ## Soundness -/

section Sound

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
    (hp : p ∈ [2, 3, 4, 10, 11, 12, 13, 14, 15, 17]) :
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

theorem rdC_q (e : program.Env I) : rdC e 3 0 = (12289 : ℕ) := by
  obtain ⟨c3, e3, -⟩ := FalconCarrierBase.consts (program := program)
  exact rdC_const c3 ((FalconCarrierBase.fields (program := program)) 3 (by simp)) e3
    (by norm_num [pGold])

theorem rdC_off (e : program.Env I) : rdC e 18 0 = (50176 : ℕ) := by
  obtain ⟨-, -, -, -, c18, e18⟩ := FalconCarrierBase.consts (program := program)
  exact rdC_const c18 ((FalconCarrierBase.fields (program := program)) 18 (by simp)) e18
    (by norm_num [pGold])

theorem rdC_zeros (e : program.Env I) {i : ℕ} (hi : i < 512) : rdC e 4 i = 0 := by
  obtain ⟨-, -, c4, e4, -⟩ := FalconCarrierBase.consts (program := program)
  rw [rdC_const c4 ((FalconCarrierBase.fields (program := program)) 4 (by simp)) (c := 0)
    (by rw [e4, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]; rfl)
    (by norm_num [pGold]), Nat.cast_zero]

/-- **The signature equation's offset** reads `q · 6291457`. -/
theorem rdC_qlo (e : program.Env I) : rdC e 2 0 = ((77315715073 : ℕ) : (I 0).K) := by
  obtain ⟨c2, e2⟩ := FalconCarrierBase.qloConst (program := program)
  exact rdC_const c2 ((FalconCarrierBase.fields (program := program)) 2 (by simp)) e2
    (by norm_num [pGold])

theorem decode_mOneG : (I 0).decode mOneG = -1 := RingField.decode_negOne

/-- **The constant `−q`** decodes to `−12289`. -/
theorem decode_mQG : (I 0).decode mQG = -((12289 : ℕ) : (I 0).K) := by
  rw [EField.decode_lt _ (by norm_num [pGold])]
  have h0 : ((pGold : ℕ) : (I 0).K) = 0 := CharP.cast_eq_zero _ pGold
  have : (mQG : ℕ) + 12289 = pGold := by norm_num [pGold]
  rw [← this] at h0
  push_cast at h0 ⊢
  linear_combination h0

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
    (hp : p ∈ [2, 3, 4, 10, 11, 12, 13, 14, 15, 17])
    (hb : ∃ t, (program.predicate p).body = .equal 0 (magLhs mag v) (.leaf 4) t)
    (hsz : (program.value mag).size = 512) {i : ℕ} (hi : i < 512) :
    (rdC e mag i - rdC e v i) * (rdC e mag i - ((12289 : ℕ) - rdC e v i)) = 0 := by
  obtain ⟨t, hbd⟩ := hb
  have h := holdsAt_carrier hs hp
  rw [hbd] at h
  have hx := holdsAt_equal0 h i (by
    rw [magLhs, RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, hsz]
    exact hi)
  rw [evalE_magLhs e mag v hi] at hx
  change _ = rdC e 4 i at hx
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
    program.evalE (program.reader e) 0 normLhs 0 = rdC e 19 0 - ∑ i : Fin 512, rdC e 15 i * rdC e 15 i -
      ∑ i : Fin 512, rdC e 16 i * rdC e 16 i := by
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
    rdC e 19 0 - ∑ i : Fin 512, rdC e 15 i * rdC e 15 i -
      ∑ i : Fin 512, rdC e 16 i * rdC e 16 i = 0 := by
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
  obtain ⟨h5, hc6, -, -, -, -, -⟩ := FalconCarrierBase.ids (program := program)
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
    rwa [hc6] at this
  have hs5 : (program.value 5).size = 32768 := by
    have := (FalconRingMember.sizes (program := program)).2.2.1
    rwa [h5] at this
  have hs6 : (program.value 6).size = 512 := by
    have := (FalconRingMember.sizes (program := program)).2.2.2.1
    rwa [hc6] at this
  refine ⟨fun i hi => ?_, fun i hi => ?_⟩
  · unfold ringEntry
    rw [h5, RealizedProgram.toNat_castElt hf5]
    exact H i (by rw [hs5]; exact hi)
  · unfold chalEntry
    rw [hc6, RealizedProgram.toNat_castElt hf6]
    exact H' i (by rw [hs6]; exact hi)

/-- **The coefficients of a ring key with entries below `q`** are the entries read as naturals. -/
theorem keyCoeffs_ringKey_of_lt {x : program.Valuation I} {r : ℕ}
    (h : ∀ j : Fin falcon512.n, (I 0).toNat (ringEntry x (r * 512 + j)) < 12289)
    (j : Fin falcon512.n) :
    EmulatedAlgebraCircuit.keyCoeffs (ringKey x r).h j = (I 0).toNat (ringEntry x (r * 512 + j)) := by
  simp only [ringKey, EmulatedAlgebraCircuit.keyCoeffs, Falcon512.coeff_ofCoeff, ZMod.val_natCast]
  exact Nat.mod_eq_of_lt (h j)

/-- **A leaf of domain `0` below a bound**, from its range. -/
theorem leaf_natBelow {e : program.Env I} (hs : program.SourceSatAt e) {p v n : ℕ}
    (hp : p ∈ [2, 3, 4, 10, 11, 12, 13, 14, 15, 17])
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

end Sound

/-! ## The signature equation -/

section Signature

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] {I : RealizedProgram.Interp} [EField (I 0)]

open Polynomial RealizedProgram.Ops

attribute [local instance] ringField_carrier

/-- `512⁻¹` and `ψ⁻¹` in a field of characteristic `p` (`Ops.natCast_eq_inv_of_mul_mod`). -/
theorem decode_nInvG : (I 0).decode 18410715272404008961 = ((512 : ℕ) : (I 0).K)⁻¹ := by
  rw [EField.decode_lt _ (by norm_num [pGold])]
  exact RealizedProgram.Ops.natCast_eq_inv_of_mul_mod pGold (by norm_num [pGold])

theorem decode_psiInvG : (I 0).decode 4295002282146690441 = (psiG : (I 0).K)⁻¹ := by
  rw [EField.decode_lt _ (by norm_num [pGold])]
  exact RealizedProgram.Ops.natCast_eq_inv_of_mul_mod pGold (by norm_num [pGold])

/-- **The carriers' transform root** decodes to `psiG`. -/
theorem decode_psiC : (I 0).decode (FalconRingMember.psi program) = (psiG : (I 0).K) := by
  rw [(FalconCarrierBase.ids (program := program)).2.2.2.2.2.1, EField.decode_lt _ (by norm_num [pGold])]

/-- **The signature equation's field facts** in a carrier's field (`FalconRandomPointField`):
`−1 = p − 1`, `512⁻¹`, `ψ⁻¹` modulo `p` at the primitive `1024`-th root `ψ = psiG`. -/
instance instRandomPointFieldCarrier : FalconRandomPointField program (I 0) where
  toRingField := ringField_carrier
  decode_nInv := by
    rw [(FalconCarrierBase.invConsts (program := program)).1]; exact decode_nInvG
  decode_psiInv := by
    rw [(FalconCarrierBase.invConsts (program := program)).2, decode_psiC]; exact decode_psiInvG
  psi_isPrimitiveRoot := by rw [decode_psiC]; exact psiG_isPrimitiveRoot
  n_ne_zero := natCast_512_ne_zero

/-- **The signature equation's left coefficients** `E = c − s1 − q · equation.q + q · 6291457`. -/
def eqLeft (e : program.Env I) (t : ℕ) : (I 0).K :=
  chalEntry e.stmt t - rdC e 11 t - ((12289 : ℕ) : (I 0).K) * rdC e 12 t +
    ((77315715073 : ℕ) : (I 0).K)

omit [EField (I 0)] in
/-- **The statement's challenge** (`statement.c`, `6`). -/
theorem evalE_chalC (e : program.Env I) (t : ℕ) :
    program.evalE (program.reader e) 0 (.leaf 6) t = chalEntry e.stmt t := by
  obtain ⟨-, hc6, -⟩ := FalconCarrierBase.ids (program := program)
  have hk6 : (program.value 6).kind = .pub (.opaque "statement.c" []) := by
    have := FalconRingMember.chalKind (program := program)
    rwa [hc6] at this
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_of_opaque_nil e hk6]
  unfold chalEntry
  rw [hc6]

/-- **A carrier's first vector** is `E = c − s1 − q · equation.q + q · 6291457` below `512`. -/
theorem eOf_eqLeft (e : program.Env I) {t : ℕ} (ht : t < 512) : eOf e t = eqLeft e t := by
  have h2 := rdC_qlo (program := program) e
  unfold rdC at h2
  unfold eOf
  rw [FalconCarrierBase.sigE_eq, RealizedProgram.evalE_add, RealizedProgram.evalE_add,
    RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_step_zero ht, evalE_chalC,
    decode_mOneG, decode_mQG, h2]
  unfold eqLeft rdC
  ring

end Signature

/-! ## The integer reading of the signature equation -/

section Coord

variable {FA : RealizedProgram.FieldInterp} [EField FA]

/-- **The constant coordinate** is the integer reading. -/
theorem coord0_eq_toNat (x : FA.K) : EField.coord0 (FA := FA) x = ((FA.toNat x : ℕ) : ZMod pGold) := by
  rw [EField.toNat_eq, ZMod.natCast_zmod_val]

/-- **The constant coordinate of a negacyclic coefficient** against naturals' casts is the
coefficient of the coordinates (`EField.coord0` is additive and commutes with natural multiples). -/
theorem coord0_negacyclicConvCoeff {n : ℕ} (h : Fin n → FA.K) (s : Fin n → ℕ) (k : Fin n) :
    EField.coord0 (FA := FA) (LatticeCrypto.negacyclicConvCoeff h (fun j => (s j : FA.K)) k) =
      LatticeCrypto.negacyclicConvCoeff (fun j => EField.coord0 (FA := FA) (h j))
        (fun j => (s j : ZMod pGold)) k := by
  have hm : ∀ (a : FA.K) (m : ℕ), EField.coord0 (FA := FA) (a * (m : FA.K)) =
      EField.coord0 (FA := FA) a * (m : ZMod pGold) := fun a m => by
    rw [_root_.mul_comm, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, _root_.mul_comm]
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [map_sum]
  refine Finset.sum_congr rfl fun ij _ => ?_
  split_ifs
  · exact hm _ _
  · rw [map_neg, hm]
  · exact map_zero _

end Coord

/-! ## The relation -/

section Relation

open Native (CoreWit)
open RealizedProgram.Ops

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] {I : RealizedProgram.Interp} [EField (I 0)]

attribute [local instance] ringField_carrier

/-- **The signature congruence** where the source program holds without the events: the spectrum
is the transform of the signer's key (`spec_eq_of_not_event`), so the signature equation's
coefficients are `E = h · s2` in the field (`eOf_eq_negacyclic`). Their constant coordinates
(`EField.coord0`) give `c − s1 − q · equation.q + q · 6291457 ≡ h · s2 (mod p)` on the integers
read, whose sides differ by less than `p` (the keys below `q`, `s1`, `s2` at most `q`, the
quotient below `2^33`): so they are equal, and `c ≡ s1 + h · s2 (mod q)`. -/
theorem congruent_carrier {e : program.Env I} (hok : program.StatementOk I e.stmt)
    (hs : program.SourceSatAt e) (hev : ¬ ringEvent 0 e)
    (hev1 : ¬ (sigEvent e).BadAt (rOf e)) {s1N s2N : Fin 512 → ℕ}
    (hs1 : ∀ i : Fin 512, rdC e 11 i = (s1N i : (I 0).K) ∧ s1N i ≤ 12289)
    (hs2 : ∀ i : Fin 512, s2Of e i = (s2N i : (I 0).K) ∧ s2N i ≤ 12289) :
    Emulated.Rows.Congruent q
      (EmulatedAlgebraCircuit.keyCoeffs (ringKey e.stmt (idxOf e)).h) (chalNat e.stmt) s1N s2N := by
  obtain ⟨-, -, -, -, -, hpsi, -⟩ := FalconCarrierBase.ids (program := program)
  obtain ⟨hring, hchal⟩ := stmt_lt (program := program) hok
  obtain ⟨-, hz12, -⟩ := FalconCarrierBase.sizes (program := program)
  have hh : ∀ j : Fin 512, (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + j)) < 12289 :=
    fun j => hring _ (by have := idxOf_lt e (memberPreds_of_source hs); have := j.isLt; omega)
  set z : Fin 512 → ℕ := fun s => (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + s)) with hzdef
  -- the kernel's polynomial is the signer's key
  have hspec := spec_eq_of_not_event (memberPreds_of_source hs) hev
  have hinv : ∀ s < 512, inverseNttNatural 512 (psiG : (I 0).K) (specOf e) s =
      ringEntry e.stmt (idxOf e * 512 + s) := fun s hs' => by
    rw [inverseNttNatural_congr (y := nttNatural 512
        (psiG : (I 0).K) (fun c => ringEntry e.stmt (idxOf e * 512 + c))) fun m hm => by
        rw [hspec ⟨m, hm⟩, keySpec, hpsi, EField.decode_lt _ (by norm_num [pGold])],
      inverseNttNatural_nttNatural (psiG_isPrimitiveRoot (K := (I 0).K))
        (natCast_512_ne_zero (K := (I 0).K)) _ hs']
  rw [show EmulatedAlgebraCircuit.keyCoeffs (ringKey e.stmt (idxOf e)).h =
      fun j : Fin falcon512.n => (I 0).toNat (ringEntry e.stmt (idxOf e * 512 + j)) from
    funext (keyCoeffs_ringKey_of_lt hh)]
  suffices H : ∀ i : Fin 512, (((I 0).toNat (chalEntry e.stmt i) : ℕ) : ZMod 12289) =
      (s1N i : ZMod 12289) + LatticeCrypto.negacyclicConvCoeff
        (fun j : Fin 512 => (z j : ZMod 12289)) (fun j => (s2N j : ZMod 12289)) i from fun i => H i
  intro i
  -- the quotient read as a natural below `2^33`
  obtain ⟨k, hk, hkv⟩ := leaf_natBelow (e := e) hs (p := 10) (by simp)
    FalconCarrierBase.rQuot hz12 i
  -- the signature equation's coefficient `i` in the field
  have hE := (eOf_eqLeft e i.isLt).symm.trans (eOf_eq_negacyclic hs hev1 i.isLt)
  rw [decode_psiC, negacyclic, ofFin_of_lt _ i.isLt] at hE
  simp only [Fin.eta] at hE
  have hN : (toFin 512 (inverseNttNatural 512 (psiG : (I 0).K) (specOf e))) =
      fun j : Fin 512 => ringEntry e.stmt (idxOf e * 512 + j) :=
    funext fun j => by rw [toFin_apply, hinv j j.isLt]
  have hS : toFin 512 (s2Of e) = fun j : Fin 512 => (s2N j : (I 0).K) :=
    funext fun j => by rw [toFin_apply, (hs2 j).1]
  rw [hN, hS] at hE
  -- its constant coordinate
  set Nint : ℤ := LatticeCrypto.negacyclicConvCoeff (fun j : Fin 512 => ((z j : ℕ) : ℤ))
    (fun j => (s2N j : ℤ)) i with hNint
  have hc := congrArg (EField.coord0 (FA := I 0)) hE
  rw [coord0_negacyclicConvCoeff] at hc
  have hzc : ∀ j : Fin 512, EField.coord0 (FA := I 0) (ringEntry e.stmt (idxOf e * 512 + j)) =
      ((z j : ℕ) : ZMod pGold) := fun j => coord0_eq_toNat _
  simp only [hzc] at hc
  rw [← Emulated.Rows.intCast_negacyclicConvCoeff, ← hNint] at hc
  unfold eqLeft at hc
  rw [(hs1 i).1, hkv, map_add, map_sub, map_sub, coord0_eq_toNat (chalEntry e.stmt i),
    show ((12289 : ℕ) : (I 0).K) * (k : (I 0).K) = ((12289 * k : ℕ) : (I 0).K) by push_cast; ring,
    EField.coord0_natCast, EField.coord0_natCast, EField.coord0_natCast] at hc
  set cN : ℕ := (I 0).toNat (chalEntry e.stmt i) with hcN
  have hcl : cN < 12289 := hchal i i.isLt
  set W : ℤ := (cN : ℤ) - (s1N i : ℤ) - 12289 * (k : ℤ) + 77315715073 - Nint with hW
  have hW0 : ((W : ℤ) : ZMod pGold) = 0 := by
    have hWc : ((W : ℤ) : ZMod pGold) = (cN : ZMod pGold) - (s1N i : ZMod pGold) -
        ((12289 * k : ℕ) : ZMod pGold) + ((77315715073 : ℕ) : ZMod pGold) -
          ((Nint : ℤ) : ZMod pGold) := by
      rw [hW]
      push_cast
      ring
    rw [hWc, hc, sub_self]
  have hdvd : (pGold : ℤ) ∣ W := (ZMod.intCast_zmod_eq_zero_iff_dvd W pGold).1 hW0
  -- the sides differ by less than `p`
  have hconv := Emulated.Rows.negacyclicConv_natAbs_le_mul (A := 12288) (B := 12289)
    (h := z) (s := s2N) (fun j => Nat.le_of_lt_succ (hh j)) (fun j => (hs2 j).2) i
  have hb := LatticeCrypto.neg_le_and_le_of_natAbs_le hconv
  rw [← hNint] at hb
  have hs1i := (hs1 i).2
  have hWlt : |W| < (pGold : ℤ) := by
    rw [abs_lt]
    norm_num [pGold] at hb ⊢
    constructor <;> omega
  have hW0' : W = 0 := Int.eq_zero_of_abs_lt_dvd hdvd hWlt
  rw [hW] at hW0'
  have hd : (12289 : ℤ) ∣ (cN : ℤ) - (s1N i : ℤ) - Nint :=
    ⟨(k : ℤ) - 6291457, by linear_combination hW0'⟩
  have hcq := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12289).2 hd
  rw [Int.cast_sub, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, hNint,
    Emulated.Rows.intCast_negacyclicConvCoeff z s2N i] at hcq
  linear_combination hcq

/-- **Soundness of a carrier's source program without the events**: the signature congruence
(`congruent_carrier`) with the magnitudes, the norm and the encoding budget, by Falcon emulated's
`algebraSpec_of_congruent`, gives the relation. -/
theorem mem_rel_of_source_carrier {e : program.Env I} (hok : program.StatementOk I e.stmt)
    (hs : program.SourceSatAt e) (hev : ¬ ringEvent 0 e)
    (hev1 : ¬ (sigEvent e).BadAt (rOf e)) :
    (e.stmt, proj e.stmt e.asg) ∈ rel := by
  classical
  obtain ⟨-, -, -, h10, -, -, -⟩ := FalconCarrierBase.ids (program := program)
  obtain ⟨hz11, -, hz15, hz16, hz17, hz19⟩ := FalconCarrierBase.sizes (program := program)
  obtain ⟨-, hk16, hk17⟩ := FalconCarrierBase.privKinds (program := program)
  have hf : ∀ v ∈ [2, 3, 4, 11, 12, 15, 16, 17, 18, 19], program.valueField v = 0 :=
    FalconCarrierBase.fields (program := program)
  -- the ranges
  choose mag1N hmag1N hmag1C using leaf_natBelow (e := e) hs (p := 11) (by simp)
    FalconCarrierBase.rMag1 hz15
  choose mag2N hmag2N hmag2C using leaf_natBelow (e := e) hs (p := 12) (by simp)
    FalconCarrierBase.rMag2 hz16
  choose low2N hlow2N hlow2C using leaf_natBelow (e := e) hs (p := 13) (by simp)
    FalconCarrierBase.rLow2 hz17
  obtain ⟨sq, hsqN, hsqC⟩ := leaf_natBelow (e := e) hs (p := 15) (by simp)
    FalconCarrierBase.rNorm hz19 ⟨0, by norm_num⟩
  -- the magnitudes
  have hm1 : ∀ i : Fin 512, (rdC e 15 i - rdC e 11 i) * (rdC e 15 i - ((12289 : ℕ) - rdC e 11 i)) = 0 :=
    fun i => mag_eq hs (p := 2) (by simp) FalconCarrierBase.magS1 hz15 i.isLt
  have hm2 : ∀ i : Fin 512, (rdC e 16 i - rdC e 10 i) * (rdC e 16 i - ((12289 : ℕ) - rdC e 10 i)) = 0 :=
    fun i => mag_eq hs (p := 3) (by simp) FalconCarrierBase.magS2 hz16 i.isLt
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
  -- the signature congruence
  have hcong := congruent_carrier hok hs hev hev1 (s1N := s1N) (s2N := s2N)
    (fun i => ⟨(hs1C i).symm, Nat.le_of_lt_succ (hs1N i)⟩)
    (fun i => ⟨hs2Of i, Nat.le_of_lt_succ (hs2N i)⟩)
  have hidx := idxOf_lt e (memberPreds_of_source hs)
  -- the encoding budget
  have hlow : ∀ i : Fin 512, low2N i = mag2N i % 128 := by
    intro i
    obtain ⟨r, hbd⟩ := FalconCarrierBase.high2 (program := program)
    have h := holdsAt_carrier hs (p := 17) (by simp)
    rw [hbd] at h
    have hd := h i (by rw [RealizedProgram.exprLen_leaf, hz16]; exact i.isLt)
    rw [RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf,
      intOf_priv hk16 (hf 16 (by simp)) (hmag2C i) (by have := hmag2N i; norm_num [pGold]; omega),
      intOf_priv hk17 (hf 17 (by simp)) (hlow2C i) (by have := hlow2N i; norm_num [pGold]; omega)] at hd
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
      simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, RealizedProgram.exprLen_leaf, hz16])
    rw [budgetExpr, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
      RealizedProgram.evalE_apply_sum, RealizedProgram.evalE_apply_sum, decode_mOneG] at hbv
    change _ + rdC e 18 0 = _ at hbv
    rw [rdC_off] at hbv
    simp only [Nat.zero_mul, Nat.zero_add] at hbv
    change -1 * ∑ t : Fin 512, rdC e 16 t + ∑ t : Fin 512, rdC e 17 t + _ = _ at hbv
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
    (s1 := fun i => rdC e 11 i) (s2 := fun i => s2Of e i) (mag1 := fun i => rdC e 15 i)
    (mag2 := fun i => rdC e 16 i) (norm := rdC e 19 0) (s1N := s1N) (s2N := s2N) (mag2N := mag2N)
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

end Relation

/-! ## The carriers' events -/

section CarrierEvent

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] {I : RealizedProgram.Interp} [EField (I 0)]

omit [EField (I 0)] in
/-- **A carrier's first vector reads the statement and the assignment.** -/
theorem eOf_congrC {e e' : program.Env I} (hs : e.stmt = e'.stmt) (ha : e.asg = e'.asg) :
    ∀ t < 512, eOf e t = eOf e' t := fun t _ => by
  obtain ⟨x, hx⟩ := FalconCarrierBase.quotBound (program := program)
  obtain ⟨-, hc6, -⟩ := FalconCarrierBase.ids (program := program)
  have hk6 : (program.value 6).kind = .pub (.opaque "statement.c" []) := by
    have := FalconRingMember.chalKind (program := program)
    rwa [hc6] at this
  have hk11 := (FalconCarrierBase.privKinds (program := program)).1
  have h2 : ∀ i, program.reader e 2 i = program.reader e' 2 i := by
    obtain ⟨c2, -⟩ := FalconCarrierBase.qloConst (program := program)
    unfold RealizedProgram.isConstant at c2
    split at c2
    · rename_i es hk
      intro i
      rw [RealizedProgram.reader_of_constant e hk, RealizedProgram.reader_of_constant e' hk]
    · cases c2
  unfold eOf
  rw [FalconCarrierBase.sigE_eq]
  simp only [RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_reindex, RealizedProgram.evalE_leaf,
    RealizedProgram.reader_of_opaque_nil e hk6, RealizedProgram.reader_of_opaque_nil e' hk6,
    RealizedProgram.reader_of_priv e hk11, RealizedProgram.reader_of_priv e' hk11,
    RealizedProgram.reader_of_bound e hx, RealizedProgram.reader_of_bound e' hx, hs, ha, h2]

/-- **The carriers' events**: the membership's at `member.ring.gamma` (challenge `0`) and the
signature equation's at `signature.r` (challenge `1`). -/
def carrierEvent (j : ℕ) (e : program.Env I) : Prop :=
  ringEvent j e ∨ (j = 1 ∧ (sigEvent e).BadAt (rOf e))

omit [EField (I 0)] in
/-- **The challenge-use rule** (`RealizedProgram.ChallengeUseAt`): each event reads the statement,
the committed assignment and its challenge. -/
theorem carrierEvent_use : RealizedProgram.ChallengeUseAt program I carrierEvent := by
  intro j e e' h
  unfold carrierEvent
  rw [ringEvent_use j h]
  by_cases hj : j = 1
  · subst hj
    have hr : rOf e = rOf e' := by
      rw [rOf_eqC, rOf_eqC, h.chal _ (Or.inr ⟨rfl, le_refl _⟩)]
    rw [sigEvent_congr (eOf_congrC h.stmt h.asg) h.asg, hr]
  · simp [hj]

/-- **The events' errors**: `511/|F|` at `member.ring.gamma`, `1022/|F|` at `signature.r`, `0`
elsewhere. -/
noncomputable def carrierEps (I : RealizedProgram.Interp) (j : ℕ) : NNReal :=
  if j = 0 then 511 / Fintype.card (I 0).K
  else if j = 1 then 1022 / Fintype.card (I 0).K else 0

/-- **The events' probabilities** (`RealizedProgram.rbr_of_events`' `hbound`): the membership's
(`ringEvent_bound`) and the signature equation's, at most `1022/|F|` at `signature.r`
(`RealizedProgram.probUniform_badAt_setChal_le`, Schwartz–Zippel). -/
theorem carrierEvent_bound : ∀ j, program.IsSourceChal j → ∀ e : program.Env I,
    Pr[c ← program.ChalVal I j : carrierEvent j (e.setChal j c)] ≤ (carrierEps I j : ENNReal) := by
  intro j hj e
  rcases (isSourceChal_iff_carrier (program := program) j).1 hj with rfl | rfl
  · have hset : ∀ c, carrierEvent 0 (e.setChal 0 c) ↔ ringEvent 0 (e.setChal 0 c) := fun c => by
      simp [carrierEvent]
    simp only [hset]
    refine (ringEvent_bound 0 hj e).trans ?_
    simp [ringEps, carrierEps]
  · have hset : ∀ c, carrierEvent 1 (e.setChal 1 c) ↔
        (sigEvent e).BadAt (RealizedProgram.castElt ((e.setChal 1 c).chal 1 0)) :=
      fun c => by
      simp only [carrierEvent, ringEvent, one_ne_zero, false_and, true_and, false_or]
      rw [sigEvent_congr (e := e.setChal 1 c) (e' := e) (eOf_congrC rfl rfl) rfl, rOf_eqC]
    simp only [hset]
    obtain ⟨hsz, hsm⟩ := FalconRandomPoint.chalR (program := program)
    have hcf := (FalconRandomPoint.rPow (program := program)).chalField
    rw [(FalconCarrierBase.sigIds (program := program)).2.1] at hsz hsm hcf
    refine (RealizedProgram.probUniform_badAt_setChal_le hsz hsm hcf (sigEvent e) e).trans ?_
    simp [carrierEps, sigEvent]

end CarrierEvent

/-! ## Round-by-round knowledge soundness of `Π_P₀` -/

section Rbr

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] {I : RealizedProgram.Interp} [EField (I 0)]

/-- **The relation from the source program without the events** (`RealizedProgram.rbr_of_events`'
`hsound`). -/
theorem sound_carrier :
    ∀ e : program.Env I, program.StatementOk I e.stmt → program.SourceSatAt e →
      (∀ j, program.IsSourceChal j → ¬ carrierEvent j e) → (e.stmt, proj e.stmt e.asg) ∈ rel :=
  fun _ hok hs hno => mem_rel_of_source_carrier hok hs
    (fun hb => hno 0 (FalconRingMember.isSourceChal_zero (program := program)) (Or.inl hb))
    (fun hb => hno 1 ((isSourceChal_iff_carrier (program := program) 1).2 (Or.inr rfl))
      (Or.inr ⟨rfl, hb⟩))

/-- **Round-by-round knowledge soundness of `Π_P₀` for a Falcon ring carrier**
(`RealizedProgram.rbr_of_events`): the relation `rel`, the extractor `extractor`, the errors
`511/|F|` at `member.ring.gamma`, `1022/|F|` at `signature.r` and `0` elsewhere (`carrierEps`). -/
theorem rbr_carrier :
    RBRKnowledgeSound rel (program.sourceVerifier I) extractor
      (program.eventState I rel proj carrierEvent carrierEvent_use sound_carrier)
      (program.roundError I (carrierEps I)) :=
  program.rbr_of_events I rel proj carrierEvent (carrierEps I) carrierEvent_use carrierEvent_bound
    sound_carrier

end Rbr

end GordieHowe.Falcon512.Ring
