-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.Frontend.Basic
public import GordieHowe.Language.Realizations.RealizeGrouped

@[expose] public section

/-!
# GordieHowe frontend: the native Falcon norm and encoding of a domain

The Falcon frontend's reading of the native norm and the encoding (`NativeNorm`,
`NativeEncoding`) off a program's predicates, generic in the program, its
interpretation `I` and the identifiers of the domain that holds them (`FalconNorm`, decided per
program): the native programs' domain `A` and the native rings' one domain hold the same
predicates up to the numbering of their values, shared expressions, predicates and index maps.
Wherever the source program holds:

* **the norm's witness** (`normWit`): the magnitude digits `norm.a`, the square digits `norm.sq`,
  each column carry `norm.cc` (below `189`) split into two base-`64` limbs, the batch digits and
  carries `norm.nd`, `norm.nc`, the complement `norm.D` and its carries `norm.Dc`; the native
  norm's constraint groups hold at the input `s1 ‖ s2` (`normHolds`) and its digits are below `64`
  (`digitsBelow`);
* **the encoding** (`encodingBits`, `slack_below`, `encodingRequests`): the parity bits of `s2`
  are bits, the high parts below `16` and the slack `392 − Σ h` below `393`.

Each lemma reads one predicate at its coordinates (`norm.center`, `norm.column0` …
`norm.column5`, `norm.normalize`, `norm.complement`, `norm.top`, the type check of `norm.Dc`,
`encoding.b.boolean`, the ranges `norm.a` … `norm.D`, `encoding.high`, `encoding.slack`), the
integer `mod_q`s (`q = 0`) as integer equalities of the values' integer readings, which cast to the
field equations as the values are in the prime subfield (`intOf_cast`, their node types).
-/

namespace GordieHowe.Falcon512.Norm

open GordieHowe.Bits Native.ROMParams

/-! ## The program facts -/

/-- **The identifiers and program facts of a native Falcon norm and encoding** (each program
instantiates them by `decide` and `rfl`): the domain `dA` and its field `fA`; the values `s2`,
`signature.s1`, `norm.a`, `norm.sq`, `norm.cc`, `norm.nd`, `norm.nc`, `norm.D`, `norm.Dc`, the
target digits, the slack offset and the zero constants of sizes `1` and `1024`; the shared
expressions of the norm (`e0 … e0 + 29`), its predicates (`p0 … p0 + 9`), the other predicates
by index, the shared expressions of the encoding, and the index maps of the norm and the
encoding, with their entries. -/
class FalconNorm (program : RealizedProgram) where
  /-- The domain. -/
  dA : ℕ
  /-- Its field. -/
  fA : ℕ
  /-- The domain's field. -/
  domainField : program.domainField dA = fA
  /-- `s2`. -/
  s2 : ℕ
  /-- `signature.s1`. -/
  s1 : ℕ
  /-- `norm.a`. -/
  a : ℕ
  /-- `norm.sq`. -/
  sq : ℕ
  /-- `norm.cc`. -/
  cc : ℕ
  /-- `norm.nd`. -/
  nd : ℕ
  /-- `norm.nc`. -/
  nc : ℕ
  /-- `norm.D`. -/
  D : ℕ
  /-- `norm.Dc`. -/
  Dc : ℕ
  /-- `norm.target`. -/
  tgt : ℕ
  /-- `enc.slack.offset`. -/
  off : ℕ
  /-- The zero constant of size `1`. -/
  z1 : ℕ
  /-- The zero constant of size `1024`. -/
  z : ℕ
  /-- The first shared expression of the norm. -/
  e0 : ℕ
  /-- `norm.center`, the first predicate of the norm. -/
  p0 : ℕ
  /-- A bound on the shared expressions read. -/
  eMax : ℕ
  /-- `norm.Dc.boolean`. -/
  pDc : ℕ
  /-- `encoding.b.boolean`. -/
  pEncB : ℕ
  /-- The ranges `norm.a`, `norm.sq`, `norm.cc`, `norm.nd`, `norm.nc`, `norm.D`. -/
  pRange : ℕ
  /-- `encoding.high`. -/
  pHigh : ℕ
  /-- `encoding.slack`. -/
  pSlack : ℕ
  /-- The high parts' shared expression. -/
  eHigh : ℕ
  /-- The middle digits' shared expression. -/
  eMid : ℕ
  /-- The parity bits' shared expression. -/
  eB : ℕ
  /-- The high parts' index map. -/
  iHigh : RealizedProgram.IndexMap
  /-- The middle digits' index map. -/
  iMid : RealizedProgram.IndexMap
  i52 : RealizedProgram.IndexMap
  i53 : RealizedProgram.IndexMap
  i54 : RealizedProgram.IndexMap
  i55 : RealizedProgram.IndexMap
  i56 : RealizedProgram.IndexMap
  i57 : RealizedProgram.IndexMap
  i58 : RealizedProgram.IndexMap
  i59 : RealizedProgram.IndexMap
  i60 : RealizedProgram.IndexMap
  i61 : RealizedProgram.IndexMap
  i62 : RealizedProgram.IndexMap
  i63 : RealizedProgram.IndexMap
  i64 : RealizedProgram.IndexMap
  i65 : RealizedProgram.IndexMap
  i66 : RealizedProgram.IndexMap
  i67 : RealizedProgram.IndexMap
  i68 : RealizedProgram.IndexMap
  i69 : RealizedProgram.IndexMap
  i70 : RealizedProgram.IndexMap
  i71 : RealizedProgram.IndexMap
  i72 : RealizedProgram.IndexMap
  i73 : RealizedProgram.IndexMap
  i74 : RealizedProgram.IndexMap
  /-- The program's shared expressions read only earlier entries. -/
  refsOrdered : program.RefsOrdered
  /-- The predicates are source predicates. -/
  inSource_A : ∀ p ∈ [p0, p0 + 1, p0 + 2, p0 + 3, p0 + 4, p0 + 5, p0 + 6, p0 + 7, p0 + 8, p0 + 9,
    pDc, pEncB, pRange, pRange + 1, pRange + 2, pRange + 3, pRange + 4, pRange + 5, pHigh, pSlack],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- `norm.center`. -/
  center : ∃ t, (program.predicate p0).body = .equal dA (.add (.mul (.ref e0) (.ref e0))
    (.scale (.const 12288) (.mul (.add (.add (.ref (e0 + 1)) (.scale (.const 64) (.ref (e0 + 2))))
      (.scale (.const 4096) (.ref (e0 + 3)))) (.add (.add (.ref (e0 + 1))
        (.scale (.const 64) (.ref (e0 + 2)))) (.scale (.const 4096) (.ref (e0 + 3))))))) (.leaf z) t
  /-- `norm.top`. -/
  top : ∃ t, (program.predicate (p0 + 1)).body = .equal dA (.ref (e0 + 4)) (.leaf z1) t
  /-- `norm.column0`. -/
  col0 : ∃ real, (program.predicate (p0 + 2)).body =
    .mod dA 0 (.mul (.ref (e0 + 5)) (.ref (e0 + 5))) (.add (.ref (e0 + 6))
      (.scale (.const 64) (.ref (e0 + 7)))) real
  /-- `norm.column1`. -/
  col1 : ∃ real, (program.predicate (p0 + 3)).body = .mod dA 0
    (.add (.scale (.const 2) (.mul (.ref (e0 + 5)) (.ref (e0 + 8)))) (.ref (e0 + 9)))
    (.add (.ref (e0 + 10)) (.scale (.const 64) (.ref (e0 + 11)))) real
  /-- `norm.column2`. -/
  col2 : ∃ real, (program.predicate (p0 + 4)).body = .mod dA 0
    (.add (.add (.scale (.const 2) (.mul (.ref (e0 + 5)) (.ref (e0 + 12))))
      (.mul (.ref (e0 + 8)) (.ref (e0 + 8)))) (.ref (e0 + 13)))
    (.add (.ref (e0 + 14)) (.scale (.const 64) (.ref (e0 + 15)))) real
  /-- `norm.column3`. -/
  col3 : ∃ real, (program.predicate (p0 + 5)).body = .mod dA 0
    (.add (.scale (.const 2) (.mul (.ref (e0 + 8)) (.ref (e0 + 12)))) (.ref (e0 + 16)))
    (.add (.ref (e0 + 17)) (.scale (.const 64) (.ref (e0 + 18)))) real
  /-- `norm.column4`. -/
  col4 : ∃ real, (program.predicate (p0 + 6)).body = .mod dA 0
    (.add (.mul (.ref (e0 + 12)) (.ref (e0 + 12))) (.ref (e0 + 19)))
    (.add (.ref (e0 + 20)) (.scale (.const 64) (.ref (e0 + 21)))) real
  /-- `norm.column5`. -/
  col5 : ∃ real, (program.predicate (p0 + 7)).body = .mod dA 0 (.ref (e0 + 22)) (.ref (e0 + 23)) real
  /-- `norm.normalize`. -/
  normalize : ∃ real, (program.predicate (p0 + 8)).body = .mod dA 0
    (.add (.add (.ref (e0 + 24)) (.apply (.batched 102 (.sum 63)) (.ref (e0 + 25)))) (.ref (e0 + 26)))
    (.add (.leaf nd) (.scale (.const 64) (.ref (e0 + 27)))) real
  /-- `norm.complement`. -/
  complement : ∃ real, (program.predicate (p0 + 9)).body = .mod dA 0
    (.add (.add (.ref (e0 + 28)) (.leaf D)) (.ref (e0 + 29)))
    (.add (.leaf tgt) (.scale (.const 64) (.leaf Dc))) real
  /-- `norm.Dc.boolean`. -/
  dcBool : ∃ t, (program.predicate pDc).body = .equal dA (.mul (.leaf Dc) (.leaf Dc)) (.leaf Dc) t
  /-- `encoding.b.boolean`. -/
  encB : ∃ t, (program.predicate pEncB).body = .equal dA (.mul (.ref eB) (.ref eB)) (.ref eB) t
  /-- `norm.a`. -/
  rangeA : ∃ real, (program.predicate pRange).body = .mem dA [.leaf a] (.range 64) real
  /-- `norm.sq`. -/
  rangeSq : ∃ real, (program.predicate (pRange + 1)).body = .mem dA [.leaf sq] (.range 64) real
  /-- `norm.cc`. -/
  rangeCc : ∃ real, (program.predicate (pRange + 2)).body = .mem dA [.leaf cc] (.range 189) real
  /-- `norm.nd`. -/
  rangeNd : ∃ real, (program.predicate (pRange + 3)).body = .mem dA [.leaf nd] (.range 64) real
  /-- `norm.nc`. -/
  rangeNc : ∃ real, (program.predicate (pRange + 4)).body = .mem dA [.leaf nc] (.range 64) real
  /-- `norm.D`. -/
  rangeD : ∃ real, (program.predicate (pRange + 5)).body = .mem dA [.leaf D] (.range 64) real
  /-- `encoding.high`. -/
  high : ∃ real, (program.predicate pHigh).body = .mem dA [.ref eHigh] (.range 16) real
  /-- `encoding.slack`. -/
  slack : ∃ real, (program.predicate pSlack).body =
    .mem dA [.add (.scale (.const 12288) (.apply (.sum 512) (.ref eHigh))) (.leaf off)] (.range 393)
      real
  /-- The norm's shared expressions. -/
  exprs_norm : program.expr e0 =
      .add (.reindex i52 (.concat (.leaf s1) (.leaf z1))) (.reindex i53 (.concat (.leaf s2) (.leaf z1))) ∧
    program.expr (e0 + 1) = .reindex i54 (.leaf a) ∧
    program.expr (e0 + 2) = .reindex i55 (.leaf a) ∧
    program.expr (e0 + 3) = .reindex i56 (.concat (.leaf a) (.leaf z1)) ∧
    program.expr (e0 + 4) = .reindex i57 (.leaf Dc) ∧
    program.expr (e0 + 5) = .reindex i54 (.leaf a) ∧
    program.expr (e0 + 6) = .reindex i58 (.leaf sq) ∧
    program.expr (e0 + 7) = .reindex i59 (.leaf cc) ∧
    program.expr (e0 + 8) = .reindex i55 (.leaf a) ∧
    program.expr (e0 + 9) = .reindex i59 (.leaf cc) ∧
    program.expr (e0 + 10) = .reindex i60 (.leaf sq) ∧
    program.expr (e0 + 11) = .reindex i61 (.leaf cc) ∧
    program.expr (e0 + 12) = .reindex i56 (.concat (.leaf a) (.leaf z1)) ∧
    program.expr (e0 + 13) = .reindex i61 (.leaf cc) ∧
    program.expr (e0 + 14) = .reindex i62 (.leaf sq) ∧
    program.expr (e0 + 15) = .reindex i63 (.leaf cc) ∧
    program.expr (e0 + 16) = .reindex i63 (.leaf cc) ∧
    program.expr (e0 + 17) = .reindex i64 (.leaf sq) ∧
    program.expr (e0 + 18) = .reindex i65 (.leaf cc) ∧
    program.expr (e0 + 19) = .reindex i65 (.leaf cc) ∧
    program.expr (e0 + 20) = .reindex i66 (.leaf sq) ∧
    program.expr (e0 + 21) = .reindex i67 (.leaf cc) ∧
    program.expr (e0 + 22) = .reindex i67 (.leaf cc) ∧
    program.expr (e0 + 23) = .reindex i68 (.leaf sq) ∧
    program.expr (e0 + 24) = .reindex i69 (.concat (.leaf nd) (.leaf z1)) ∧
    program.expr (e0 + 25) = .reindex i70 (.concat (.leaf sq) (.leaf z1)) ∧
    program.expr (e0 + 26) = .reindex i71 (.concat (.leaf nc) (.leaf z1)) ∧
    program.expr (e0 + 27) = .reindex i72 (.concat (.leaf nc) (.leaf z1)) ∧
    program.expr (e0 + 28) = .reindex i73 (.leaf nd) ∧
    program.expr (e0 + 29) = .reindex i74 (.concat (.leaf Dc) (.leaf z1))
  /-- The encoding's shared expressions. -/
  exprs_enc : program.expr eHigh = .reindex iHigh (.leaf a) ∧
    program.expr eMid = .reindex iMid (.leaf a) ∧
    program.expr eB = .add (.ref eMid) (.scale (.const 12287) (.ref eHigh))
  /-- The norm's shared expressions are below `eMax`. -/
  norm_le : e0 + 29 ≤ eMax
  /-- The encoding's shared expressions are below `eMax`. -/
  enc_le : eHigh ≤ eMax ∧ eMid ≤ eMax ∧ eB ≤ eMax
  /-- The encoding's index maps. -/
  idx_enc : (∀ j < 512, iHigh.entry j = 3 * (512 + j) + 2) ∧
    (∀ j < 512, iMid.entry j = 3 * (512 + j) + 1) ∧ iHigh.size = 512 ∧ iMid.size = 512
  /-- The shared expressions read are below the table's length. -/
  exprs_length : eMax < program.exprs.length
  /-- The sizes of the values read. -/
  sizes_A : (program.value s2).size = 512 ∧ (program.value s1).size = 512 ∧
    (program.value a).size = 3072 ∧ (program.value sq).size = 6144 ∧
    (program.value cc).size = 5120 ∧ (program.value nd).size = 102 ∧
    (program.value nc).size = 85 ∧ (program.value D).size = 6 ∧
    (program.value Dc).size = 6 ∧ (program.value z1).size = 1 ∧
    (program.value z).size = 1024
  /-- The values read are prime-typed private source values. -/
  primeA_all : ∀ v ∈ [s2, s1, a, sq, cc, nd, nc, D], v < program.values.length ∧
    program.IsSourceValue v ∧ (program.value v).typeSource = .node ∧
    (program.value v).type = .sub "GF(p^1)" ∧ program.valueField v = fA ∧
    program.isConstant v = false
  /-- `norm.Dc` is a non-constant value of field `fA`. -/
  fields_A : program.valueField Dc = fA ∧ program.isConstant Dc = false
  /-- The program binds no value to an expression. -/
  noBound : ∀ v < program.values.length,
    (match (program.value v).kind with
      | .bound _ => false
      | _ => true) = true
  /-- The zero constants and the slack offset. -/
  consts_A : program.isConstant z1 = true ∧ program.valueField z1 = fA ∧
    (program.constEntries z1).getD 0 0 = 0 ∧ program.isConstant z = true ∧
    program.valueField z = fA ∧ program.constEntries z = List.replicate 1024 0 ∧
    program.isConstant off = true ∧ program.valueField off = fA ∧
    (program.constEntries off).getD 0 0 = 392
  /-- The constant `z1` is zero. -/
  const41 : ∃ es, (program.value z1).kind = .constant es ∧ es.getD 0 0 = 0
  /-- The target holds the base-`64` digits of `β² = 34034726`. -/
  const555 : program.valueField tgt = fA ∧ ∃ es, (program.value tgt).kind = .constant es ∧
    ∀ m < 6, es.getD m 0 = NativeNorm.digit 34034726 m
  /-- The entries of the norm's index maps (coefficient `i < 1024`: digit `3 i + l`, square digit
  `6 i + m`, carry `5 i + m`; the top digit of an `s2` coefficient reads the zero padding at
  `3072`). -/
  i52_entry : ∀ i < 1024, i52.entry i = if i < 512 then i else 512
  i53_entry : ∀ i < 1024, i53.entry i = if i < 512 then 512 else i - 512
  i54_entry : ∀ i < 1024, i54.entry i = 3 * i
  i55_entry : ∀ i < 1024, i55.entry i = 3 * i + 1
  i56_entry : ∀ i < 1024, i56.entry i = if i < 512 then 3 * i + 2 else 3072
  i58_entry : ∀ i < 1024, i58.entry i = 6 * i
  i59_entry : ∀ i < 1024, i59.entry i = 5 * i
  i60_entry : ∀ i < 1024, i60.entry i = 6 * i + 1
  i61_entry : ∀ i < 1024, i61.entry i = 5 * i + 1
  i62_entry : ∀ i < 1024, i62.entry i = 6 * i + 2
  i63_entry : ∀ i < 1024, i63.entry i = 5 * i + 2
  i64_entry : ∀ i < 1024, i64.entry i = 6 * i + 3
  i65_entry : ∀ i < 1024, i65.entry i = 5 * i + 3
  i66_entry : ∀ i < 1024, i66.entry i = 6 * i + 4
  i67_entry : ∀ i < 1024, i67.entry i = 5 * i + 4
  i68_entry : ∀ i < 1024, i68.entry i = 6 * i + 5
  i52_size : i52.size = 1024
  i54_size : i54.size = 1024
  i55_size : i55.size = 1024
  i56_size : i56.size = 1024
  i67_size : i67.size = 1024
  /-- The entries of the batches' maps (`6 b + m`: batch `b`, column `m`) and the complement's. -/
  i69_entry : ∀ j < 102, i69.entry j = if j < 6 then 102 else j - 6
  i71_entry : ∀ j < 102, i71.entry j = if j % 6 = 0 then 85 else 5 * (j / 6) + j % 6 - 1
  i72_entry : ∀ j < 102, i72.entry j = if j % 6 < 5 then 5 * (j / 6) + j % 6 else 85
  i73_entry : ∀ j < 6, i73.entry j = 96 + j
  i74_entry : ∀ j < 6, i74.entry j = if j = 0 then 6 else j - 1
  i57_entry : i57.entry 0 = 5
  i70_entry : ∀ b < 17, ∀ m < 6, ∀ s < 63, i70.entry ((6 * b + m) * 63 + s) =
    if 63 * b + s < 1024 then 6 * (63 * b + s) + m else 6144
  /-- The sizes of the batches', the complement's and the encoding's maps. -/
  idx_sizes : i69.size = 102 ∧ i70.size = 6426 ∧ i71.size = 102 ∧ i72.size = 102 ∧
    i73.size = 6 ∧ i74.size = 6 ∧ iHigh.size = 512 ∧ iMid.size = 512 ∧ i57.size = 1

variable {program : RealizedProgram} {I : RealizedProgram.Interp} [FalconNorm program]

set_option hygiene false in
local notation "dA" => FalconNorm.dA program
set_option hygiene false in
local notation "fA" => FalconNorm.fA program
set_option hygiene false in
local notation "vS2" => FalconNorm.s2 program
set_option hygiene false in
local notation "vS1" => FalconNorm.s1 program
set_option hygiene false in
local notation "vA" => FalconNorm.a program
set_option hygiene false in
local notation "vSq" => FalconNorm.sq program
set_option hygiene false in
local notation "vCc" => FalconNorm.cc program
set_option hygiene false in
local notation "vNd" => FalconNorm.nd program
set_option hygiene false in
local notation "vNc" => FalconNorm.nc program
set_option hygiene false in
local notation "vD" => FalconNorm.D program
set_option hygiene false in
local notation "vDc" => FalconNorm.Dc program
set_option hygiene false in
local notation "vTgt" => FalconNorm.tgt program
set_option hygiene false in
local notation "vOff" => FalconNorm.off program
set_option hygiene false in
local notation "vZ1" => FalconNorm.z1 program
set_option hygiene false in
local notation "vZ" => FalconNorm.z program
set_option hygiene false in
local notation "eN" => FalconNorm.e0 program
set_option hygiene false in
local notation "pN" => FalconNorm.p0 program
set_option hygiene false in
local notation "eMax" => FalconNorm.eMax program

variable [AField (I fA)]

/-- A norm expression's identifier is below `eMax`. -/
theorem eN_le {k : ℕ} (hk : k ≤ 29) : eN + k ≤ eMax :=
  le_trans (by omega) (FalconNorm.norm_le (program := program))

/-- The first norm expression's identifier is below `eMax`. -/
theorem eN_le0 : eN ≤ eMax := le_trans (by omega) (FalconNorm.norm_le (program := program))

/-- The discharger of the side conditions of the readings: a shared expression of the norm below
`eMax`, or arithmetic. -/
macro "norm_disch" : tactic =>
  `(tactic| first | exact eN_le0 | exact eN_le (by norm_num) | norm_num)

variable (program) in
/-- The high parts' shared expression (`FalconNorm.eHigh`). -/
abbrev eHi : ℕ := FalconNorm.eHigh (program := program)

variable (program) in
/-- The middle digits' shared expression (`FalconNorm.eMid`). -/
abbrev eMd : ℕ := FalconNorm.eMid (program := program)

variable (program) in
/-- The parity bits' shared expression (`FalconNorm.eB`). -/
abbrev eBt : ℕ := FalconNorm.eB (program := program)

/-! ## Reading the values -/

/-- **A value of the domain** read in its field. -/
def rdA (e : program.Env I) (v i : ℕ) : (I fA).K :=
  program.evalE (program.reader e) fA (.leaf v) i

/-- **`s2`** read in the domain's field. -/
def s2F (e : program.Env I) (i : Fin falcon512.n) : (I fA).K := rdA e vS2 i

/-- **A field `equal` of the domain holds coordinatewise in its field.** -/
theorem holdsAt_equalA {e : program.Env I} {lhs rhs : RealizedProgram.Expr} {t : RealizedProgram.Target}
    (h : program.HoldsAt e (.equal dA lhs rhs t)) :
    ∀ i < program.exprLen lhs,
      program.evalE (program.reader e) fA lhs i = program.evalE (program.reader e) fA rhs i :=
  fun i hi => by
    have := h i hi
    unfold RealizedProgram.evalWith at this
    rwa [FalconNorm.domainField (program := program)] at this

/-- **The integer reading of a value** for `mod_q` (`RealizedProgram.intOf`). -/
abbrev ia (e : program.Env I) (v i : ℕ) : ℤ :=
  program.intOf (program.reader e) v i

theorem cast_toNat_castElt {a : ℕ} (ha : a = fA) (x : (I a).K)
    (hx : x ∈ (I a).node "GF(p^1)") :
    (((I a).toNat x : ℕ) : (I fA).K) = (RealizedProgram.castElt x : (I fA).K) := by
  subst ha
  rw [RealizedProgram.castElt_self]
  exact AField.natCast_toNat hx

variable (program) in
/-- **A private source value of `A` typed in the prime subfield by its node.** -/
def PrimeA (v : ℕ) : Prop :=
  v < program.values.length ∧ program.IsSourceValue v ∧ (program.value v).typeSource = .node ∧
    (program.value v).type = .sub "GF(p^1)" ∧ program.valueField v = fA ∧
    program.isConstant v = false

/-- **No value of the program is bound** (`noBound`; a value past the table is the default). -/
theorem kind_ne_bound (v : ℕ) (x : RealizedProgram.Expr) : (program.value v).kind ≠ .bound x := by
  intro h
  by_cases hv : v < program.values.length
  · have := FalconNorm.noBound (program := program) v hv
    rw [h] at this
    cases this
  · have hd : program.value v = default := by
      simp only [RealizedProgram.value, List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by omega), Option.getD_none]
    rw [hd] at h
    cases h

/-- **The integer reading of a prime-typed value casts to the value** where the source program holds
(its node type, `SourceSatAt.types`). -/
theorem intOf_cast {e : program.Env I} (hs : program.SourceSatAt e) {v : ℕ} (hv : PrimeA program v)
    {i : ℕ} (hi : i < (program.value v).size) : ((ia e v i : ℤ) : (I fA).K) = rdA e v i := by
  obtain ⟨hvl, hsrc, hts, hty, hf, hc⟩ := hv
  have hmem := hs.types v hvl hsrc hts i hi
  rw [hty] at hmem
  have hint : program.intOf (program.reader e) v i =
      ((I (program.valueField v)).toNat (program.reader e v i) : ℤ) := by
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
theorem holdsAt {e : program.Env I} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p < program.predicates.length) (hsrc : program.inSource (program.predicate p) = true) :
    program.HoldsAt e (program.predicate p).body :=
  hs.preds _ (RealizedProgram.predicate_mem hp) hsrc

/-- **An integer `mod_q` with `q = 0`** is an integer equality at every coordinate. -/
theorem eq_of_modZero {rd : program.Valuation I} {d : ℕ} {l r : RealizedProgram.Expr} {real : RealizedProgram.ModRealization}
    (h : program.HoldsWith rd (.mod d 0 l r real)) {i : ℕ} (hi : i < program.exprLen l) :
    program.evalIntWith rd d l i = program.evalIntWith rd d r i := by
  have := h i hi
  rwa [Nat.cast_zero, zero_dvd_iff, sub_eq_zero] at this

/-- **A range membership of one record** gives a natural below the bound. -/
theorem natBelow_of_mem {rd : program.Valuation I} {n : ℕ} {r : RealizedProgram.Expr} {real : RealizedProgram.InRealization}
    (h : program.HoldsWith rd (.mem dA [r] (.range n) real)) {i : ℕ} (hi : i < program.exprLen r) :
    ∃ k < n, program.evalE rd fA r i = k := by
  have := h i hi
  obtain ⟨k, hk, hkv⟩ := this r (List.mem_singleton_self r)
  refine ⟨k, hk, ?_⟩
  unfold RealizedProgram.evalWith at hkv
  rw [(FalconNorm.domainField (program := program))] at hkv
  exact hkv

/-! ## The shared expressions of domain `A` -/

theorem expr492 : program.expr eN =
    .add (.reindex (FalconNorm.i52 program) (.concat (.leaf vS1) (.leaf vZ1)))
      (.reindex (FalconNorm.i53 program) (.concat (.leaf vS2) (.leaf vZ1))) := FalconNorm.exprs_norm.1
theorem expr493 : program.expr (eN + 1) = .reindex (FalconNorm.i54 program) (.leaf vA) :=
  FalconNorm.exprs_norm.2.1
theorem expr494 : program.expr (eN + 2) = .reindex (FalconNorm.i55 program) (.leaf vA) :=
  FalconNorm.exprs_norm.2.2.1
theorem expr495 : program.expr (eN + 3) = .reindex (FalconNorm.i56 program) (.concat (.leaf vA) (.leaf vZ1)) :=
  FalconNorm.exprs_norm.2.2.2.1
theorem expr496 : program.expr (eN + 4) = .reindex (FalconNorm.i57 program) (.leaf vDc) :=
  FalconNorm.exprs_norm.2.2.2.2.1
theorem expr497 : program.expr (eN + 5) = .reindex (FalconNorm.i54 program) (.leaf vA) :=
  FalconNorm.exprs_norm.2.2.2.2.2.1
theorem expr498 : program.expr (eN + 6) = .reindex (FalconNorm.i58 program) (.leaf vSq) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.1
theorem expr499 : program.expr (eN + 7) = .reindex (FalconNorm.i59 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.1
theorem expr500 : program.expr (eN + 8) = .reindex (FalconNorm.i55 program) (.leaf vA) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.1
theorem expr501 : program.expr (eN + 9) = .reindex (FalconNorm.i59 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.1
theorem expr502 : program.expr (eN + 10) = .reindex (FalconNorm.i60 program) (.leaf vSq) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.1
theorem expr503 : program.expr (eN + 11) = .reindex (FalconNorm.i61 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr504 : program.expr (eN + 12) = .reindex (FalconNorm.i56 program) (.concat (.leaf vA) (.leaf vZ1)) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr505 : program.expr (eN + 13) = .reindex (FalconNorm.i61 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr506 : program.expr (eN + 14) = .reindex (FalconNorm.i62 program) (.leaf vSq) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr507 : program.expr (eN + 15) = .reindex (FalconNorm.i63 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr508 : program.expr (eN + 16) = .reindex (FalconNorm.i63 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr509 : program.expr (eN + 17) = .reindex (FalconNorm.i64 program) (.leaf vSq) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr510 : program.expr (eN + 18) = .reindex (FalconNorm.i65 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr511 : program.expr (eN + 19) = .reindex (FalconNorm.i65 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr512 : program.expr (eN + 20) = .reindex (FalconNorm.i66 program) (.leaf vSq) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr513 : program.expr (eN + 21) = .reindex (FalconNorm.i67 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr514 : program.expr (eN + 22) = .reindex (FalconNorm.i67 program) (.leaf vCc) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr515 : program.expr (eN + 23) = .reindex (FalconNorm.i68 program) (.leaf vSq) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr516 : program.expr (eN + 24) = .reindex (FalconNorm.i69 program) (.concat (.leaf vNd) (.leaf vZ1)) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr517 : program.expr (eN + 25) = .reindex (FalconNorm.i70 program) (.concat (.leaf vSq) (.leaf vZ1)) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr518 : program.expr (eN + 26) = .reindex (FalconNorm.i71 program) (.concat (.leaf vNc) (.leaf vZ1)) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr519 : program.expr (eN + 27) = .reindex (FalconNorm.i72 program) (.concat (.leaf vNc) (.leaf vZ1)) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr520 : program.expr (eN + 28) = .reindex (FalconNorm.i73 program) (.leaf vNd) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
theorem expr521 : program.expr (eN + 29) = .reindex (FalconNorm.i74 program) (.concat (.leaf vDc) (.leaf vZ1)) :=
  FalconNorm.exprs_norm.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem exprHigh : program.expr (eHi program) = .reindex (FalconNorm.iHigh program) (.leaf vA) :=
  FalconNorm.exprs_enc.1
theorem exprMid : program.expr (eMd program) = .reindex (FalconNorm.iMid program) (.leaf vA) :=
  FalconNorm.exprs_enc.2.1
theorem exprB : program.expr (eBt program) = .add (.ref (eMd program))
    (.scale (.const 12287) (.ref (eHi program))) := FalconNorm.exprs_enc.2.2

/-- Domain `A`'s values are prime-typed private source values. -/
theorem primeA {v : ℕ} (hv : v ∈ [vS2, vS1, vA, vSq, vCc, vNd, vNc, vD]) :
    PrimeA program v :=
  FalconNorm.primeA_all v hv

/-! ## The square columns -/

/-- A reference of domain `A` reads its shared expression on the integers. -/
theorem evalIntWith_refA (rd : program.Valuation I) (d : ℕ) {k : ℕ} (hk : k ≤ eMax) :
    program.evalIntWith rd d (.ref k) = program.evalIntWith rd d (program.expr k) :=
  RealizedProgram.evalIntWith_ref (FalconNorm.refsOrdered (program := program)) rd d (lt_of_le_of_lt hk (FalconNorm.exprs_length (program := program)))

/-- A reference of domain `A` reads its shared expression. -/
theorem evalE_refA (rd : program.Valuation I) (f : ℕ) {k : ℕ} (hk : k ≤ eMax) :
    program.evalE rd f (.ref k) = program.evalE rd f (program.expr k) :=
  RealizedProgram.evalE_ref (FalconNorm.refsOrdered (program := program)) rd f (lt_of_le_of_lt hk (FalconNorm.exprs_length (program := program)))

/-- A reference of domain `A` has its shared expression's length. -/
theorem exprLen_refA {k : ℕ} (hk : k ≤ eMax) :
    program.exprLen (.ref k) = program.exprLen (program.expr k) :=
  RealizedProgram.exprLen_ref (FalconNorm.refsOrdered (program := program)) (lt_of_le_of_lt hk (FalconNorm.exprs_length (program := program)))

set_option maxRecDepth 2048 in
/-- The zero constant `const41` reads `0` on the integers. -/
theorem intOf_41 (rd : program.Valuation I) : program.intOf rd vZ1 0 = 0 := by
  obtain ⟨es, hk, he⟩ := FalconNorm.const41 (program := program)
  unfold RealizedProgram.intOf
  simp only [hk, he]
  simp [RealizedProgram.FieldInterp.centered]

/-- **The magnitude's top digit** on the integers: digit `2` of coefficient `i`, `0` for an `s₂`
coefficient (its top slot holds the encoding's high part). -/
def topInt (e : program.Env I) (i : ℕ) : ℤ :=
  if i < 512 then ia e vA (3 * i + 2) else 0

theorem evalIntWith_top (e : program.Env I) {i : ℕ} (hi : i < 1024) :
    program.evalIntWith (program.reader e) dA (.ref (eN + 12)) i = topInt e i := by
  rw [evalIntWith_refA _ _ (by norm_disch), expr504, RealizedProgram.evalIntWith_reindex, (FalconNorm.i56_entry (program := program)) i hi,
    RealizedProgram.evalIntWith_concat, RealizedProgram.exprLen_leaf, (FalconNorm.sizes_A (program := program)).2.2.1, topInt]
  split_ifs with h1 h2 h2
  · rfl
  · omega
  · omega
  · rw [show 3072 - 3072 = 0 from rfl, RealizedProgram.evalIntWith_leaf]
    exact intOf_41 _

set_option maxRecDepth 2048 in
/-- **`norm.column0`**: `a₀² = sq₀ + 64 c₀`. -/
theorem column0_int {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ia e vA (3 * i) * ia e vA (3 * i) = ia e vSq (6 * i) + 64 * ia e vCc (5 * i) := by
  obtain ⟨_, hbd⟩ := FalconNorm.col0 (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 2) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 2) (by simp)).2
  rw [hbd] at h
  have := eq_of_modZero h (i := i) (by
    rw [RealizedProgram.exprLen_mul, exprLen_refA (by norm_disch), expr497, RealizedProgram.exprLen_reindex,
      (FalconNorm.i54_size (program := program))]
    exact hi)
  simp (disch := norm_disch) only [(FalconNorm.domainField (program := program)), RealizedProgram.FieldInterp.centered,
    AField.spec_char, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_scale_const, evalIntWith_refA, expr497, expr498, expr499,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf, (FalconNorm.i54_entry (program := program)) i hi, (FalconNorm.i58_entry (program := program)) i hi,
    (FalconNorm.i59_entry (program := program)) i hi] at this
  exact this

set_option maxRecDepth 2048 in
/-- **`norm.column1`**: `2 a₀ a₁ + c₀ = sq₁ + 64 c₁`. -/
theorem column1_int {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    2 * (ia e vA (3 * i) * ia e vA (3 * i + 1)) + ia e vCc (5 * i) =
      ia e vSq (6 * i + 1) + 64 * ia e vCc (5 * i + 1) := by
  obtain ⟨_, hbd⟩ := FalconNorm.col1 (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 3) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 3) (by simp)).2
  rw [hbd] at h
  have := eq_of_modZero h (i := i) (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale, RealizedProgram.exprLen_mul, exprLen_refA (by norm_disch),
      expr497, RealizedProgram.exprLen_reindex, (FalconNorm.i54_size (program := program))]
    exact hi)
  simp (disch := norm_disch) only [(FalconNorm.domainField (program := program)), RealizedProgram.FieldInterp.centered,
    AField.spec_char, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_scale_const, evalIntWith_refA, expr497, expr500, expr501, expr502, expr503,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf, (FalconNorm.i54_entry (program := program)) i hi, (FalconNorm.i55_entry (program := program)) i hi,
    (FalconNorm.i59_entry (program := program)) i hi, (FalconNorm.i60_entry (program := program)) i hi, (FalconNorm.i61_entry (program := program)) i hi] at this
  exact this

set_option maxRecDepth 2048 in
/-- **`norm.column2`**: `2 a₀ a₂ + a₁² + c₁ = sq₂ + 64 c₂` (`a₂` the top digit, `topInt`). -/
theorem column2_int {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    2 * (ia e vA (3 * i) * topInt e i) + ia e vA (3 * i + 1) * ia e vA (3 * i + 1) +
        ia e vCc (5 * i + 1) = ia e vSq (6 * i + 2) + 64 * ia e vCc (5 * i + 2) := by
  obtain ⟨_, hbd⟩ := FalconNorm.col2 (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 4) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 4) (by simp)).2
  rw [hbd] at h
  have := eq_of_modZero h (i := i) (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale, RealizedProgram.exprLen_mul,
      exprLen_refA (by norm_disch), expr497, RealizedProgram.exprLen_reindex, (FalconNorm.i54_size (program := program))]
    exact hi)
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const,
    RealizedProgram.evalIntWith_mul, evalIntWith_top e hi] at this
  simp (disch := norm_disch) only [(FalconNorm.domainField (program := program)), RealizedProgram.FieldInterp.centered,
    AField.spec_char, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_scale_const, evalIntWith_refA, expr497, expr500, expr505, expr506, expr507,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf, (FalconNorm.i54_entry (program := program)) i hi, (FalconNorm.i55_entry (program := program)) i hi,
    (FalconNorm.i61_entry (program := program)) i hi, (FalconNorm.i62_entry (program := program)) i hi, (FalconNorm.i63_entry (program := program)) i hi] at this
  exact this

set_option maxRecDepth 2048 in
/-- **`norm.column3`**: `2 a₁ a₂ + c₂ = sq₃ + 64 c₃`. -/
theorem column3_int {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    2 * (ia e vA (3 * i + 1) * topInt e i) + ia e vCc (5 * i + 2) =
      ia e vSq (6 * i + 3) + 64 * ia e vCc (5 * i + 3) := by
  obtain ⟨_, hbd⟩ := FalconNorm.col3 (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 5) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 5) (by simp)).2
  rw [hbd] at h
  have := eq_of_modZero h (i := i) (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale, RealizedProgram.exprLen_mul,
      exprLen_refA (by norm_disch), expr500, RealizedProgram.exprLen_reindex]
    rw [(FalconNorm.i55_size (program := program))]
    exact hi)
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_mul,
    evalIntWith_top e hi] at this
  simp (disch := norm_disch) only [(FalconNorm.domainField (program := program)), RealizedProgram.FieldInterp.centered,
    AField.spec_char, RealizedProgram.evalIntWith_add, evalIntWith_refA, expr500, expr508,
    expr509, expr510, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_reindex,
    RealizedProgram.evalIntWith_leaf, (FalconNorm.i55_entry (program := program)) i hi, (FalconNorm.i63_entry (program := program)) i hi, (FalconNorm.i64_entry (program := program)) i hi,
    (FalconNorm.i65_entry (program := program)) i hi] at this
  exact this

set_option maxRecDepth 2048 in
/-- **`norm.column4`**: `a₂² + c₃ = sq₄ + 64 c₄`. -/
theorem column4_int {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    topInt e i * topInt e i + ia e vCc (5 * i + 3) =
      ia e vSq (6 * i + 4) + 64 * ia e vCc (5 * i + 4) := by
  obtain ⟨_, hbd⟩ := FalconNorm.col4 (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 6) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 6) (by simp)).2
  rw [hbd] at h
  have := eq_of_modZero h (i := i) (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_mul, exprLen_refA (by norm_disch), expr504,
      RealizedProgram.exprLen_reindex]
    rw [(FalconNorm.i56_size (program := program))]
    exact hi)
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul, evalIntWith_top e hi] at this
  simp (disch := norm_disch) only [(FalconNorm.domainField (program := program)), RealizedProgram.FieldInterp.centered,
    AField.spec_char, RealizedProgram.evalIntWith_add, evalIntWith_refA, expr511, expr512,
    expr513, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_reindex,
    RealizedProgram.evalIntWith_leaf, (FalconNorm.i65_entry (program := program)) i hi, (FalconNorm.i66_entry (program := program)) i hi, (FalconNorm.i67_entry (program := program)) i hi,
    ] at this
  exact this

set_option maxRecDepth 2048 in
/-- **`norm.column5`**: `c₄ = sq₅`. -/
theorem column5_int {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ia e vCc (5 * i + 4) = ia e vSq (6 * i + 5) := by
  obtain ⟨_, hbd⟩ := FalconNorm.col5 (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 7) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 7) (by simp)).2
  rw [hbd] at h
  have := eq_of_modZero h (i := i) (by
    rw [exprLen_refA (by norm_disch), expr514, RealizedProgram.exprLen_reindex]
    rw [(FalconNorm.i67_size (program := program))]
    exact hi)
  simp (disch := norm_disch) only [(FalconNorm.domainField (program := program)), RealizedProgram.FieldInterp.centered,
    AField.spec_char, evalIntWith_refA, expr514, expr515, RealizedProgram.evalIntWith_reindex,
    RealizedProgram.evalIntWith_leaf, (FalconNorm.i67_entry (program := program)) i hi, (FalconNorm.i68_entry (program := program)) i hi] at this
  exact this

/-! ## The batches and the complement -/

theorem coefInt_zero : (I (program.domainField dA)).coefInt 0 = 0 := by
  rw [(FalconNorm.domainField (program := program))]
  change (I fA).centered ((I fA).toNat 0) = 0
  rw [AField.toNat_zero]
  simp [RealizedProgram.FieldInterp.centered, AField.spec_char]

theorem coefInt_one : (I (program.domainField dA)).coefInt 1 = 1 := by
  rw [(FalconNorm.domainField (program := program))]
  change (I fA).centered ((I fA).toNat 1) = 1
  rw [AField.toNat_one]
  simp [RealizedProgram.FieldInterp.centered, AField.spec_char]

theorem centered_2 : (I (program.domainField dA)).centered 2 = 2 := by
  rw [(FalconNorm.domainField (program := program))]
  change (I fA).centered 2 = 2
  simp [RealizedProgram.FieldInterp.centered, AField.spec_char]

theorem centered_64 : (I (program.domainField dA)).centered 64 = 64 := by
  rw [(FalconNorm.domainField (program := program))]
  change (I fA).centered 64 = 64
  simp [RealizedProgram.FieldInterp.centered, AField.spec_char]

/-- **A coordinate of a value padded by the zero constant**, on the integers. -/
theorem evalIntWith_concat41 (e : program.Env I) {v n : ℕ} (hn : (program.value v).size = n)
    (j : ℕ) (hj : j ≤ n) :
    program.evalIntWith (program.reader e) dA (.concat (.leaf v) (.leaf vZ1)) j =
      if j < n then ia e v j else 0 := by
  rw [RealizedProgram.evalIntWith_concat, RealizedProgram.exprLen_leaf, hn]
  split_ifs with h
  · rfl
  · rw [RealizedProgram.evalIntWith_leaf, show j - n = 0 by omega]
    exact intOf_41 _

/-- **The previous batch's digits** on the integers: `norm.nd` of batch `b − 1`, `0` for the first
batch. -/
def prevInt (e : program.Env I) (b m : ℕ) : ℤ :=
  if b = 0 then 0 else ia e vNd (6 * (b - 1) + m)

/-- **The square digits of batch `b`** in column `m`, on the integers: coefficients
`63 b, …, 63 b + 62` below `1024`. -/
def batchSqInt (e : program.Env I) (b m : ℕ) : ℤ :=
  ∑ s : Fin 63, if 63 * b + (s : ℕ) < 1024 then ia e vSq (6 * (63 * b + s) + m) else 0

/-- **The incoming batch carry** on the integers: `norm.nc` of column `m − 1`, `0` for column
`0`. -/
def ncInInt (e : program.Env I) (b m : ℕ) : ℤ :=
  if m = 0 then 0 else ia e vNc (5 * b + m - 1)

/-- **The outgoing batch carry** on the integers: `norm.nc` of column `m`, `0` for column `5`. -/
def ncOutInt (e : program.Env I) (b m : ℕ) : ℤ :=
  if m < 5 then ia e vNc (5 * b + m) else 0

theorem evalIntWith_516 (e : program.Env I) {b m : ℕ} (hb : b < 17) (hm : m < 6) :
    program.evalIntWith (program.reader e) dA (.ref (eN + 24)) (6 * b + m) = prevInt e b m := by
  rw [evalIntWith_refA _ _ (by norm_disch), expr516, RealizedProgram.evalIntWith_reindex,
    (FalconNorm.i69_entry (program := program)) _ (by omega), prevInt]
  by_cases hb0 : b = 0
  · subst hb0
    rw [if_pos (by omega), if_pos rfl, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.1 _ le_rfl,
      if_neg (lt_irrefl _)]
  · rw [if_neg (by omega), if_neg hb0, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.1 _ (by omega),
      if_pos (by omega), show 6 * b + m - 6 = 6 * (b - 1) + m by omega]

theorem evalIntWith_518 (e : program.Env I) {b m : ℕ} (hb : b < 17) (hm : m < 6) :
    program.evalIntWith (program.reader e) dA (.ref (eN + 26)) (6 * b + m) = ncInInt e b m := by
  rw [evalIntWith_refA _ _ (by norm_disch), expr518, RealizedProgram.evalIntWith_reindex,
    (FalconNorm.i71_entry (program := program)) _ (by omega), ncInInt, show (6 * b + m) % 6 = m by omega,
    show (6 * b + m) / 6 = b by omega]
  by_cases hm0 : m = 0
  · rw [if_pos hm0, if_pos hm0, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.1 _ le_rfl,
      if_neg (lt_irrefl _)]
  · rw [if_neg hm0, if_neg hm0, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.1 _ (by omega),
      if_pos (by omega)]

theorem evalIntWith_519 (e : program.Env I) {b m : ℕ} (hb : b < 17) (hm : m < 6) :
    program.evalIntWith (program.reader e) dA (.ref (eN + 27)) (6 * b + m) = ncOutInt e b m := by
  rw [evalIntWith_refA _ _ (by norm_disch), expr519, RealizedProgram.evalIntWith_reindex,
    (FalconNorm.i72_entry (program := program)) _ (by omega), ncOutInt, show (6 * b + m) % 6 = m by omega,
    show (6 * b + m) / 6 = b by omega]
  by_cases hm5 : m < 5
  · rw [if_pos hm5, if_pos hm5, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.1 _ (by omega),
      if_pos (by omega)]
  · rw [if_neg hm5, if_neg hm5, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.1 _ le_rfl,
      if_neg (lt_irrefl _)]

theorem evalIntWith_517 (e : program.Env I) {b m : ℕ} (hb : b < 17) (hm : m < 6)
    (s : Fin 63) :
    program.evalIntWith (program.reader e) dA (.ref (eN + 25)) ((6 * b + m) * 63 + s) =
      if 63 * b + (s : ℕ) < 1024 then ia e vSq (6 * (63 * b + s) + m) else 0 := by
  rw [evalIntWith_refA _ _ (by norm_disch), expr517, RealizedProgram.evalIntWith_reindex,
    (FalconNorm.i70_entry (program := program)) b hb m hm s s.isLt]
  split_ifs with h1
  · rw [evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.1 _ (by omega), if_pos (by omega)]
  · rw [evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.1 _ le_rfl, if_neg (lt_irrefl _)]

/-- **`norm.normalize`**: batch `b`'s column `m`, `prev + Σ sq + nc_{m−1} = nd + 64 nc_m`. -/
theorem normalize_int {e : program.Env I} (hs : program.SourceSatAt e) {b m : ℕ}
    (hb : b < 17) (hm : m < 6) :
    prevInt e b m + batchSqInt e b m + ncInInt e b m =
      ia e vNd (6 * b + m) + 64 * ncOutInt e b m := by
  obtain ⟨_, hbd⟩ := FalconNorm.normalize (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 8) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 8) (by simp)).2
  rw [hbd] at h
  have hj : 6 * b + m < 102 := by omega
  have := eq_of_modZero h (i := 6 * b + m) (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, exprLen_refA (by norm_disch), expr516,
      RealizedProgram.exprLen_reindex, (FalconNorm.idx_sizes (program := program)).1]
    exact hj)
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_apply,
    RealizedProgram.NamedOp.applyInt_batched_sum coefInt_zero coefInt_one _ _ hj, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_scale_const, centered_64, RealizedProgram.evalIntWith_leaf,
    evalIntWith_516 e hb hm, evalIntWith_518 e hb hm, evalIntWith_519 e hb hm] at this
  rw [Finset.sum_congr rfl fun s _ => evalIntWith_517 e hb hm s] at this
  exact this

set_option maxRecDepth 2048 in
/-- The complement's target digits (`norm.target`, value `555`) read on the integers: the base-`64`
digits of `β² = 34034726`. -/
theorem intOf_555 (rd : program.Valuation I) {m : ℕ} (hm : m < 6) :
    program.intOf rd vTgt m = (NativeNorm.digit 34034726 m : ℤ) := by
  obtain ⟨hf, es, hk, he⟩ := FalconNorm.const555 (program := program)
  unfold RealizedProgram.intOf
  simp only [hk, he m hm, hf]
  have hd : NativeNorm.digit 34034726 m < 64 := Nat.mod_lt _ (by norm_disch)
  change (I fA).centered _ = _
  unfold RealizedProgram.FieldInterp.centered
  rw [AField.spec_char, if_pos (by omega)]

/-- **The incoming complement carry** on the integers: `norm.Dc` of column `m − 1`, `0` for
column `0`. -/
def dcInInt (e : program.Env I) (m : ℕ) : ℤ :=
  if m = 0 then 0 else ia e vDc (m - 1)

/-- **`norm.complement`**: `S_m + D_m + Dc_{m−1} = digit(β², m) + 64 Dc_m`, `S` the last batch's
digits. -/
theorem complement_int {e : program.Env I} (hs : program.SourceSatAt e) {m : ℕ}
    (hm : m < 6) :
    ia e vNd (96 + m) + ia e vD m + dcInInt e m =
      (NativeNorm.digit 34034726 m : ℤ) + 64 * ia e vDc m := by
  obtain ⟨_, hbd⟩ := FalconNorm.complement (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 9) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 9) (by simp)).2
  rw [hbd] at h
  have := eq_of_modZero h (i := m) (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, exprLen_refA (by norm_disch), expr520,
      RealizedProgram.exprLen_reindex, (FalconNorm.idx_sizes (program := program)).2.2.2.2.1]
    exact hm)
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_scale_const, centered_64, RealizedProgram.evalIntWith_leaf,
    RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf, intOf_555 _ hm,
    evalIntWith_refA _ _ (by norm_disch), expr520, evalIntWith_refA _ _ (by norm_disch), expr521,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_reindex, (FalconNorm.i73_entry (program := program)) m hm,
    (FalconNorm.i74_entry (program := program)) m hm, RealizedProgram.evalIntWith_leaf] at this
  rw [dcInInt]
  by_cases hm0 : m = 0
  · rw [if_pos hm0]
    rw [if_pos hm0, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.2.1 _ le_rfl,
      if_neg (lt_irrefl _)] at this
    exact this
  · rw [if_neg hm0]
    rw [if_neg hm0, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.2.1 _ (by omega),
      if_pos (by omega)] at this
    exact this

/-! ## The field equations -/

/-- A value of domain `A` read through the zero constant `const41` reads `0`. -/
theorem evalE_41 (e : program.Env I) :
    program.evalE (program.reader e) fA (.leaf vZ1) 0 = 0 := by
  obtain ⟨c41, f41, e41, -⟩ := FalconNorm.consts_A (program := program)
  rw [RealizedProgram.evalE_leaf_of_isConstant e c41, RealizedProgram.constRead_of_valueField f41, e41]
  exact (AField.decode_eq (FA := I fA) 0).trans Nat.cast_zero

/-- The zero constant `const42` reads `0`. -/
theorem evalE_42 (e : program.Env I) (i : ℕ) :
    program.evalE (program.reader e) fA (.leaf vZ) i = 0 := by
  obtain ⟨-, -, -, c42, f42, e42, -⟩ := FalconNorm.consts_A (program := program)
  rw [RealizedProgram.evalE_leaf_of_isConstant e c42, RealizedProgram.constRead_of_valueField f42, e42,
    List.getD_eq_getElem?_getD, List.getElem?_replicate]
  split <;> exact (AField.decode_eq (FA := I fA) 0).trans Nat.cast_zero

/-- **A coordinate of a value padded by the zero constant.** -/
theorem evalE_concat41 (e : program.Env I) {v n : ℕ} (hn : (program.value v).size = n)
    (j : ℕ) (hj : j ≤ n) :
    program.evalE (program.reader e) fA (.concat (.leaf v) (.leaf vZ1)) j =
      if j < n then rdA e v j else 0 := by
  rw [RealizedProgram.evalE_concat, RealizedProgram.exprLen_leaf, hn]
  split_ifs with h
  · rfl
  · rw [show j - n = 0 by omega]
    exact evalE_41 e

/-- **`norm.top`**: the last complement carry is `0`. -/
theorem top_eq {e : program.Env I} (hs : program.SourceSatAt e) : rdA e vDc 5 = 0 := by
  obtain ⟨_, hbd⟩ := FalconNorm.top (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (pN + 1) (by simp)).1
    (FalconNorm.inSource_A (program := program) (pN + 1) (by simp)).2
  rw [hbd] at h
  have := holdsAt_equalA h 0 (by
    rw [exprLen_refA (by norm_disch), expr496, RealizedProgram.exprLen_reindex, (FalconNorm.idx_sizes (program := program)).2.2.2.2.2.2.2.2]
    norm_num)
  change program.evalE _ fA (.ref (eN + 4)) 0 = program.evalE _ fA (.leaf vZ1) 0 at this
  rw [evalE_refA _ _ (by norm_disch), expr496, RealizedProgram.evalE_reindex, (FalconNorm.i57_entry (program := program)), evalE_41] at this
  exact this

/-- **The type check of `norm.Dc`**: the complement carries are bits. -/
theorem dc_bool {e : program.Env I} (hs : program.SourceSatAt e) {m : ℕ} (hm : m < 6) :
    rdA e vDc m * rdA e vDc m = rdA e vDc m := by
  obtain ⟨_, hbd⟩ := FalconNorm.dcBool (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (FalconNorm.pDc (program := program)) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pDc (program := program)) (by simp)).2
  rw [hbd] at h
  exact holdsAt_equalA h m (by rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_leaf, (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.2.1]; exact hm)

/-- **The coefficient the norm reads**: `s₁` below `512`, then `s₂` (the norm's input
`s₁ ‖ s₂`). -/
def normInF (e : program.Env I) (i : ℕ) : (I fA).K :=
  if i < 512 then rdA e vS1 i else rdA e vS2 (i - 512)

/-- **The magnitude's top digit**: digit `2` of coefficient `i`, `0` for an `s₂` coefficient. -/
def topF (e : program.Env I) (i : ℕ) : (I fA).K :=
  if i < 512 then rdA e vA (3 * i + 2) else 0

theorem evalE_492 (e : program.Env I) {i : ℕ} (hi : i < 1024) :
    program.evalE (program.reader e) fA (.ref eN) i = normInF e i := by
  rw [evalE_refA _ _ (by norm_disch), expr492, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, (FalconNorm.i52_entry (program := program)) i hi, (FalconNorm.i53_entry (program := program)) i hi, normInF]
  by_cases h : i < 512
  · rw [if_pos h, if_pos h, if_pos h, evalE_concat41 e (FalconNorm.sizes_A (program := program)).2.1 _ (by omega), if_pos h,
      evalE_concat41 e (FalconNorm.sizes_A (program := program)).1 _ le_rfl, if_neg (lt_irrefl _), add_zero]
  · rw [if_neg h, if_neg h, if_neg h, evalE_concat41 e (FalconNorm.sizes_A (program := program)).2.1 _ le_rfl,
      if_neg (lt_irrefl _), evalE_concat41 e (FalconNorm.sizes_A (program := program)).1 _ (by omega), if_pos (by omega), zero_add]

theorem evalE_495 (e : program.Env I) {i : ℕ} (hi : i < 1024) :
    program.evalE (program.reader e) fA (.ref (eN + 3)) i = topF e i := by
  rw [evalE_refA _ _ (by norm_disch), expr495, RealizedProgram.evalE_reindex, (FalconNorm.i56_entry (program := program)) i hi, topF]
  by_cases h : i < 512
  · rw [if_pos h, if_pos h, evalE_concat41 e (FalconNorm.sizes_A (program := program)).2.2.1 _ (by omega), if_pos (by omega)]
  · rw [if_neg h, if_neg h, evalE_concat41 e (FalconNorm.sizes_A (program := program)).2.2.1 _ le_rfl, if_neg (lt_irrefl _)]

theorem decode_A (c : ℕ) : (I fA).decode c = (c : (I fA).K) := AField.decode_eq c

/-- **`norm.center`**: `v² = mag²`, `v` the coefficient and `mag = a₀ + 64 a₁ + 4096 a₂` its
magnitude (`a₂` the top digit, `topF`). -/
theorem center_eq {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    normInF e i * normInF e i =
      (rdA e vA (3 * i) + 64 * rdA e vA (3 * i + 1) + 4096 * topF e i) *
        (rdA e vA (3 * i) + 64 * rdA e vA (3 * i + 1) + 4096 * topF e i) := by
  obtain ⟨_, hbd⟩ := FalconNorm.center (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) pN (by simp)).1
    (FalconNorm.inSource_A (program := program) pN (by simp)).2
  rw [hbd] at h
  have := holdsAt_equalA h i (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_mul, exprLen_refA (by norm_disch), expr492,
      RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex, (FalconNorm.i52_size (program := program))]
    exact hi)
  change program.evalE _ fA _ i = program.evalE _ fA (.leaf vZ) i at this
  rw [evalE_42, RealizedProgram.evalE_add, RealizedProgram.evalE_mul, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_scale_const, evalE_492 e hi, evalE_495 e hi, evalE_refA _ _ (by norm_disch),
    expr493, evalE_refA _ _ (by norm_disch), expr494, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, (FalconNorm.i54_entry (program := program)) i hi, (FalconNorm.i55_entry (program := program)) i hi] at this
  try dsimp only at this
  simp only [AField.decode_eq] at this
  change normInF e i * normInF e i + ((12288 : ℕ) : (I fA).K) *
    ((rdA e vA (3 * i) + ((64 : ℕ) : (I fA).K) * rdA e vA (3 * i + 1) +
      ((4096 : ℕ) : (I fA).K) * topF e i) *
    (rdA e vA (3 * i) + ((64 : ℕ) : (I fA).K) * rdA e vA (3 * i + 1) +
      ((4096 : ℕ) : (I fA).K) * topF e i)) = 0 at this
  have hq : ((12288 : ℕ) : (I fA).K) = -1 := by
    have h0 : ((12289 : ℕ) : (I fA).K) = 0 := CharP.cast_eq_zero _ 12289
    push_cast at h0 ⊢
    linear_combination h0
  rw [hq] at this
  push_cast at this
  linear_combination this

/-- **The parity bit** of `s₂` coefficient `i`: its middle digit minus twice its top digit. -/
def parityF (e : program.Env I) (i : ℕ) : (I fA).K :=
  rdA e vA (3 * (512 + i) + 1) - 2 * rdA e vA (3 * (512 + i) + 2)

/-- **`encoding.b.boolean`**: the parity bit of every `s₂` coefficient is a bit. -/
theorem parity_bool {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 512) :
    parityF e i * parityF e i = parityF e i := by
  obtain ⟨_, hbd⟩ := FalconNorm.encB (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (FalconNorm.pEncB (program := program)) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pEncB (program := program)) (by simp)).2
  rw [hbd] at h
  have := holdsAt_equalA h i (by
    rw [RealizedProgram.exprLen_mul, exprLen_refA (FalconNorm.enc_le (program := program)).2.2, exprB, RealizedProgram.exprLen_add,
      exprLen_refA (FalconNorm.enc_le (program := program)).2.1, exprMid, RealizedProgram.exprLen_reindex, (FalconNorm.idx_enc (program := program)).2.2.2]
    exact hi)
  change program.evalE _ fA (.mul (.ref (eBt program)) (.ref (eBt program))) i = program.evalE _ fA (.ref (eBt program)) i at this
  have h529 : program.evalE (program.reader e) fA (.ref (eBt program)) i = parityF e i := by
    rw [evalE_refA _ _ (FalconNorm.enc_le (program := program)).2.2, exprB, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
      evalE_refA _ _ (FalconNorm.enc_le (program := program)).2.1, exprMid, evalE_refA _ _ (FalconNorm.enc_le (program := program)).1, exprHigh,
      RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex, (FalconNorm.idx_enc (program := program)).2.1 i hi, (FalconNorm.idx_enc (program := program)).1 i hi, parityF,
      decode_A]
    have hq : ((12287 : ℕ) : (I fA).K) = -2 := by
      have h0 : ((12289 : ℕ) : (I fA).K) = 0 := CharP.cast_eq_zero _ 12289
      push_cast at h0 ⊢
      linear_combination h0
    rw [hq]
    unfold rdA
    ring
  rw [RealizedProgram.evalE_mul, h529] at this
  exact this

/-! ## The advice -/

/-- **The integer reading of a value of `A`** as a natural. -/
def nA (e : program.Env I) (v j : ℕ) : ℕ := (I fA).toNat (rdA e v j)

/-- The integer reading of a natural below `q` in `FA` is the natural. -/
theorem toNat_natCast_A {k : ℕ} (hk : k < 12289) : (I fA).toNat (k : (I fA).K) = k :=
  AField.toNat_natCast hk

/-- **The integer reading of a non-constant value of `A`** is its natural reading. -/
theorem ia_eq_nA (e : program.Env I) {v : ℕ} (hf : program.valueField v = fA)
    (hc : program.isConstant v = false) (j : ℕ) : ia e v j = nA e v j := by
  have hint : program.intOf (program.reader e) v j =
      ((I (program.valueField v)).toNat (program.reader e v j) : ℤ) := by
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
theorem nA_cast {e : program.Env I} (hs : program.SourceSatAt e) {v : ℕ} (hv : PrimeA program v)
    {j : ℕ} (hj : j < (program.value v).size) : ((nA e v j : ℕ) : (I fA).K) = rdA e v j := by
  have := intOf_cast hs hv hj
  rw [ia_eq_nA e hv.2.2.2.2.1 hv.2.2.2.2.2, Int.cast_natCast] at this
  exact this

/-- **Limb `l` of a column carry** `norm.cc[j]`, base `64`. -/
def ccLimb (e : program.Env I) (j : ℕ) (l : Fin 2) : (I fA).K :=
  ((if (l : ℕ) = 0 then nA e vCc j % 64 else nA e vCc j / 64 : ℕ) : (I fA).K)

/-- **The native norm's witness read off the program** (`NativeNorm.Wit`): the magnitude digits
`norm.a`, the square digits `norm.sq`, each carry `norm.cc` in two base-`64` limbs, the batch
digits and carries `norm.nd`, `norm.nc`, the complement `norm.D` and its carries `norm.Dc`. -/
def normWit (e : program.Env I) : NativeNorm.Wit (I fA).K where
  square i := ⟨fun l => rdA e vA (3 * i + l), fun m => rdA e vSq (6 * i + m),
    fun m l => ccLimb e (5 * i + m) l⟩
  batch b := ⟨fun m => rdA e vNd (6 * b + m), fun m => rdA e vNc (5 * b + m)⟩
  D m := rdA e vD m
  Dcarry m := rdA e vDc m

/-- **A column carry is its two limbs.** -/
theorem carryVal_normWit {e : program.Env I} (hs : program.SourceSatAt e) (i : Fin 1024)
    (m : Fin 5) : NativeNorm.carryVal ((normWit e).square i) m = rdA e vCc (5 * i + m) := by
  unfold NativeNorm.carryVal
  simp only [normWit, List.ofFn_succ, List.ofFn_zero, Range.reconstruct_cons]
  simp only [Range.reconstruct, List.zipIdx_nil, List.map_nil, List.sum_nil, mul_zero, add_zero,
    ccLimb, Fin.isValue, Fin.val_zero, Fin.val_succ, ite_true, show (0 : ℕ) + 1 ≠ 0 by omega,
    ite_false]
  rw [← nA_cast hs (primeA (program := program) (v := vCc) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.1]; omega)]
  have := Nat.mod_add_div (nA e vCc (5 * ↑i + ↑m)) 64
  exact_mod_cast congrArg (Nat.cast : ℕ → (I fA).K) this

/-- **The advice of the algebra read off the program** (`Native.Committed`): `signature.s1`,
the norm's witness (`normWit`), and the encoding's high slack digit `slackHi`. -/
def algOf (e : program.Env I) (slackHi : (I fA).K) :
    Native.Committed (I fA).K :=
  ⟨fun i => rdA e vS1 i, normWit e, slackHi⟩

theorem algOf_s1 (e : program.Env I) (slackHi : (I fA).K) (i : Fin falcon512.n) :
    (algOf e slackHi).s1 i = rdA e vS1 i := rfl

theorem normInputs_algOf (e : program.Env I) (slackHi : (I fA).K) (i : Fin 1024) :
    Native.normInputs (s2F e) (algOf e slackHi) i = normInF e i := by
  unfold Native.normInputs normInF
  by_cases h : (i : ℕ) < 512
  · rw [dif_pos (show (i : ℕ) < falcon512.n from h), if_pos h]
    simp only [algOf]
  · rw [dif_neg (show ¬ (i : ℕ) < falcon512.n from h), if_neg h]
    simp only [s2F, rdA]
    rfl

/-- The top digit's integer reading casts to the top digit. -/
theorem topInt_cast {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 1024) :
    ((topInt e i : ℤ) : (I fA).K) = topF e i := by
  unfold topInt topF
  split_ifs with h
  · exact intOf_cast hs (primeA (program := program) (v := vA) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.1]; omega)
  · exact Int.cast_zero

/-- The limbs the schoolbook square reads: the magnitude digits, the top one `topF`. -/
theorem limbs_normWit (e : program.Env I) (i : Fin 1024) (l : Fin 3) :
    NativeNorm.limbs (decide (512 ≤ (i : ℕ))) ((normWit e).square i) l =
      if (l : ℕ) = 2 then topF e i else rdA e vA (3 * i + l) := by
  unfold NativeNorm.limbs topF
  by_cases hl : (l : ℕ) = 2
  · rw [if_pos hl]
    by_cases hi : (i : ℕ) < 512
    · rw [if_neg (by simp; omega), if_pos hi]
      simp only [normWit, hl]
    · rw [if_pos (by simp; omega), if_neg hi]
  · rw [if_neg hl, if_neg (by simp [hl])]
    simp only [normWit]

/-- **The square check of coefficient `i`** holds (`NativeNorm.square_ok_iff`): `norm.center` and
the six columns, cast from the integers (`column0_int` … `column5_int`). -/
theorem square_ok {e : program.Env I} (hs : program.SourceSatAt e) (slackHi : (I fA).K)
    (i : Fin 1024) :
    (NativeNorm.square (decide (512 ≤ (i : ℕ)))
      (Native.normInputs (s2F e) (algOf e slackHi) i)
      ((normWit e).square i)).ok = true := by
  have hi := i.isLt
  rw [NativeNorm.square_ok_iff, normInputs_algOf]
  have hl : ∀ l : Fin 3, NativeNorm.limbs (decide (512 ≤ (i : ℕ))) ((normWit e).square i) l =
      if (l : ℕ) = 2 then topF e i else rdA e vA (3 * i + l) := limbs_normWit e i
  have c548 : ∀ j < 3072, ((ia e vA j : ℤ) : (I fA).K) = rdA e vA j := fun j hj =>
    intOf_cast hs (primeA (program := program) (v := vA) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.1]; exact hj)
  have c549 : ∀ j < 6144, ((ia e vSq j : ℤ) : (I fA).K) = rdA e vSq j := fun j hj =>
    intOf_cast hs (primeA (program := program) (v := vSq) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.1]; exact hj)
  have c550 : ∀ j < 5120, ((ia e vCc j : ℤ) : (I fA).K) = rdA e vCc j := fun j hj =>
    intOf_cast hs (primeA (program := program) (v := vCc) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.1]; exact hj)
  have ht := topInt_cast hs hi
  refine ⟨?_, fun m => ?_⟩
  · rw [center_eq hs hi]
    unfold NativeNorm.mag
    simp only [List.ofFn_succ, List.ofFn_zero, Range.reconstruct_cons, hl]
    simp only [Range.reconstruct, List.zipIdx_nil, List.map_nil, List.sum_nil, Fin.isValue,
      Fin.val_zero, Fin.val_succ]
    norm_num
    ring
  · have hcv : ∀ m' : Fin 5, NativeNorm.carryVal ((normWit e).square i) m' =
        rdA e vCc (5 * i + m') := carryVal_normWit hs i
    fin_cases m
    · have h0 := congrArg (Int.cast : ℤ → (I fA).K) (column0_int hs hi)
      push_cast at h0
      rw [c548 (3 * i) (by omega), c549 (6 * i) (by omega), c550 (5 * i) (by omega)] at h0
      simp only [NativeNorm.colprod, Fin.sum_univ_three, hl, NativeNorm.carryIn,
        NativeNorm.carryOut, hcv]
      norm_num
      simp only [normWit]
      linear_combination h0
    · have h0 := congrArg (Int.cast : ℤ → (I fA).K) (column1_int hs hi)
      push_cast at h0
      rw [c548 (3 * i) (by omega), c548 (3 * i + 1) (by omega), c549 (6 * i + 1) (by omega),
        c550 (5 * i) (by omega), c550 (5 * i + 1) (by omega)] at h0
      simp only [NativeNorm.colprod, Fin.sum_univ_three, hl, NativeNorm.carryIn,
        NativeNorm.carryOut, hcv]
      norm_num
      simp only [normWit]
      linear_combination h0
    · have h0 := congrArg (Int.cast : ℤ → (I fA).K) (column2_int hs hi)
      push_cast at h0
      rw [c548 (3 * i) (by omega), c548 (3 * i + 1) (by omega), ht, c549 (6 * i + 2) (by omega),
        c550 (5 * i + 1) (by omega), c550 (5 * i + 2) (by omega)] at h0
      simp only [NativeNorm.colprod, Fin.sum_univ_three, hl, NativeNorm.carryIn,
        NativeNorm.carryOut, hcv]
      norm_num
      simp only [normWit]
      linear_combination h0
    · have h0 := congrArg (Int.cast : ℤ → (I fA).K) (column3_int hs hi)
      push_cast at h0
      rw [c548 (3 * i + 1) (by omega), ht, c549 (6 * i + 3) (by omega),
        c550 (5 * i + 2) (by omega), c550 (5 * i + 3) (by omega)] at h0
      simp only [NativeNorm.colprod, Fin.sum_univ_three, hl, NativeNorm.carryIn,
        NativeNorm.carryOut, hcv]
      norm_num
      simp only [normWit]
      linear_combination h0
    · have h0 := congrArg (Int.cast : ℤ → (I fA).K) (column4_int hs hi)
      push_cast at h0
      rw [ht, c549 (6 * i + 4) (by omega), c550 (5 * i + 3) (by omega),
        c550 (5 * i + 4) (by omega)] at h0
      simp only [NativeNorm.colprod, Fin.sum_univ_three, hl, NativeNorm.carryIn,
        NativeNorm.carryOut, hcv]
      norm_num
      simp only [normWit]
      linear_combination h0
    · have h0 := congrArg (Int.cast : ℤ → (I fA).K) (column5_int hs hi)
      push_cast at h0
      rw [c549 (6 * i + 5) (by omega), c550 (5 * i + 4) (by omega)] at h0
      simp only [NativeNorm.colprod, Fin.sum_univ_three, hl, NativeNorm.carryIn,
        NativeNorm.carryOut, hcv]
      norm_num
      simp only [normWit]
      linear_combination h0

/-- The integer readings of domain `A`'s prime-typed values cast to the values. -/
theorem cast551 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 102) :
    ((ia e vNd j : ℤ) : (I fA).K) = rdA e vNd j :=
  intOf_cast hs (primeA (program := program) (v := vNd) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.2.1]; exact hj)

theorem cast552 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 85) :
    ((ia e vNc j : ℤ) : (I fA).K) = rdA e vNc j :=
  intOf_cast hs (primeA (program := program) (v := vNc) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.1]; exact hj)

theorem cast553 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 6) :
    ((ia e vD j : ℤ) : (I fA).K) = rdA e vD j :=
  intOf_cast hs (primeA (program := program) (v := vD) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.1]; exact hj)

theorem cast549 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 6144) :
    ((ia e vSq j : ℤ) : (I fA).K) = rdA e vSq j :=
  intOf_cast hs (primeA (program := program) (v := vSq) (by simp)) (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.1]; exact hj)

/-- The complement carries `norm.Dc` (bits by their type check) cast from their integer
readings. -/
theorem cast554 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 6) :
    ((ia e vDc j : ℤ) : (I fA).K) = rdA e vDc j := by
  rw [ia_eq_nA e (FalconNorm.fields_A (program := program)).1 (FalconNorm.fields_A (program := program)).2, Int.cast_natCast, nA]
  rcases eq_zero_or_one_of_sq_eq_self ((sq _).trans (dc_bool hs hj)) with h | h
  · rw [h]
    change (((I fA).toNat 0 : ℕ) : (I fA).K) = 0
    rw [AField.toNat_zero, Nat.cast_zero]
  · rw [h]
    change (((I fA).toNat 1 : ℕ) : (I fA).K) = 1
    rw [AField.toNat_one, Nat.cast_one]

/-- **The batch normalization of batch `b`** holds (`NativeNorm.batchNormalize_ok_iff`), cast from
`norm.normalize` (`normalize_int`). -/
theorem batch_ok {e : program.Env I} (hs : program.SourceSatAt e) (b : Fin 17) :
    (NativeNorm.batchNormalize (NativeNorm.batchCol (normWit e) b) ((normWit e).batch b)).ok =
      true := by
  rw [NativeNorm.batchNormalize_ok_iff]
  intro m
  have hb := b.isLt
  have hm := m.isLt
  have h := congrArg (Int.cast : ℤ → (I fA).K) (normalize_int hs hb hm)
  push_cast at h
  have hprev : ((prevInt e b m : ℤ) : (I fA).K) = NativeNorm.prevDigits (normWit e) b m := by
    unfold prevInt NativeNorm.prevDigits
    split_ifs with h0
    · exact Int.cast_zero
    · rw [cast551 hs (by omega)]
      simp only [normWit]
  have hsq : ((batchSqInt e b m : ℤ) : (I fA).K) =
      ∑ k ∈ Finset.Ico (NativeNorm.startOf b) (NativeNorm.startOf ((b : ℕ) + 1)),
        NativeNorm.sqAt (normWit e) k m := by
    rw [NativeNorm.sum_Ico_startOf (fun k hk => by rw [NativeNorm.sqAt, dif_neg (by omega)]) hb,
      batchSqInt, Int.cast_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold NativeNorm.sqAt
    split_ifs with h1
    · rw [cast549 hs (by omega)]
      simp only [normWit]
    · exact Int.cast_zero
  have hin : ((ncInInt e b m : ℤ) : (I fA).K) =
      NativeNorm.carryIn ((normWit e).batch b).ncarry m := by
    unfold ncInInt NativeNorm.carryIn
    split_ifs with h0
    · exact Int.cast_zero
    · rw [cast552 hs (by omega)]
      simp only [normWit]
      congr 2
      omega
  have hout : ((ncOutInt e b m : ℤ) : (I fA).K) =
      NativeNorm.carryOut ((normWit e).batch b).ncarry m := by
    unfold ncOutInt NativeNorm.carryOut
    split_ifs with h0
    · rw [cast552 hs (by omega)]
      simp only [normWit]
    · exact Int.cast_zero
  rw [hprev, hsq, hin, hout, cast551 hs (by omega)] at h
  unfold NativeNorm.batchCol
  simp only [normWit] at h ⊢
  linear_combination h

/-- **The complement bound** holds (`NativeNorm.leqConst_ok_iff`): `norm.Dc` bits, the
complement's columns (`complement_int`) and the last carry `0` (`norm.top`). -/
theorem bound_ok {e : program.Env I} (hs : program.SourceSatAt e) :
    (NativeNorm.leqConst 34034726 ((normWit e).batch 16).ndig (normWit e).D
      (normWit e).Dcarry).ok = true := by
  rw [NativeNorm.leqConst_ok_iff]
  refine ⟨fun m => ?_, fun m => ?_, by simp only [normWit]; exact top_eq hs⟩
  · have := dc_bool hs m.isLt
    simp only [normWit]
    linear_combination this
  · have hm := m.isLt
    have h := congrArg (Int.cast : ℤ → (I fA).K) (complement_int hs hm)
    push_cast at h
    have hdc : ((dcInInt e m : ℤ) : (I fA).K) = NativeNorm.dcIn (normWit e).Dcarry m := by
      unfold dcInInt NativeNorm.dcIn
      split_ifs with h0
      · exact Int.cast_zero
      · rw [cast554 hs (by omega)]
        simp only [normWit]
    rw [cast551 hs (by omega), cast553 hs hm, cast554 hs hm, hdc] at h
    simp only [normWit] at h ⊢
    linear_combination h

/-- **The native norm's constraint groups hold** at the program's witness (`NativeNorm.Holds`). -/
theorem normHolds {e : program.Env I} (hs : program.SourceSatAt e) (slackHi : (I fA).K) :
    NativeNorm.Holds (Native.normInputs (s2F e) (algOf e slackHi))
      (algOf e slackHi).norm :=
  ⟨square_ok hs slackHi, batch_ok hs, bound_ok hs⟩

/-- **The encoding's Boolean checks hold** (`encoding.b.boolean`, `parity_bool`). -/
theorem encodingBits {e : program.Env I} (hs : program.SourceSatAt e)
    (slackHi : (I fA).K) : NativeEncoding.BitsHold (algOf e slackHi).norm := by
  intro i
  have := parity_bool hs i.isLt
  have hp : NativeEncoding.parityBit (algOf e slackHi).norm i = parityF e i := by
    simp only [NativeEncoding.parityBit, NativeEncoding.high, algOf, normWit, parityF]
    norm_num
  rw [hp]
  linear_combination this

/-! ## The range requests -/

/-- **A range membership of a value of `A`, read at its predicate.** -/
theorem natBelow_pred {e : program.Env I} (hs : program.SourceSatAt e) {p v n sz : ℕ}
    (hp : p < program.predicates.length) (hsrc : program.inSource (program.predicate p) = true)
    {real : RealizedProgram.InRealization} (hb : (program.predicate p).body = .mem dA [.leaf v] (.range n) real)
    (hsz : (program.value v).size = sz) {i : ℕ} (hi : i < sz) :
    Range.IsNatBelow n (rdA e v i) := by
  have h := holdsAt hs hp hsrc
  rw [hb] at h
  obtain ⟨k, hk, hkv⟩ := natBelow_of_mem h (i := i) (by rw [RealizedProgram.exprLen_leaf, hsz]; exact hi)
  exact ⟨k, hk, hkv.symm⟩

theorem below548 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 3072) :
    Range.IsNatBelow 64 (rdA e vA j) :=
  natBelow_pred hs (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program)) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program)) (by simp)).2 (FalconNorm.rangeA (program := program)).choose_spec (FalconNorm.sizes_A (program := program)).2.2.1 hj

theorem below549 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 6144) :
    Range.IsNatBelow 64 (rdA e vSq j) :=
  natBelow_pred hs (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 1) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 1) (by simp)).2 (FalconNorm.rangeSq (program := program)).choose_spec (FalconNorm.sizes_A (program := program)).2.2.2.1 hj

theorem below550 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 5120) :
    Range.IsNatBelow 189 (rdA e vCc j) :=
  natBelow_pred hs (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 2) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 2) (by simp)).2 (FalconNorm.rangeCc (program := program)).choose_spec (FalconNorm.sizes_A (program := program)).2.2.2.2.1 hj

theorem below551 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 102) :
    Range.IsNatBelow 64 (rdA e vNd j) :=
  natBelow_pred hs (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 3) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 3) (by simp)).2 (FalconNorm.rangeNd (program := program)).choose_spec (FalconNorm.sizes_A (program := program)).2.2.2.2.2.1 hj

theorem below552 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 85) :
    Range.IsNatBelow 64 (rdA e vNc j) :=
  natBelow_pred hs (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 4) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 4) (by simp)).2 (FalconNorm.rangeNc (program := program)).choose_spec (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.1 hj

theorem below553 {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 6) :
    Range.IsNatBelow 64 (rdA e vD j) :=
  natBelow_pred hs (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 5) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pRange (program := program) + 5) (by simp)).2 (FalconNorm.rangeD (program := program)).choose_spec (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.1 hj

/-- **A column carry's limbs are below `64`**: the carry is below `189` (`norm.cc`). -/
theorem ccLimb_below {e : program.Env I} (hs : program.SourceSatAt e) {j : ℕ} (hj : j < 5120)
    (l : Fin 2) : Range.IsNatBelow 64 (ccLimb e j l) := by
  obtain ⟨k, hk, hkv⟩ := below550 hs hj
  have hn : nA e vCc j = k := by
    rw [nA, ← hkv, toNat_natCast_A (by omega)]
  unfold ccLimb
  rw [hn]
  split_ifs with hl
  · exact ⟨k % 64, Nat.mod_lt _ (by norm_disch), rfl⟩
  · exact ⟨k / 64, by omega, rfl⟩

/-- **The norm's digits are below `64`** (`norm.a`, `norm.sq`, `norm.cc`, `norm.nd`, `norm.nc`,
`norm.D`). -/
theorem digitsBelow {e : program.Env I} (hs : program.SourceSatAt e) :
    NativeNorm.DigitsBelow (normWit e) where
  a i l := by
    simp only [normWit]
    exact below548 hs (by have := i.isLt; have := l.isLt; omega)
  sq i m := by
    simp only [normWit]
    exact below549 hs (by have := i.isLt; have := m.isLt; omega)
  carry i m l := by
    simp only [normWit]
    exact ccLimb_below hs (by have := i.isLt; have := m.isLt; omega) l
  ndig b m := by
    simp only [normWit]
    exact below551 hs (by have := b.isLt; have := m.isLt; omega)
  ncarry b m := by
    simp only [normWit]
    exact below552 hs (by have := b.isLt; have := m.isLt; omega)
  D m := by
    simp only [normWit]
    exact below553 hs m.isLt

/-- **The high part of `s₂` coefficient `i`**: the top digit slot `norm.a[3 (512 + i) + 2]`. -/
def highF (e : program.Env I) (i : ℕ) : (I fA).K :=
  rdA e vA (3 * (512 + i) + 2)

theorem evalE_526 (e : program.Env I) {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) fA (.ref (eHi program)) i = highF e i := by
  rw [evalE_refA _ _ (FalconNorm.enc_le (program := program)).1, exprHigh, RealizedProgram.evalE_reindex, (FalconNorm.idx_enc (program := program)).1 i hi]
  rfl

theorem exprLen_526 : program.exprLen (.ref (eHi program)) = 512 := by
  rw [exprLen_refA (FalconNorm.enc_le (program := program)).1, exprHigh, RealizedProgram.exprLen_reindex, (FalconNorm.idx_enc (program := program)).2.2.1]

/-- **`encoding.high`**: the high part of every `s₂` coefficient is below `16`. -/
theorem high_below {e : program.Env I} (hs : program.SourceSatAt e) {i : ℕ} (hi : i < 512) :
    ∃ k : ℕ, k < 16 ∧ (k : (I fA).K) = highF e i := by
  obtain ⟨_, hbd⟩ := FalconNorm.high (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (FalconNorm.pHigh (program := program)) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pHigh (program := program)) (by simp)).2
  rw [hbd] at h
  obtain ⟨k, hk, hkv⟩ := natBelow_of_mem h (i := i) (by rw [exprLen_526]; exact hi)
  refine ⟨k, hk, ?_⟩
  change program.evalE _ fA (.ref (eHi program)) i = _ at hkv
  rw [evalE_526 e hi] at hkv
  exact hkv.symm

/-- **`encoding.slack`**: the slack `392 − Σ h` of the high parts is a natural below `393`. -/
theorem slack_below {e : program.Env I} (hs : program.SourceSatAt e) :
    ∃ k : ℕ, k < 393 ∧ (k : (I fA).K) = 392 - ∑ i : Fin 512, highF e i := by
  obtain ⟨_, hbd⟩ := FalconNorm.slack (program := program)
  have h := holdsAt hs (FalconNorm.inSource_A (program := program) (FalconNorm.pSlack (program := program)) (by simp)).1
    (FalconNorm.inSource_A (program := program) (FalconNorm.pSlack (program := program)) (by simp)).2
  rw [hbd] at h
  obtain ⟨k, hk, hkv⟩ := natBelow_of_mem h (i := 0) (by
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale, RealizedProgram.exprLen_apply, exprLen_526]
    simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols])
  refine ⟨k, hk, ?_⟩
  change program.evalE _ fA (.add (.scale (.const 12288) (.apply (.sum 512) (.ref (eHi program))))
    (.leaf vOff)) 0 = _ at hkv
  rw [RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, RealizedProgram.evalE_apply_sum,
    RealizedProgram.evalE_leaf_of_isConstant e (FalconNorm.consts_A (program := program)).2.2.2.2.2.2.1,
    RealizedProgram.constRead_of_valueField (FalconNorm.consts_A (program := program)).2.2.2.2.2.2.2.1,
    (FalconNorm.consts_A (program := program)).2.2.2.2.2.2.2.2, decode_A] at hkv
  rw [Finset.sum_congr rfl fun t _ => by rw [Nat.zero_mul, Nat.zero_add, evalE_526 e t.isLt]]
    at hkv
  have hq : ((12288 : ℕ) : (I fA).K) = -1 := by
    have h0 : ((12289 : ℕ) : (I fA).K) = 0 := CharP.cast_eq_zero _ 12289
    push_cast at h0 ⊢
    linear_combination h0
  try dsimp only at hkv
  simp only [AField.decode_eq] at hkv
  change ((12288 : ℕ) : (I fA).K) * _ + ((392 : ℕ) : (I fA).K) = _ at hkv
  rw [hq] at hkv
  have hkv' : (-1 : (I fA).K) * ∑ t : Fin 512, highF e t + ((392 : ℕ) : (I fA).K) =
      (k : (I fA).K) := hkv
  push_cast at hkv'
  linear_combination -hkv'

/-- **The encoding's requests hold** at the high slack digit `k / 64` of the slack `k`
(`NativeEncoding.RequestsHold`). -/
theorem encodingRequests {e : program.Env I} (hs : program.SourceSatAt e) {k : ℕ}
    (hk : k < 393) (hkv : (k : (I fA).K) = 392 - ∑ i : Fin 512, highF e i) :
    NativeEncoding.RequestsHold (algOf e ((k / 64 : ℕ) : (I fA).K)).norm
      ((k / 64 : ℕ) : (I fA).K) where
  high i := by
    obtain ⟨h0, hh0, hh⟩ := high_below hs i.isLt
    refine ⟨h0 + 48, by omega, ?_⟩
    simp only [algOf, normWit]
    rw [Nat.cast_add, hh, highF]
    norm_num
  slackLo := by
    refine ⟨k % 64, Nat.mod_lt _ (by norm_disch), ?_⟩
    have hsum : ∑ i : Fin 512, NativeEncoding.high (algOf e ((k / 64 : ℕ) : (I fA).K)).norm i =
        ∑ i : Fin 512, highF e i := by
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [NativeEncoding.high, algOf, normWit, highF]
      norm_num
    rw [hsum, ← hkv]
    have := Nat.mod_add_div k 64
    have hc := congrArg (Nat.cast : ℕ → (I fA).K) this
    push_cast at hc
    linear_combination hc
  slackHi := ⟨k / 64, by omega, rfl⟩

end GordieHowe.Falcon512.Norm
