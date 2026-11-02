-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Frontend.Basic
public import GordieHowe.Applications.Falcon512.Emulated.Interp
public import GordieHowe.Applications.Falcon512.Emulated.System.Algebra
public import GordieHowe.Language.RealizedProgram.Interval
public import GordieHowe.Language.Realizations.Realize

@[expose] public section

/-!
# GordieHowe frontend: emulated Falcon, the algebra of domain `A`

Domain `A`'s obligation of the Falcon frontend (`GordieHowe.Falcon512.AlgebraSound`) for an
emulated Falcon program (Falcon's arithmetic modulo `q` emulated over a Goldilocks extension),
generic in the program and its fields at the program facts `FalconEAlg` (decided per program) and
domain `A`'s field facts (`GordieHowe.Falcon512.EField`). Wherever the source program holds, at the
key its statement decodes to:

* **the signature congruence** (`congruent`): `signature.equation` states
  `s1 + h · s2 ≡ c (mod q)` on the integer readings, with `h` the statement value
  `key.coefficients`, computed from `statement.hhat` by `RealizedProgram.keyCoeffs`. At a
  statement that decodes to the key `pk` these are `pk`'s coefficients (`intOf_key`), and the
  right side `batched 512 (fromDigits 16 2)` of the Boolean sample bits is the challenge
  `Emulated.cNat` (`evalIntWith_sigRhs`), so the congruence is Falcon's (`Emulated.Rows.Congruent`);
* **the magnitudes, the norm and the encoding** (`magnitudes.s1`, `magnitudes.s2`, `norm.sum`, the
  ranges of `mag1`, `mag2`, `low2`, the budget and the norm, `encoding.high2`): with the
  congruence, Falcon emulated's `Emulated.algebraSpec_of_congruent` gives Falcon's algebraic
  verifier and the encoding bounds (`algebraSound`).

The integer reading of a coefficient-form negacyclic operator with entries below `p/2`
(`coefInt_negCoef`) is stated here for every emulated field.
-/

namespace GordieHowe.Falcon512.Emulated

open GordieHowe.Bits _root_.GordieHowe.Falcon512.Emulated.Params

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
theorem coefInt_negCoef (n : ℕ) {h : ℕ → FA.K} {z : ℕ → ℕ}
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

/-! ## The expressions of domain `A` -/

/-- **The constant `−1`** of the Goldilocks fields: `p − 1`. -/
abbrev mOne : ℕ := 18446744069414584320

/-- **A magnitude equation** `(mag − s)(mag − (q − s)) = 0` of the value `s` at the magnitude
`mag`, `q` the constant `41`. -/
def magLhs (mag s : ℕ) : RealizedProgram.Expr :=
  .mul (.add (.leaf mag) (.scale (.const mOne) (.leaf s)))
    (.add (.leaf mag) (.scale (.const mOne) (.add (.scale (.const mOne) (.leaf s))
      (.reindex [(0, 0, 512)] (.leaf 41)))))

/-- **The norm's left side** (`norm.sum`): `squares − Σ mag1² − Σ mag2²`. -/
def normLhs : RealizedProgram.Expr :=
  .add (.add (.leaf 602) (.scale (.const mOne) (.apply (.sum 512) (.mul (.leaf 598) (.leaf 598)))))
    (.scale (.const mOne) (.apply (.sum 512) (.mul (.leaf 599) (.leaf 599))))

/-- **The encoding budget's expression**: `Σ low2 − Σ mag2 + 50176`. -/
def budgetExpr : RealizedProgram.Expr :=
  .add (.add (.scale (.const mOne) (.apply (.sum 512) (.leaf 599))) (.apply (.sum 512) (.leaf 600)))
    (.leaf 601)

/-- **The signature equation's left side** (`signature.equation`): `s1 + h · s2`, the negacyclic
product by the coefficients `key.coefficients`. -/
def sigLhs : RealizedProgram.Expr :=
  .add (.leaf 597) (.apply (.negacyclicConv 594 .coefficients) (.leaf 596))

/-- **The signature equation's right side**: the challenge from the sample bits `c_A`, `16` bits
to a sample. -/
def sigRhs : RealizedProgram.Expr :=
  .apply (.batched 512 (.fromDigits 16 2)) (.leaf 595)

/-! ## The program facts -/

/-- **The program facts of an emulated Falcon program's domain `A`** (decided per program): the
numbering (`statement.hhat` `593`, `key.coefficients` `594`, `crossing.c_A` `595`, `s2` `596`,
`signature.s1` `597`, `magnitudes.mag1` `598`, `magnitudes.mag2` `599`, `encoding.low2` `600`, the
budget offset `601`, `norm.squares` `602`; `q` at `41`, the zero row `42`, the zero `43`); the
signature equation (predicate `297`), the magnitudes (`275`, `276`), the norm (`277`), the ranges
(`286` … `290`) and `encoding.high2` (`298`), source predicates; the constants; the fields, sizes
and kinds of the values read; `key.coefficients` computed from `statement.hhat`, with its declared
bound `q`. -/
class FalconEAlg (program : RealizedProgram) [FalconACore program] : Prop where
  /-- `crossing.c_A` is value `595`. -/
  cA_eq : FalconACore.cA program = 595
  /-- `s2` is value `596`. -/
  s2_eq : FalconACore.s2 program = 596
  /-- `signature.equation`: `s1 + h · s2 ≡ c (mod q)`. -/
  sig : ∃ real, (program.predicate 297).body = .mod 1 12289 sigLhs sigRhs real
  /-- `magnitudes.s1`. -/
  magS1 : ∃ t, (program.predicate 275).body = .equal 1 (magLhs 598 597) (.leaf 42) t
  /-- `magnitudes.s2`. -/
  magS2 : ∃ t, (program.predicate 276).body = .equal 1 (magLhs 599 596) (.leaf 42) t
  /-- `norm.sum`. -/
  normSum : ∃ t, (program.predicate 277).body = .equal 1 normLhs (.leaf 43) t
  /-- `magnitudes.mag1`. -/
  rMag1 : ∃ r, (program.predicate 286).body = .mem 1 [.leaf 598] (.range 6145) r
  /-- `magnitudes.mag2`. -/
  rMag2 : ∃ r, (program.predicate 287).body = .mem 1 [.leaf 599] (.range 2048) r
  /-- `encoding.low2`. -/
  rLow2 : ∃ r, (program.predicate 288).body = .mem 1 [.leaf 600] (.range 128) r
  /-- `encoding.budget`. -/
  rBudget : ∃ r, (program.predicate 289).body = .mem 1 [budgetExpr] (.range 50177) r
  /-- `norm.bound`. -/
  rNorm : ∃ r, (program.predicate 290).body = .mem 1 [.leaf 602] (.range 34034727) r
  /-- `encoding.high2`. -/
  high2 : ∃ r, (program.predicate 298).body = .mod 1 128 (.leaf 599) (.leaf 600) r
  /-- The predicates read are source predicates. -/
  inSource : ∀ p ∈ [275, 276, 277, 286, 287, 288, 289, 290, 297, 298],
    p < program.predicates.length ∧ program.inSource (program.predicate p) = true
  /-- The constants: `q`, the zero row, the zero, the budget offset. -/
  consts : program.isConstant 41 = true ∧ (program.constEntries 41).getD 0 0 = 12289 ∧
    program.isConstant 42 = true ∧ program.constEntries 42 = List.replicate 512 0 ∧
    program.isConstant 43 = true ∧ (program.constEntries 43).getD 0 0 = 0 ∧
    program.isConstant 601 = true ∧ (program.constEntries 601).getD 0 0 = 50176
  /-- The values read are of field `1`. -/
  fields : ∀ v ∈ [41, 42, 43, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602],
    program.valueField v = 1
  /-- The sizes of the values read. -/
  sizes : (program.value 594).size = 512 ∧ (program.value 596).size = 512 ∧
    (program.value 597).size = 512 ∧ (program.value 598).size = 512 ∧
    (program.value 599).size = 512 ∧ (program.value 600).size = 512 ∧
    (program.value 602).size = 1
  /-- `crossing.c_A`, `s2`, `signature.s1`, `magnitudes.mag2` and `encoding.low2` are committed. -/
  privKinds : (program.value 595).kind = .priv ∧ (program.value 596).kind = .priv ∧
    (program.value 597).kind = .priv ∧ (program.value 599).kind = .priv ∧
    (program.value 600).kind = .priv
  /-- `key.coefficients` is computed from `statement.hhat`. -/
  keyKind : (program.value 594).kind = .pub (.opaque "key.coefficients" [593])
  /-- `statement.hhat` is an opaque statement value of no argument. -/
  hhatKind : (program.value 593).kind = .pub (.opaque "statement.hhat" [])
  /-- `key.coefficients` declares the bound `q`. -/
  keyDeclared : (594, 12289) ∈ program.declaredRanges

/-! ## Soundness -/

section Sound

variable {program : RealizedProgram} {FH FA : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.falconInterpOf FH FA

variable [EField FA]

instance : CharP (interp 1).K pGold := EField.charP (FA := FA)

/-! ### Domain `A`'s field -/

/-- Constants below `p` decode to their casts in field `1`. -/
theorem decode1 {c : ℕ} (hc : c < pGold) : (interp 1).decode c = (c : (interp 1).K) :=
  EField.decode_lt (FA := FA) c hc

/-- The integer reading inverts the casts below `p` in field `1`. -/
theorem toNat1 {k : ℕ} (hk : k < pGold) : (interp 1).toNat (k : (interp 1).K) = k :=
  EField.toNat_natCast (FA := FA) hk

/-- **`p − 1` decodes to `−1`.** -/
theorem decode_mOne : (interp 1).decode mOne = -1 := by
  rw [decode1 (by norm_num [pGold])]
  have h : ((mOne + 1 : ℕ) : (interp 1).K) = 0 := by
    rw [show mOne + 1 = pGold by norm_num [pGold]]
    exact CharP.cast_eq_zero _ _
  push_cast at h
  linear_combination h

/-- **The centred reading of `p − 1`** is `−1`. -/
theorem centered_mOne : (interp 1).centered mOne = -1 := by
  rw [RealizedProgram.FieldInterp.centered_eq]
  change RealizedProgram.centeredZ FA.spec.characteristic mOne = -1
  rw [EField.spec_char (FA := FA)]
  unfold RealizedProgram.centeredZ
  norm_num [pGold]

/-! ### Reading the values of `A` -/

variable [FalconACore program]

/-- **A value of domain `A`** read in field `1`. -/
abbrev rdA (e : program.Env interp) (v i : ℕ) : (interp 1).K :=
  program.evalE (program.reader e) 1 (.leaf v) i

section EAlg

variable [FalconEAlg program]

omit [EField FA] in
/-- **A predicate of domain `A` holds** where the source program holds. -/
theorem holdsAt {e : program.Env interp} (hs : program.SourceSatAt e) {p : ℕ}
    (hp : p ∈ [275, 276, 277, 286, 287, 288, 289, 290, 297, 298]) :
    program.HoldsAt e (program.predicate p).body :=
  hs.holdsAt_of_lt (FalconEAlg.inSource p hp).1 (FalconEAlg.inSource p hp).2

omit [EField FA] [FalconEAlg program] in
/-- **A field `equal` of domain `A` holds coordinatewise in field `1`.** -/
theorem holdsAt_equal1 {e : program.Env interp} {lhs rhs : RealizedProgram.Expr}
    {t : RealizedProgram.Target} (h : program.HoldsAt e (.equal 1 lhs rhs t)) :
    ∀ i < program.exprLen lhs,
      program.evalE (program.reader e) 1 lhs i = program.evalE (program.reader e) 1 rhs i :=
  fun i hi => by
    have := h i hi
    unfold RealizedProgram.evalWith at this
    rwa [FalconACore.domainField1 (program := program)] at this

omit [EField FA] [FalconEAlg program] in
/-- **A range membership of one record** of domain `A` gives a natural below the bound. -/
theorem natBelow_mem1 {e : program.Env interp} {r : RealizedProgram.Expr} {n : ℕ}
    {real : RealizedProgram.InRealization} (h : program.HoldsAt e (.mem 1 [r] (.range n) real))
    {i : ℕ} (hi : i < program.exprLen r) :
    ∃ k < n, program.evalE (program.reader e) 1 r i = (k : (interp 1).K) := by
  obtain ⟨k, hk, hkv⟩ := h i hi r (List.mem_singleton_self r)
  refine ⟨k, hk, ?_⟩
  unfold RealizedProgram.evalWith at hkv
  rw [FalconACore.domainField1 (program := program)] at hkv
  exact hkv

omit [EField FA] in
/-- **A leaf of domain `A` below a bound**, from its range. -/
theorem leaf_natBelow {e : program.Env interp} (hs : program.SourceSatAt e) {p v n : ℕ}
    (hp : p ∈ [275, 276, 277, 286, 287, 288, 289, 290, 297, 298])
    (hb : ∃ r, (program.predicate p).body = .mem 1 [.leaf v] (.range n) r)
    {sz : ℕ} (hsz : (program.value v).size = sz) (i : Fin sz) :
    ∃ k < n, rdA e v i = (k : (interp 1).K) := by
  obtain ⟨r, hbd⟩ := hb
  have h := holdsAt hs hp
  rw [hbd] at h
  exact natBelow_mem1 h (by rw [RealizedProgram.exprLen_leaf, hsz]; exact i.isLt)

omit [FalconACore program] [FalconEAlg program] in
/-- A constant of field `1` below `p` reads its cast. -/
theorem rdA_const (e : program.Env interp) {v c i : ℕ} (hc : program.isConstant v = true)
    (hf : program.valueField v = 1) (he : (program.constEntries v).getD i 0 = c)
    (hcp : c < pGold) : rdA e v i = (c : (interp 1).K) := by
  unfold rdA
  rw [RealizedProgram.evalE_leaf_of_isConstant e hc, RealizedProgram.constRead_of_valueField hf, he,
    decode1 hcp]

theorem rdA_q (e : program.Env interp) : rdA e 41 0 = (12289 : ℕ) := by
  obtain ⟨c, h, -⟩ := FalconEAlg.consts (program := program)
  exact rdA_const e c (FalconEAlg.fields 41 (by simp)) h (by norm_num [pGold])

theorem rdA_zeros (e : program.Env interp) {i : ℕ} (hi : i < 512) : rdA e 42 i = 0 := by
  obtain ⟨-, -, c, h, -⟩ := FalconEAlg.consts (program := program)
  rw [rdA_const e c (FalconEAlg.fields 42 (by simp)) (c := 0)
    (by rw [h, List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos hi]; rfl)
    (by norm_num [pGold]), Nat.cast_zero]

theorem rdA_zero (e : program.Env interp) : rdA e 43 0 = 0 := by
  obtain ⟨-, -, -, -, c, h, -⟩ := FalconEAlg.consts (program := program)
  rw [rdA_const e c (FalconEAlg.fields 43 (by simp)) h (by norm_num [pGold]), Nat.cast_zero]

theorem rdA_off (e : program.Env interp) : rdA e 601 0 = (50176 : ℕ) := by
  obtain ⟨-, -, -, -, -, -, c, h⟩ := FalconEAlg.consts (program := program)
  exact rdA_const e c (FalconEAlg.fields 601 (by simp)) h (by norm_num [pGold])

omit [FalconACore program] [FalconEAlg program] in
/-- **The integer reading of a committed natural below `p`** is the natural. -/
theorem intOf_priv {e : program.Env interp} {v i n : ℕ} (hk : (program.value v).kind = .priv)
    (hf : program.valueField v = 1) (hr : rdA e v i = (n : (interp 1).K)) (hn : n < pGold) :
    program.intOf (program.reader e) v i = n := by
  unfold RealizedProgram.intOf
  rw [hk]
  unfold rdA at hr
  rw [RealizedProgram.evalE_leaf] at hr
  have h := congrArg (interp 1).toNat hr
  rw [RealizedProgram.toNat_castElt hf, toNat1 hn] at h
  exact congrArg (fun m : ℕ => (m : ℤ)) h

/-! ### The magnitudes and the norm -/

/-- **A magnitude equation's left side** at coordinate `i < 512`: `(mag − s)(mag − (q − s))`. -/
theorem evalE_magLhs (e : program.Env interp) (mag v : ℕ) {i : ℕ} (hi : i < 512) :
    program.evalE (program.reader e) 1 (magLhs mag v) i =
      (rdA e mag i - rdA e v i) * (rdA e mag i - ((12289 : ℕ) - rdA e v i)) := by
  have hq := rdA_q (program := program) e
  rw [magLhs, RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, RealizedProgram.evalE_scale_const, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_step_zero hi, decode_mOne]
  unfold rdA at hq ⊢
  rw [hq]
  ring

/-- **The magnitude equations** (`magnitudes.s1`, `magnitudes.s2`): at every coordinate,
`(mag − s)(mag − (q − s)) = 0`. -/
theorem mag_eq {e : program.Env interp} (hs : program.SourceSatAt e) {p mag v : ℕ}
    (hp : p ∈ [275, 276, 277, 286, 287, 288, 289, 290, 297, 298])
    (hb : ∃ t, (program.predicate p).body = .equal 1 (magLhs mag v) (.leaf 42) t)
    (hsz : (program.value mag).size = 512) {i : ℕ} (hi : i < 512) :
    (rdA e mag i - rdA e v i) * (rdA e mag i - ((12289 : ℕ) - rdA e v i)) = 0 := by
  obtain ⟨t, hbd⟩ := hb
  have h := holdsAt hs hp
  rw [hbd] at h
  have hx := holdsAt_equal1 h i (by
    rw [magLhs, RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add,
      RealizedProgram.exprLen_leaf, hsz]
    exact hi)
  rw [evalE_magLhs e mag v hi] at hx
  change _ = rdA e 42 i at hx
  rw [rdA_zeros e hi] at hx
  exact hx

omit [FalconACore program] [FalconEAlg program] in
/-- **The norm's left side**: `squares − Σ mag1² − Σ mag2²`. -/
theorem evalE_normLhs (e : program.Env interp) :
    program.evalE (program.reader e) 1 normLhs 0 = rdA e 602 0 -
      ∑ i : Fin 512, rdA e 598 i * rdA e 598 i - ∑ i : Fin 512, rdA e 599 i * rdA e 599 i := by
  rw [normLhs, RealizedProgram.evalE_add, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_apply_sum, RealizedProgram.evalE_apply_sum, decode_mOne]
  simp only [Nat.zero_mul, Nat.zero_add, RealizedProgram.evalE_mul]
  ring

/-- **The norm's equation** (`norm.sum`): `squares − Σ mag1² − Σ mag2² = 0`. -/
theorem norm_eq {e : program.Env interp} (hs : program.SourceSatAt e) :
    rdA e 602 0 - ∑ i : Fin 512, rdA e 598 i * rdA e 598 i -
      ∑ i : Fin 512, rdA e 599 i * rdA e 599 i = 0 := by
  obtain ⟨t, hbd⟩ := FalconEAlg.normSum (program := program)
  have h := holdsAt hs (p := 277) (by simp)
  rw [hbd] at h
  have hx := holdsAt_equal1 h 0 (by
    rw [normLhs, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add,
      RealizedProgram.exprLen_leaf, (FalconEAlg.sizes (program := program)).2.2.2.2.2.2]
    norm_num)
  rw [evalE_normLhs] at hx
  change _ = rdA e 43 0 at hx
  rw [rdA_zero] at hx
  exact hx

/-! ### The signature congruence -/

/-- **The key's coefficients as the program reads them** (`key.coefficients`): the statement's
`statement.hhat` read as naturals, decoded (`RealizedProgram.keyCoeffs`). -/
def keyNat (x : program.Valuation interp) (s : ℕ) : ℕ :=
  RealizedProgram.keyCoeffs [fun j => (interp (program.valueField 593)).toNat (x 593 j)] s

/-- **A natural below `p` decoded and read back** in a field identifier equal to `1`. -/
theorem toNat_decode_of {f : ℕ} (hf : f = 1) {n : ℕ} (hn : n < pGold) :
    (interp f).toNat ((interp f).decode n) = n := by
  subst hf
  rw [decode1 hn, toNat1 hn]

/-- **The opaque function `key.coefficients`** is `RealizedProgram.keyCoeffs`. -/
theorem falconOps_key (xs : List (ℕ → ℕ)) (i : ℕ) :
    RealizedProgram.falconOps "key.coefficients" xs i = RealizedProgram.keyCoeffs xs i := by
  simp only [RealizedProgram.falconOps, ↓reduceIte]

omit [EField FA] in
/-- **`key.coefficients` reads the decoded key** (`RealizedProgram.reader_of_declared`): its
coordinate `s` decodes `keyNat`. -/
theorem reader_key (e : program.Env interp) (s : ℕ) :
    program.reader e 594 s = (interp (program.valueField 594)).decode (keyNat e.stmt s) := by
  rw [RealizedProgram.reader_of_declared e (FalconEAlg.keyDeclared (program := program))]
  simp only [RealizedProgram.stmtRead, FalconEAlg.keyKind (program := program), List.map_cons,
    List.map_nil]
  show (interp _).decode (RealizedProgram.falconOps "key.coefficients" _ s) = _
  rw [falconOps_key]
  rfl

/-- **The integer reading of `key.coefficients`** is `keyNat`. -/
theorem intOf_key (e : program.Env interp) (s : ℕ) :
    program.intOf (program.reader e) 594 s = keyNat e.stmt s := by
  have hf594 := FalconEAlg.fields (program := program) 594 (by simp)
  unfold RealizedProgram.intOf
  rw [FalconEAlg.keyKind (program := program)]
  show ((interp (program.valueField 594)).toNat (program.reader e 594 s) : ℤ) = _
  have hlt : keyNat e.stmt s < pGold :=
    (RealizedProgram.keyCoeffs_lt _ s).trans (by norm_num [pGold])
  rw [reader_key, toNat_decode_of hf594 hlt]

omit [EField FA] [FalconACore program] in
/-- **The key's coefficients at a statement that decodes to `pk`** are `pk`'s. -/
theorem keyNat_of_keyOf {x : program.Valuation interp} {pk : PublicKey} (h : keyOf x = some pk)
    (j : Fin falcon512.n) :
    keyNat x j = EmulatedAlgebraCircuit.keyCoeffs pk.h j := by
  unfold keyOf at h
  obtain ⟨c, hc, hpk⟩ := Option.map_eq_some_iff.1 h
  have hlt := ((KeyNTT.falconDecode_512_eq_some_iff _ c).1 hc).1
  unfold keyNat RealizedProgram.keyCoeffs
  simp only [List.headD_cons, hc]
  rw [dif_pos (show (j : ℕ) < 512 from j.isLt), ← hpk]
  simp only [EmulatedAlgebraCircuit.keyCoeffs, Falcon512.coeff_ofCoeff, ZMod.val_natCast]
  exact (Nat.mod_eq_of_lt (hlt j)).symm

/-! ### The challenge -/

omit [EField FA] in
/-- **`c_A` is value `595`** (`FalconEAlg.cA_eq`). -/
theorem cABits_eq (e : program.Env interp) (j : Fin falcon512.n) :
    cABits e j = program.wordAt (program.reader e) 1 595 16 j := by
  unfold cABits
  rw [FalconEAlg.cA_eq]

omit [EField FA] in
/-- **`s2` is value `596`** (`FalconEAlg.s2_eq`). -/
theorem s2Vals_eq (e : program.Env interp) (i : Fin falcon512.n) :
    s2Vals (program.reader e) i = rdA e 596 i := by
  unfold s2Vals rdA
  rw [FalconEAlg.s2_eq]

omit [EField FA] in
/-- **The samples' bits are bits** (`crossing.c_A.boolean`). -/
theorem cA_bool {e : program.Env interp} (hs : program.SourceSatAt e) {t : ℕ} (ht : t < 8192) :
    rdA e 595 t = 0 ∨ rdA e 595 t = 1 := by
  obtain ⟨pb, hpb, hbc, hsrcb⟩ := FalconACore.cABoolean (program := program)
  have hsz := (FalconACore.raw_facts (program := program)).2.2
  rw [FalconEAlg.cA_eq] at hbc hsz
  have hbool := hs.holdsAt_of_predNameB hpb hsrcb
  have := RealizedProgram.bool_of_boolCheck hbc hbool (i := t)
    (by change t < (program.value 595).size; rw [hsz]; exact ht)
  rw [FalconACore.domainField1] at this
  exact this

/-- **The integer reading of a sample bit** is the bit. -/
theorem intOf_cA {e : program.Env interp} (hs : program.SourceSatAt e) {t : ℕ} (ht : t < 8192) :
    program.intOf (program.reader e) 595 t = if rdA e 595 t = 1 then 1 else 0 := by
  have hf := FalconEAlg.fields (program := program) 595 (by simp)
  have hn : ∀ n < pGold, rdA e 595 t = (n : (interp 1).K) →
      program.intOf (program.reader e) 595 t = n :=
    fun n hn hr => intOf_priv (FalconEAlg.privKinds (program := program)).1 hf hr hn
  rcases cA_bool hs ht with h0 | h1
  · rw [if_neg (by rw [h0]; exact zero_ne_one), hn 0 (by norm_num [pGold]) (by rw [h0, Nat.cast_zero])]
    rfl
  · rw [if_pos h1, hn 1 (by norm_num [pGold]) (by rw [h1, Nat.cast_one])]
    rfl

/-- **The signature equation's right side on the integers** is the challenge: the samples of
`c_A`, `16` Boolean bits each, as naturals (`Emulated.cNat`). -/
theorem evalIntWith_sigRhs {e : program.Env interp} (hs : program.SourceSatAt e)
    (i : Fin falcon512.n) :
    program.evalIntWith (program.reader e) 1 sigRhs i = (Emulated.cNat (cABits e) i : ℤ) := by
  have hd1 := FalconACore.domainField1 (program := program)
  rw [sigRhs, RealizedProgram.evalIntWith_apply]
  rw [hd1]
  rw [RealizedProgram.NamedOp.applyInt_batched_fromDigits program (p := pGold) (EField.spec_char (FA := FA))
    (EField.charP (FA := FA)) (fun k hk => toNat1 hk) (by norm_num [pGold]) _ (by norm_num)
    (decode1 (by norm_num [pGold]))
    (fun l hl => by
      have : 2 ^ l ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
      norm_num [pGold]
      omega)]
  rw [Nat.div_eq_of_lt (show (i : ℕ) < 512 from i.isLt),
    Nat.mod_eq_of_lt (show (i : ℕ) < 512 from i.isLt)]
  simp only [Nat.zero_mul, Nat.zero_add, RealizedProgram.evalIntWith_leaf]
  unfold Emulated.cNat Bits.natOfBits
  push_cast
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intOf_cA hs (by have : (i : ℕ) < 512 := i.isLt; have := l.isLt; omega), cABits_eq]
  unfold RealizedProgram.wordAt rdA
  split_ifs <;> simp

/-! ### The signature congruence -/

/-- **The signature congruence** where the source program holds, at the key the statement decodes
to: `signature.equation` on the integers is `c ≡ s1 + h · s2 (mod q)`, with `h` the key's
coefficients (`keyNat_of_keyOf`) and `c` the challenge (`evalIntWith_sigRhs`). -/
theorem congruent {e : program.Env interp} (hs : program.SourceSatAt e) {pk : PublicKey}
    (hpk : keyOf e.stmt = some pk) {s1N s2N : Fin 512 → ℕ}
    (hs1 : ∀ i : Fin 512, rdA e 597 i = (s1N i : (interp 1).K) ∧ s1N i ≤ 12289)
    (hs2 : ∀ i : Fin 512, rdA e 596 i = (s2N i : (interp 1).K) ∧ s2N i ≤ 12289) :
    Emulated.Rows.Congruent q (EmulatedAlgebraCircuit.keyCoeffs pk.h) (Emulated.cNat (cABits e))
      s1N s2N := by
  have hd1 := FalconACore.domainField1 (program := program)
  have hf594 := FalconEAlg.fields (program := program) 594 (by simp)
  obtain ⟨hz594, hz596, hz597, -⟩ := FalconEAlg.sizes (program := program)
  obtain ⟨-, hk596, hk597, -⟩ := FalconEAlg.privKinds (program := program)
  set z : ℕ → ℕ := keyNat e.stmt with hzdef
  have hz : ∀ s < 512, (interp 1).toNat
      (RealizedProgram.castElt (program.reader e 594 s) : (interp 1).K) = z s ∧ 2 * z s < pGold := by
    intro s _
    have hlt : keyNat e.stmt s < 12289 := RealizedProgram.keyCoeffs_lt _ s
    refine ⟨?_, by rw [hzdef]; norm_num [pGold]; omega⟩
    rw [RealizedProgram.toNat_castElt hf594, reader_key,
      toNat_decode_of (n := keyNat e.stmt s) hf594 (hlt.trans (by norm_num [pGold]))]
  have hcoef : ∀ (j k : ℕ), (interp 1).coefInt (RealizedProgram.Ops.negCoef 512
      (fun s => (RealizedProgram.castElt (program.reader e 594 s) : (interp 1).K)) j k) =
      RealizedProgram.Ops.negCoef 512 (fun s => (z s : ℤ)) j k :=
    fun j k => coefInt_negCoef (FA := FA) 512 hz j k
  have hkey : EmulatedAlgebraCircuit.keyCoeffs pk.h = fun j : Fin falcon512.n => z j :=
    funext fun j => (keyNat_of_keyOf hpk j).symm
  rw [hkey]
  intro i
  show ((Emulated.cNat (cABits e) i : ℕ) : ZMod 12289) = (s1N i : ZMod 12289) +
    LatticeCrypto.negacyclicConvCoeff (fun j : Fin 512 => ((z j : ℕ) : ZMod 12289))
      (fun j => (s2N j : ZMod 12289)) i
  obtain ⟨real, hb⟩ := FalconEAlg.sig (program := program)
  have h := holdsAt hs (p := 297) (by simp)
  rw [hb] at h
  have hd := h.1 i (by
    rw [sigLhs, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, hz597]
    exact i.isLt)
  rw [evalIntWith_sigRhs hs i, sigLhs, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_apply, hd1,
    RealizedProgram.NamedOp.applyInt_negacyclicConv _ _ _ _ _ (by rw [hz594]; norm_num), hz594,
    Nat.mod_eq_of_lt (show (i : ℕ) < 512 from i.isLt),
    Nat.div_eq_of_lt (show (i : ℕ) < 512 from i.isLt)] at hd
  simp only [Nat.zero_mul, Nat.zero_add, RealizedProgram.NamedOp.formPoly, hcoef,
    RealizedProgram.evalIntWith_leaf] at hd
  have hs1i : program.intOf (program.reader e) 597 i = s1N i :=
    intOf_priv hk597 (FalconEAlg.fields 597 (by simp)) (hs1 i).1
      (by have := (hs1 i).2; norm_num [pGold]; omega)
  have hs2k : ∀ k : Fin 512, program.intOf (program.reader e) 596 k = s2N k := fun k =>
    intOf_priv hk596 (FalconEAlg.fields 596 (by simp)) (hs2 k).1
      (by have := (hs2 k).2; norm_num [pGold]; omega)
  simp only [hs1i, hs2k] at hd
  have hsum : ∑ k : Fin 512, RealizedProgram.Ops.negCoef 512 (fun s => (z s : ℤ)) i k * (s2N k : ℤ) =
      LatticeCrypto.negacyclicConvCoeff (fun k : Fin 512 => ((z k : ℕ) : ℤ)) (fun k => (s2N k : ℤ)) i :=
    (Finset.sum_congr rfl fun k _ => by rw [negCoef_eq_convWeight z i k]).trans
      (Emulated.Rows.sum_convWeight_eq_negacyclicConvCoeff (fun t : Fin 512 => z t) _ i)
  rw [hsum] at hd
  have hc := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12289).2 hd
  rw [Int.cast_sub, Int.cast_add, Int.cast_natCast, Int.cast_natCast,
    Emulated.Rows.intCast_negacyclicConvCoeff (fun t : Fin 512 => z t) s2N i] at hc
  linear_combination -hc

/-! ### The encoding -/

/-- **`encoding.high2`**: `low2 = mag2 mod 128`. -/
theorem low2_eq {e : program.Env interp} (hs : program.SourceSatAt e) {mag2N low2N : Fin 512 → ℕ}
    (hmag2N : ∀ i, mag2N i < 2048) (hmag2C : ∀ i : Fin 512, rdA e 599 i = (mag2N i : (interp 1).K))
    (hlow2N : ∀ i, low2N i < 128) (hlow2C : ∀ i : Fin 512, rdA e 600 i = (low2N i : (interp 1).K))
    (i : Fin 512) : low2N i = mag2N i % 128 := by
  obtain ⟨-, -, -, -, hz599, -⟩ := FalconEAlg.sizes (program := program)
  obtain ⟨-, -, -, hk599, hk600⟩ := FalconEAlg.privKinds (program := program)
  obtain ⟨r, hbd⟩ := FalconEAlg.high2 (program := program)
  have h := holdsAt hs (p := 298) (by simp)
  rw [hbd] at h
  have hd := h.1 i (by rw [RealizedProgram.exprLen_leaf, hz599]; exact i.isLt)
  rw [RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf,
    intOf_priv hk599 (FalconEAlg.fields 599 (by simp)) (hmag2C i)
      (by have := hmag2N i; norm_num [pGold]; omega),
    intOf_priv hk600 (FalconEAlg.fields 600 (by simp)) (hlow2C i)
      (by have := hlow2N i; norm_num [pGold]; omega)] at hd
  obtain ⟨m, hm⟩ := hd
  have := hlow2N i
  omega

/-- **The encoding budget** (`encoding.budget` with `encoding.high2`): the high parts
`⌊mag2 / 128⌋` sum to at most `392`. -/
theorem budget_le {e : program.Env interp} (hs : program.SourceSatAt e) {mag2N low2N : Fin 512 → ℕ}
    (hmag2N : ∀ i, mag2N i < 2048) (hmag2C : ∀ i : Fin 512, rdA e 599 i = (mag2N i : (interp 1).K))
    (hlow2N : ∀ i, low2N i < 128) (hlow2C : ∀ i : Fin 512, rdA e 600 i = (low2N i : (interp 1).K)) :
    ∑ i : Fin 512, mag2N i / 128 ≤ 392 := by
  obtain ⟨-, -, -, -, hz599, -⟩ := FalconEAlg.sizes (program := program)
  have hlow := low2_eq hs hmag2N hmag2C hlow2N hlow2C
  obtain ⟨r, hbd⟩ := FalconEAlg.rBudget (program := program)
  have h := holdsAt hs (p := 289) (by simp)
  rw [hbd] at h
  obtain ⟨b, hb, hbv⟩ := natBelow_mem1 h (i := 0) (by
    rw [budgetExpr, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add,
      RealizedProgram.exprLen_scale, RealizedProgram.exprLen_apply]
    simp [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols, RealizedProgram.exprLen_leaf,
      hz599])
  rw [budgetExpr, RealizedProgram.evalE_add, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, RealizedProgram.evalE_apply_sum,
    RealizedProgram.evalE_apply_sum, decode_mOne] at hbv
  change _ + rdA e 601 0 = _ at hbv
  rw [rdA_off] at hbv
  simp only [Nat.zero_mul, Nat.zero_add] at hbv
  change -1 * ∑ t : Fin 512, rdA e 599 t + ∑ t : Fin 512, rdA e 600 t + _ = _ at hbv
  simp only [hmag2C, hlow2C] at hbv
  have hcast : (((∑ t : Fin 512, low2N t) + 50176 : ℕ) : (interp 1).K) =
      ((b + ∑ t : Fin 512, mag2N t : ℕ) : (interp 1).K) := by
    push_cast
    linear_combination hbv
  have hl : ∑ t : Fin 512, low2N t ≤ 512 * 128 := by
    calc _ ≤ ∑ _t : Fin 512, 128 := Finset.sum_le_sum fun t _ => (hlow2N t).le
      _ = 512 * 128 := by simp
  have hm' : ∑ t : Fin 512, mag2N t ≤ 512 * 2048 := by
    calc _ ≤ ∑ _t : Fin 512, 2048 := Finset.sum_le_sum fun t _ => (hmag2N t).le
      _ = 512 * 2048 := by simp
  have hnat := IntLift.natCast_inj_of_lt (K := (interp 1).K) (p := pGold)
    (by norm_num [pGold]; omega) (by norm_num [pGold]; omega) hcast
  have hsplit : ∑ t : Fin 512, mag2N t =
      ∑ t : Fin 512, low2N t + 128 * ∑ t : Fin 512, mag2N t / 128 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hlow t]
    omega
  omega

end EAlg

end Sound

/-! ## Domain `A`'s obligation -/

section Obligation

variable {program : RealizedProgram} {FH FA : RealizedProgram.FieldInterp}

set_option hygiene false in
local notation "interp" => RealizedProgram.falconInterpOf FH FA

variable [EField FA] [FalconACore program] [FalconEAlg program]

/-- **Domain `A`'s obligation for an emulated Falcon program** (`AlgebraSound`): wherever the
source program holds, at the key its statement decodes to, the ranges, the magnitude equations,
the norm, the encoding budget and the signature congruence (`congruent`) give Falcon's algebraic
verifier and the encoding bounds (`Emulated.algebraSpec_of_congruent`). -/
theorem algebraSound : AlgebraSound (program := program) (FH := FH) (FA := FA) := by
  classical
  intro e hs pk hpk
  obtain ⟨-, hz596, hz597, hz598, hz599, hz600, hz602⟩ := FalconEAlg.sizes (program := program)
  -- the ranges
  choose mag1N hmag1N hmag1C using leaf_natBelow (e := e) hs (p := 286) (by simp)
    FalconEAlg.rMag1 hz598
  choose mag2N hmag2N hmag2C using leaf_natBelow (e := e) hs (p := 287) (by simp)
    FalconEAlg.rMag2 hz599
  choose low2N hlow2N hlow2C using leaf_natBelow (e := e) hs (p := 288) (by simp)
    FalconEAlg.rLow2 hz600
  obtain ⟨sq, hsqN, hsqC⟩ := leaf_natBelow (e := e) hs (p := 290) (by simp)
    FalconEAlg.rNorm hz602 ⟨0, by norm_num⟩
  -- the magnitudes
  have hm1 : ∀ i : Fin 512,
      (rdA e 598 i - rdA e 597 i) * (rdA e 598 i - ((12289 : ℕ) - rdA e 597 i)) = 0 :=
    fun i => mag_eq hs (p := 275) (by simp) FalconEAlg.magS1 hz598 i.isLt
  have hm2 : ∀ i : Fin 512,
      (rdA e 599 i - rdA e 596 i) * (rdA e 599 i - ((12289 : ℕ) - rdA e 596 i)) = 0 :=
    fun i => mag_eq hs (p := 276) (by simp) FalconEAlg.magS2 hz599 i.isLt
  have hs1R : ∀ i : Fin 512, Range.IsNatBelow (12289 + 1) (rdA e 597 i) := fun i =>
    EmulatedNorm.isNatBelow_of_centering ⟨mag1N i, by have := hmag1N i; omega, (hmag1C i).symm⟩
      (hm1 i)
  have hs2R : ∀ i : Fin 512, Range.IsNatBelow (12289 + 1) (rdA e 596 i) := fun i =>
    EmulatedNorm.isNatBelow_of_centering ⟨mag2N i, by have := hmag2N i; omega, (hmag2C i).symm⟩
      (hm2 i)
  choose s1N hs1N hs1C using hs1R
  choose s2N hs2N hs2C using hs2R
  -- the signature congruence and the encoding budget
  have hcong := congruent hs hpk (s1N := s1N) (s2N := s2N)
    (fun i => ⟨(hs1C i).symm, Nat.le_of_lt_succ (hs1N i)⟩)
    (fun i => ⟨(hs2C i).symm, Nat.le_of_lt_succ (hs2N i)⟩)
  have hbudget := budget_le hs hmag2N hmag2C hlow2N hlow2C
  -- the algebra
  have hA := Emulated.algebraSpec_of_congruent (F := (interp 1).K)
    (h := pk.h) (c := Emulated.cNat (cABits e))
    (s1 := fun i : Fin falcon512.n => rdA e 597 i) (s2 := fun i : Fin falcon512.n => rdA e 596 i)
    (mag1 := fun i : Fin falcon512.n => rdA e 598 i) (mag2 := fun i : Fin falcon512.n => rdA e 599 i) (norm := rdA e 602 0) (s1N := s1N) (s2N := s2N)
    (mag2N := mag2N)
    (fun i => ⟨Nat.le_of_lt_succ (hs1N i), hs1C i⟩)
    (fun i => ⟨Nat.le_of_lt_succ (hs2N i), hs2C i⟩)
    (fun i => ⟨mag1N i, hmag1N i, (hmag1C i).symm⟩)
    (fun i => ⟨hmag2N i, (hmag2C i).symm⟩)
    (fun i => hm1 i) (fun i => hm2 i) (norm_eq hs) ⟨sq, hsqN, hsqC.symm⟩ hbudget hcong
  have hs2 : s2Vals (program.reader e) = fun i : Fin falcon512.n => rdA e 596 i :=
    funext (s2Vals_eq e)
  unfold AlgebraAt
  rw [hs2]
  exact ⟨hA.algebra, hA.encoding⟩

end Obligation

end GordieHowe.Falcon512.Emulated
