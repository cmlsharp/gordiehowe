-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Emulated.Frontend.Algebra
public import GordieHoweCerts.Applications.Falcon512.Native.HonestFull
public import GordieHowe.Applications.Falcon512.Ring.Carrier.Honest

@[expose] public section

/-!
# GordieHowe: the honest algebra of an emulated Falcon program

The honest values of domain `A` of an emulated Falcon program (`Falcon512.Emulated.ROMParams`,
`Falcon512.Emulated.QROMParams`) and its source predicates at them, generic in the program
(`FalconEAlg` and `FalconEHonest`, decided per program) and in domain `A`'s Goldilocks field
(`GordieHowe.Falcon512.EField`).

* **The honest naturals** (`aNat`, at the signature `GordieHowe.Falcon512.Native.hIn` of the
  honest input): the samples' bits `c_A`, the canonical `s2` and `s1`, the magnitudes of `s2` and
  their low parts `mag2 mod 128`, and the digits of the values bound to their digits (the
  magnitudes of `s1` in base `128`, the squared norm in base `2048`). The magnitudes, the budget
  and the squared norm are the Falcon ring carriers' (`GordieHowe.Falcon512.Ring.Carrier`). The
  realization's values (the complements of the two-sided digits, the signature equation's quotient
  digits, the histograms) are generated (`GordieHowe.RealizedProgram.genCommitted`).
* **The readings** at the source environment of these values (`rdA_aVal`): a committed value its
  honest natural, a value bound to its digits the natural they hold (`rd_mag1`, `rd_sq`).
* **The source predicates of domain `A`**: the magnitudes (`magS1_honest`, `magS2_honest`), the
  norm (`normSum_honest`), the five ranges (`ranges_honest`), `encoding.high2` (`high2_honest`),
  the signature congruence `s1 + h · s2 ≡ c (mod q)` on the integer readings at the key's
  coefficients (`sig_honest`), `c_A`'s type check (`cABool_honest`) and the crossing `mac.equal`
  (`cross_honest`).
-/

namespace GordieHowe.Falcon512.Emulated

open GordieHowe.Bits RealizedProgram
open _root_.GordieHowe.Falcon512.Norm (NormIn)
open _root_.GordieHowe.Falcon512.Emulated.Params

set_option linter.unusedSectionVars false

/-! ## The prime subfield of the Goldilocks fields -/

/-- **Goldilocks²'s node `GF(p^1)` is its prime subfield.** -/
instance instPrimeNodeGold2 : Ring.PrimeNode RealizedProgram.gold2 :=
  ⟨⟨RelativePacking.fixedField _ pGold 1, fun x => by
    change x ∈ gold2Node "GF(p^1)" ↔ _
    rw [gold2Node, if_pos rfl]
    rfl⟩⟩

/-- **Goldilocks⁴'s node `GF(p^1)` is its prime subfield.** -/
instance instPrimeNodeGold4 : Ring.PrimeNode RealizedProgram.gold4 :=
  ⟨⟨RelativePacking.fixedField _ pGold 1, fun x => by
    change x ∈ gold4Node "GF(p^1)" ↔ _
    rw [gold4Node, if_pos rfl]
    rfl⟩⟩

/-! ## The program facts -/

/-- **The committed values of domain `A` with honest naturals**: `crossing.c_A` (`595`), `s2`
(`596`), `signature.s1` (`597`), `magnitudes.mag2` (`599`), `encoding.low2` (`600`), the digits
of `magnitudes.mag1` (`612`, `613`) and of `norm.squares` (`622 … 624`). -/
def aValues : List ℕ := [595, 596, 597, 599, 600, 612, 613, 622, 623, 624]

/-- **The program facts of an emulated Falcon program's honest domain `A`** beyond the frontend's
(`FalconEAlg`; each program instantiates them by `decide`): the values bound to their digits
(`magnitudes.mag1` to `612 + 128 · 613`, `norm.squares` to `622 + 2048 · 623 + 2048² · 624`) and
their `BoundOk`; the committed values of `aValues`, checked committed cells of field `1`, and the
digits' sizes; the bodies of `signature.equation` and `encoding.high2`;
`c_A`'s type check (predicate `284`); `mac.equal` (predicate `299`), crossing the raw view `589`
of field `0` and `c_A`. -/
class FalconEHonest (program : RealizedProgram) [FalconACore program] [FalconEAlg program] :
    Prop where
  /-- `magnitudes.mag1` is bound to its two base-`128` digits. -/
  mag1Kind : (program.value 598).kind = .bound (.add (.leaf 612) (.scale (.const 128) (.leaf 613)))
  /-- `norm.squares` is bound to its three base-`2048` digits. -/
  sqKind : (program.value 602).kind = .bound (.add (.add (.leaf 622) (.scale (.const 2048)
    (.leaf 623))) (.scale (.const 4194304) (.leaf 624)))
  /-- Every value bound to its digits reads committed values and constants. -/
  bound : ∀ v < program.values.length, program.BoundOk v
  /-- The values of `aValues` are checked committed cells of field `1`. -/
  a_cells : ∀ v ∈ aValues, program.privCellB v = true ∧ program.valueField v = 1
  /-- The digits' sizes. -/
  digitSizes : (program.value 612).size = 512 ∧ (program.value 613).size = 512 ∧
    (program.value 622).size = 1 ∧ (program.value 623).size = 1 ∧ (program.value 624).size = 1
  /-- The program has the bound values. -/
  lens : 602 < program.values.length
  /-- `signature.equation`. -/
  sigForm : ∃ real, (program.predicate 297).body = .mod 1 12289 sigLhs sigRhs real
  /-- `encoding.high2`. -/
  high2Form : ∃ real, (program.predicate 298).body = .mod 1 128 (.leaf 599) (.leaf 600) real
  /-- `c_A`'s type check. -/
  caBody : ∃ t, (program.predicate 284).body = .equal 1 (.mul (.leaf 595) (.leaf 595)) (.leaf 595) t
  /-- `mac.equal` crosses the raw view `589` and `c_A`. -/
  macBody : ∃ o r, (program.predicate 299).body = .cross 0 (.leaf 589) 1 (.leaf 595) o r ∧
    1 ≤ o.width
  /-- The raw view is of field `0`. -/
  rawField : program.valueField 589 = 0

/-! ## The honest naturals -/

section Naturals

variable {L : ℕ} (y : Falcon512.PoP.HonestInput L)

/-- **The honest natural of value `v` at coordinate `j`** of domain `A`, at the signature
`Native.hIn y` of the honest input: the samples' bits (`595`), `s2` (`596`), `s1` (`597`), the
magnitudes of `s2` (`599`) and their low parts (`600`), the base-`128` digits of the magnitudes of
`s1` (`612`, `613`), the base-`2048` digits of the squared norm (`622 … 624`); `0` elsewhere. -/
-- spec-side
noncomputable def aNat (v j : ℕ) : ℕ :=
  if v = 595 then
    (if h : j < 8192 then y.samples ⟨j / 16, by have : falcon512.n = 512 := rfl; omega⟩ /
      2 ^ (j % 16) % 2 else 0)
  else if v = 596 then (Native.hIn y).nS2 j
  else if v = 597 then (Native.hIn y).nS1 j
  else if v = 599 then Ring.Carrier.mag2 (Native.hIn y) j
  else if v = 600 then Ring.Carrier.mag2 (Native.hIn y) j % 128
  else if v = 612 then Ring.Carrier.mag1 (Native.hIn y) j % 128
  else if v = 613 then Ring.Carrier.mag1 (Native.hIn y) j / 128 % 128
  else if v = 622 then Ring.Carrier.squares (Native.hIn y) % 2048
  else if v = 623 then Ring.Carrier.squares (Native.hIn y) / 2048 % 2048
  else if v = 624 then Ring.Carrier.squares (Native.hIn y) / 4194304 % 2048
  else 0

variable {y}

theorem aNat_595 {j : ℕ} (hj : j < 8192) : aNat y 595 j =
    y.samples ⟨j / 16, by have : falcon512.n = 512 := rfl; omega⟩ / 2 ^ (j % 16) % 2 := by
  simp [aNat, hj]

theorem aNat_596 (j : ℕ) : aNat y 596 j = (Native.hIn y).nS2 j := by simp [aNat]
theorem aNat_597 (j : ℕ) : aNat y 597 j = (Native.hIn y).nS1 j := by simp [aNat]
theorem aNat_599 (j : ℕ) : aNat y 599 j = Ring.Carrier.mag2 (Native.hIn y) j := by simp [aNat]
theorem aNat_600 (j : ℕ) : aNat y 600 j = Ring.Carrier.mag2 (Native.hIn y) j % 128 := by
  simp [aNat]
theorem aNat_612 (j : ℕ) : aNat y 612 j = Ring.Carrier.mag1 (Native.hIn y) j % 128 := by
  simp [aNat]
theorem aNat_613 (j : ℕ) : aNat y 613 j = Ring.Carrier.mag1 (Native.hIn y) j / 128 % 128 := by
  simp [aNat]
theorem aNat_622 (j : ℕ) : aNat y 622 j = Ring.Carrier.squares (Native.hIn y) % 2048 := by
  simp [aNat]
theorem aNat_623 (j : ℕ) : aNat y 623 j = Ring.Carrier.squares (Native.hIn y) / 2048 % 2048 := by
  simp [aNat]
theorem aNat_624 (j : ℕ) : aNat y 624 j = Ring.Carrier.squares (Native.hIn y) / 4194304 % 2048 := by
  simp [aNat]

/-- The samples' bits are bits. -/
theorem aNat_595_lt (j : ℕ) : aNat y 595 j < 2 := by
  by_cases hj : j < 8192
  · rw [aNat_595 hj]
    exact Nat.mod_lt _ (by norm_num)
  · simp [aNat, hj]

/-- **The honest naturals lie below `p`.** -/
theorem aNat_lt (hy : y.Valid) {v : ℕ} (hv : v ∈ aValues) (j : ℕ) : aNat y v j < pGold := by
  have hp : (12289 : ℕ) < pGold := by norm_num [pGold]
  have h2048 : (2048 : ℕ) < pGold := by norm_num [pGold]
  simp only [aValues, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (aNat_595_lt j).trans (by norm_num [pGold])
  · rw [aNat_596]; exact (Ring.Carrier.nS2_lt j).trans hp
  · rw [aNat_597]; exact (Ring.Carrier.nS1_lt j).trans hp
  · rw [aNat_599]; exact (Ring.Carrier.mag2_lt (Native.hIn_valid hy) j).trans h2048
  · rw [aNat_600]; exact (Nat.mod_lt _ (by norm_num)).trans (by norm_num [pGold])
  · rw [aNat_612]; exact (Nat.mod_lt _ (by norm_num)).trans (by norm_num [pGold])
  · rw [aNat_613]; exact (Nat.mod_lt _ (by norm_num)).trans (by norm_num [pGold])
  · rw [aNat_622]; exact (Nat.mod_lt _ (by norm_num)).trans h2048
  · rw [aNat_623]; exact (Nat.mod_lt _ (by norm_num)).trans h2048
  · rw [aNat_624]; exact (Nat.mod_lt _ (by norm_num)).trans h2048

end Naturals

/-! ## The honest values and their readings -/

variable {program : RealizedProgram} [FalconACore program] [FalconEAlg program]
  [FalconEHonest program] {FH FA : FieldInterp} [EField FA]

set_option hygiene false in
local notation "interp" => falconInterpOf FH FA

variable (program FH FA) in
/-- **The honest values of domain `A`**: the honest naturals (`aNat`) in domain `A`'s field.

Running time: computing these values takes the honest residues (one negacyclic product), then a
constant number of digit operations per coefficient. This running time is argued here, not proved
in Lean. -/
-- spec-side
noncomputable def aVal {L : ℕ} (y : Falcon512.PoP.HonestInput L) (v j : ℕ) :
    (interp (program.valueField v)).K :=
  castElt (a := 1) ((aNat y v j : ℕ) : (interp 1).K)

omit [FalconEAlg program] [FalconEHonest program] [EField FA] in
/-- **A field `equal` of domain `A` holds** where its sides agree coordinatewise in field `1`. -/
theorem holdsWith_equalA_of {rd : program.Valuation interp} {lhs rhs : Expr} {t : Target}
    (h : ∀ i < program.exprLen lhs, program.evalE rd 1 lhs i = program.evalE rd 1 rhs i) :
    program.HoldsWith rd (.equal 1 lhs rhs t) := fun i hi => by
  unfold evalWith
  rw [FalconACore.domainField1 (program := program)]
  exact h i hi

omit [FalconEHonest program] [EField FA] in
/-- `c_A` has `8192` coordinates. -/
theorem cA_size : (program.value 595).size = 8192 := by
  have := (FalconACore.raw_facts (program := program)).2.2
  rwa [FalconEAlg.cA_eq] at this

section Readings

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

set_option hygiene false in
local notation "env" => program.srcEnv interp x val c π

/-- **A committed value of `aValues` reads its honest natural** at the source environment of
values agreeing with `aVal` there. -/
theorem rdA_aVal (h : ∀ v ∈ aValues, val v = aVal program FH FA y v) {v j : ℕ}
    (hv : v ∈ aValues) (hj : j < (program.value v).size) :
    rdA env v j = (aNat y v j : (interp 1).K) := by
  obtain ⟨hp, hf⟩ := FalconEHonest.a_cells (program := program) v hv
  unfold rdA
  rw [evalE_leaf, reader_srcEnv_of_privCellB x val c π hp hj, h v hv]
  exact castElt_castElt_of_eq hf.symm _

/-- **A value bound to its digits reads its expression** at the source environment. -/
theorem rdA_bound {v : ℕ} {ex : Expr} (hk : (program.value v).kind = .bound ex)
    (hf : program.valueField v = 1) (hv : v < program.values.length) (j : ℕ) :
    rdA env v j = program.evalE (program.reader env) 1 ex j := by
  unfold rdA
  rw [evalE_leaf, reader_bindAsg_of_boundOk (FalconEHonest.bound (program := program)) rfl hv hk]
  revert hf
  generalize program.valueField v = f
  intro hf
  subst hf
  rfl

variable (h : ∀ v ∈ aValues, val v = aVal program FH FA y v)
include h

theorem rd_cA {j : ℕ} (hj : j < 8192) :
    rdA env 595 j = ((y.samples ⟨j / 16, by have : falcon512.n = 512 := rfl; omega⟩ /
      2 ^ (j % 16) % 2 : ℕ) : (interp 1).K) := by
  rw [rdA_aVal h (by simp [aValues]) (by
    rw [cA_size (program := program)]; exact hj), aNat_595 hj]

theorem rd_cA_bool {j : ℕ} (hj : j < 8192) : rdA env 595 j = 0 ∨ rdA env 595 j = 1 := by
  rw [rd_cA h hj]
  rcases Nat.mod_two_eq_zero_or_one (y.samples ⟨j / 16, by have : falcon512.n = 512 := rfl; omega⟩ /
    2 ^ (j % 16)) with h0 | h1
  · left; rw [h0, Nat.cast_zero]
  · right; rw [h1, Nat.cast_one]

theorem rd_s2 {j : ℕ} (hj : j < 512) : rdA env 596 j = ((Native.hIn y).nS2 j : (interp 1).K) := by
  rw [rdA_aVal h (by simp [aValues]) (by rw [(FalconEAlg.sizes (program := program)).2.1]; exact hj),
    aNat_596]

theorem rd_s1 {j : ℕ} (hj : j < 512) : rdA env 597 j = ((Native.hIn y).nS1 j : (interp 1).K) := by
  rw [rdA_aVal h (by simp [aValues])
    (by rw [(FalconEAlg.sizes (program := program)).2.2.1]; exact hj), aNat_597]

theorem rd_mag2 {j : ℕ} (hj : j < 512) :
    rdA env 599 j = (Ring.Carrier.mag2 (Native.hIn y) j : (interp 1).K) := by
  rw [rdA_aVal h (by simp [aValues])
    (by rw [(FalconEAlg.sizes (program := program)).2.2.2.2.1]; exact hj), aNat_599]

theorem rd_low2 {j : ℕ} (hj : j < 512) :
    rdA env 600 j = ((Ring.Carrier.mag2 (Native.hIn y) j % 128 : ℕ) : (interp 1).K) := by
  rw [rdA_aVal h (by simp [aValues])
    (by rw [(FalconEAlg.sizes (program := program)).2.2.2.2.2.1]; exact hj), aNat_600]

/-- **The magnitudes of `s1`** read their honest naturals through their digits. -/
theorem rd_mag1 {j : ℕ} (hj : j < 512) :
    rdA env 598 j = (Ring.Carrier.mag1 (Native.hIn y) j : (interp 1).K) := by
  obtain ⟨h612, h613, -⟩ := FalconEHonest.digitSizes (program := program)
  rw [rdA_bound FalconEHonest.mag1Kind (FalconEAlg.fields (program := program) 598 (by simp))
    (by have := FalconEHonest.lens (program := program); omega),
    evalE_add, evalE_scale_const, decode1 (by norm_num [pGold])]
  change rdA env 612 j + _ * rdA env 613 j = _
  rw [rdA_aVal h (by simp [aValues]) (by rw [h612]; exact hj),
    rdA_aVal h (by simp [aValues]) (by rw [h613]; exact hj), aNat_612, aNat_613]
  have hd := Ring.Carrier.digits128 (n := Ring.Carrier.mag1 (Native.hIn y) j)
    (lt_of_le_of_lt (Ring.Carrier.mag1_le j) (by norm_num))
  simp only [pow_zero, pow_one, Nat.div_one] at hd
  conv_rhs => rw [← hd]
  push_cast
  ring

/-- **The squared norm** reads its honest natural through its digits. -/
theorem rd_sq (hy : y.Valid) : rdA env 602 0 = (Ring.Carrier.squares (Native.hIn y) : (interp 1).K) := by
  obtain ⟨-, -, h622, h623, h624⟩ := FalconEHonest.digitSizes (program := program)
  rw [rdA_bound FalconEHonest.sqKind (FalconEAlg.fields (program := program) 602 (by simp))
    (FalconEHonest.lens (program := program)),
    evalE_add, evalE_add, evalE_scale_const, evalE_scale_const, decode1 (by norm_num [pGold]),
    decode1 (by norm_num [pGold])]
  change rdA env 622 0 + _ * rdA env 623 0 + _ * rdA env 624 0 = _
  rw [rdA_aVal h (by simp [aValues]) (by rw [h622]; norm_num),
    rdA_aVal h (by simp [aValues]) (by rw [h623]; norm_num),
    rdA_aVal h (by simp [aValues]) (by rw [h624]; norm_num), aNat_622, aNat_623, aNat_624]
  have hd := Ring.Carrier.digits3 (n := Ring.Carrier.squares (Native.hIn y))
    (lt_of_le_of_lt (Ring.Carrier.squares_le (Native.hIn_valid hy)) (by norm_num))
  norm_num only [pow_zero, pow_one, Nat.div_one] at hd
  conv_rhs => rw [← hd]
  push_cast
  ring

end Readings

/-! ## The magnitudes, the norm, the ranges and the encoding -/

section Preds

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

set_option hygiene false in
local notation "env" => program.srcEnv interp x val c π

variable (h : ∀ v ∈ aValues, val v = aVal program FH FA y v)
include h

/-- **`magnitudes.s1` holds**: the centered magnitude (`Ring.Carrier.centering1`). -/
theorem magS1_honest : program.HoldsAt env (program.predicate 275).body := by
  obtain ⟨t, hb⟩ := FalconEAlg.magS1 (program := program)
  rw [HoldsAt, hb]
  refine holdsWith_equalA_of fun i hi => ?_
  rw [magLhs, exprLen_mul, exprLen_add, exprLen_leaf,
    (FalconEAlg.sizes (program := program)).2.2.2.1] at hi
  change _ = rdA env 42 i
  rw [rdA_zeros _ hi, evalE_magLhs _ _ _ hi, rd_mag1 h hi, rd_s1 h hi]
  exact Ring.Carrier.centering1 hi

/-- **`magnitudes.s2` holds**: the centered magnitude (`Ring.Carrier.centering2`). -/
theorem magS2_honest : program.HoldsAt env (program.predicate 276).body := by
  obtain ⟨t, hb⟩ := FalconEAlg.magS2 (program := program)
  rw [HoldsAt, hb]
  refine holdsWith_equalA_of fun i hi => ?_
  rw [magLhs, exprLen_mul, exprLen_add, exprLen_leaf,
    (FalconEAlg.sizes (program := program)).2.2.2.2.1] at hi
  change _ = rdA env 42 i
  rw [rdA_zeros _ hi, evalE_magLhs _ _ _ hi, rd_mag2 h hi, rd_s2 h hi]
  exact Ring.Carrier.centering2 hi

/-- **`norm.sum` holds**: `squares = Σ mag1² + Σ mag2²`. -/
theorem normSum_honest (hy : y.Valid) : program.HoldsAt env (program.predicate 277).body := by
  obtain ⟨t, hb⟩ := FalconEAlg.normSum (program := program)
  rw [HoldsAt, hb]
  refine holdsWith_equalA_of fun i hi => ?_
  rw [normLhs, exprLen_add, exprLen_add, exprLen_leaf,
    (FalconEAlg.sizes (program := program)).2.2.2.2.2.2] at hi
  obtain rfl : i = 0 := by omega
  change _ = rdA env 43 0
  rw [rdA_zero, evalE_normLhs, rd_sq h hy]
  simp only [fun t : Fin 512 => rd_mag1 (x := x) (c := c) (π := π) h t.isLt,
    fun t : Fin 512 => rd_mag2 (x := x) (c := c) (π := π) h t.isLt]
  unfold Ring.Carrier.squares
  push_cast
  simp only [sq]
  ring

omit h in
/-- **A range of one record of domain `A` holds** where each coordinate reads a natural below the
bound. -/
theorem mem_honest {p n : ℕ} {E : Expr} {r : InRealization}
    (hb : (program.predicate p).body = .mem 1 [E] (.range n) r)
    (hk : ∀ i < program.exprLen E, ∃ k < n,
      program.evalE (program.reader env) 1 E i = (k : (interp 1).K)) :
    program.HoldsAt env (program.predicate p).body := by
  rw [HoldsAt, hb]
  intro i hi e he
  rw [List.mem_singleton] at he
  subst he
  obtain ⟨k, hkn, hkv⟩ := hk i hi
  refine ⟨k, hkn, ?_⟩
  unfold evalWith
  rw [FalconACore.domainField1 (program := program)]
  exact hkv

/-- **The budget's expression** reads the honest budget (`Ring.Carrier.budget`). -/
theorem evalE_budget (hy : y.Valid) :
    program.evalE (program.reader env) 1 budgetExpr 0 =
      (Ring.Carrier.budget (Native.hIn y) : (interp 1).K) := by
  rw [budgetExpr, evalE_add, evalE_add, evalE_scale_const, evalE_apply_sum, evalE_apply_sum,
    decode_mOne]
  change _ + rdA env 601 0 = _
  rw [rdA_off]
  simp only [Nat.zero_mul, Nat.zero_add]
  change -1 * ∑ t : Fin 512, rdA env 599 t + ∑ t : Fin 512, rdA env 600 t + _ = _
  simp only [fun t : Fin 512 => rd_mag2 (x := x) (c := c) (π := π) h t.isLt,
    fun t : Fin 512 => rd_low2 (x := x) (c := c) (π := π) h t.isLt]
  have hb := congrArg (Nat.cast : ℕ → (interp 1).K) (Ring.Carrier.budget_add (Native.hIn_valid hy))
  push_cast [Nat.cast_sum] at hb
  have hsub : ∀ t : Fin 512,
      ((Ring.Carrier.mag2 (Native.hIn y) t - Ring.Carrier.mag2 (Native.hIn y) t % 128 : ℕ) :
        (interp 1).K) = (Ring.Carrier.mag2 (Native.hIn y) t : (interp 1).K) -
          ((Ring.Carrier.mag2 (Native.hIn y) t % 128 : ℕ) : (interp 1).K) :=
    fun t => Nat.cast_sub (Nat.mod_le _ _)
  simp only [hsub, Finset.sum_sub_distrib] at hb
  linear_combination -hb

/-- **The ranges hold on the honest values**: the magnitudes of `s1` below `6145`, of `s2` below
`2048`, the low parts below `128`, the budget below `50177`, the squared norm below
`34034727`. -/
theorem ranges_honest (hy : y.Valid) :
    ∀ q ∈ [286, 287, 288, 289, 290], program.HoldsAt env (program.predicate q).body := by
  obtain ⟨-, -, -, hz598, hz599, hz600, hz602⟩ := FalconEAlg.sizes (program := program)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r, hb⟩ := FalconEAlg.rMag1 (program := program)
    exact mem_honest hb fun i hi => ⟨_, Nat.lt_succ_of_le (Ring.Carrier.mag1_le i),
      rd_mag1 h (by rwa [exprLen_leaf, hz598] at hi)⟩
  · obtain ⟨r, hb⟩ := FalconEAlg.rMag2 (program := program)
    exact mem_honest hb fun i hi => ⟨_, Ring.Carrier.mag2_lt (Native.hIn_valid hy) i,
      rd_mag2 h (by rwa [exprLen_leaf, hz599] at hi)⟩
  · obtain ⟨r, hb⟩ := FalconEAlg.rLow2 (program := program)
    exact mem_honest hb fun i hi => ⟨_, Nat.mod_lt _ (by norm_num),
      rd_low2 h (by rwa [exprLen_leaf, hz600] at hi)⟩
  · obtain ⟨r, hb⟩ := FalconEAlg.rBudget (program := program)
    refine mem_honest hb fun i hi => ?_
    rw [budgetExpr, exprLen_add, exprLen_add, exprLen_scale, exprLen_apply] at hi
    have hi0 : i = 0 := by
      simp [NamedOp.rows, NamedOp.cols, exprLen_leaf, hz599] at hi
      omega
    subst hi0
    exact ⟨_, Nat.lt_succ_of_le Ring.Carrier.budget_le, evalE_budget h hy⟩
  · obtain ⟨r, hb⟩ := FalconEAlg.rNorm (program := program)
    refine mem_honest hb fun i hi => ?_
    rw [exprLen_leaf, hz602] at hi
    obtain rfl : i = 0 := by omega
    exact ⟨_, Nat.lt_succ_of_le (Ring.Carrier.squares_le (Native.hIn_valid hy)), rd_sq h hy⟩

/-- **`encoding.high2` holds**: `128 ∣ mag2 − mag2 mod 128` on the integer readings. -/
theorem high2_honest (hy : y.Valid) : program.HoldsAt env (program.predicate 298).body := by
  obtain ⟨r, hb⟩ := FalconEHonest.high2Form (program := program)
  obtain ⟨-, -, -, hk599, hk600⟩ := FalconEAlg.privKinds (program := program)
  obtain ⟨-, -, -, -, hz599, -⟩ := FalconEAlg.sizes (program := program)
  rw [HoldsAt, hb, holdsWith_mod_iff]
  intro i hi
  rw [exprLen_leaf, hz599] at hi
  have hm := Ring.Carrier.mag2_lt (Native.hIn_valid hy) (w := Native.hIn y) i
  rw [evalIntWith_leaf, evalIntWith_leaf,
    intOf_priv hk599 (FalconEAlg.fields 599 (by simp)) (rd_mag2 h hi) (by norm_num [pGold]; omega),
    intOf_priv hk600 (FalconEAlg.fields 600 (by simp)) (rd_low2 h hi)
      (by have := Nat.mod_lt (Ring.Carrier.mag2 (Native.hIn y) i) (show 0 < 128 by norm_num)
          norm_num [pGold]; omega)]
  exact ⟨(Ring.Carrier.mag2 (Native.hIn y) i / 128 : ℕ), by
    push_cast; have := Nat.mod_add_div (Ring.Carrier.mag2 (Native.hIn y) i) 128; omega⟩

/-- **`c_A`'s type check holds**: the honest sample bits are bits. -/
theorem cABool_honest : program.HoldsAt env (program.predicate 284).body := by
  obtain ⟨_, hcb⟩ := FalconEHonest.caBody (program := program)
  rw [HoldsAt, hcb]
  refine holdsWith_equalA_of fun j hj => ?_
  rw [exprLen_mul, exprLen_leaf, cA_size (program := program)] at hj
  change rdA env 595 j * rdA env 595 j = rdA env 595 j
  rcases rd_cA_bool h hj with h0 | h1
  · rw [h0, mul_zero]
  · rw [h1, mul_one]

end Preds

/-! ## The signature congruence -/

section Signature

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

set_option hygiene false in
local notation "env" => program.srcEnv interp x val c π

variable (h : ∀ v ∈ aValues, val v = aVal program FH FA y v)
include h

/-- **The integer reading of a sample bit** is the bit. -/
theorem intOf_cA_honest {t : ℕ} (ht : t < 8192) :
    program.intOf (program.reader env) 595 t =
      ((y.samples ⟨t / 16, by have : falcon512.n = 512 := rfl; omega⟩ / 2 ^ (t % 16) % 2 : ℕ) : ℤ) :=
  intOf_priv (FalconEAlg.privKinds (program := program)).1
    (FalconEAlg.fields (program := program) 595 (by simp)) (rd_cA h ht)
    ((Nat.mod_lt _ (by norm_num)).trans (by norm_num [pGold]))

/-- **The signature equation's right side on the integers** is the honest sample. -/
theorem evalIntWith_sigRhs_honest (hy : y.Valid) (i : Fin falcon512.n) :
    program.evalIntWith (program.reader env) 1 sigRhs i = (y.samples i : ℤ) := by
  have hd1 := FalconACore.domainField1 (program := program)
  rw [sigRhs, evalIntWith_apply, hd1,
    NamedOp.applyInt_batched_fromDigits program (p := pGold) (EField.spec_char (FA := FA))
      (EField.charP (FA := FA)) (fun k hk => toNat1 hk) (by norm_num [pGold]) _ (by norm_num)
      (decode1 (by norm_num [pGold]))
      (fun l hl => by
        have : 2 ^ l ≤ 2 ^ 15 := Nat.pow_le_pow_right (by norm_num) (by omega)
        norm_num [pGold]
        omega),
    Nat.div_eq_of_lt (show (i : ℕ) < 512 from i.isLt),
    Nat.mod_eq_of_lt (show (i : ℕ) < 512 from i.isLt)]
  simp only [Nat.zero_mul, Nat.zero_add, evalIntWith_leaf]
  have hi := i.isLt
  have hbit : ∀ l : Fin 16, program.intOf (program.reader env) 595 (i * 16 + l) =
      ((y.samples i / 2 ^ (l : ℕ) % 2 : ℕ) : ℤ) := fun l => by
    rw [intOf_cA_honest h (by have : falcon512.n = 512 := rfl; omega)]
    have e2 : ((i : ℕ) * 16 + (l : ℕ)) % 16 = l := by omega
    have e3 : ((i : ℕ) * 16 + (l : ℕ)) / 16 = i := by omega
    simp only [e2, e3]
  simp only [hbit]
  have hs := Native.sum_bits_field (K := ℚ) (y.samples i)
  rw [Nat.mod_eq_of_lt (Emulated.samples_lt hy i)] at hs
  exact_mod_cast hs

/-- **The signature equation's left side on the integers**: `s1 + Σ_k negCoef(h)_{i,k} s2_k`,
`h` the key's coefficients (`keyNat`). -/
theorem evalIntWith_sigLhs_honest {i : ℕ} (hi : i < 512) :
    program.evalIntWith (program.reader env) 1 sigLhs i =
      ((Native.hIn y).nS1 i : ℤ) + ∑ k : Fin 512,
        Ops.negCoef 512 (fun s => (keyNat x s : ℤ)) i k * ((Native.hIn y).nS2 k : ℤ) := by
  have hd1 := FalconACore.domainField1 (program := program)
  have hf594 := FalconEAlg.fields (program := program) 594 (by simp)
  obtain ⟨hz594, -⟩ := FalconEAlg.sizes (program := program)
  obtain ⟨-, hk596, hk597, -⟩ := FalconEAlg.privKinds (program := program)
  have hz : ∀ s < 512, (interp 1).toNat
      (castElt (program.reader env 594 s) : (interp 1).K) = keyNat x s ∧
        2 * keyNat x s < pGold := by
    intro s _
    have hlt : keyNat x s < 12289 := keyCoeffs_lt _ s
    refine ⟨?_, by norm_num [pGold]; omega⟩
    have hd := toNat_decode_of (FH := FH) (FA := FA) (n := keyNat x s) hf594
      (hlt.trans (by norm_num [pGold]))
    rw [toNat_castElt hf594, reader_key]
    exact hd
  have hcoef : ∀ (j k : ℕ), (interp 1).coefInt (Ops.negCoef 512
      (fun s => (castElt (program.reader env 594 s) : (interp 1).K)) j k) =
      Ops.negCoef 512 (fun s => (keyNat x s : ℤ)) j k :=
    fun j k => coefInt_negCoef (FA := FA) 512 hz j k
  rw [sigLhs, evalIntWith_add, evalIntWith_leaf, evalIntWith_apply, hd1,
    NamedOp.applyInt_negacyclicConv _ _ _ _ _ (by rw [hz594]; norm_num), hz594,
    Nat.mod_eq_of_lt hi, Nat.div_eq_of_lt hi]
  simp only [Nat.zero_mul, Nat.zero_add, NamedOp.formPoly, hcoef, evalIntWith_leaf]
  rw [intOf_priv hk597 (FalconEAlg.fields 597 (by simp)) (rd_s1 h hi)
    ((Ring.Carrier.nS1_lt i).trans (by norm_num [pGold]))]
  refine congrArg (((Native.hIn y).nS1 i : ℤ) + ·) (Finset.sum_congr rfl fun k _ => ?_)
  rw [intOf_priv hk596 (FalconEAlg.fields 596 (by simp)) (rd_s2 h k.isLt)
    ((Ring.Carrier.nS2_lt k).trans (by norm_num [pGold]))]

/-- **`signature.equation` holds** on the honest values at the key's statement: on the integer
readings `s1 + h · s2 ≡ c (mod q)`, `h` the key's coefficients (`keyNat_of_keyOf`) and `c` the
samples (`EmulatedAlgebraCircuit.Honest.congruent_honest`). -/
theorem sig_honest (hy : y.Valid) (hx : keyOf x = some y.pk) :
    program.HoldsAt env (program.predicate 297).body := by
  obtain ⟨real, hb⟩ := FalconEHonest.sigForm (program := program)
  obtain ⟨-, -, hz597, -⟩ := FalconEAlg.sizes (program := program)
  rw [HoldsAt, hb, holdsWith_mod_iff]
  intro i hi
  rw [sigLhs, exprLen_add, exprLen_leaf, hz597] at hi
  rw [evalIntWith_sigLhs_honest h hi]
  rw [show (i : ℕ) = ((⟨i, hi⟩ : Fin falcon512.n) : ℕ) from rfl,
    evalIntWith_sigRhs_honest h hy ⟨i, hi⟩]
  refine (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12289).1 ?_
  have hsum : ∑ k : Fin 512, Ops.negCoef 512 (fun s => (keyNat x s : ℤ)) i k *
      ((Native.hIn y).nS2 k : ℤ) =
      LatticeCrypto.negacyclicConvCoeff (fun k : Fin 512 => ((keyNat x k : ℕ) : ℤ))
        (fun k : Fin 512 => ((Native.hIn y).nS2 k : ℤ)) ⟨i, hi⟩ :=
    (Finset.sum_congr rfl fun k _ => by
      rw [negCoef_eq_convWeight (keyNat x) ⟨i, hi⟩ k]).trans
      (Emulated.Rows.sum_convWeight_eq_negacyclicConvCoeff (fun t : Fin 512 => keyNat x t) _ ⟨i, hi⟩)
  rw [hsum]
  push_cast
  rw [Emulated.Rows.intCast_negacyclicConvCoeff (fun t : Fin 512 => keyNat x t)
    (fun k : Fin 512 => (Native.hIn y).nS2 k) ⟨i, hi⟩]
  have hc := EmulatedAlgebraCircuit.Honest.congruent_honest (P := falcon512) rfl y.pk.h y.samples
    y.signature ⟨i, hi⟩
  simp only [show ∀ j : Fin 512, keyNat x j = EmulatedAlgebraCircuit.keyCoeffs y.pk.h j from
    keyNat_of_keyOf hx]
  have hs1 : (Native.hIn y).nS1 i = EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) y.pk.h
      y.samples y.signature ⟨i, hi⟩ := Native.nS1_hIn hi
  have hs2 : (fun k : Fin 512 => (((Native.hIn y).nS2 k : ℕ) : ZMod 12289)) =
      fun k => ((EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) y.signature k : ℕ) :
        ZMod 12289) := funext fun k => by rw [Native.nS2_hIn k.isLt]; rfl
  rw [hs1, hs2]
  change ((y.samples ⟨i, hi⟩ : ℕ) : ZMod 12289) = _ at hc
  rw [hc]
  exact sub_eq_zero.mpr rfl

end Signature

/-! ## The crossing -/

section Crossing

variable [HField FH] [FalconHBase program] [FalconHHonest program] [FalconHSelHonest program]
  [FalconHConsts program FH] [FalconSelField program FH FA]

variable {L : ℕ} {y : Falcon512.PoP.HonestInput L} {val x : program.Valuation interp}
  {c : ∀ k, (program.layout interp).Ch k} {π : (program.layout interp).Pads}

set_option hygiene false in
local notation "env" => program.srcEnv interp x val c π

/-- **The raw view's bit `j mod 16` of sample `j / 16`** (the honest natural of `c_A`). -/
theorem raw_honest (hsel : ∀ v ∈ [588, 590, 591], val v = selVal program FH FA y v) {j : ℕ}
    (hj : j < 8192) :
    program.evalE (program.reader env) 0 (.leaf 589) j = ((aNat y 595 j : ℕ) : (interp 0).K) := by
  have := congrFun (selWord_honest (x := x) (c := c) (π := π) hsel ⟨j / 16, by omega⟩)
    ⟨j % 16, by omega⟩
  simp only [selWord, SelectShape.word, wordAt] at this
  rw [show (j / 16) * 16 + j % 16 = j by omega] at this
  have hsf := selField (program := program)
  revert this
  generalize SelectShape.field program selShape = f at hsf ⊢
  subst hsf
  intro this
  refine this.trans ?_
  rw [Native.constBit_eq_cast, aNat_595 hj]
  rfl

/-- **`mac.equal` holds at the source environment** on the honest values: the raw view and `c_A`
are the same sample bits. -/
theorem cross_honest (hsel : ∀ v ∈ [588, 590, 591], val v = selVal program FH FA y v)
    (h : ∀ v ∈ aValues, val v = aVal program FH FA y v) :
    program.HoldsAt env (program.predicate 299).body := by
  obtain ⟨_, _, hmb, hwid⟩ := FalconEHonest.macBody (program := program)
  rw [HoldsAt, hmb]
  have hsz : program.exprLen (.leaf 589) = 8192 := by
    rw [exprLen_leaf]; exact (FalconACore.raw_facts (program := program)).2.1
  have hf589' : program.valueField 589 = 0 := FalconEHonest.rawField (program := program)
  have hf589 : program.valueField 589 = program.domainField 0 :=
    hf589'.trans (FalconHBase.domainField0 (program := program)).symm
  have hf595' : program.valueField 595 = 1 := FalconEAlg.fields (program := program) 595 (by simp)
  have hf595 : program.valueField 595 = program.domainField 1 :=
    hf595'.trans (FalconACore.domainField1 (program := program)).symm
  have hbit : ∀ j < 8192, (interp (program.domainField 0)).toNat
      (program.evalWith (program.reader env) 0 (.leaf 589) j) = aNat y 595 j := by
    intro j hj
    have h1 : (interp (program.domainField 0)).toNat
        (program.evalWith (program.reader env) 0 (.leaf 589) j) =
        (interp (program.valueField 589)).toNat (program.reader env 589 j) := by
      unfold evalWith
      rw [evalE_leaf]
      exact toNat_castElt_of_eq hf589 _
    have h2 : (interp 0).toNat (program.evalE (program.reader env) 0 (.leaf 589) j) =
        (interp (program.valueField 589)).toNat (program.reader env 589 j) := by
      rw [evalE_leaf]
      exact toNat_castElt_of_eq hf589' _
    rw [h1, ← h2, raw_honest hsel hj]
    rcases (show aNat y 595 j = 0 ∨ aNat y 595 j = 1 by have := aNat_595_lt (y := y) j; omega)
      with h0 | h0 <;> rw [h0]
    · rw [Nat.cast_zero]
      exact HField.toNat_zero (FH := FH)
    · rw [Nat.cast_one]
      exact HField.toNat_one (FH := FH)
  have hbitA : ∀ j < 8192, (interp (program.domainField 1)).toNat
      (program.evalWith (program.reader env) 1 (.leaf 595) j) = aNat y 595 j := by
    intro j hj
    have h1 : (interp (program.domainField 1)).toNat
        (program.evalWith (program.reader env) 1 (.leaf 595) j) =
        (interp 1).toNat (rdA env 595 j) := by
      unfold rdA evalWith
      rw [evalE_leaf, evalE_leaf, toNat_castElt_of_eq hf595, toNat_castElt_of_eq hf595']
    rw [h1, rdA_aVal h (by simp [aValues]) (by
      rw [cA_size (program := program)]; exact hj)]
    exact toNat1 ((aNat_595_lt j).trans (by norm_num [pGold]))
  simp only [HoldsWith]
  rw [hsz]
  refine ⟨fun j hj => ?_, fun _ j hj => ?_⟩
  · rw [hbitA j hj]
    exact lt_of_lt_of_le (aNat_595_lt j)
      ((Nat.pow_le_pow_right (by norm_num) hwid).trans_eq' (by norm_num))
  · rw [hbit j hj, hbitA j hj]

end Crossing

end GordieHowe.Falcon512.Emulated
