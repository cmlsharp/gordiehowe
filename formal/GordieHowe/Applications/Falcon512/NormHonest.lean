-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Frontend.Norm
public import GordieHowe.Language.Honest.Source
public import GordieHowe.Applications.Falcon512.Circuits.NativeAlgebraHonest

@[expose] public section

/-!
# GordieHowe: the honest native Falcon norm and encoding of a domain

The honest values of the native norm and the encoding (`FalconNorm`) of a Falcon signature
`(h, c, s₂)` (`NormIn`: a key, a challenge and the signature's `s₂`; valid when Falcon's algebraic
verifier accepts and the encoding bounds hold, `NormIn.Valid`), read off the honest native norm
witness on the canonical residues of `s₁ ‖ s₂` (`GordieHowe.Falcon512.NativeAlgebraCircuit.Honest.honestVals`, in naturals:
`NativeNorm.honestMagNat`, `NativeNorm.honestColprodNat`, `NativeNorm.sixDigit`,
`NativeNorm.sixCarry`, `NativeNorm.honestBatchColAt`); and the norm's and the encoding's source
predicates at the source environment of these values (the converses of
`GordieHowe/Applications/Falcon512/Frontend/Norm.lean`'s readings). Generic in the program (`FalconNorm`, and
`FalconNormHonest`: the values' cells, decided per program), its interpretation and the
identifiers of the domain.

The honest committed values enter through `NormVals`: each value of the norm holds the cast of its
honest natural (`nS2`, `nS1`, `nA`, `nSq`, `nCc`, `nNd`, `nNc`, `nD`, `nDc`).
-/

namespace GordieHowe.Falcon512.Norm

open GordieHowe.Bits Native.ROMParams

/-! ## The honest input -/

/-- **A Falcon signature the norm reads**: the key `h`, the challenge `c` (the coefficients of
`HashToPoint`) and the signature's `s₂`. -/
structure NormIn where
  /-- The key. -/
  h : _root_.Falcon.Rq falcon512.n
  /-- The challenge's coefficients. -/
  c : Fin falcon512.n → ℕ
  /-- The signature's `s₂`. -/
  s2 : _root_.Falcon.IntPoly falcon512.n

/-- **A valid signature**: Falcon's algebraic verifier accepts `s₂` at the key and the challenge,
and `s₂` meets the encoding bounds. -/
structure NormIn.Valid (w : NormIn) : Prop where
  /-- The algebraic verifier accepts. -/
  algebra : Falcon512.algebraOk falcon512 w.h
    (Falcon512.ofCoeff fun i => (w.c i : _root_.Falcon.Coeff)) w.s2.toRq
  /-- The encoding bounds hold. -/
  encoding : Falcon512.EncodingBounds falcon512 w.s2

namespace NormIn

variable (w : NormIn)

/-- **The honest residues** of `s₁ ‖ s₂` (`GordieHowe.Falcon512.NativeAlgebraCircuit.Honest.honestVals`). -/
-- spec-side
noncomputable abbrev vals : Fin 1024 → ℕ := Falcon512.NativeAlgebraCircuit.Honest.honestVals w.h w.c w.s2

/-- **The honest magnitude** of coefficient `i` (`0` past `1024`). -/
-- spec-side
noncomputable def mag (i : ℕ) : ℕ :=
  if h : i < 1024 then NativeNorm.honestMagNat w.vals ⟨i, h⟩ else 0

/-- **The honest schoolbook columns** of coefficient `i` (its masked magnitude digits). -/
-- spec-side
noncomputable def col (i : ℕ) : Fin 6 → ℕ :=
  NativeNorm.honestColprodNat (decide (512 ≤ i)) (w.mag i)

/-- **Magnitude digit `l` of coefficient `i`**, the program's `norm.a[i][l]`: base-`64` digits,
slot `2` of an `s₂` coefficient the encoding's high part `mag / 128`. -/
-- spec-side
noncomputable def digit (i l : ℕ) : ℕ :=
  if 512 ≤ i ∧ l = 2 then w.mag i / 128 else w.mag i / 64 ^ l % 64

/-- **The honest encoding slack**: the budget `392` less the `s₂` coefficients' high parts. -/
-- spec-side
noncomputable def slack : ℕ := 392 - ∑ i : Fin 512, w.mag (512 + i) / 128

/-- The last batch's digits. -/
-- spec-side
noncomputable abbrev lastDigits : Fin 6 → ℕ := NativeNorm.honestBatchNdig w.vals 16

/-! ### The honest naturals of the values -/

/-- `s2`: the canonical residues of `s₂`. -/
-- spec-side
noncomputable def nS2 (j : ℕ) : ℕ :=
  if h : j < 512 then Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) w.s2 ⟨j, h⟩ else 0

/-- `signature.s1`: the canonical residues of `s₁ = c − s₂ h`. -/
-- spec-side
noncomputable def nS1 (j : ℕ) : ℕ :=
  if h : j < 512 then Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) w.h w.c w.s2 ⟨j, h⟩ else 0

theorem nS2_fin (j : Fin falcon512.n) :
    w.nS2 j = Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) w.s2 j := by
  unfold nS2
  exact dif_pos j.isLt

theorem nS1_fin (j : Fin falcon512.n) :
    w.nS1 j = Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) w.h w.c w.s2 j := by
  unfold nS1
  exact dif_pos j.isLt

/-- `norm.a`: the magnitude digits. -/
-- spec-side
noncomputable def nA (j : ℕ) : ℕ := w.digit (j / 3) (j % 3)

/-- `norm.sq`: the square digits. -/
-- spec-side
noncomputable def nSq (j : ℕ) : ℕ := NativeNorm.sixDigit (w.col (j / 6)) ⟨j % 6, by omega⟩

/-- `norm.cc`: the column carries. -/
-- spec-side
noncomputable def nCc (j : ℕ) : ℕ := NativeNorm.sixCarry (w.col (j / 5)) ⟨j % 5, by omega⟩

/-- `norm.nd`: the batches' digits. -/
-- spec-side
noncomputable def nNd (j : ℕ) : ℕ := NativeNorm.honestBatchNdig w.vals (j / 6) ⟨j % 6, by omega⟩

/-- `norm.nc`: the batches' carries. -/
-- spec-side
noncomputable def nNc (j : ℕ) : ℕ :=
  NativeNorm.sixCarry (NativeNorm.honestBatchColAt w.vals (j / 5 + 1)) ⟨j % 5, by omega⟩

/-- `norm.D`: the complement's digits. -/
-- spec-side
noncomputable def nD (j : ℕ) : ℕ :=
  if j < 6 then (34034726 - ∑ k : Fin 6, w.lastDigits k * 64 ^ (k : ℕ)) / 64 ^ j % 64 else 0

/-- `norm.Dc`: the complement's carries. -/
-- spec-side
noncomputable def nDc (j : ℕ) : ℕ :=
  if h : j < 5 then NativeNorm.sixCarry (NativeNorm.honestDcol w.lastDigits) ⟨j, h⟩ else 0

end NormIn

/-! ## The program facts of the honest prover -/

/-- **The program facts of the honest norm** (each program instantiates them by `decide`): the
norm's values are private committed cells. -/
class FalconNormHonest (program : RealizedProgram) [FalconNorm program] : Prop where
  /-- The norm's values are private committed cells. -/
  privCell : ∀ v ∈ [FalconNorm.s2 program, FalconNorm.s1 program, FalconNorm.a program,
    FalconNorm.sq program, FalconNorm.cc program, FalconNorm.nd program, FalconNorm.nc program,
    FalconNorm.D program, FalconNorm.Dc program], program.privCellB v = true

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
local notation "vOff" => FalconNorm.off program
set_option hygiene false in
local notation "vZ1" => FalconNorm.z1 program
set_option hygiene false in
local notation "eN" => FalconNorm.e0 program
set_option hygiene false in
local notation "pN" => FalconNorm.p0 program
set_option hygiene false in
local notation "eMax" => FalconNorm.eMax program

variable [AField (I fA)]

/-- **The honest values of the norm** (`val` at the honest input `w`): every value of the norm
holds the cast of its honest natural. -/
structure NormVals (val : program.Valuation I) (w : NormIn) : Prop where
  s2 : ∀ j, val vS2 j = RealizedProgram.castElt (a := fA) ((w.nS2 j : ℕ) : (I fA).K)
  s1 : ∀ j, val vS1 j = RealizedProgram.castElt (a := fA) ((w.nS1 j : ℕ) : (I fA).K)
  a : ∀ j, val vA j = RealizedProgram.castElt (a := fA) ((w.nA j : ℕ) : (I fA).K)
  sq : ∀ j, val vSq j = RealizedProgram.castElt (a := fA) ((w.nSq j : ℕ) : (I fA).K)
  cc : ∀ j, val vCc j = RealizedProgram.castElt (a := fA) ((w.nCc j : ℕ) : (I fA).K)
  nd : ∀ j, val vNd j = RealizedProgram.castElt (a := fA) ((w.nNd j : ℕ) : (I fA).K)
  nc : ∀ j, val vNc j = RealizedProgram.castElt (a := fA) ((w.nNc j : ℕ) : (I fA).K)
  D : ∀ j, val vD j = RealizedProgram.castElt (a := fA) ((w.nD j : ℕ) : (I fA).K)
  Dc : ∀ j, val vDc j = RealizedProgram.castElt (a := fA) ((w.nDc j : ℕ) : (I fA).K)

/-! ## Reading the honest values -/

section Reading

variable {val x : program.Valuation I} {c : ∀ k, (program.layout I).Ch k}
  {π : (program.layout I).Pads}

/-- **A private committed value of the domain reads its honest natural** at the source
environment. -/
theorem rdA_honest {v j n : ℕ} (hv : program.privCellB v = true) (hf : program.valueField v = fA)
    (hval : val v j = RealizedProgram.castElt (a := fA) ((n : ℕ) : (I fA).K))
    (hj : j < (program.value v).size) :
    rdA (program.srcEnv I x val c π) v j = (n : (I fA).K) := by
  unfold rdA
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_srcEnv_of_privCellB x val c π hv hj, hval]
  exact RealizedProgram.castElt_castElt_of_eq hf.symm _

/-- **Its integer reading** is the natural, below `q`. -/
theorem ia_honest {v j n : ℕ} (hv : program.privCellB v = true) (hf : program.valueField v = fA)
    (hc : program.isConstant v = false)
    (hval : val v j = RealizedProgram.castElt (a := fA) ((n : ℕ) : (I fA).K))
    (hj : j < (program.value v).size) (hn : n < 12289) :
    ia (program.srcEnv I x val c π) v j = n := by
  rw [ia_eq_nA _ hf hc, nA, rdA_honest hv hf hval hj]
  exact congrArg Nat.cast (AField.toNat_natCast (FA := I fA) hn)

variable [FalconNormHonest program]

/-- The cells of the norm's values: private, of the domain's field, not constant. -/
theorem cells {v : ℕ} (hv : v ∈ [vS2, vS1, vA, vSq, vCc, vNd, vNc, vD, vDc]) :
    program.privCellB v = true ∧ program.valueField v = fA ∧ program.isConstant v = false := by
  refine ⟨FalconNormHonest.privCell v hv, ?_⟩
  by_cases hdc : v = vDc
  · subst hdc
    exact FalconNorm.fields_A (program := program)
  · have hp : v ∈ [vS2, vS1, vA, vSq, vCc, vNd, vNc, vD] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv ⊢
      tauto
    obtain ⟨-, -, -, -, hf, hc⟩ := FalconNorm.primeA_all (program := program) v hp
    exact ⟨hf, hc⟩

/-- **A value of the norm reads its honest natural** (`rdA_honest` at `cells`). -/
theorem rdA_of {v : ℕ} (hv : v ∈ [vS2, vS1, vA, vSq, vCc, vNd, vNc, vD, vDc]) {n : ℕ → ℕ}
    (hval : ∀ j, val v j = RealizedProgram.castElt (a := fA) ((n j : ℕ) : (I fA).K)) {j : ℕ}
    (hj : j < (program.value v).size) :
    rdA (program.srcEnv I x val c π) v j = (n j : (I fA).K) :=
  rdA_honest (cells hv).1 (cells hv).2.1 (hval j) hj

/-- **A value of the norm's integer reading** is its honest natural, below `q`. -/
theorem ia_of {v : ℕ} (hv : v ∈ [vS2, vS1, vA, vSq, vCc, vNd, vNc, vD, vDc]) {n : ℕ → ℕ}
    (hval : ∀ j, val v j = RealizedProgram.castElt (a := fA) ((n j : ℕ) : (I fA).K)) {j : ℕ}
    (hj : j < (program.value v).size) (hn : n j < 12289) :
    ia (program.srcEnv I x val c π) v j = n j :=
  ia_honest (cells hv).1 (cells hv).2.1 (cells hv).2.2 (hval j) hj hn

end Reading

/-! ## The converses of the readings -/

/-- **An integer equality at every coordinate is an integer `mod_q` with `q = 0`.** -/
theorem modZero_of_eq {rd : program.Valuation I} {d : ℕ} {l r : RealizedProgram.Expr} {real : RealizedProgram.ModRealization}
    (h : ∀ i < program.exprLen l, program.evalIntWith rd d l i = program.evalIntWith rd d r i) :
    program.HoldsWith rd (.mod d 0 l r real) := by
  intro i hi
  rw [Nat.cast_zero, zero_dvd_iff, sub_eq_zero]
  exact h i hi

/-- **A field `equal` of the domain holds** where it holds coordinatewise in its field (the
converse of `holdsAt_equalA`). -/
theorem holdsWith_equalA_of {rd : program.Valuation I} {lhs rhs : RealizedProgram.Expr} {t : RealizedProgram.Target}
    (h : ∀ i < program.exprLen lhs, program.evalE rd fA lhs i = program.evalE rd fA rhs i) :
    program.HoldsWith rd (.equal dA lhs rhs t) :=
  fun i hi => by
    have := h i hi
    unfold RealizedProgram.evalWith
    rw [FalconNorm.domainField (program := program)]
    exact this

/-- **A range membership of one record holds** where every coordinate is a natural below the
bound (the converse of `natBelow_of_mem`). -/
theorem mem_of_natBelow {rd : program.Valuation I} {n : ℕ} {r : RealizedProgram.Expr} {real : RealizedProgram.InRealization}
    (h : ∀ i < program.exprLen r, ∃ k < n, program.evalE rd fA r i = k) :
    program.HoldsWith rd (.mem dA [r] (.range n) real) := by
  intro i hi r' hr'
  rw [List.mem_singleton] at hr'
  subst hr'
  obtain ⟨k, hk, hkv⟩ := h i hi
  refine ⟨k, hk, ?_⟩
  unfold RealizedProgram.evalWith
  rw [FalconNorm.domainField (program := program)]
  exact hkv

/-- **A range membership of a value of the domain holds** where every coordinate is a natural
below the bound. -/
theorem range_leaf_holds {e : program.Env I} {p v n sz : ℕ} {real : RealizedProgram.InRealization}
    (hb : (program.predicate p).body = .mem dA [.leaf v] (.range n) real)
    (hsz : (program.value v).size = sz) (h : ∀ i < sz, ∃ k < n, rdA e v i = k) :
    program.HoldsAt e (program.predicate p).body := by
  rw [RealizedProgram.HoldsAt, hb]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_leaf, hsz] at hi
  exact h i hi

/-- `q − 1` is `−1` in the domain's field. -/
theorem q_neg_one : ((12288 : ℕ) : (I fA).K) = -1 := by
  have h0 : ((12289 : ℕ) : (I fA).K) = 0 := CharP.cast_eq_zero _ 12289
  push_cast at h0 ⊢
  linear_combination h0

section Columns

variable {e : program.Env I}

set_option maxRecDepth 2048

/-- **`norm.column0` holds** where its integer equation holds (the converse of `column0_int`). -/
theorem column0_holds (h : ∀ i < 1024,
    ia e vA (3 * i) * ia e vA (3 * i) = ia e vSq (6 * i) + 64 * ia e vCc (5 * i)) :
    program.HoldsAt e (program.predicate (pN + 2)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.col0 (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine modZero_of_eq fun i hi => ?_
  rw [RealizedProgram.exprLen_mul, exprLen_refA (by norm_disch), expr497, RealizedProgram.exprLen_reindex,
    FalconNorm.i54_size (program := program)] at hi
  simp (disch := norm_disch) only [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_scale_const, evalIntWith_refA, expr497, expr498, expr499,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf, FalconNorm.i54_entry (program := program) i hi,
    FalconNorm.i58_entry (program := program) i hi, FalconNorm.i59_entry (program := program) i hi]
  try erw [centered_64]
  try erw [centered_2]
  exact h i hi

theorem column1_holds (h : ∀ i < 1024,
    2 * (ia e vA (3 * i) * ia e vA (3 * i + 1)) + ia e vCc (5 * i) =
      ia e vSq (6 * i + 1) + 64 * ia e vCc (5 * i + 1)) :
    program.HoldsAt e (program.predicate (pN + 3)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.col1 (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine modZero_of_eq fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale, RealizedProgram.exprLen_mul, exprLen_refA (by norm_disch),
    expr497, RealizedProgram.exprLen_reindex, FalconNorm.i54_size (program := program)] at hi
  simp (disch := norm_disch) only [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_scale_const, evalIntWith_refA, expr497, expr500, expr501, expr502, expr503,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf, FalconNorm.i54_entry (program := program) i hi,
    FalconNorm.i55_entry (program := program) i hi, FalconNorm.i59_entry (program := program) i hi,
    FalconNorm.i60_entry (program := program) i hi, FalconNorm.i61_entry (program := program) i hi]
  try erw [centered_64]
  try erw [centered_2]
  exact h i hi

theorem column2_holds (h : ∀ i < 1024,
    2 * (ia e vA (3 * i) * topInt e i) + ia e vA (3 * i + 1) * ia e vA (3 * i + 1) +
        ia e vCc (5 * i + 1) = ia e vSq (6 * i + 2) + 64 * ia e vCc (5 * i + 2)) :
    program.HoldsAt e (program.predicate (pN + 4)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.col2 (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine modZero_of_eq fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale, RealizedProgram.exprLen_mul,
    exprLen_refA (by norm_disch), expr497, RealizedProgram.exprLen_reindex,
    FalconNorm.i54_size (program := program)] at hi
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const,
    RealizedProgram.evalIntWith_mul, evalIntWith_top e hi]
  simp (disch := norm_disch) only [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul,
    RealizedProgram.evalIntWith_scale_const, evalIntWith_refA, expr497, expr500, expr505, expr506, expr507,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_leaf, FalconNorm.i54_entry (program := program) i hi,
    FalconNorm.i55_entry (program := program) i hi, FalconNorm.i61_entry (program := program) i hi,
    FalconNorm.i62_entry (program := program) i hi, FalconNorm.i63_entry (program := program) i hi]
  try erw [centered_64]
  try erw [centered_2]
  exact h i hi

theorem column3_holds (h : ∀ i < 1024,
    2 * (ia e vA (3 * i + 1) * topInt e i) + ia e vCc (5 * i + 2) =
      ia e vSq (6 * i + 3) + 64 * ia e vCc (5 * i + 3)) :
    program.HoldsAt e (program.predicate (pN + 5)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.col3 (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine modZero_of_eq fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale, RealizedProgram.exprLen_mul,
    exprLen_refA (by norm_disch), expr500, RealizedProgram.exprLen_reindex,
    FalconNorm.i55_size (program := program)] at hi
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_mul,
    evalIntWith_top e hi]
  simp (disch := norm_disch) only [RealizedProgram.evalIntWith_add, evalIntWith_refA, expr500, expr508,
    expr509, expr510, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_reindex,
    RealizedProgram.evalIntWith_leaf, FalconNorm.i55_entry (program := program) i hi,
    FalconNorm.i63_entry (program := program) i hi, FalconNorm.i64_entry (program := program) i hi,
    FalconNorm.i65_entry (program := program) i hi]
  try erw [centered_64]
  try erw [centered_2]
  exact h i hi

theorem column4_holds (h : ∀ i < 1024,
    topInt e i * topInt e i + ia e vCc (5 * i + 3) =
      ia e vSq (6 * i + 4) + 64 * ia e vCc (5 * i + 4)) :
    program.HoldsAt e (program.predicate (pN + 6)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.col4 (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine modZero_of_eq fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_mul, exprLen_refA (by norm_disch), expr504,
    RealizedProgram.exprLen_reindex, FalconNorm.i56_size (program := program)] at hi
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_mul, evalIntWith_top e hi]
  simp (disch := norm_disch) only [RealizedProgram.evalIntWith_add, evalIntWith_refA, expr511, expr512,
    expr513, RealizedProgram.evalIntWith_scale_const, RealizedProgram.evalIntWith_reindex,
    RealizedProgram.evalIntWith_leaf, FalconNorm.i65_entry (program := program) i hi,
    FalconNorm.i66_entry (program := program) i hi, FalconNorm.i67_entry (program := program) i hi]
  try erw [centered_64]
  try erw [centered_2]
  exact h i hi

theorem column5_holds (h : ∀ i < 1024, ia e vCc (5 * i + 4) = ia e vSq (6 * i + 5)) :
    program.HoldsAt e (program.predicate (pN + 7)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.col5 (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine modZero_of_eq fun i hi => ?_
  rw [exprLen_refA (by norm_disch), expr514, RealizedProgram.exprLen_reindex,
    FalconNorm.i67_size (program := program)] at hi
  simp (disch := norm_disch) only [evalIntWith_refA, expr514, expr515, RealizedProgram.evalIntWith_reindex,
    RealizedProgram.evalIntWith_leaf, FalconNorm.i67_entry (program := program) i hi,
    FalconNorm.i68_entry (program := program) i hi]
  try erw [centered_64]
  try erw [centered_2]
  exact h i hi

end Columns

/-- **`norm.center` holds** where its field equation holds (the converse of `center_eq`). -/
theorem center_holds {e : program.Env I} (h : ∀ i < 1024,
    normInF e i * normInF e i =
      (rdA e vA (3 * i) + 64 * rdA e vA (3 * i + 1) + 4096 * topF e i) *
        (rdA e vA (3 * i) + 64 * rdA e vA (3 * i + 1) + 4096 * topF e i)) :
    program.HoldsAt e (program.predicate pN).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.center (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine holdsWith_equalA_of fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_mul, exprLen_refA (by norm_disch), expr492,
    RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex, FalconNorm.i52_size (program := program)] at hi
  rw [evalE_42, RealizedProgram.evalE_add, RealizedProgram.evalE_mul, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_mul, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_scale_const, evalE_492 e hi, evalE_495 e hi, evalE_refA _ _ (by norm_disch),
    expr493, evalE_refA _ _ (by norm_disch), expr494, RealizedProgram.evalE_reindex,
    RealizedProgram.evalE_reindex, FalconNorm.i54_entry (program := program) i hi,
    FalconNorm.i55_entry (program := program) i hi]
  try dsimp only
  try simp only [AField.decode_eq]
  change normInF e i * normInF e i + ((12288 : ℕ) : (I fA).K) *
    ((rdA e vA (3 * i) + ((64 : ℕ) : (I fA).K) * rdA e vA (3 * i + 1) +
      ((4096 : ℕ) : (I fA).K) * topF e i) *
    (rdA e vA (3 * i) + ((64 : ℕ) : (I fA).K) * rdA e vA (3 * i + 1) +
      ((4096 : ℕ) : (I fA).K) * topF e i)) = 0
  rw [q_neg_one]
  push_cast
  linear_combination h i hi

/-- **`norm.normalize` holds** where its integer equations hold (the converse of
`normalize_int`). -/
theorem normalize_holds {e : program.Env I} (h : ∀ b < 17, ∀ m < 6,
    prevInt e b m + batchSqInt e b m + ncInInt e b m =
      ia e vNd (6 * b + m) + 64 * ncOutInt e b m) :
    program.HoldsAt e (program.predicate (pN + 8)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.normalize (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine modZero_of_eq fun j hj => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, exprLen_refA (by norm_disch), expr516,
    RealizedProgram.exprLen_reindex, (FalconNorm.idx_sizes (program := program)).1] at hj
  obtain ⟨b, m, hb, hm, rfl⟩ : ∃ b m, b < 17 ∧ m < 6 ∧ j = 6 * b + m :=
    ⟨j / 6, j % 6, by omega, by omega, by omega⟩
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_apply,
    RealizedProgram.NamedOp.applyInt_batched_sum coefInt_zero coefInt_one _ _ hj, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_scale_const, centered_64, RealizedProgram.evalIntWith_leaf,
    evalIntWith_516 e hb hm, evalIntWith_518 e hb hm, evalIntWith_519 e hb hm]
  rw [Finset.sum_congr rfl fun s _ => evalIntWith_517 e hb hm s]
  exact h b hb m hm

/-- **`norm.complement` holds** where its integer equations hold (the converse of
`complement_int`). -/
theorem complement_holds {e : program.Env I} (h : ∀ m < 6,
    ia e vNd (96 + m) + ia e vD m + dcInInt e m =
      (NativeNorm.digit 34034726 m : ℤ) + 64 * ia e vDc m) :
    program.HoldsAt e (program.predicate (pN + 9)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.complement (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine modZero_of_eq fun m hm => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, exprLen_refA (by norm_disch), expr520,
    RealizedProgram.exprLen_reindex, (FalconNorm.idx_sizes (program := program)).2.2.2.2.1] at hm
  rw [RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add, RealizedProgram.evalIntWith_add,
    RealizedProgram.evalIntWith_scale_const, centered_64, RealizedProgram.evalIntWith_leaf,
    RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf, intOf_555 _ hm,
    evalIntWith_refA _ _ (by norm_disch), expr520, evalIntWith_refA _ _ (by norm_disch), expr521,
    RealizedProgram.evalIntWith_reindex, RealizedProgram.evalIntWith_reindex,
    FalconNorm.i73_entry (program := program) m hm, FalconNorm.i74_entry (program := program) m hm,
    RealizedProgram.evalIntWith_leaf]
  have := h m hm
  rw [dcInInt] at this
  by_cases hm0 : m = 0
  · rw [if_pos hm0] at this
    rw [if_pos hm0, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.2.1 _ le_rfl,
      if_neg (lt_irrefl _)]
    exact this
  · rw [if_neg hm0] at this
    rw [if_neg hm0, evalIntWith_concat41 e (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.2.1 _ (by omega),
      if_pos (by omega)]
    exact this

/-- **`encoding.b.boolean` holds** where the parity bits are bits (the converse of
`parity_bool`). -/
theorem parity_holds {e : program.Env I}
    (h : ∀ i < 512, parityF e i * parityF e i = parityF e i) :
    program.HoldsAt e (program.predicate (FalconNorm.pEncB program)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.encB (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine holdsWith_equalA_of fun i hi => ?_
  rw [RealizedProgram.exprLen_mul, exprLen_refA (FalconNorm.enc_le (program := program)).2.2, exprB,
    RealizedProgram.exprLen_add, exprLen_refA (FalconNorm.enc_le (program := program)).2.1, exprMid,
    RealizedProgram.exprLen_reindex, (FalconNorm.idx_enc (program := program)).2.2.2] at hi
  have h529 : program.evalE (program.reader e) fA (.ref (eBt program)) i = parityF e i := by
    rw [evalE_refA _ _ (FalconNorm.enc_le (program := program)).2.2, exprB, RealizedProgram.evalE_add,
      RealizedProgram.evalE_scale_const, evalE_refA _ _ (FalconNorm.enc_le (program := program)).2.1,
      exprMid, evalE_refA _ _ (FalconNorm.enc_le (program := program)).1, exprHigh,
      RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
      (FalconNorm.idx_enc (program := program)).2.1 i hi,
      (FalconNorm.idx_enc (program := program)).1 i hi, parityF, decode_A]
    have hq : ((12287 : ℕ) : (I fA).K) = -2 := by
      have h0 : ((12289 : ℕ) : (I fA).K) = 0 := CharP.cast_eq_zero _ 12289
      push_cast at h0 ⊢
      linear_combination h0
    rw [hq]
    unfold rdA
    ring
  rw [RealizedProgram.evalE_mul, h529]
  exact h i hi

/-! ## The honest facts of the input -/

namespace NormIn

variable {w : NormIn}

/-- An honest `s₂` coefficient's magnitude is below `2048`. -/
theorem mag_2048 (hw : w.Valid) {i : ℕ} (hi : 512 ≤ i) (h1 : i < 1024) : w.mag i < 2048 := by
  unfold mag
  rw [dif_pos h1]
  have := Falcon512.NativeAlgebraCircuit.Honest.honestVals_hs₂ w.h w.c hw.encoding ⟨i, h1⟩ hi
  have hb : Codec.magnitudeBound = 2048 := by decide
  rwa [hb] at this

/-- An honest `s₂` coefficient's magnitude fits two digits. -/
theorem mag_hi (hw : w.Valid) {i : ℕ} (hi : 512 ≤ i) (h1 : i < 1024) : w.mag i < 4096 :=
  lt_trans (mag_2048 hw hi h1) (by norm_num)

/-- **The honest norm bound.** -/
theorem global (hw : w.Valid) :
    ∑ i : Fin 1024, NativeNorm.honestMagNat w.vals i ^ 2 ≤ 34034726 :=
  Falcon512.NativeAlgebraCircuit.Honest.honestVals_hnorm w.h w.c w.s2 hw.algebra

theorem hi (hw : w.Valid) :
    ∀ i : Fin 1024, 512 ≤ (i : ℕ) → NativeNorm.honestMagNat w.vals i < 4096 := fun i h => by
  have := mag_hi hw h i.isLt
  unfold mag at this
  rwa [dif_pos i.isLt] at this

/-- The honest high parts fit the budget. -/
theorem highSum_le (hw : w.Valid) : ∑ i : Fin 512, w.mag (512 + i) / 128 ≤ 392 := by
  have := Falcon512.NativeAlgebraCircuit.Honest.honestVals_highSum w.h w.c hw.encoding
  have hr : Codec.lowRadix = 128 := by decide
  have hb : falcon512.encodingHighBudget = 392 := by decide
  rw [hr, hb] at this
  refine le_of_eq_of_le (Finset.sum_congr rfl fun i _ => ?_) this
  unfold mag
  rw [dif_pos (by omega)]
  rfl

theorem slack_le : w.slack ≤ 392 := by unfold slack; omega

/-- The masked digits of coefficient `i`. -/
theorem digit_eq_limbs {i l : ℕ} (hl : l ≠ 2 ∨ i < 512) (hl3 : l < 3) :
    w.digit i l = NativeNorm.honestLimbsNat (decide (512 ≤ i)) (w.mag i) ⟨l, hl3⟩ := by
  unfold digit NativeNorm.honestLimbsNat
  simp only [decide_eq_true_eq]
  split_ifs with h1 h2 h2 <;> first | rfl | omega

theorem col_eq {k : ℕ} (hk : k < 1024) (m : Fin 6) :
    NativeNorm.sixDigit (w.col k) m = NativeNorm.honestSqDigitAt w.vals k m := by
  unfold col mag NativeNorm.honestSqDigitAt NativeNorm.honestSqDigit
  rw [dif_pos hk, dif_pos hk]

theorem lastDigits_lt (hw : w.Valid) (k : Fin 6) : w.lastDigits k < 64 :=
  NativeNorm.honestBatchNdig_lt _ (global hw) (hi hw) (b := 16) le_rfl k

theorem nA_lt (hw : w.Valid) (j : ℕ) : w.nA j < 64 := by
  unfold nA digit
  split_ifs with h1
  · by_cases hj : j / 3 < 1024
    · have := mag_2048 hw h1.1 hj
      omega
    · unfold mag
      rw [dif_neg hj]
      norm_num
  · exact Nat.mod_lt _ (by norm_num)

theorem nSq_lt (hw : w.Valid) {j : ℕ} (hj : j < 6144) : w.nSq j < 64 := by
  unfold nSq
  rw [col_eq (by omega)]
  unfold NativeNorm.honestSqDigitAt
  rw [dif_pos (by omega)]
  exact NativeNorm.honestSqDigit_lt _ _ (hi hw _) _

theorem nCc_lt (j : ℕ) : w.nCc j < 189 :=
  NativeNorm.honestColprodNat_carry_lt_189 _ _ _

theorem nNd_lt (hw : w.Valid) {j : ℕ} (hj : j < 102) : w.nNd j < 64 :=
  NativeNorm.honestBatchNdig_lt _ (global hw) (hi hw) (by omega) _

theorem nNc_lt (hw : w.Valid) {j : ℕ} (hj : j < 85) : w.nNc j < 64 := by
  unfold nNc
  have := NativeNorm.sixCarry_le (col := NativeNorm.honestBatchColAt w.vals (j / 5 + 1)) (C := 63)
    (fun m => (NativeNorm.honestBatchColAt_facts _ (global hw) (hi hw) (j / 5 + 1)
      (by omega)).1 m) ⟨j % 5, by omega⟩
  omega

theorem nD_lt (j : ℕ) : w.nD j < 64 := by
  unfold nD
  split_ifs
  · exact Nat.mod_lt _ (by norm_num)
  · norm_num

theorem nDc_le (hw : w.Valid) (j : ℕ) : w.nDc j ≤ 1 := by
  unfold nDc
  split_ifs with h5
  · exact NativeNorm.honestDcol_sixCarry_le (lastDigits_lt hw) _
  · norm_num

end NormIn

/-! ## The honest predicates -/

section Honest

variable [FalconNormHonest program] {w : NormIn} {val x : program.Valuation I}
  {c : ∀ k, (program.layout I).Ch k} {π : (program.layout I).Pads}

set_option hygiene false in
local notation "env" => program.srcEnv I x val c π

/-- The norm's values as members of `cells`' list. -/
macro "norm_mem" : tactic => `(tactic| simp only [List.mem_cons, List.not_mem_nil, or_false, true_or, or_true])

theorem ia_A (hv : NormVals val w) {j : ℕ} (hj : j < 3072) (hw : w.Valid) :
    ia env vA j = w.nA j :=
  ia_of (by norm_mem) hv.a (by rw [(FalconNorm.sizes_A (program := program)).2.2.1]; exact hj)
    (lt_trans (NormIn.nA_lt hw j) (by norm_num))

theorem ia_Sq (hv : NormVals val w) {j : ℕ} (hj : j < 6144) (hw : w.Valid) :
    ia env vSq j = w.nSq j :=
  ia_of (by norm_mem) hv.sq (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.1]; exact hj)
    (lt_trans (NormIn.nSq_lt hw hj) (by norm_num))

theorem ia_Cc (hv : NormVals val w) {j : ℕ} (hj : j < 5120) :
    ia env vCc j = w.nCc j :=
  ia_of (by norm_mem) hv.cc (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.1]; exact hj)
    (lt_trans (NormIn.nCc_lt j) (by norm_num))

theorem ia_Nd (hv : NormVals val w) {j : ℕ} (hj : j < 102) (hw : w.Valid) :
    ia env vNd j = w.nNd j :=
  ia_of (by norm_mem) hv.nd (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.2.1]; exact hj)
    (lt_trans (NormIn.nNd_lt hw hj) (by norm_num))

theorem ia_Nc (hv : NormVals val w) {j : ℕ} (hj : j < 85) (hw : w.Valid) :
    ia env vNc j = w.nNc j :=
  ia_of (by norm_mem) hv.nc (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.1]; exact hj)
    (lt_trans (NormIn.nNc_lt hw hj) (by norm_num))

theorem ia_D (hv : NormVals val w) {j : ℕ} (hj : j < 6) :
    ia env vD j = w.nD j :=
  ia_of (by norm_mem) hv.D (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.1]; exact hj)
    (lt_trans (NormIn.nD_lt j) (by norm_num))

theorem ia_Dc (hv : NormVals val w) {j : ℕ} (hj : j < 6) (hw : w.Valid) :
    ia env vDc j = w.nDc j :=
  ia_of (by norm_mem) hv.Dc
    (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.2.1]; exact hj)
    (lt_of_le_of_lt (NormIn.nDc_le hw j) (by norm_num))

theorem rdA_A (hv : NormVals val w) {j : ℕ} (hj : j < 3072) : rdA env vA j = (w.nA j : (I fA).K) :=
  rdA_of (by norm_mem) hv.a (by rw [(FalconNorm.sizes_A (program := program)).2.2.1]; exact hj)

theorem rdA_Dc (hv : NormVals val w) {j : ℕ} (hj : j < 6) : rdA env vDc j = (w.nDc j : (I fA).K) :=
  rdA_of (by norm_mem) hv.Dc
    (by rw [(FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.2.1]; exact hj)

/-- **The honest square columns hold** at the source environment (`norm.column0` …
`norm.column5`): the honest chain of the masked digits' schoolbook columns
(`NativeNorm.sixDigit_sixCarry_eq`, `NativeNorm.honestColprodNat_apply`). -/
theorem columns_honest (hw : w.Valid) (hv : NormVals val w) :
    ∀ q ∈ [pN + 2, pN + 3, pN + 4, pN + 5, pN + 6, pN + 7],
      program.HoldsAt env (program.predicate q).body := by
  have hx : ∀ i < 1024, ∀ l (hl : l < 2), ia env vA (3 * i + l) =
      NativeNorm.honestLimbsNat (decide (512 ≤ i)) (w.mag i) ⟨l, by omega⟩ := by
    intro i hi l hl
    rw [ia_A hv (by omega) hw]
    unfold NormIn.nA
    rw [show (3 * i + l) / 3 = i by omega, show (3 * i + l) % 3 = l by omega,
      NormIn.digit_eq_limbs (Or.inl (by omega)) (by omega)]
  have htop : ∀ i < 1024, topInt env i =
      NativeNorm.honestLimbsNat (decide (512 ≤ i)) (w.mag i) 2 := by
    intro i hi
    unfold topInt
    split_ifs with h5
    · rw [ia_A hv (by omega) hw]
      unfold NormIn.nA
      rw [show (3 * i + 2) / 3 = i by omega, show (3 * i + 2) % 3 = 2 by omega,
        NormIn.digit_eq_limbs (Or.inr h5) (by omega)]
      rfl
    · unfold NativeNorm.honestLimbsNat
      simp only [decide_eq_true_eq, show 512 ≤ i by omega, true_and, Fin.val_two, ite_true]
      rfl
  have hsq : ∀ i < 1024, ∀ m (hm : m < 6), ia env vSq (6 * i + m) =
      NativeNorm.sixDigit (w.col i) ⟨m, hm⟩ := by
    intro i hi m hm
    rw [ia_Sq hv (by omega) hw]
    unfold NormIn.nSq
    have e1 : (⟨(6 * i + m) % 6, by omega⟩ : Fin 6) = ⟨m, hm⟩ := Fin.ext (by simp only; omega)
    rw [show (6 * i + m) / 6 = i by omega, e1]
  have hcc : ∀ i < 1024, ∀ m (hm : m < 5), ia env vCc (5 * i + m) =
      NativeNorm.sixCarry (w.col i) ⟨m, hm⟩ := by
    intro i hi m hm
    rw [ia_Cc hv (by omega)]
    unfold NormIn.nCc
    have e1 : (⟨(5 * i + m) % 5, by omega⟩ : Fin 5) = ⟨m, hm⟩ := Fin.ext (by simp only; omega)
    rw [show (5 * i + m) / 5 = i by omega, e1]
  have hchain : ∀ i, _ := fun i => NativeNorm.sixDigit_sixCarry_eq (w.col i)
  have happ : ∀ i, _ := fun i =>
    NativeNorm.honestColprodNat_apply (decide (512 ≤ i)) (w.mag i)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · refine column0_holds fun i hi => ?_
    have h0 := hx i hi 0 (by norm_num)
    rw [Nat.add_zero] at h0
    have h1 := hsq i hi 0 (by norm_num)
    have h2 := hcc i hi 0 (by norm_num)
    rw [Nat.add_zero] at h1 h2
    rw [h0, h1, h2]
    obtain ⟨e0, -⟩ := hchain i
    obtain ⟨a0, -⟩ := happ i
    unfold NormIn.col at e0
    rw [a0] at e0
    exact_mod_cast e0
  · refine column1_holds fun i hi => ?_
    have h0 := hx i hi 0 (by norm_num)
    rw [Nat.add_zero] at h0
    rw [h0, hx i hi 1 (by norm_num), hsq i hi 1 (by norm_num), hcc i hi 1 (by norm_num)]
    have h2 := hcc i hi 0 (by norm_num)
    rw [Nat.add_zero] at h2
    rw [h2]
    obtain ⟨-, e1, -⟩ := hchain i
    obtain ⟨-, a1, -⟩ := happ i
    unfold NormIn.col at e1
    rw [a1] at e1
    exact_mod_cast e1
  · refine column2_holds fun i hi => ?_
    have h0 := hx i hi 0 (by norm_num)
    rw [Nat.add_zero] at h0
    rw [h0, hx i hi 1 (by norm_num), htop i hi, hsq i hi 2 (by norm_num), hcc i hi 1 (by norm_num),
      hcc i hi 2 (by norm_num)]
    obtain ⟨-, -, e2, -⟩ := hchain i
    obtain ⟨-, -, a2, -⟩ := happ i
    unfold NormIn.col at e2
    rw [a2] at e2
    exact_mod_cast e2
  · refine column3_holds fun i hi => ?_
    rw [hx i hi 1 (by norm_num), htop i hi, hsq i hi 3 (by norm_num), hcc i hi 2 (by norm_num),
      hcc i hi 3 (by norm_num)]
    obtain ⟨-, -, -, e3, -⟩ := hchain i
    obtain ⟨-, -, -, a3, -⟩ := happ i
    unfold NormIn.col at e3
    rw [a3] at e3
    exact_mod_cast e3
  · refine column4_holds fun i hi => ?_
    rw [htop i hi, hsq i hi 4 (by norm_num), hcc i hi 3 (by norm_num), hcc i hi 4 (by norm_num)]
    obtain ⟨-, -, -, -, e4, -⟩ := hchain i
    obtain ⟨-, -, -, -, a4, -⟩ := happ i
    unfold NormIn.col at e4
    rw [a4] at e4
    exact_mod_cast e4
  · refine column5_holds fun i hi => ?_
    rw [hsq i hi 5 (by norm_num), hcc i hi 4 (by norm_num)]
    obtain ⟨-, -, -, -, -, e5⟩ := hchain i
    obtain ⟨-, -, -, -, -, a5⟩ := happ i
    unfold NormIn.col at e5
    rw [a5, Nat.zero_add] at e5
    exact_mod_cast e5

/-- The honest residues read as the norm's inputs. -/
theorem normInF_honest (hv : NormVals val w) {i : ℕ} (hi : i < 1024) :
    normInF env i = (w.vals ⟨i, hi⟩ : (I fA).K) := by
  obtain ⟨hs2, hs1, -⟩ := FalconNorm.sizes_A (program := program)
  unfold normInF
  split_ifs with h5
  · rw [rdA_of (by norm_mem) hv.s1 (by rw [hs1]; exact h5)]
    unfold NormIn.nS1
    simp only [h5, ↓reduceDIte]
    unfold NormIn.vals Falcon512.NativeAlgebraCircuit.Honest.honestVals
    simp only [show (i : ℕ) < falcon512.n from h5, ↓reduceDIte]
  · rw [rdA_of (by norm_mem) hv.s2 (by rw [hs2]; omega)]
    unfold NormIn.nS2
    simp only [show i - 512 < 512 by omega, ↓reduceDIte]
    unfold NormIn.vals Falcon512.NativeAlgebraCircuit.Honest.honestVals
    simp only [show ¬ ((i : ℕ) < falcon512.n) from h5, ↓reduceDIte]
    rfl

/-- **`norm.center` holds on the honest values**: the magnitude digits reconstruct the centered
magnitude, whose square is the residue's (`Centered.cast_eq_centeredRepr_natAbs`). -/
theorem center_honest (hw : w.Valid) (hv : NormVals val w) :
    program.HoldsAt env (program.predicate pN).body := by
  refine center_holds fun i hi => ?_
  have hd : ∀ l (hl : l < 3), (l ≠ 2 ∨ i < 512) → rdA env vA (3 * i + l) =
      (NativeNorm.honestLimbsNat (decide (512 ≤ i)) (w.mag i) ⟨l, hl⟩ : (I fA).K) := by
    intro l hl hl2
    rw [rdA_A hv (by omega)]
    unfold NormIn.nA
    rw [show (3 * i + l) / 3 = i by omega, show (3 * i + l) % 3 = l by omega,
      NormIn.digit_eq_limbs hl2 hl]
  have ht : topF env i =
      (NativeNorm.honestLimbsNat (decide (512 ≤ i)) (w.mag i) 2 : (I fA).K) := by
    unfold topF
    split_ifs with h5
    · exact hd 2 (by norm_num) (Or.inr h5)
    · unfold NativeNorm.honestLimbsNat
      simp only [decide_eq_true_eq, show 512 ≤ i by omega, true_and, Fin.val_two, ite_true,
        Nat.cast_zero]
  have hsum := NativeNorm.honestLimbsNat_sum (hi := decide (512 ≤ i)) (magNat := w.mag i)
    (fun hh => NormIn.mag_hi hw (of_decide_eq_true hh) hi) (by
      unfold NormIn.mag; rw [dif_pos hi]; exact NativeNorm.honestMagNat_lt3 _ _)
  have hmag : rdA env vA (3 * i) + 64 * rdA env vA (3 * i + 1) + 4096 * topF env i =
      (w.mag i : (I fA).K) := by
    have h0 := hd 0 (by norm_num) (Or.inl (by norm_num))
    rw [Nat.add_zero] at h0
    rw [h0, hd 1 (by norm_num) (Or.inl (by norm_num)), ht]
    conv_rhs => rw [← hsum]
    simp only [Fin.sum_univ_three]
    push_cast
    norm_num
    ring
  rw [hmag, normInF_honest hv hi]
  have := Centered.cast_eq_centeredRepr_natAbs (K := (I fA).K) (q := 12289) (w.vals ⟨i, hi⟩)
  have hm : w.mag i = (LatticeCrypto.centeredRepr (w.vals ⟨i, hi⟩ : ZMod 12289)).natAbs := by
    unfold NormIn.mag NativeNorm.honestMagNat
    rw [dif_pos hi]
  rw [hm]
  rcases this with h1 | h1 <;> rw [h1] <;> ring

theorem ia_Nd_batch (hw : w.Valid) (hv : NormVals val w) {b m : ℕ} (hb : b < 17) (hm : m < 6) :
    ia env vNd (6 * b + m) = NativeNorm.honestBatchNdig w.vals b ⟨m, hm⟩ := by
  rw [ia_Nd hv (by omega) hw]
  unfold NormIn.nNd
  have e1 : (⟨(6 * b + m) % 6, by omega⟩ : Fin 6) = ⟨m, hm⟩ := Fin.ext (by simp only; omega)
  rw [show (6 * b + m) / 6 = b by omega, e1]

theorem ia_Nc_batch (hw : w.Valid) (hv : NormVals val w) {b m : ℕ} (hb : b < 17) (hm : m < 5) :
    ia env vNc (5 * b + m) =
      NativeNorm.sixCarry (NativeNorm.honestBatchColAt w.vals (b + 1)) ⟨m, hm⟩ := by
  rw [ia_Nc hv (by omega) hw]
  unfold NormIn.nNc
  have e1 : (⟨(5 * b + m) % 5, by omega⟩ : Fin 5) = ⟨m, hm⟩ := Fin.ext (by simp only; omega)
  rw [show (5 * b + m) / 5 = b by omega, e1]

theorem ia_Sq_at (hw : w.Valid) (hv : NormVals val w) {k m : ℕ} (hk : k < 1024) (hm : m < 6) :
    ia env vSq (6 * k + m) = NativeNorm.honestSqDigitAt w.vals k ⟨m, hm⟩ := by
  rw [ia_Sq hv (by omega) hw]
  unfold NormIn.nSq
  have e1 : (⟨(6 * k + m) % 6, by omega⟩ : Fin 6) = ⟨m, hm⟩ := Fin.ext (by simp only; omega)
  rw [show (6 * k + m) / 6 = k by omega, e1, NormIn.col_eq hk]

/-- **`norm.normalize` holds on the honest values**: each batch's column is the previous batch's
digits plus its coefficients' square digits (`NativeNorm.honestBatchColAt_succ`), normalized by
the honest chain. -/
theorem normalize_honest (hw : w.Valid) (hv : NormVals val w) :
    program.HoldsAt env (program.predicate (pN + 8)).body := by
  refine normalize_holds fun b hb m hm => ?_
  set col := NativeNorm.honestBatchColAt w.vals (b + 1) with hcol
  have hprev : prevInt env b m =
      NativeNorm.sixDigit (NativeNorm.honestBatchColAt w.vals b) ⟨m, hm⟩ := by
    unfold prevInt
    split_ifs with h0
    · subst h0
      unfold NativeNorm.sixDigit NativeNorm.honestBatchColAt
      simp
    · rw [ia_Nd_batch hw hv (by omega) hm]
      unfold NativeNorm.honestBatchNdig
      rw [show b - 1 + 1 = b by omega]
  have hsq : batchSqInt env b m =
      ∑ s : Fin 63, (NativeNorm.honestSqDigitAt w.vals (63 * b + s) ⟨m, hm⟩ : ℤ) := by
    unfold batchSqInt
    refine Finset.sum_congr rfl fun s _ => ?_
    split_ifs with h1
    · rw [ia_Sq_at hw hv h1 hm]
    · unfold NativeNorm.honestSqDigitAt
      rw [dif_neg h1, Nat.cast_zero]
  have hcolm : (col ⟨m, hm⟩ : ℤ) = prevInt env b m + batchSqInt env b m := by
    rw [hprev, hsq, hcol, NativeNorm.honestBatchColAt_succ,
      NativeNorm.sum_batch_honestSqDigitAt _ hb]
    push_cast
    rfl
  rw [← hcolm, ia_Nd_batch hw hv hb hm]
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := NativeNorm.sixDigit_sixCarry_eq col
  have hnd : NativeNorm.honestBatchNdig w.vals b ⟨m, hm⟩ = NativeNorm.sixDigit col ⟨m, hm⟩ := rfl
  rw [hnd]
  unfold ncInInt ncOutInt
  interval_cases m
  · have h0 := ia_Nc_batch (x := x) (c := c) (π := π) hw hv hb (m := 0) (by norm_num)
    rw [Nat.add_zero] at h0
    rw [if_pos rfl, if_pos (by norm_num), Nat.add_zero, h0, add_zero]
    exact_mod_cast e0
  · rw [if_neg (by norm_num), if_pos (by norm_num), show 5 * b + 1 - 1 = 5 * b + 0 by omega,
      ia_Nc_batch hw hv hb (by norm_num), ia_Nc_batch hw hv hb (by norm_num)]
    exact_mod_cast e1
  · rw [if_neg (by norm_num), if_pos (by norm_num), show 5 * b + 2 - 1 = 5 * b + 1 by omega,
      ia_Nc_batch hw hv hb (by norm_num), ia_Nc_batch hw hv hb (by norm_num)]
    exact_mod_cast e2
  · rw [if_neg (by norm_num), if_pos (by norm_num), show 5 * b + 3 - 1 = 5 * b + 2 by omega,
      ia_Nc_batch hw hv hb (by norm_num), ia_Nc_batch hw hv hb (by norm_num)]
    exact_mod_cast e3
  · rw [if_neg (by norm_num), if_pos (by norm_num), show 5 * b + 4 - 1 = 5 * b + 3 by omega,
      ia_Nc_batch hw hv hb (by norm_num), ia_Nc_batch hw hv hb (by norm_num)]
    exact_mod_cast e4
  · rw [if_neg (by norm_num), if_neg (by norm_num), show 5 * b + 5 - 1 = 5 * b + 4 by omega,
      ia_Nc_batch hw hv hb (by norm_num), mul_zero, add_zero]
    exact_mod_cast e5

/-- **`norm.complement` holds on the honest values**: the honest complement's chain has the
bound's digits (`NativeNorm.honestDcol_sixDigit`). -/
theorem complement_honest (hw : w.Valid) (hv : NormVals val w) :
    program.HoldsAt env (program.predicate (pN + 9)).body := by
  set S := w.lastDigits with hSdef
  have hS : ∀ k, S k < 64 := NormIn.lastDigits_lt hw
  have hSle := NativeNorm.honestBatchNdig_last_sum _ (NormIn.global hw) (NormIn.hi hw)
  refine complement_holds fun m hm => ?_
  have hS96 : ia env vNd (96 + m) = (S ⟨m, hm⟩ : ℤ) :=
    ia_Nd_batch hw hv (b := 16) (by norm_num) hm
  have hDc : ∀ m' < 6, ia env vDc m' = (if hm5 : m' < 5 then
      NativeNorm.sixCarry (NativeNorm.honestDcol S) ⟨m', hm5⟩ else 0 : ℕ) := fun m' hm' => by
    rw [ia_Dc hv hm' hw]
    rfl
  have hdig := NativeNorm.honestDcol_sixDigit hS hSle
  obtain ⟨e0, e1, e2, e3, e4, e5⟩ := NativeNorm.sixDigit_sixCarry_eq (NativeNorm.honestDcol S)
  rw [hS96, ia_D hv hm, hDc m hm]
  unfold NormIn.nD dcInInt
  rw [if_pos hm]
  have hcol : ∀ k : Fin 6, NativeNorm.honestDcol S k = S k +
      (34034726 - ∑ j : Fin 6, S j * 64 ^ (j : ℕ)) / 64 ^ (k : ℕ) % 64 := fun k => rfl
  interval_cases m
  · rw [if_pos rfl]
    rw [hcol, hdig] at e0
    simp only [show (0 : ℕ) < 5 by norm_num, ↓reduceDIte]
    exact_mod_cast (by simpa using e0)
  · rw [if_neg (by norm_num), hDc _ (by norm_num)]
    rw [hcol, hdig] at e1
    simp only [show (1 : ℕ) < 5 by norm_num, show (1 - 1 : ℕ) < 5 by norm_num, ↓reduceDIte]
    exact_mod_cast e1
  · rw [if_neg (by norm_num), hDc _ (by norm_num)]
    rw [hcol, hdig] at e2
    simp only [show (2 : ℕ) < 5 by norm_num, show (2 - 1 : ℕ) < 5 by norm_num, ↓reduceDIte]
    exact_mod_cast e2
  · rw [if_neg (by norm_num), hDc _ (by norm_num)]
    rw [hcol, hdig] at e3
    simp only [show (3 : ℕ) < 5 by norm_num, show (3 - 1 : ℕ) < 5 by norm_num, ↓reduceDIte]
    exact_mod_cast e3
  · rw [if_neg (by norm_num), hDc _ (by norm_num)]
    rw [hcol, hdig] at e4
    simp only [show (4 : ℕ) < 5 by norm_num, show (4 - 1 : ℕ) < 5 by norm_num, ↓reduceDIte]
    exact_mod_cast e4
  · rw [if_neg (by norm_num), hDc _ (by norm_num)]
    rw [hcol, hdig] at e5
    simp only [show ¬ (5 : ℕ) < 5 by norm_num, show (5 - 1 : ℕ) < 5 by norm_num, ↓reduceDIte]
    change ((S 5 : ℕ) : ℤ) + (((34034726 - ∑ k : Fin 6, S k * 64 ^ (k : ℕ)) /
      64 ^ ((5 : Fin 6) : ℕ) % 64 : ℕ) : ℤ) +
        ((NativeNorm.sixCarry (NativeNorm.honestDcol S) 4 : ℕ) : ℤ) =
      ((NativeNorm.digit 34034726 ((5 : Fin 6) : ℕ) : ℕ) : ℤ) + 64 * ((0 : ℕ) : ℤ)
    rw [Nat.cast_zero, mul_zero, add_zero]
    exact_mod_cast e5

/-- **`norm.top` holds**: the honest top complement carry is `0`. -/
theorem top_honest (hv : NormVals val w) :
    program.HoldsAt env (program.predicate (pN + 1)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.top (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine holdsWith_equalA_of fun i hi => ?_
  rw [exprLen_refA (by norm_disch), expr496, RealizedProgram.exprLen_reindex,
    (FalconNorm.idx_sizes (program := program)).2.2.2.2.2.2.2.2] at hi
  obtain rfl : i = 0 := by omega
  change program.evalE _ fA (.ref (eN + 4)) 0 = program.evalE _ fA (.leaf vZ1) 0
  rw [evalE_refA _ _ (by norm_disch), expr496, RealizedProgram.evalE_reindex,
    FalconNorm.i57_entry (program := program), evalE_41]
  change rdA _ vDc 5 = 0
  rw [rdA_Dc hv (by norm_num)]
  unfold NormIn.nDc
  simp

/-- **The type check of `norm.Dc` holds**: the honest complement carries are bits. -/
theorem dcBool_honest (hw : w.Valid) (hv : NormVals val w) :
    program.HoldsAt env (program.predicate (FalconNorm.pDc program)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.dcBool (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine holdsWith_equalA_of fun m hm => ?_
  rw [RealizedProgram.exprLen_mul, RealizedProgram.exprLen_leaf,
    (FalconNorm.sizes_A (program := program)).2.2.2.2.2.2.2.2.1] at hm
  change rdA env vDc m * rdA env vDc m = rdA env vDc m
  rw [rdA_Dc hv hm]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (NormIn.nDc_le hw m) with h0 | h1
  · rw [h0, Nat.cast_zero, mul_zero]
  · rw [h1, Nat.cast_one, mul_one]

/-- **`encoding.b.boolean` holds on the honest values**: the middle digit less twice the high part
of an `s₂` magnitude below `4096` is its bit `6`. -/
theorem parity_honest (hw : w.Valid) (hv : NormVals val w) :
    program.HoldsAt env (program.predicate (FalconNorm.pEncB program)).body := by
  refine parity_holds fun i hi => ?_
  have hp : parityF env i = ((w.mag (512 + i) / 64 % 2 : ℕ) : (I fA).K) := by
    unfold parityF
    rw [rdA_A hv (by omega), rdA_A hv (by omega)]
    unfold NormIn.nA NormIn.digit
    simp only [show (3 * (512 + i) + 1) / 3 = 512 + i by omega,
      show (3 * (512 + i) + 1) % 3 = 1 by omega, show (3 * (512 + i) + 2) / 3 = 512 + i by omega,
      show (3 * (512 + i) + 2) % 3 = 2 by omega, show (1 : ℕ) ≠ 2 by norm_num, and_false,
      and_true, show 512 ≤ 512 + i by omega, pow_one, ite_false, ite_true]
    have : w.mag (512 + i) / 64 % 64 = 2 * (w.mag (512 + i) / 128) +
        w.mag (512 + i) / 64 % 2 := by
      have := NormIn.mag_hi hw (i := 512 + i) (by omega) (by omega)
      omega
    rw [this]
    push_cast
    ring
  rw [hp]
  rcases Nat.mod_two_eq_zero_or_one (w.mag (512 + i) / 64) with h0 | h1
  · rw [h0]; simp
  · rw [h1]; simp

theorem highF_honest (hv : NormVals val w) {i : ℕ} (hi : i < 512) :
    highF env i = (w.mag (512 + i) / 128 : ℕ) := by
  unfold highF
  rw [rdA_A hv (by omega)]
  unfold NormIn.nA NormIn.digit
  simp only [show (3 * (512 + i) + 2) / 3 = 512 + i by omega,
    show (3 * (512 + i) + 2) % 3 = 2 by omega, show 512 ≤ 512 + i by omega, and_self, ite_true]

/-- **`encoding.high` holds**: every honest `s₂` high part is below `16`. -/
theorem high_honest (hw : w.Valid) (hv : NormVals val w) :
    program.HoldsAt env (program.predicate (FalconNorm.pHigh program)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.high (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine mem_of_natBelow fun i hi => ?_
  rw [exprLen_526 (program := program)] at hi
  refine ⟨w.mag (512 + i) / 128, ?_, ?_⟩
  · have := NormIn.mag_2048 hw (i := 512 + i) (by omega) (by omega)
    omega
  · rw [evalE_526 _ hi, highF_honest hv hi]

/-- The slack's expression reads the honest slack. -/
theorem evalE_slack_honest (hw : w.Valid) (hv : NormVals val w) :
    program.evalE (program.reader env) fA (.add (.scale (.const 12288)
      (.apply (.sum 512) (.ref (eHi program)))) (.leaf vOff)) 0 = (w.slack : (I fA).K) := by
  obtain ⟨-, -, -, -, -, -, coff, foff, eoff⟩ := FalconNorm.consts_A (program := program)
  rw [RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, RealizedProgram.evalE_apply_sum,
    RealizedProgram.evalE_leaf_of_isConstant _ coff, RealizedProgram.constRead_of_valueField foff, eoff]
  rw [Finset.sum_congr rfl fun t _ => by rw [Nat.zero_mul, Nat.zero_add, evalE_526 _ t.isLt,
    highF_honest hv t.isLt]]
  try dsimp only
  try simp only [AField.decode_eq]
  change ((12288 : ℕ) : (I fA).K) * _ + ((392 : ℕ) : (I fA).K) = _
  rw [q_neg_one]
  unfold NormIn.slack
  rw [Nat.cast_sub (NormIn.highSum_le hw)]
  push_cast
  ring_nf

/-- **`encoding.slack` holds**: the honest slack is a natural below `393`. -/
theorem slack_honest (hw : w.Valid) (hv : NormVals val w) :
    program.HoldsAt env (program.predicate (FalconNorm.pSlack program)).body := by
  obtain ⟨_, hpb⟩ := FalconNorm.slack (program := program)
  rw [RealizedProgram.HoldsAt, hpb]
  refine mem_of_natBelow fun i hi => ?_
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale, RealizedProgram.exprLen_apply,
    exprLen_526 (program := program)] at hi
  obtain rfl : i = 0 := by simpa [RealizedProgram.NamedOp.rows, RealizedProgram.NamedOp.cols] using hi
  exact ⟨w.slack, by have := NormIn.slack_le (w := w); omega, evalE_slack_honest hw hv⟩

/-- **The norm's digit ranges hold** on the honest values (`norm.a` … `norm.D`). -/
theorem ranges_honest (hw : w.Valid) (hv : NormVals val w) :
    ∀ q ∈ [FalconNorm.pRange program, FalconNorm.pRange program + 1,
      FalconNorm.pRange program + 2, FalconNorm.pRange program + 3,
      FalconNorm.pRange program + 4, FalconNorm.pRange program + 5],
      program.HoldsAt env (program.predicate q).body := by
  obtain ⟨r3, b3⟩ := FalconNorm.rangeA (program := program)
  obtain ⟨r4, b4⟩ := FalconNorm.rangeSq (program := program)
  obtain ⟨r5, b5⟩ := FalconNorm.rangeCc (program := program)
  obtain ⟨r6, b6⟩ := FalconNorm.rangeNd (program := program)
  obtain ⟨r7, b7⟩ := FalconNorm.rangeNc (program := program)
  obtain ⟨r8, b8⟩ := FalconNorm.rangeD (program := program)
  obtain ⟨-, -, s548, s549, s550, s551, s552, s553, -⟩ := FalconNorm.sizes_A (program := program)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · exact range_leaf_holds b3 s548 fun j hj =>
      ⟨_, NormIn.nA_lt hw j, rdA_of (by norm_mem) hv.a (by rw [s548]; exact hj)⟩
  · exact range_leaf_holds b4 s549 fun j hj =>
      ⟨_, NormIn.nSq_lt hw hj, rdA_of (by norm_mem) hv.sq (by rw [s549]; exact hj)⟩
  · exact range_leaf_holds b5 s550 fun j hj =>
      ⟨_, NormIn.nCc_lt j, rdA_of (by norm_mem) hv.cc (by rw [s550]; exact hj)⟩
  · exact range_leaf_holds b6 s551 fun j hj =>
      ⟨_, NormIn.nNd_lt hw hj, rdA_of (by norm_mem) hv.nd (by rw [s551]; exact hj)⟩
  · exact range_leaf_holds b7 s552 fun j hj =>
      ⟨_, NormIn.nNc_lt hw hj, rdA_of (by norm_mem) hv.nc (by rw [s552]; exact hj)⟩
  · exact range_leaf_holds b8 s553 fun j hj =>
      ⟨_, NormIn.nD_lt j, rdA_of (by norm_mem) hv.D (by rw [s553]; exact hj)⟩

/-- **The norm's and the encoding's source predicates hold on the honest values** (the norm's
`10`, the type check of `norm.Dc`, the parity bits, the ranges, the high parts and the slack). -/
theorem preds_honest (hw : w.Valid) (hv : NormVals val w) :
    ∀ q ∈ [pN, pN + 1, pN + 2, pN + 3, pN + 4, pN + 5, pN + 6, pN + 7, pN + 8, pN + 9,
      FalconNorm.pDc program, FalconNorm.pEncB program, FalconNorm.pRange program,
      FalconNorm.pRange program + 1, FalconNorm.pRange program + 2, FalconNorm.pRange program + 3,
      FalconNorm.pRange program + 4, FalconNorm.pRange program + 5, FalconNorm.pHigh program,
      FalconNorm.pSlack program],
      program.HoldsAt env (program.predicate q).body := by
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  have hc := columns_honest (x := x) (c := c) (π := π) hw hv
  have hr := ranges_honest (x := x) (c := c) (π := π) hw hv
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  · exact center_honest hw hv
  · exact top_honest hv
  · exact hc _ (by simp)
  · exact hc _ (by simp)
  · exact hc _ (by simp)
  · exact hc _ (by simp)
  · exact hc _ (by simp)
  · exact hc _ (by simp)
  · exact normalize_honest hw hv
  · exact complement_honest hw hv
  · exact dcBool_honest hw hv
  · exact parity_honest hw hv
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact hr _ (by simp)
  · exact high_honest hw hv
  · exact slack_honest hw hv

end Honest

end GordieHowe.Falcon512.Norm
