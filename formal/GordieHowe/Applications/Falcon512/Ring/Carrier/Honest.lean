-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Ring.Honest
public import GordieHowe.Applications.Falcon512.Ring.Carrier.Frontend

@[expose] public section

/-!
# GordieHowe: the honest execution of a Falcon ring carrier

The execution of the source program of the Falcon ring carriers (`Falcon512.Ring.Carrier.ROMParams`,
`Falcon512.Ring.Carrier.QROMParams`), the generic Falcon ring execution (`GordieHowe.Falcon512.Ring.sourceExecutionOf`) at the
carriers' roles (`carrierRoles`), generic in the program (`FalconCarrierBase`,
`FalconCarrierHonest`: the realization's predicates and the bound values, decided per program) and
its Goldilocks field (`GordieHowe.Falcon512.EField`):

* **The honest naturals** (`Carrier`, at the signature `GordieHowe.Falcon512.Norm.NormIn`): the canonical `s1` and
  `s2`, their centered magnitudes (`honestMagnitude_centering`), the low parts `mag2 mod 128`, the
  quotient `(bias + c − h s2 − s1)/q` of the biased signature equation (an integer identity,
  `GordieHowe.Falcon512.Emulated.Rows.residual_add_bias_eq_honestQuotient_of_nonneg`, below `2^33`), the encoding
  budget `50176 − Σ 128 ⌊mag2/128⌋` and the squared norm `Σ mag1² + Σ mag2²`; the digits of the
  values bound to their digits (base `2048`, the magnitudes of `s1` base `128`).
* **The source predicates** (`source_holds_carrier`): the membership and the index bits' check
  (generic), the signature equation (`c + bias − s1 − q · quot = h · s2` in the field, through the
  transform at `ψ`), the magnitudes, the norm, the ranges and `encoding.high2`; and the execution
  (`GordieHowe.Falcon512.Ring.carrierSourceExecution`).
-/

namespace GordieHowe.Falcon512.Ring

open GordieHowe.Ring Native RealizedProgram
open Norm (NormIn)

set_option linter.unusedSectionVars false

/-! ## The honest naturals -/

namespace Carrier

variable {w : NormIn}

theorem nS1_lt (j : ℕ) : w.nS1 j < 12289 := by
  unfold NormIn.nS1
  split
  · exact ZMod.val_lt _
  · norm_num

theorem nS2_lt (j : ℕ) : w.nS2 j < 12289 := by
  unfold NormIn.nS2
  split
  · exact ZMod.val_lt _
  · norm_num

/-- The honest residues below `512` are `s1`'s. -/
theorem vals_s1 {j : ℕ} (hj : j < 512) : w.vals ⟨j, by omega⟩ = w.nS1 j := by
  unfold NormIn.nS1
  rw [dif_pos hj]
  exact dif_pos (show j < falcon512.n from hj)

/-- The honest residues from `512` are `s2`'s. -/
theorem vals_s2 {j : ℕ} (hj : j < 512) : w.vals ⟨512 + j, by omega⟩ = w.nS2 j := by
  unfold NormIn.nS2
  rw [dif_pos hj]
  have hn : falcon512.n = 512 := rfl
  show (if h : 512 + j < falcon512.n then _ else _) = _
  rw [dif_neg (by rw [hn]; omega)]
  exact congrArg _ (Fin.ext (show 512 + j - falcon512.n = j by rw [hn]; omega))

/-- **The magnitude of `s1`'s coefficient** is the centered magnitude of the canonical residue. -/
theorem mag1_eq {j : ℕ} (hj : j < 512) :
    mag1 w j = (LatticeCrypto.centeredRepr ((w.nS1 j : ℕ) : ZMod 12289)).natAbs := by
  unfold mag1 NormIn.mag
  rw [if_pos hj, dif_pos (by omega)]
  unfold NativeNorm.honestMagNat
  rw [vals_s1 hj]

/-- **The magnitude of `s2`'s coefficient** is the centered magnitude of the canonical residue. -/
theorem mag2_eq {j : ℕ} (hj : j < 512) :
    mag2 w j = (LatticeCrypto.centeredRepr ((w.nS2 j : ℕ) : ZMod 12289)).natAbs := by
  unfold mag2 NormIn.mag
  rw [if_pos hj, dif_pos (by omega)]
  unfold NativeNorm.honestMagNat
  rw [vals_s2 hj]

/-- **The centering equation of `s1`**: `(mag1 − s1)(mag1 − (q − s1)) = 0`. -/
theorem centering1 {K : Type*} [Field K] {j : ℕ} (hj : j < 512) :
    ((mag1 w j : K) - (w.nS1 j : K)) * ((mag1 w j : K) - ((12289 : ℕ) - (w.nS1 j : K))) = 0 := by
  have h := EmulatedNorm.honestMagnitude_centering (F := K) (q := 12289) ((w.nS1 j : ℕ) : ZMod 12289)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (nS1_lt j)] at h
  unfold EmulatedNorm.honestMagnitude at h
  rw [mag1_eq hj]
  exact h

/-- **The centering equation of `s2`**: `(mag2 − s2)(mag2 − (q − s2)) = 0`. -/
theorem centering2 {K : Type*} [Field K] {j : ℕ} (hj : j < 512) :
    ((mag2 w j : K) - (w.nS2 j : K)) * ((mag2 w j : K) - ((12289 : ℕ) - (w.nS2 j : K))) = 0 := by
  have h := EmulatedNorm.honestMagnitude_centering (F := K) (q := 12289) ((w.nS2 j : ℕ) : ZMod 12289)
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt (nS2_lt j)] at h
  unfold EmulatedNorm.honestMagnitude at h
  rw [mag2_eq hj]
  exact h

/-- The magnitudes of `s1` are at most `6144`. -/
theorem mag1_le (j : ℕ) : mag1 w j ≤ 6144 := by
  by_cases hj : j < 512
  · rw [mag1_eq hj]
    exact LatticeCrypto.centeredRepr_abs_le _
  · unfold mag1
    rw [if_neg hj]
    norm_num

/-- The magnitudes of `s2` are below `2048`. -/
theorem mag2_lt (hw : w.Valid) (j : ℕ) : mag2 w j < 2048 := by
  unfold mag2
  split_ifs with hj
  · exact NormIn.mag_2048 hw (by omega) (by omega)
  · norm_num

/-- **The high parts of `s2` fit the budget**: `Σ (mag2 − mag2 mod 128) ≤ 50176`. -/
theorem highSum_le (hw : w.Valid) : ∑ i : Fin 512, (mag2 w i - mag2 w i % 128) ≤ 50176 := by
  have h := NormIn.highSum_le hw
  have e : ∀ i : Fin 512, mag2 w i - mag2 w i % 128 = 128 * (w.mag (512 + i) / 128) := fun i => by
    unfold mag2
    rw [if_pos i.isLt]
    omega
  rw [Finset.sum_congr rfl fun i _ => e i, ← Finset.mul_sum]
  omega

/-- **The budget and the high parts** sum to `50176`. -/
theorem budget_add (hw : w.Valid) : budget w + ∑ i : Fin 512, (mag2 w i - mag2 w i % 128) = 50176 := by
  unfold budget
  have := highSum_le hw
  omega

theorem budget_le : budget w ≤ 50176 := by
  unfold budget
  omega

/-- **The squared norm is within Falcon's bound** `34034726`. -/
theorem squares_le (hw : w.Valid) : squares w ≤ 34034726 := by
  have h := NormIn.global hw
  have hmag : ∑ i : Fin 1024, NativeNorm.honestMagNat w.vals i ^ 2 = ∑ i : Fin 1024, w.mag i ^ 2 :=
    Finset.sum_congr rfl fun i _ => by
      unfold NormIn.mag
      rw [dif_pos i.isLt]
  have hsplit : ∑ i : Fin 1024, w.mag i ^ 2 =
      ∑ i : Fin 512, mag1 w i ^ 2 + ∑ i : Fin 512, mag2 w i ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i => w.mag i ^ 2), Fin.sum_univ_eq_sum_range (fun i => mag1 w i ^ 2),
      Fin.sum_univ_eq_sum_range (fun i => mag2 w i ^ 2), show (1024 : ℕ) = 512 + 512 from rfl,
      Finset.sum_range_add]
    refine congrArg₂ (· + ·) ?_ ?_
    · refine Finset.sum_congr rfl fun i hi => ?_
      unfold mag1
      rw [if_pos (Finset.mem_range.1 hi)]
    · refine Finset.sum_congr rfl fun i hi => ?_
      unfold mag2
      rw [if_pos (Finset.mem_range.1 hi)]
  rw [hmag, hsplit] at h
  unfold squares
  omega

/-- The challenge's coefficients are below `q`. -/
theorem c_lt {msgLen : ℕ} {G : Signer msgLen} (y : RingIn G) (i : Fin falcon512.n) :
    y.normIn.c i < 12289 :=
  stmtChallenge_lt y.x i

/-- **The shifted residual is nonnegative**: the carriers' bias exceeds `512 (q − 1)² + (q − 1)`. -/
theorem residual_nonneg (j : Fin falcon512.n) :
    0 ≤ Emulated.Rows.residual (EmulatedAlgebraCircuit.keyCoeffs w.h) w.c
      (Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) w.h w.c w.s2)
      (Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) w.s2) j + (bias : ℤ) := by
  have hconv := Emulated.Rows.negacyclicConv_natAbs_le_mul (A := 12288) (B := 12288)
    (h := EmulatedAlgebraCircuit.keyCoeffs w.h)
    (s := Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) w.s2)
    (fun k => Nat.le_of_lt_succ (ZMod.val_lt _)) (fun k => Nat.le_of_lt_succ (ZMod.val_lt _)) j
  have hb := LatticeCrypto.neg_le_and_le_of_natAbs_le hconv
  have hn : falcon512.n * 12288 * 12288 = 77309411328 := rfl
  rw [hn] at hb
  have hs1 : Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) w.h w.c w.s2 j < 12289 :=
    ZMod.val_lt _
  unfold Emulated.Rows.residual
  push_cast at hb ⊢
  have : (0 : ℤ) ≤ (w.c j : ℤ) := Int.natCast_nonneg _
  omega

/-- **The biased signature equation on the integers**: `c − h s2 − s1 + bias = q · quot`. -/
theorem residual_eq (j : Fin falcon512.n) :
    Emulated.Rows.residual (EmulatedAlgebraCircuit.keyCoeffs w.h) w.c
      (Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) w.h w.c w.s2)
      (Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) w.s2) j + (bias : ℤ) =
      (12289 : ℤ) * (quot w j : ℤ) := by
  have h := Emulated.Rows.residual_add_bias_eq_honestQuotient_of_nonneg
    (q := 12289) (BIAS := bias) (by norm_num)
    (Falcon512.EmulatedAlgebraCircuit.Honest.congruent_honest (P := falcon512) rfl w.h w.c w.s2) (residual_nonneg j)
  unfold quot
  rw [dif_pos (show (j : ℕ) < 512 from j.isLt)]
  exact_mod_cast h

/-- **The honest quotient is below `2^33`** (`2048³`). -/
theorem quot_lt (hc : ∀ i, w.c i < 12289) (j : ℕ) : quot w j < 2048 ^ 3 := by
  by_cases hj : j < 512
  · have he := residual_eq (w := w) ⟨j, hj⟩
    have hconv := Emulated.Rows.negacyclicConv_natAbs_le_mul (A := 12288) (B := 12288)
      (h := EmulatedAlgebraCircuit.keyCoeffs w.h)
      (s := Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) w.s2)
      (fun k => Nat.le_of_lt_succ (ZMod.val_lt _)) (fun k => Nat.le_of_lt_succ (ZMod.val_lt _))
      ⟨j, hj⟩
    have hb := LatticeCrypto.neg_le_and_le_of_natAbs_le hconv
    have hn : falcon512.n * 12288 * 12288 = 77309411328 := rfl
    rw [hn] at hb
    have hcj := hc ⟨j, hj⟩
    unfold Emulated.Rows.residual at he
    push_cast at hb he
    have : (0 : ℤ) ≤ (Falcon512.EmulatedAlgebraCircuit.Honest.s₁Coeffs (P := falcon512) w.h w.c w.s2 ⟨j, hj⟩ : ℤ) :=
      Int.natCast_nonneg _
    have hq : (quot w j : ℤ) < 2048 ^ 3 := by omega
    exact_mod_cast hq
  · unfold quot
    rw [dif_neg hj]
    norm_num

/-- **The biased signature equation in a field**: `c + bias − s1 − q · quot = h · s2`, the
negacyclic product of the casts. -/
theorem quot_field {K : Type*} [Field K] (j : Fin falcon512.n) :
    (w.c j : K) + (bias : ℕ) - (w.nS1 j : K) - (12289 : ℕ) * (quot w j : K) =
      LatticeCrypto.negacyclicConvCoeff (Native.Rows.keyVec (F := K) w.h)
        (fun i : Fin falcon512.n => ((w.nS2 i : ℕ) : K)) j := by
  have he := congrArg (fun z : ℤ => (z : K)) (residual_eq (w := w) j)
  unfold Emulated.Rows.residual at he
  push_cast at he
  rw [Emulated.Rows.intCast_negacyclicConvCoeff] at he
  have hk : (fun i => ((EmulatedAlgebraCircuit.keyCoeffs w.h i : ℕ) : K)) =
      Native.Rows.keyVec (F := K) w.h := rfl
  have hs : (fun i => ((Falcon512.EmulatedAlgebraCircuit.Honest.s₂Coeffs (P := falcon512) w.s2 i : ℕ) : K)) =
      fun i : Fin falcon512.n => ((w.nS2 i : ℕ) : K) := funext fun i => by rw [NormIn.nS2_fin]
  rw [hk, hs] at he
  rw [NormIn.nS1_fin]
  linear_combination he

/-- **Three base-`2048` digits** reconstruct a natural below `2048³`. -/
theorem digits3 {n : ℕ} (hn : n < 2048 ^ 3) :
    n / 2048 ^ 0 % 2048 + 2048 * (n / 2048 ^ 1 % 2048) + 4194304 * (n / 2048 ^ 2 % 2048) = n := by
  norm_num at hn ⊢
  omega

/-- **Two base-`128` digits** reconstruct a natural below `128²`. -/
theorem digits128 {n : ℕ} (hn : n < 128 ^ 2) :
    n / 128 ^ 0 % 128 + 128 * (n / 128 ^ 1 % 128) = n := by
  norm_num at hn ⊢
  omega

end Carrier

/-! ## The carriers' roles and needles -/

/-- **The carriers' source values with honest naturals**: `s2` (`10`), `signature.s1` (`11`), the
magnitudes of `s2` (`14`) and their low parts (`15`), and the digits of the values bound to their
digits: the quotient's (`20 … 22`), the magnitudes of `s1`'s (`23`, `24`), the norm's
(`33 … 35`). -/
def carrierRoles : List (ℕ × NatRole) :=
  [(10, .s2), (11, .s1), (14, .mag2), (15, .low2), (20, .quotD 0), (21, .quotD 1), (22, .quotD 2),
    (23, .mag1D 0), (24, .mag1D 1), (33, .normD 0), (34, .normD 1), (35, .normD 2)]

variable (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] in
/-- **The carriers' roles** (`FalconRingRoles`). -/
instance carrierRolesInst : FalconRingRoles program where
  natRoles := carrierRoles

variable (program : RealizedProgram) [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] in
/-- **The program facts of a carrier's honest execution** (decided per program): the realization's
predicates (`range.magnitudes.mag1.top` `5`, `range.encoding.budget.reconstruct` `6`,
`range.encoding.budget.top` `7`, `range.norm.bound.top` `8`, `encoding.high2.q` `16`) are no
source predicates; the values bound to their digits (the quotient `12`, the magnitudes of `s1`
`13`, the norm `17`); the fields and sizes; the bound values' `BoundOk`; the eighteen
predicates. -/
class FalconCarrierHonest : Prop where
  refsOrdered : program.RefsOrdered
  idx9 : FalconRingMember.idxPred program = 9
  realPreds : ∀ q ∈ [5, 6, 7, 8, 16], program.inSource (program.predicate q) = false
  quotKind : (program.value 12).kind = .bound (.add (.add (.leaf 20) (.scale (.const 2048) (.leaf 21)))
    (.scale (.const 4194304) (.leaf 22)))
  mag1Kind : (program.value 13).kind = .bound (.add (.leaf 23) (.scale (.const 128) (.leaf 24)))
  sqKind : (program.value 17).kind = .bound (.add (.add (.leaf 33) (.scale (.const 2048) (.leaf 34)))
    (.scale (.const 4194304) (.leaf 35)))
  fields : ∀ v ∈ [12, 13, 17, 27, 32, 39], program.valueField v = 0
  roleFields : ∀ p ∈ carrierRoles, program.valueField p.1 = 0
  sizes512 : ∀ v ∈ [10, 20, 21, 22, 23, 24, 25, 26, 27], (program.value v).size = 512
  sizes1 : ∀ v ∈ [28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39], (program.value v).size = 1
  lens : 17 < program.values.length
  bound : ∀ v < program.values.length, program.BoundOk v
  cover : program.predicates.length = 18

/-! ## The predicates at the honest values -/

section Honest

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] [FalconCarrierHonest program]
  [FalconRingRoleFacts program] {I : Interp} [EField (I 0)]
  {msgLen : ℕ} {G : Signer msgLen}

attribute [local instance] ringField_carrier

variable (y : RingIn G) {c : ∀ k, (program.layout I).Ch k} {π : (program.layout I).Pads}

set_option hygiene false in
local notation "env" =>
  program.srcEnv I (stmtOf (program := program) (I := I) y.x) (honestVal program I y) c π

/-- **A value of `carrierRoles` reads its honest natural** in field `0`. -/
theorem rd_role {v : ℕ} {r : NatRole} (hr : (v, r) ∈ carrierRoles) {j : ℕ}
    (hj : j < (program.value v).size) : rdC env v j = ((r.natOf y.normIn j : ℕ) : (I 0).K) :=
  leaf_nat_env y (program := program) hr (FalconCarrierHonest.roleFields (program := program) _ hr) hj

/-- **A value bound to its digits reads its expression** at the source environment. -/
theorem rdC_bound {v : ℕ} {x : Expr} (hk : (program.value v).kind = .bound x)
    (hf : program.valueField v = 0) (hv : v < program.values.length) (j : ℕ) :
    rdC env v j = program.evalE (program.reader env) 0 x j := by
  unfold rdC
  rw [RealizedProgram.evalE_leaf, RealizedProgram.reader_bindAsg_of_boundOk (FalconCarrierHonest.bound (program := program)) rfl hv hk]
  revert hf
  generalize program.valueField v = f
  intro hf
  subst hf
  rfl

theorem decode2048 : (I 0).decode 2048 = ((2048 : ℕ) : (I 0).K) :=
  EField.decode_lt _ (by norm_num [pGold])

theorem decode128 : (I 0).decode 128 = ((128 : ℕ) : (I 0).K) :=
  EField.decode_lt _ (by norm_num [pGold])

theorem decode4194304 : (I 0).decode 4194304 = ((4194304 : ℕ) : (I 0).K) :=
  EField.decode_lt _ (by norm_num [pGold])

/-- **The quotient** reads its honest natural through its digits. -/
theorem rd_quot {j : ℕ} (hj : j < 512) : rdC env 12 j = ((Carrier.quot y.normIn j : ℕ) : (I 0).K) := by
  have hs := FalconCarrierHonest.sizes512 (program := program)
  rw [rdC_bound y FalconCarrierHonest.quotKind (FalconCarrierHonest.fields (program := program) 12
    (by simp)) (by have := FalconCarrierHonest.lens (program := program); omega),
    RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, RealizedProgram.evalE_scale_const,
    decode2048, decode4194304]
  change rdC env 20 j + _ * rdC env 21 j + _ * rdC env 22 j = _
  rw [rd_role y (r := .quotD 0) (by simp [carrierRoles]) (by rw [hs 20 (by simp)]; exact hj),
    rd_role y (r := .quotD 1) (by simp [carrierRoles]) (by rw [hs 21 (by simp)]; exact hj),
    rd_role y (r := .quotD 2) (by simp [carrierRoles]) (by rw [hs 22 (by simp)]; exact hj)]
  have hd := Carrier.digits3 (Carrier.quot_lt (Carrier.c_lt y) j)
  simp only [NatRole.natOf]
  conv_rhs => rw [← hd]
  push_cast
  ring

/-- **The magnitudes of `s1`** read their honest naturals through their digits. -/
theorem rd_mag1 {j : ℕ} (hj : j < 512) : rdC env 13 j = ((Carrier.mag1 y.normIn j : ℕ) : (I 0).K) := by
  have hs := FalconCarrierHonest.sizes512 (program := program)
  rw [rdC_bound y FalconCarrierHonest.mag1Kind (FalconCarrierHonest.fields (program := program) 13
    (by simp)) (by have := FalconCarrierHonest.lens (program := program); omega),
    RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, decode128]
  change rdC env 23 j + _ * rdC env 24 j = _
  rw [rd_role y (r := .mag1D 0) (by simp [carrierRoles]) (by rw [hs 23 (by simp)]; exact hj),
    rd_role y (r := .mag1D 1) (by simp [carrierRoles]) (by rw [hs 24 (by simp)]; exact hj)]
  have hd := Carrier.digits128 (n := Carrier.mag1 y.normIn j)
    (lt_of_le_of_lt (Carrier.mag1_le j) (by norm_num))
  simp only [NatRole.natOf]
  conv_rhs => rw [← hd]
  push_cast
  ring

/-- **The squared norm** reads its honest natural through its digits. -/
theorem rd_sq : rdC env 17 0 = ((Carrier.squares y.normIn : ℕ) : (I 0).K) := by
  have hs := FalconCarrierHonest.sizes1 (program := program)
  rw [rdC_bound y FalconCarrierHonest.sqKind (FalconCarrierHonest.fields (program := program) 17
    (by simp)) (by have := FalconCarrierHonest.lens (program := program); omega),
    RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const, RealizedProgram.evalE_scale_const,
    decode2048, decode4194304]
  change rdC env 33 0 + _ * rdC env 34 0 + _ * rdC env 35 0 = _
  rw [rd_role y (r := .normD 0) (by simp [carrierRoles]) (by rw [hs 33 (by simp)]; norm_num),
    rd_role y (r := .normD 1) (by simp [carrierRoles]) (by rw [hs 34 (by simp)]; norm_num),
    rd_role y (r := .normD 2) (by simp [carrierRoles]) (by rw [hs 35 (by simp)]; norm_num)]
  have hd := Carrier.digits3 (n := Carrier.squares y.normIn)
    (lt_of_le_of_lt (Carrier.squares_le y.valid) (by norm_num))
  simp only [NatRole.natOf]
  conv_rhs => rw [← hd]
  push_cast
  ring

theorem rd_s2 {j : ℕ} (hj : j < 512) : rdC env 10 j = ((y.normIn.nS2 j : ℕ) : (I 0).K) :=
  rd_role y (r := .s2) (by simp [carrierRoles])
    (by rw [FalconCarrierHonest.sizes512 (program := program) 10 (by simp)]; exact hj)

theorem rd_s1 {j : ℕ} (hj : j < 512) : rdC env 11 j = ((y.normIn.nS1 j : ℕ) : (I 0).K) :=
  rd_role y (r := .s1) (by simp [carrierRoles])
    (by rw [(FalconCarrierBase.sizes (program := program)).1]; exact hj)

theorem rd_mag2 {j : ℕ} (hj : j < 512) : rdC env 14 j = ((Carrier.mag2 y.normIn j : ℕ) : (I 0).K) :=
  rd_role y (r := .mag2) (by simp [carrierRoles])
    (by rw [(FalconCarrierBase.sizes (program := program)).2.2.2.1]; exact hj)

theorem rd_low2 {j : ℕ} (hj : j < 512) :
    rdC env 15 j = ((Carrier.mag2 y.normIn j % 128 : ℕ) : (I 0).K) :=
  rd_role y (r := .low2) (by simp [carrierRoles])
    (by rw [(FalconCarrierBase.sizes (program := program)).2.2.2.2.1]; exact hj)

/-- **The budget's expression** reads the honest budget. -/
theorem evalE_budget :
    program.evalE (program.reader env) 0 budgetExpr 0 = ((Carrier.budget y.normIn : ℕ) : (I 0).K) := by
  rw [budgetExpr, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_scale_const,
    RealizedProgram.evalE_apply_sum, RealizedProgram.evalE_apply_sum, decode_mOneG]
  change _ + rdC env 16 0 = _
  rw [rdC_off]
  simp only [Nat.zero_mul, Nat.zero_add]
  change -1 * ∑ t : Fin 512, rdC env 14 t + ∑ t : Fin 512, rdC env 15 t + _ = _
  simp only [fun t : Fin 512 => rd_mag2 (c := c) (π := π) y t.isLt,
    fun t : Fin 512 => rd_low2 (c := c) (π := π) y t.isLt]
  have hb := congrArg (Nat.cast : ℕ → (I 0).K) (Carrier.budget_add y.valid)
  push_cast [Nat.cast_sum] at hb
  have hsub : ∀ t : Fin 512, ((Carrier.mag2 y.normIn t - Carrier.mag2 y.normIn t % 128 : ℕ) : (I 0).K) =
      (Carrier.mag2 y.normIn t : (I 0).K) - ((Carrier.mag2 y.normIn t % 128 : ℕ) : (I 0).K) :=
    fun t => Nat.cast_sub (Nat.mod_le _ _)
  simp only [hsub, Finset.sum_sub_distrib] at hb
  linear_combination -hb

end Honest

/-! ### The predicates -/

section Preds

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] [FalconCarrierHonest program]
  [FalconRingRoleFacts program] {I : Interp} [EField (I 0)]
  {msgLen : ℕ} {G : Signer msgLen}

attribute [local instance] ringField_carrier

variable (y : RingIn G) {c : ∀ k, (program.layout I).Ch k} {π : (program.layout I).Pads}

set_option hygiene false in
local notation "env" =>
  program.srcEnv I (stmtOf (program := program) (I := I) y.x) (honestVal program I y) c π

/-- **The signature equation holds on the honest values**: `c + bias − s1 − q · quot` is the
negacyclic product `h · s2` (`Carrier.quot_field`), whose transform at `ψ` is the key's spectrum
times `s2`'s (`DFT.negSpectrum_negacyclicConvCoeff`). -/
theorem sig_honest_carrier : program.HoldsAt env (program.predicate 1).body := by
  obtain ⟨-, -, h7, h10, -, hpsi, -⟩ := FalconCarrierBase.ids (program := program)
  obtain ⟨t, hb⟩ := FalconCarrierBase.sig (program := program)
  rw [RealizedProgram.HoldsAt, hb]
  refine holdsWith_equal0_of fun k hk => ?_
  rw [exprLen_carrierSigLhs] at hk
  change _ = rdC env 3 k
  rw [rdC_zeros _ hk, evalE_carrierSigLhs _ hk, sub_eq_zero, specOf_env y hk]
  have hst : (env).stmt = stmtOf (program := program) (I := I) y.x := rfl
  have hfun : (fun j : Fin 512 => chalEntry (env).stmt j + ((77309435394 : ℕ) : (I 0).K) -
      rdC env 11 j - ((12289 : ℕ) : (I 0).K) * rdC env 12 j) =
      LatticeCrypto.negacyclicConvCoeff (Native.Rows.keyVec (F := (I 0).K) y.normIn.h)
        (fun i : Fin falcon512.n => ((y.normIn.nS2 i : ℕ) : (I 0).K)) := by
    funext j
    rw [hst, show chalEntry (stmtOf (program := program) (I := I) y.x) (j : ℕ) =
      ((stmtChallenge y.x j : ℕ) : (I 0).K) from chalEntry_stmtOf y.x j, rd_s1 y j.isLt,
      rd_quot y j.isLt]
    exact Carrier.quot_field (K := (I 0).K) (w := y.normIn) j
  have hs2 : (fun j : Fin 512 => s2Of env j) = fun j : Fin falcon512.n => ((y.normIn.nS2 j : ℕ) : (I 0).K) := by
    funext j
    unfold s2Of
    rw [(FalconCarrierBase.ids (program := program)).2.2.2.1]
    exact rd_s2 y j.isLt
  have hspec : specK program y k = DFT.negSpectrum (psiG : (I 0).K)
      (Native.Rows.keyVec (F := (I 0).K) y.normIn.h) ⟨k, hk⟩ := by
    unfold specK
    rw [hpsi, EField.decode_lt _ (by norm_num [pGold]), nttNatural_eq_negSpectrum' _ _ ⟨k, hk⟩]
    congr 1
    funext j
    exact congrArg (fun n : ℕ => (n : (I 0).K)) (keyEntry_add y.x y.w.idx j)
  have e1 := congrArg (fun f => f ⟨k, hk⟩) (DFT.negSpectrum_negacyclicConvCoeff
    (psiG_pow (K := (I 0).K)) (Native.Rows.keyVec (F := (I 0).K) y.normIn.h)
    (fun i : Fin falcon512.n => ((y.normIn.nS2 i : ℕ) : (I 0).K)))
  simp only [Pi.mul_apply] at e1
  rw [nttNatural_eq_negSpectrum' _ _ ⟨k, hk⟩, nttNatural_eq_negSpectrum' _ _ ⟨k, hk⟩, hfun, hs2, hspec]
  exact e1

/-- **The magnitudes of `s1` hold**: the centered magnitude (`Carrier.centering1`). -/
theorem magS1_honest : program.HoldsAt env (program.predicate 2).body := by
  obtain ⟨t, hb⟩ := FalconCarrierBase.magS1 (program := program)
  rw [RealizedProgram.HoldsAt, hb]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [magLhs, RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf,
    (FalconCarrierBase.sizes (program := program)).2.2.1] at hi
  change _ = rdC env 3 i
  rw [rdC_zeros _ hi, evalE_magLhs _ _ _ hi, rd_mag1 y hi, rd_s1 y hi]
  exact Carrier.centering1 hi

/-- **The magnitudes of `s2` hold**: the centered magnitude (`Carrier.centering2`). -/
theorem magS2_honest : program.HoldsAt env (program.predicate 3).body := by
  obtain ⟨t, hb⟩ := FalconCarrierBase.magS2 (program := program)
  rw [RealizedProgram.HoldsAt, hb]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [magLhs, RealizedProgram.exprLen_mul, RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf,
    (FalconCarrierBase.sizes (program := program)).2.2.2.1] at hi
  change _ = rdC env 3 i
  rw [rdC_zeros _ hi, evalE_magLhs _ _ _ hi, rd_mag2 y hi, rd_s2 y hi]
  exact Carrier.centering2 hi

/-- **The norm's equation holds**: `squares = Σ mag1² + Σ mag2²`. -/
theorem normSum_honest : program.HoldsAt env (program.predicate 4).body := by
  obtain ⟨t, hb⟩ := FalconCarrierBase.normSum (program := program)
  rw [RealizedProgram.HoldsAt, hb]
  refine holdsWith_equal0_of fun i hi => ?_
  rw [exprLen_normLhs] at hi
  obtain rfl : i = 0 := by omega
  rw [rdC_zero1, evalE_normLhs, rd_sq]
  simp only [fun t : Fin 512 => rd_mag1 (c := c) (π := π) y t.isLt,
    fun t : Fin 512 => rd_mag2 (c := c) (π := π) y t.isLt]
  unfold Carrier.squares
  push_cast
  simp only [sq]
  ring

/-- **A range of one record holds** where each coordinate reads a natural below the bound. -/
theorem mem_honest {p n : ℕ} {E : Expr} {r : InRealization}
    (hb : (program.predicate p).body = .mem 0 [E] (.range n) r)
    (h : ∀ i < program.exprLen E, ∃ k < n, program.evalE (program.reader env) 0 E i = (k : (I 0).K)) :
    program.HoldsAt env (program.predicate p).body := by
  rw [RealizedProgram.HoldsAt, hb]
  intro i hi e he
  rw [List.mem_singleton] at he
  subst he
  obtain ⟨k, hk, hkv⟩ := h i hi
  refine ⟨k, hk, ?_⟩
  unfold RealizedProgram.evalWith
  rw [FalconRingMember.domainField0 (program := program)]
  exact hkv

/-- **The ranges hold on the honest values**: the quotient below `2^33`, the magnitudes of `s1`
below `6145`, of `s2` below `2048`, the low parts below `128`, the budget below `50177`, the norm
below `34034727`. -/
theorem ranges_honest_carrier :
    ∀ q ∈ [10, 11, 12, 13, 14, 15], program.HoldsAt env (program.predicate q).body := by
  obtain ⟨hz11, hz12, hz13, hz14, hz15, hz17⟩ := FalconCarrierBase.sizes (program := program)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨r, hb⟩ := FalconCarrierBase.rQuot (program := program)
    refine mem_honest y hb fun i hi => ⟨_, ?_, rd_quot y (by rwa [RealizedProgram.exprLen_leaf, hz12] at hi)⟩
    exact lt_of_lt_of_eq (Carrier.quot_lt (Carrier.c_lt y) i) (by norm_num)
  · obtain ⟨r, hb⟩ := FalconCarrierBase.rMag1 (program := program)
    exact mem_honest y hb fun i hi => ⟨_, Nat.lt_succ_of_le (Carrier.mag1_le i),
      rd_mag1 y (by rwa [RealizedProgram.exprLen_leaf, hz13] at hi)⟩
  · obtain ⟨r, hb⟩ := FalconCarrierBase.rMag2 (program := program)
    exact mem_honest y hb fun i hi => ⟨_, Carrier.mag2_lt y.valid i,
      rd_mag2 y (by rwa [RealizedProgram.exprLen_leaf, hz14] at hi)⟩
  · obtain ⟨r, hb⟩ := FalconCarrierBase.rLow2 (program := program)
    exact mem_honest y hb fun i hi => ⟨_, Nat.mod_lt _ (by norm_num),
      rd_low2 y (by rwa [RealizedProgram.exprLen_leaf, hz15] at hi)⟩
  · obtain ⟨r, hb⟩ := FalconCarrierBase.rBudget (program := program)
    refine mem_honest y hb fun i hi => ?_
    rw [budgetExpr, RealizedProgram.exprLen_add, RealizedProgram.exprLen_add, RealizedProgram.exprLen_scale,
      RealizedProgram.exprLen_apply] at hi
    have hi0 : i = 0 := by
      simp [NamedOp.rows, NamedOp.cols, RealizedProgram.exprLen_leaf, hz14] at hi
      omega
    subst hi0
    exact ⟨_, Nat.lt_succ_of_le Carrier.budget_le, evalE_budget y⟩
  · obtain ⟨r, hb⟩ := FalconCarrierBase.rNorm (program := program)
    refine mem_honest y hb fun i hi => ?_
    rw [RealizedProgram.exprLen_leaf, hz17] at hi
    obtain rfl : i = 0 := by omega
    exact ⟨_, Nat.lt_succ_of_le (Carrier.squares_le y.valid), rd_sq y⟩

/-- **`encoding.high2` holds**: `128 ∣ mag2 − mag2 mod 128` on the integer readings. -/
theorem high2_honest : program.HoldsAt env (program.predicate 17).body := by
  obtain ⟨r, hb⟩ := FalconCarrierBase.high2 (program := program)
  obtain ⟨hk14, hk15⟩ := FalconCarrierBase.privKinds (program := program)
  have hf := FalconCarrierBase.fields (program := program)
  obtain ⟨-, -, -, hz14, -⟩ := FalconCarrierBase.sizes (program := program)
  rw [RealizedProgram.HoldsAt, hb]
  intro i hi
  rw [RealizedProgram.exprLen_leaf, hz14] at hi
  have hm := Carrier.mag2_lt y.valid (w := y.normIn) i
  rw [RealizedProgram.evalIntWith_leaf, RealizedProgram.evalIntWith_leaf,
    intOf_priv hk14 (hf 14 (by simp)) (rd_mag2 y hi) (by norm_num [pGold]; omega),
    intOf_priv hk15 (hf 15 (by simp)) (rd_low2 y hi)
      (by have := Nat.mod_lt (Carrier.mag2 y.normIn i) (show 0 < 128 by norm_num); norm_num [pGold]; omega)]
  exact ⟨(Carrier.mag2 y.normIn i / 128 : ℕ), by push_cast; have := Nat.mod_add_div (Carrier.mag2 y.normIn i) 128; omega⟩

/-- **Every source predicate of a carrier holds at the source environment of the honest values**
(the realization's predicates `5`–`8` and `16` are no source predicates,
`FalconCarrierHonest.realPreds`). -/
theorem source_holds_carrier {q : ℕ} (hq : q < program.predicates.length)
    (hs : program.inSource (program.predicate q) = true) :
    program.HoldsAt env (program.predicate q).body := by
  rw [FalconCarrierHonest.cover (program := program)] at hq
  have hr := ranges_honest_carrier (c := c) (π := π) y
  have h9 := FalconCarrierHonest.idx9 (program := program)
  have hreal : ∀ q ∈ [5, 6, 7, 8, 16], program.inSource (program.predicate q) = true → False :=
    fun q hq h => by
      rw [FalconCarrierHonest.realPreds (program := program) q hq] at h
      cases h
  interval_cases q
  · exact member_honest y
  · exact sig_honest_carrier y
  · exact magS1_honest y
  · exact magS2_honest y
  · exact normSum_honest y
  · exact (hreal 5 (by simp) hs).elim
  · exact (hreal 6 (by simp) hs).elim
  · exact (hreal 7 (by simp) hs).elim
  · exact (hreal 8 (by simp) hs).elim
  · have := idxBool_honest (c := c) (π := π) y
    rwa [h9] at this
  all_goals first
    | exact high2_honest y
    | exact hr _ (by decide)
    | exact (hreal 16 (by decide) hs).elim

end Preds

/-! ### The execution of the source program -/

section Strategy

variable {program : RealizedProgram} [FalconRingPowers program] [FalconRingSelect program]
  [FalconRingMember program] [FalconCarrierBase program] [FalconCarrierHonest program]
  [FalconRingRoleFacts program] {I : Interp} [EField (I 0)]
  {msgLen : ℕ} {G : Signer msgLen}

attribute [local instance] ringField_carrier

variable [FalconRingSource program] [PrimeNode (I 0)]

/-- **The carriers' root lies in `F_p`**: `ψ` is a constant below `p`. -/
theorem psi_mem_carrier : (I 0).decode (FalconRingMember.psi program) ∈ (I 0).node "GF(p^1)" := by
  rw [(FalconCarrierBase.ids (program := program)).2.2.2.2.2.1,
    EField.decode_lt _ (by norm_num [pGold])]
  exact natCast_mem_prime0 rfl _

variable (program I PN) in
/-- **The execution of a Falcon ring carrier's source program** (`sourceExecutionOf` at the carriers'
predicates `source_holds_carrier`). -/
noncomputable def carrierSourceExecution (hI : I.Registered program) (hL : I.Lawful program PN)
    {Gn : RealizedProgram.Gens} (R : program.CommittedFacts I Gn)
    (hbc : program.BoundNoCopy)
    (hk : program.KprivTyped) (hone : program.BoundOneMem I)
    (hff : ∀ p < program.predicates.length, program.isFieldForm p = false)
    (hng : program.NoGammaTables) :
    program.SourceExecution I (relH G program I) :=
  sourceExecutionOf program I PN psi_mem_carrier (fun y _ _ _ hq hs => source_holds_carrier y hq hs) hI hL R hbc
    hk hone hff hng

end Strategy

end GordieHowe.Falcon512.Ring
