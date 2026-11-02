-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.HonestValues

@[expose] public section

/-!
# GordieHowe: the signature relation of the native ML-DSA-44 ring programs at the honest values

The four spectral rows `signature.relation.0 … 3` (predicates `1 … 4`;
`lib/gordiehowe/examples/rings/mldsa_ring_native.h`, `spectral_relation`) hold at the source
environment of the honest values (`sig_holds`): the honest `w′` is `computeWApprox(Â, c, z, t1)`
(FIPS 204 Algorithm 8, line 9) at the signer's key, so its NTT is
`Σ_j Â_ij ⊙ NTT(z_j) − NTT(2^d · t1_i) ⊙ NTT(c)` coefficientwise (`ntt_honestW`, the vendored
`ntt_invNTT` and `MultiplyNTTs`), and the field rows are the images of those `ZMod q` equations
under the cast `ZMod q → F` (`nttScheme_map`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits RealizedProgram
open MLDSA44.NativeAlgebraCircuit (flat)
open MLDSA44.NativeAlgebraCircuit.Honest (wCoeff zCentered)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

/-! ## The honest `w′` in the NTT domain -/

/-- **The NTT of the honest `w′`**: at a key whose `ExpandA` finishes within the byte budget,
coefficient `k` of `NTT(w′_i)` is `Σ_j Â_ijk · NTT(z_j)_k − NTT(2^d · t1_i)_k · NTT(c)_k`
(`computeWApprox_get`, `ntt_invNTT`, `ntt_mul_get`). -/
theorem ntt_honestW (pk : PublicKey) (hpk : MLDSA44.ExpandAWithin _root_.MLDSA.mldsa44 pk.rho)
    (c : Fin mldsa44.N → ℤ) (z : _root_.MLDSA.RqVec _root_.MLDSA.mldsa44.l) (i : Fin _root_.MLDSA.mldsa44.k)
    (k : Fin _root_.MLDSA.ringDegree) :
    (_root_.MLDSA.Concrete.ntt ((MLDSA44.PoP.Compose.honestWApprox pk c z).get i)).coeffs.get k =
      ∑ j : Fin _root_.MLDSA.mldsa44.l, ((((MLDSA44.expandABounded _root_.MLDSA.mldsa44 pk.rho).get i).get j).coeffs.get k) *
          (_root_.MLDSA.Concrete.ntt (z.get j)).coeffs.get k -
        (_root_.MLDSA.Concrete.ntt (MLDSA44.Native.Rows.prims.power2RoundShift (pk.t1.get i))).coeffs.get k *
          (_root_.MLDSA.Concrete.ntt (MLDSA44.ofCoeff fun k => (c k : _root_.MLDSA.Coeff))).coeffs.get k := by
  unfold MLDSA44.PoP.Compose.honestWApprox
  erw [MLDSA44.computeWApprox_get]
  rw [← nttCoeffHom_apply]
  erw [map_sub, map_sum]
  simp only [nttCoeffHom_apply, ntt_mul_get, fromHat_eq, _root_.MLDSA.Concrete.ntt_invNTT]
  rw [← MLDSA44.expandABounded_eq_expandAFull hpk]
  ring

/-! ## The cast of `ZMod q` into domain `A`'s field -/

section Cast

variable {K : Type*} [Field K] [CharP K _root_.MLDSA.modulus]

set_option hygiene false in
local notation "φ" => (ZMod.castHom (dvd_refl _root_.MLDSA.modulus) K : _root_.MLDSA.Coeff →+* K)

theorem φ_apply (x : _root_.MLDSA.Coeff) : φ x = ((x.val : ℕ) : K) := by
  change (ZMod.cast x : K) = _
  rw [ZMod.cast_eq_val]

/-- **The scheme-order transform commutes with the cast** `ZMod q → F`. -/
theorem nttScheme_map (ψ : _root_.MLDSA.Coeff) (x : ℕ → _root_.MLDSA.Coeff) (m : ℕ) :
    Ops.nttScheme 256 (φ ψ) (fun t => φ (x t)) m = φ (Ops.nttScheme 256 ψ x m) := by
  by_cases hm : m < 256
  · rw [Ops.nttScheme_apply (k := 8) (by norm_num) _ _ hm,
      Ops.nttScheme_apply (k := 8) (by norm_num) _ _ hm, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, map_pow]
  · unfold Ops.nttScheme
    rw [if_neg hm, if_neg hm, map_zero]

theorem φ_centered (x : _root_.MLDSA.Coeff) : (((LatticeCrypto.centeredRepr x : ℤ)) : K) = φ x := by
  conv_rhs => rw [LatticeCrypto.centeredRepr_intCast x]
  rw [map_intCast]

/-- **The support less twice the sign of a ternary coefficient** is the coefficient. -/
theorem ternary_sub (z : ℤ) (hz : z = 0 ∨ z = 1 ∨ z = -1) :
    (HashCircuit.ternaryBits (K := K) z).1 - 2 * (HashCircuit.ternaryBits (K := K) z).2 =
      φ ((z : ℤ) : _root_.MLDSA.Coeff) := by
  rw [map_intCast]
  rcases hz with rfl | rfl | rfl <;> norm_num [HashCircuit.ternaryBits]

end Cast

/-! ## The flat index of a coefficient -/

theorem flat_fm {α : Type*} (f : Fin MLDSA44.Native.Rows.nRows → Fin MLDSA44.Native.Rows.deg → α)
    (i : Fin 4) (s : ℕ) (hs : s < 256) (hm : (i : ℕ) * 256 + s < 1024) :
    flat f (Native.fm ((i : ℕ) * 256 + s) hm) = f ⟨i, i.isLt⟩ ⟨s, hs⟩ := by
  have hi := i.isLt
  unfold flat Native.fm
  congr 1 <;> apply Fin.ext <;>
    simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat,
      show MLDSA44.Native.Rows.deg = 256 from rfl] <;> omega

theorem flat_fmz {α : Type*} (f : Fin MLDSA44.Native.Rows.nCols → Fin MLDSA44.Native.Rows.deg → α)
    (j : Fin 4) (s : ℕ) (hs : s < 256) (hm : (j : ℕ) * 256 + s < 1024) :
    flat f (Native.fmz ((j : ℕ) * 256 + s) hm) = f ⟨j, j.isLt⟩ ⟨s, hs⟩ := by
  have hj := j.isLt
  unfold flat Native.fmz
  congr 1 <;> apply Fin.ext <;>
    simp only [finProdFinEquiv_symm_apply, Fin.coe_divNat, Fin.coe_modNat,
      show MLDSA44.Native.Rows.deg = 256 from rfl] <;> omega

/-! ## The rows at the honest values -/

section Rows

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "σ" => MldsaRingEmbed.σ program

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program] [MldsaRingHonest program]
  {F0 FH : FieldInterp} [QField F0] [HField FH] [Native.MldsaAAlgebra nat] [hN : Native.MldsaNativeHonest nat F0 FH]
  [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MldsaHNativeData FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "φ" => (ZMod.castHom (dvd_refl _root_.MLDSA.modulus) (interp 0).K :
  _root_.MLDSA.Coeff →+* (interp 0).K)

variable (y : RingIn msgLen) (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
  (π : (program.layout interp).Pads)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH y) c π

/-- **A held value of domain `A` reads its honest value** at the source environment. -/
theorem evalE_held {u : ℕ} (hA : u ∈ Native.AValues) {j : ℕ} (hj : j < ((nat).value u).size) :
    program.evalE (program.reader E) 0 (.leaf ((σ).val u)) j = aValR y F0.K u j := by
  rw [← evalE_pull E (MldsaRingHonest.aV (program := program) u (List.mem_append_left _ hA)) j]
  exact (readsA_pull y x c π).cells u hA j hj

/-- **A member's value reads its honest value** at the source environment. -/
theorem evalE_member {v : ℕ} (hv : v ∈ [MldsaRingRelation.aHat program, MldsaRingRelation.t1 program,
    MldsaRingFront.muA program, (TableSelect.shape program).idx]) {j : ℕ}
    (hj : j < (program.value v).size) :
    program.evalE (program.reader E) 0 (.leaf v) j =
      castElt (b := 0) (honestVal program F0 FH y v j) := by
  rw [evalE_leaf, reader_srcEnv_of_privCellB x _ c π
    ((MldsaRingHonest.memberCells (program := program) v hv).1) hj]

/-- The honest value of `member.a_hat`. -/
theorem honestVal_aHat (j : ℕ) :
    castElt (b := 0) (honestVal program F0 FH y (MldsaRingRelation.aHat program) j) =
      ((keyEntry y.key j : ℕ) : (interp 0).K) := by
  have hf := (MldsaRingHonest.memberCells (program := program) (MldsaRingRelation.aHat program)
    (by simp)).2
  unfold honestVal
  rw [if_pos rfl]
  exact castElt_castElt_of_eq hf.symm _

/-- The honest value of `member.t1`. -/
theorem honestVal_t1 (j : ℕ) :
    castElt (b := 0) (honestVal program F0 FH y (MldsaRingRelation.t1 program) j) =
      ((keyEntry y.key (4096 + j) : ℕ) : (interp 0).K) := by
  have hd := MldsaRingHonest.member_nodup (program := program)
  have hf := (MldsaRingHonest.memberCells (program := program) (MldsaRingRelation.t1 program)
    (by simp)).2
  unfold honestVal
  rw [if_neg (by simp at hd; exact fun h => hd.1.1 h.symm), if_pos rfl]
  exact castElt_castElt_of_eq hf.symm _

/-- **Coefficient `t` of a polynomial**, `0` past `256`. -/
def cf (f : _root_.MLDSA.Rq) (t : ℕ) : _root_.MLDSA.Coeff :=
  if h : t < 256 then MLDSA44.coeff f ⟨t, h⟩ else 0

theorem cf_get (f : _root_.MLDSA.Rq) : ∀ t (ht : t < 256), cf f t = f.get ⟨t, ht⟩ := fun t ht => by
  unfold cf
  rw [dif_pos ht, MLDSA44.coeff_apply]

/-- **Row `i` of `signature.relation` holds** at the honest values. -/
theorem sig_row (i : Fin 4) :
    program.HoldsAt E (program.predicate ((i : ℕ) + 1)).body := by
  obtain ⟨t, hb⟩ := MldsaRingRelation.rows (program := program) i
  obtain ⟨h57, h58, h59, h60, -⟩ := MldsaRingFront.vals (program := program)
  obtain ⟨-, -, -, -, -, -, -, -, hs59, hs60, -⟩ := Native.MldsaNativeHonest.a_bound (program := nat)
  rw [HoldsAt, hb]
  intro k hk
  rw [MldsaRingRelation.rowLen i] at hk
  unfold evalWith
  rw [MldsaRingRelation.domainField0 (program := program), evalE_leaf2 E hk, evalE_rowLhs _ i hk,
    sub_eq_zero]
  have hi := i.isLt
  have hψ : (interp 0).decode 1753 = φ _root_.MLDSA.zeta := by
    rw [decode_psi, show _root_.MLDSA.zeta = ((1753 : ℕ) : _root_.MLDSA.Coeff) from rfl]
    exact (map_natCast _ 1753).symm
  set w := MLDSA44.PoP.Compose.honestWApprox y.key y.c y.z
  set cP : _root_.MLDSA.Rq := MLDSA44.ofCoeff fun k => (y.c k : _root_.MLDSA.Coeff)
  -- the honest readings
  have hW : ∀ s < 256, program.evalE (program.reader E) 0 (.leaf (MldsaRingRelation.w program))
      ((i : ℕ) * 256 + s) = φ (cf (w.get i) s) := fun s hs' => by
    have hm : (i : ℕ) * 256 + s < 1024 := by omega
    rw [← h60, evalE_held y x c π (by decide) (by rw [hs60]; exact hm), aValR_60 y _ hm, φ_apply]
    rw [flat_fm _ i s hs' hm]
    unfold cf
    rw [dif_pos hs']
    rfl
  have hZ : ∀ j : Fin 4, ∀ s < 256, program.evalE (program.reader E) 0
      (.leaf (MldsaRingRelation.z program)) ((j : ℕ) * 256 + s) = φ (cf (y.z.get j) s) :=
    fun j s hs' => by
      have hj := j.isLt
      have hm : (j : ℕ) * 256 + s < 1024 := by omega
      rw [← h57, ← evalE_pull E (MldsaRingHonest.aV (program := program) 57 (by simp)) _]
      change Native.rdA (pull E) 57 _ = _
      rw [rdA_58 (readsA_pull y x c π) hm]
      rw [flat_fmz _ j s hs' hm]
      unfold cf
      rw [dif_pos hs']
      exact φ_centered _
  have hC : ∀ s < 256, program.evalE (program.reader E) 0 (.leaf (MldsaRingRelation.c program)) (2 * s) -
      2 * program.evalE (program.reader E) 0 (.leaf (MldsaRingRelation.c program)) (2 * s + 1) =
        φ (cf cP s) := fun s hs' => by
    rw [← h59, evalE_held y x c π (by decide) (by rw [hs59]; omega),
      evalE_held y x c π (by decide) (by rw [hs59]; omega), aValR_59 y _ (by omega),
      aValR_59 y _ (by omega)]
    unfold cA cf
    rw [dif_pos hs']
    simp only [show 2 * s / 2 = s by omega, show 2 * s % 2 = 0 by omega,
      show (2 * s + 1) / 2 = s by omega, show (2 * s + 1) % 2 = 1 by omega, cP,
      MLDSA44.coeff_ofCoeff]
    exact ternary_sub _ (c_ternary y _)
  have hA : ∀ j : Fin 4, program.evalE (program.reader E) 0 (.leaf (MldsaRingRelation.aHat program))
      ((i : ℕ) * 1024 + ((j : ℕ) * 256 + k)) =
        φ ((((MLDSA44.expandABounded _root_.MLDSA.mldsa44 y.key.rho).get i).get j).coeffs.get
          ⟨k, hk⟩) := fun j => by
    have hj := j.isLt
    rw [evalE_member y x c π (by simp) (by rw [(MldsaRingRelation.sizes (program := program)).1]; omega),
      honestVal_aHat, show (i : ℕ) * 1024 + ((j : ℕ) * 256 + k) = ((i : ℕ) * 4 + j) * 256 +
        (⟨k, hk⟩ : Fin 256) by simp only; ring, keyEntry_aHat, φ_apply]
    rfl
  have hT : program.evalE (program.reader E) 0 (.leaf (MldsaRingRelation.t1 program))
      ((i : ℕ) * 256 + k) = φ ((_root_.MLDSA.Concrete.ntt (MLDSA44.Native.Rows.prims.power2RoundShift
        (y.key.t1.get i))).coeffs.get ⟨k, hk⟩) := by
    rw [evalE_member y x c π (by simp) (by rw [(MldsaRingRelation.sizes (program := program)).2.1]; omega),
      honestVal_t1, show (i : ℕ) * 256 + k = (i : ℕ) * 256 + (⟨k, hk⟩ : Fin 256) from rfl,
      keyEntry_t1, φ_apply]
    rfl
  have hntt : ∀ (f : _root_.MLDSA.Rq) (g : ℕ → (interp 0).K), (∀ s < 256, g s = φ (cf f s)) →
      Ops.nttScheme 256 ((interp 0).decode 1753) g k =
        φ ((_root_.MLDSA.Concrete.ntt f).coeffs.get ⟨k, hk⟩) := fun f g hg => by
    rw [nttScheme_congr hg, hψ, nttScheme_map, nttScheme_eq_ntt f (cf_get f) ⟨k, hk⟩]
  rw [hntt (w.get i) _ hW, Finset.sum_congr rfl fun j _ => by rw [hA j, hntt _ _ (hZ j)], hT,
    hntt cP _ hC]
  have key := congrArg φ (ntt_honestW y.key y.expandAWithin y.c y.z i ⟨k, hk⟩)
  simp only [map_sub, map_sum, map_mul] at key
  exact key

/-- **`signature.relation.0 … 3` hold** at the honest values. -/
theorem sig_holds {q : ℕ} (hq : q ∈ [1, 2, 3, 4]) :
    program.HoldsAt E (program.predicate q).body := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact sig_row y x c π 0
  · exact sig_row y x c π 1
  · exact sig_row y x c π 2
  · exact sig_row y x c π 3

end Rows

end GordieHowe.MLDSA44.Ring.Native
