-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.HonestValues
public import GordieHoweCerts.Applications.MLDSA44.Ring.Carrier.Frontend.Select
public import GordieHoweCerts.Applications.MLDSA44.Ring.Native.HonestMember

@[expose] public section

/-!
# GordieHowe: the selected member of the ML-DSA-44 ring carriers at the honest values

The member checks of an ML-DSA-44 ring carrier (`lib/gordiehowe/examples/rings/mldsa_ring.h`,
`select_member`) at the source environment of the honest values, at a statement holding the
ring's carrier rows (`RowsOf`, which the frontend's statement `stmtOf` holds, `rowsOf_stmtOf`):

* **The index bits** (`idxOf_honest`) name the signer's position; their check
  `member.select.index.boolean` holds (`idxBool_honest`).
* **`member.mu.boolean`** holds (`muBool_honest`): the committed `μ` bits are bits.
* **`member.select`** holds (`select_honest`): the record (`member.a_hat ‖ member.t1 ‖` the `μ`
  limbs) is the carriers' row map (`carrierMap`: the scheme-order transform at `ψ = psi512` of
  each key block, the identity on the limbs) applied to the signer's row of the table, coordinate
  by coordinate (`record_honest`), so the record's fingerprint is the selected row's at every
  challenge `γ` (`TableSelect.evalE_lhs`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt muBitNat muBitNat_le muLimb muOf)
open MLDSA44.Emulated (MldsaEAlgebra)

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

/-- **The identifiers of a carrier's table selection** (decided per carrier): the index bits are
value `59`, the selection predicate `0`, the index bits' check predicate `11`. -/
class MldsaCarrierSelect (program : RealizedProgram) [TableSelect program] : Prop where
  /-- The index bits are value `59`. -/
  idx59 : (TableSelect.shape program).idx = 59

variable {program : RealizedProgram} [CarrierHEmbed program] [CarrierAEmbed program]
  [MldsaEAlgebra (CarrierAEmbed.emu program)] [MldsaCarrierHonest program]
  [MldsaCarrierRelation program] [MldsaRingStmt program] [TableSelect program]
  [MldsaCarrierFront program] [MldsaCarrierSelect program]
  {F0 FH : FieldInterp} [RealizedProgram.PrimeCastField F0 pGold] [HField FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

set_option hygiene false in
local notation "nat" => CarrierHEmbed.nat program

set_option hygiene false in
local notation "qD" => MldsaCarrierHonest.qD program

variable [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]

variable (y : RingIn msgLen) (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
  (π : (program.layout interp).Pads)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH y) c π

/-- **A member value or a quotient digit reads its honest value** at the source environment. -/
theorem evalE_member {v : ℕ} (hv : v ∈ [56, 57, 58, 59, 66] ++ (qD).ids) {j : ℕ}
    (hj : j < (program.value v).size) :
    program.evalE (program.reader E) 0 (.leaf v) j = castElt (b := 0) (honestVal program F0 FH y v j) := by
  rw [evalE_leaf, reader_srcEnv_of_privCellB x _ c π
    (MldsaCarrierHonest.member_cells (program := program) v hv).1 hj]

/-- **`member.mu` reads the bits of the signer's `μ`.** -/
theorem evalE_mu {t : ℕ} (ht : t < 512) :
    program.evalE (program.reader E) 0 (.leaf 58) t = ((muBitNat y.mu t : ℕ) : (interp 0).K) := by
  rw [evalE_member y x c π (by simp) (by rw [MldsaCarrierFront.muSize]; exact ht),
    (honestVal_member y t).2.2.1]

/-- **The index bits read the bits of the signer's position.** -/
theorem evalE_idx {i : ℕ} (hi : i < 6) :
    program.evalE (program.reader E) 0 (.leaf 59) i = ((y.w.idx / 2 ^ i % 2 : ℕ) : (interp 0).K) := by
  have hs := (TableSelect.sizes (program := program)).2.2.1
  rw [MldsaCarrierFront.shape.2.2.2.2.2.2.2.2, MldsaCarrierSelect.idx59] at hs
  rw [evalE_member y x c π (by simp) (by rw [hs]; exact hi), (honestVal_member y i).2.2.2.1]

theorem bit_lt_gold (n i : ℕ) : n / 2 ^ i % 2 < pGold :=
  (Nat.mod_lt _ (by norm_num)).trans (by norm_num [pGold])

/-- **The index bits are the bits of the signer's position** (`TableSelect.bitsOf`). -/
theorem bitsOf_honest {i : ℕ} (hi : i < (TableSelect.shape program).bits) :
    TableSelect.bitsOf 0 E i = y.w.idx / 2 ^ i % 2 := by
  have h6 := (MldsaCarrierFront.shape (program := program)).2.2.2.2.2.2.2.2
  unfold TableSelect.bitsOf
  rw [if_pos hi, MldsaCarrierSelect.idx59, evalE_idx y x c π (by rw [h6] at hi; exact hi)]
  exact RealizedProgram.PrimeCastField.toNat_natCast (p := pGold) _ (bit_lt_gold _ _)

/-- **The index bits name the signer's position.** -/
theorem idxOf_honest : TableSelect.idxOf 0 E = y.w.idx := by
  have h6 := (MldsaCarrierFront.shape (program := program)).2.2.2.2.2.2.2.2
  unfold TableSelect.idxOf
  have h : TableSelect.bitsOf 0 E = fun i =>
      if i < (TableSelect.shape program).bits then y.w.idx / 2 ^ i % 2 else 0 := by
    funext i
    by_cases hi : i < (TableSelect.shape program).bits
    · rw [bitsOf_honest y x c π hi, if_pos hi]
    · unfold TableSelect.bitsOf
      rw [if_neg hi, if_neg hi]
  rw [h]
  have hl : idxVal (fun i => if i < (TableSelect.shape program).bits then y.w.idx / 2 ^ i % 2 else 0)
      (TableSelect.shape program).bits = idxVal (fun i => y.w.idx / 2 ^ i % 2)
        (TableSelect.shape program).bits := by
    unfold idxVal
    exact Finset.sum_congr rfl fun i hi => by
      simp only [if_pos (Finset.mem_range.1 hi)]
  rw [hl, Native.idxVal_bits, h6, Nat.mod_eq_of_lt (by have := y.idx_lt_64; norm_num; omega)]

/-- **The index bits' check holds** (`member.select.index.boolean`). -/
theorem idxBool_honest :
    program.HoldsAt E (program.predicate (TableSelect.shape program).idxPred).body := by
  obtain ⟨t, hb⟩ := TableSelect.idxBool (program := program)
  rw [HoldsAt, hb]
  intro i hi
  have hs := (TableSelect.sizes (program := program)).2.2.1
  rw [exprLen_mul, exprLen_leaf, hs, MldsaCarrierFront.shape.2.2.2.2.2.2.2.2] at hi
  unfold evalWith
  rw [domainField_shape, evalE_mul, MldsaCarrierSelect.idx59, evalE_idx y x c π hi]
  rcases Nat.mod_two_eq_zero_or_one (y.w.idx / 2 ^ i) with h | h <;> rw [h] <;> simp

/-- **`member.mu.boolean` holds**: the committed `μ` bits are bits. -/
theorem muBool_honest :
    program.HoldsAt E (program.predicate (MldsaCarrierFront.muBoolPred program)).body := by
  obtain ⟨hc, -, -⟩ := MldsaCarrierFront.muBool (program := program)
  refine holdsWith_of_boolCheck hc fun i hi => ?_
  rw [MldsaCarrierFront.muSize] at hi
  change program.evalE _ (program.domainField 0) _ i = 0 ∨ program.evalE _ (program.domainField 0) _ i = 1
  rw [MldsaCarrierFront.domains.1, evalE_mu y x c π hi]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (muBitNat_le y.mu i) with h | h <;> rw [h] <;> simp

/-- **The honest spectra at a key block**: coordinate `cc < 5120` is the scheme-order transform of
the signer's carrier row's block. -/
theorem specE_lt (K : Type*) [Field K] {cc : ℕ} (hc : cc < 5120) :
    specE y K cc = Ops.nttScheme 256 (psi512 : K)
      (fun k => ((keyEntry y.key (256 * (cc / 256) + k) : ℕ) : K)) (cc % 256) := by
  unfold specE
  rw [if_pos hc]

/-- **The row map on a key block of a ring's row**: coordinate `cc < 5120` of the row map applied
to row `y.w.idx` of a statement holding the ring's carrier rows is the honest spectrum. -/
theorem rowApply_key (hx : RowsOf y.x x) {cc : ℕ} (hc : cc < 5120) :
    rowApply (interp 0).decode carrierMap (rowEntry x y.w.idx) cc = specE y (interp 0).K cc := by
  have h := rowApply_carrier_key (interp 0).decode (rowEntry x y.w.idx) (b := cc / 256)
    (m := cc % 256) (by omega) (Nat.mod_lt _ (by norm_num))
  rw [show 256 * (cc / 256) + cc % 256 = cc by omega] at h
  rw [h, decode_psi, specE_lt y _ hc]
  refine nttScheme_congr _ (fun k hk => ?_) _
  rw [rowEntry, if_pos (by omega), hx.keys _ y.idx_lt_64 _ (by omega), Native.keyAt_idx]

/-- **The record is the row map applied to the signer's row** of the table, at a statement
holding the ring's carrier rows. -/
theorem record_honest (hx : RowsOf y.x x) {cc : ℕ} (hc : cc < 5144) :
    program.evalE (program.reader E) 0 (.ref 1) cc =
      rowApply (interp 0).decode carrierMap (rowEntry x y.w.idx) cc := by
  have hidx := y.idx_lt_64
  by_cases h1 : cc < 4096
  · rw [rec_aHat _ h1, evalE_member y x c π (by simp)
      (by rw [(MldsaCarrierRelation.sizes (program := program)).1]; exact h1),
      (honestVal_member y cc).1, if_pos h1,
      rowApply_key y x hx (by omega)]
  by_cases h2 : cc < 5120
  · obtain ⟨d, hd, rfl⟩ : ∃ d < 1024, cc = 4096 + d := ⟨cc - 4096, by omega, by omega⟩
    rw [rec_t1 _ hd, evalE_member y x c π (by simp)
      (by rw [(MldsaCarrierRelation.sizes (program := program)).2.1]; exact hd),
      (honestVal_member y d).2.1, if_pos hd,
      rowApply_key y x hx h2]
  · obtain ⟨l, hl, rfl⟩ : ∃ l < 24, cc = 5120 + l := ⟨cc - 5120, by omega, by omega⟩
    rw [rec_mu E hl, rowApply_carrier_mu _ _ hl, rowEntry, if_neg h2, if_pos (by omega),
      Nat.add_sub_cancel_left, hx.mu _ hidx _ hl, Native.muOf_key, ← Native.cast_muLimb y.mu l]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [evalE_mu y x c π h]
    · rfl

/-- **The selected row of the table is the signer's row**, read off the statement. -/
theorem rowAt_honest :
    TableSelect.rowAt 0 E (TableSelect.rowIdx 0 E) = rowEntry x y.w.idx := by
  obtain ⟨-, -, -, -, -, hparts, -, hrows, -⟩ := MldsaCarrierFront.shape (program := program)
  have hidx : TableSelect.rowIdx 0 E = y.w.idx := by
    unfold TableSelect.rowIdx
    rw [hrows, idxOf_honest y x c π, if_pos y.idx_lt_64]
  rw [hidx]
  funext cc
  unfold TableSelect.rowAt rowEntry
  rw [hparts]
  simp only [rowOf]
  by_cases h' : cc < 5120
  · rw [if_pos h', if_pos h']
    unfold RealizedProgram.rowRead
    rw [read_opaque E MldsaRingStmt.keysKind]
    rfl
  · rw [if_neg h', if_neg h']
    by_cases h'' : cc < 5144
    · rw [if_pos (by omega), if_pos h'']
      unfold RealizedProgram.rowRead
      rw [read_opaque E MldsaRingStmt.muKind]
      rfl
    · rw [if_neg (by omega), if_neg h'']

/-- **`member.select` holds** at the honest values, at a statement holding the ring's carrier
rows: the record is the row map applied to the selected row (`record_honest`, `rowAt_honest`), so
both fingerprints agree (`TableSelect.evalE_lhs`). -/
theorem select_honest (hx : RowsOf y.x x) :
    program.HoldsAt E (program.predicate (TableSelect.shape program).pred).body := by
  have := selectField_shape (program := program) (F0 := F0) (FH := FH)
  obtain ⟨-, -, -, -, hrec, -, hmap, -, h6⟩ := MldsaCarrierFront.shape (program := program)
  obtain ⟨T, F, tg, hbody, hT, hF⟩ := TableShape.bodyOk_spec (TableSelect.bodyOk (program := program))
  have hbits : ∀ i < (TableSelect.shape program).bits, TableSelect.bitsOf 0 E i ≤ 1 ∧
      program.evalE (program.reader E) 0 (.leaf (TableSelect.shape program).idx) i =
        (TableSelect.bitsOf 0 E i : (interp 0).K) := fun i hi => by
    rw [bitsOf_honest y x c π hi]
    refine ⟨Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num)), ?_⟩
    rw [h6] at hi
    rw [MldsaCarrierSelect.idx59]
    exact evalE_idx y x c π hi
  obtain ⟨hlen, hval⟩ := TableSelect.evalE_lhs domainField_shape E hT hF hbits
  rw [HoldsAt, hbody]
  intro i hi
  rw [hlen] at hi
  obtain rfl : i = 0 := by omega
  unfold evalWith
  rw [domainField_shape, hval, TableSelect.evalE_zero domainField_shape E, sub_eq_zero]
  refine Finset.sum_congr rfl fun cc hc => ?_
  have hc' : cc < 5144 := by
    have := Finset.mem_range.1 hc
    unfold TableSelect.W at this
    rwa [hmap, carrierMap_width] at this
  congr 1
  unfold TableSelect.recOf TableSelect.mapOf
  rw [hrec, record_honest y x c π hx hc', hmap, rowAt_honest y x c π]

end GordieHowe.MLDSA44.Ring.Carrier
