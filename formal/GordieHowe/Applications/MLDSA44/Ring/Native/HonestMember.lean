-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.HonestRelation
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Select

@[expose] public section

/-!
# GordieHowe: the selected member of the native ML-DSA-44 ring programs at the honest values

The member checks of a native ML-DSA-44 ring program (`lib/gordiehowe/examples/rings/mldsa_ring.h`,
`select_member`) at the source environment of the honest values, at a statement holding the
ring's rows (`RowsOf`, which the frontend's statement `stmtOf` holds, `rowsOf_stmtOf`):

* **The index bits** (`idxOf_honest`) name the signer's position; their check
  `member.select.index.boolean` holds (`idxBool_honest`).
* **`member.mu.boolean`** holds (`muBool_honest`): the committed `μ` bits are bits.
* **`member.select`** holds (`select_honest`): the record (`member.a_hat ‖ member.t1 ‖` the `μ`
  limbs) is the signer's row of the table, coordinate by coordinate (`record_honest`), so the
  record's fingerprint is the selected row's at every challenge `γ`
  (`TableSelect.evalE_lhs`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits GordieHowe.Ring RealizedProgram

set_option linter.unusedSectionVars false

variable {msgLen : ℕ}

/-- **The low bits of a natural**: `Σ_{i < t} (n / 2^i mod 2) 2^i = n mod 2^t`. -/
theorem idxVal_bits (n : ℕ) : ∀ t, idxVal (fun i => n / 2 ^ i % 2) t = n % 2 ^ t
  | 0 => by simp [idxVal, Nat.mod_one]
  | t + 1 => by
    rw [idxVal_succ, idxVal_bits n t, Nat.mod_pow_succ]
    ring

/-- **A sum of bits weighted by powers of two, cast into a field**, is the cast of the natural. -/
theorem cast_muLimb {K : Type*} [Field K] (mu : _root_.MLDSA.Bytes 64) (l : ℕ) :
    ∑ b : Fin 22, (2 : K) ^ (b : ℕ) *
        (if l * 22 + (b : ℕ) < 512 then ((muBitNat mu (l * 22 + b) : ℕ) : K) else 0) =
      ((muLimb mu l : ℕ) : K) := by
  unfold muLimb
  push_cast
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [show 22 * l + (b : ℕ) = l * 22 + b by ring]
  split_ifs with h
  · ring
  · unfold muBitNat
    rw [dif_neg h]
    simp

set_option hygiene false in
local notation "nat" => MldsaRingEmbed.nat program

set_option hygiene false in
local notation "vMu" => MldsaRingFront.muA program

set_option hygiene false in
local notation "vI" => (TableSelect.shape program).idx

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program] [MldsaRingHonest program]
  {F0 FH : FieldInterp} [QField F0] [HField FH] [Native.MldsaAAlgebra nat] [hN : Native.MldsaNativeHonest nat F0 FH]
  [MldsaHHonest nat] [MldsaHShuffle nat] [MldsaHSelHonest nat] [MldsaHConsts nat FH]
  [MldsaHNativeData FH]

set_option hygiene false in
local notation "interp" => mldsaInterpOf F0 FH

variable (y : RingIn msgLen) (x : program.Valuation interp) (c : ∀ k, (program.layout interp).Ch k)
  (π : (program.layout interp).Pads)

set_option hygiene false in
local notation "E" => program.srcEnv interp x (honestVal program F0 FH y) c π

/-- The honest value of `member.mu`. -/
theorem honestVal_mu (j : ℕ) :
    castElt (b := 0) (honestVal program F0 FH y vMu j) = ((muBitNat y.mu j : ℕ) : (interp 0).K) := by
  have hd := MldsaRingHonest.member_nodup (program := program)
  have hf := (MldsaRingHonest.memberCells (program := program) vMu (by simp)).2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  unfold honestVal
  rw [if_neg (fun h => hd.1.2.1 h.symm), if_neg (fun h => hd.2.1.1 h.symm), if_pos rfl]
  exact castElt_castElt_of_eq hf.symm _

/-- The honest value of the index bits. -/
theorem honestVal_idx (j : ℕ) :
    castElt (b := 0) (honestVal program F0 FH y vI j) =
      ((y.w.idx / 2 ^ j % 2 : ℕ) : (interp 0).K) := by
  have hd := MldsaRingHonest.member_nodup (program := program)
  have hf := (MldsaRingHonest.memberCells (program := program) vI (by simp)).2
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at hd
  unfold honestVal
  rw [if_neg (fun h => hd.1.2.2 h.symm), if_neg (fun h => hd.2.1.2 h.symm),
    if_neg (fun h => hd.2.2.1 h.symm), if_pos rfl]
  exact castElt_castElt_of_eq hf.symm _

/-- **`member.mu` reads the bits of the signer's `μ`.** -/
theorem evalE_mu {t : ℕ} (ht : t < 512) :
    program.evalE (program.reader E) 0 (.leaf vMu) t = ((muBitNat y.mu t : ℕ) : (interp 0).K) := by
  rw [evalE_member y x c π (by simp) (by rw [MldsaRingFront.muSize]; exact ht), honestVal_mu]

/-- **The index bits read the bits of the signer's position.** -/
theorem evalE_idx {i : ℕ} (hi : i < 6) :
    program.evalE (program.reader E) 0 (.leaf vI) i = ((y.w.idx / 2 ^ i % 2 : ℕ) : (interp 0).K) := by
  have hs := (TableSelect.sizes (program := program)).2.2.1
  rw [MldsaRingFront.shape.2.2.2.2.2.2.2.2] at hs
  rw [evalE_member y x c π (by simp) (by rw [hs]; exact hi), honestVal_idx]

theorem bit_lt (n i : ℕ) : n / 2 ^ i % 2 < 8380417 := (Nat.mod_lt _ (by norm_num)).trans (by norm_num)

/-- **The index bits name the signer's position** (`TableSelect.idxOf`). -/
theorem bitsOf_honest {i : ℕ} (hi : i < (TableSelect.shape program).bits) :
    TableSelect.bitsOf 0 E i = y.w.idx / 2 ^ i % 2 := by
  have h6 := (MldsaRingFront.shape (program := program)).2.2.2.2.2.2.2.2
  unfold TableSelect.bitsOf
  rw [if_pos hi, evalE_idx y x c π (by rw [h6] at hi; exact hi)]
  exact QField.toNat_natCast (bit_lt _ _)

theorem idxOf_honest : TableSelect.idxOf 0 E = y.w.idx := by
  have h6 := (MldsaRingFront.shape (program := program)).2.2.2.2.2.2.2.2
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
  rw [hl, idxVal_bits, h6, Nat.mod_eq_of_lt (by have := y.idx_lt_64; norm_num; omega)]

/-- **The index bits' check holds** (`member.select.index.boolean`). -/
theorem idxBool_honest :
    program.HoldsAt E (program.predicate (TableSelect.shape program).idxPred).body := by
  obtain ⟨t, hb⟩ := TableSelect.idxBool (program := program)
  rw [HoldsAt, hb]
  intro i hi
  have hs := (TableSelect.sizes (program := program)).2.2.1
  rw [exprLen_mul, exprLen_leaf, hs, MldsaRingFront.shape.2.2.2.2.2.2.2.2] at hi
  unfold evalWith
  rw [domainField_shape, evalE_mul, evalE_idx y x c π hi]
  rcases Nat.mod_two_eq_zero_or_one (y.w.idx / 2 ^ i) with h | h <;> rw [h] <;> simp

/-- **`member.mu.boolean` holds**: the committed `μ` bits are bits. -/
theorem muBool_honest : program.HoldsAt E (program.predicate 10).body := by
  obtain ⟨hc, -, -⟩ := MldsaRingFront.muBool (program := program)
  refine holdsWith_of_boolCheck hc fun i hi => ?_
  rw [MldsaRingFront.muSize] at hi
  change program.evalE _ (program.domainField 0) _ i = 0 ∨ program.evalE _ (program.domainField 0) _ i = 1
  rw [MldsaRingFront.domains.1, evalE_mu y x c π hi]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (muBitNat_le y.mu i) with h | h <;> rw [h] <;> simp

/-- **The signer's key is the ring's key at its position.** -/
theorem keyAt_idx : y.x.keyAt y.w.idx = y.key := RingStmt.keyAt_eq y.idx_lt_length

/-- **The signer's `μ` is its key's `μ` of the message representative** (`muOf`). -/
theorem muOf_key : muOf (y.x.keyAt y.w.idx) y.x.msg = y.mu := by
  rw [keyAt_idx]
  rfl

/-- **The record is the signer's row** of the table, at a statement holding the ring's rows. -/
theorem record_honest (hx : RowsOf y.x x) {cc : ℕ} (hc : cc < 5144) :
    program.evalE (program.reader E) 0 (.ref 1) cc = rowEntry x y.w.idx cc := by
  have hidx := y.idx_lt_64
  unfold rowEntry
  by_cases h1 : cc < 4096
  · rw [rec_aHat _ h1, if_pos (by omega), hx.keys _ hidx _ (by omega), keyAt_idx,
      evalE_member y x c π (by simp)
        (by rw [(MldsaRingRelation.sizes (program := program)).1]; exact h1), honestVal_aHat]
  by_cases h2 : cc < 5120
  · obtain ⟨d, hd, rfl⟩ : ∃ d < 1024, cc = 4096 + d := ⟨cc - 4096, by omega, by omega⟩
    rw [rec_t1 _ hd, if_pos h2, hx.keys _ hidx _ h2, keyAt_idx,
      evalE_member y x c π (by simp)
        (by rw [(MldsaRingRelation.sizes (program := program)).2.1]; exact hd), honestVal_t1]
  · obtain ⟨l, hl, rfl⟩ : ∃ l < 24, cc = 5120 + l := ⟨cc - 5120, by omega, by omega⟩
    rw [rec_mu E hl, if_neg h2, Nat.add_sub_cancel_left, hx.mu _ hidx _ hl, muOf_key,
      ← cast_muLimb y.mu l]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [evalE_mu y x c π h]
    · rfl

/-- **`member.select` holds** at the honest values, at a statement holding the ring's rows: the
record is the selected row (`record_honest`), so both fingerprints agree
(`TableSelect.evalE_lhs`). -/
theorem select_honest (hx : RowsOf y.x x) :
    program.HoldsAt E (program.predicate (TableSelect.shape program).pred).body := by
  have := selectField_shape (program := program) (F0 := F0) (FH := FH)
  obtain ⟨-, hchal, -, -, hrec, hparts, hmap, hrows, h6⟩ := MldsaRingFront.shape (program := program)
  obtain ⟨T, F, tg, hbody, hT, hF⟩ := TableShape.bodyOk_spec (TableSelect.bodyOk (program := program))
  have hbits : ∀ i < (TableSelect.shape program).bits, TableSelect.bitsOf 0 E i ≤ 1 ∧
      program.evalE (program.reader E) 0 (.leaf (TableSelect.shape program).idx) i =
        (TableSelect.bitsOf 0 E i : (interp 0).K) := fun i hi => by
    rw [bitsOf_honest y x c π hi]
    refine ⟨Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num)), ?_⟩
    rw [h6] at hi
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
    rwa [hmap, nativeMap_facts.1] at this
  congr 1
  unfold TableSelect.recOf TableSelect.mapOf
  rw [hrec, record_honest y x c π hx hc', hmap,
    rowApply_id _ _ nativeMap_facts.2 _ (by rw [nativeMap_facts.1]; exact hc')]
  have hidx : TableSelect.rowIdx 0 E = y.w.idx := by
    unfold TableSelect.rowIdx
    rw [hrows, idxOf_honest y x c π, if_pos y.idx_lt_64]
  rw [hidx]
  unfold TableSelect.rowAt rowEntry
  rw [hparts]
  simp only [rowOf]
  by_cases h' : cc < 5120
  · rw [if_pos h', if_pos h']
    unfold RealizedProgram.rowRead
    rw [read_of_opaque_nil E TableSelect.values_pos MldsaRingStmt.keysKind]
    rfl
  · rw [if_neg h', if_neg h', if_pos (by omega)]
    unfold RealizedProgram.rowRead
    rw [read_of_opaque_nil E TableSelect.values_pos MldsaRingStmt.muKind]
    rfl

end GordieHowe.MLDSA44.Ring.Native
