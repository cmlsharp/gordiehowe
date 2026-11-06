-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Readings

@[expose] public section

/-!
# GordieHowe frontend: the selected member of the native ML-DSA-44 ring programs

The public table's selection (`select_member`, `lib/gordiehowe/examples/rings/mldsa_ring.h`;
`GordieHowe.RealizedProgram.TableSelect`) read at the native ML-DSA-44 ring programs: without the
selection's event (`TableSelect.SelBad` at `member.table.gamma`), the record (`member.a_hat ‖
member.t1 ‖` the `24` limbs of `member.mu`) is row `idx` of the statement, `idx` the natural the
index bits name (`TableSelect.idxOf`, below `64`).

* `selectField`: the field facts the selection reads in `F_q^m` (`q − 1` is `−1`).
* `ref0_eq`, `rec_aHat`, `rec_t1`, `rec_mu`: the record's coordinates (the limbs
  `Σ_b 2^b μ_{22 l + b}` of the zero-extended `μ` bits).
* `record_row`: the record is the selected row (`TableSelect.record_eq_of_not_bad`, the identity
  row map `nativeMap`).
* `aHatVals_eq`, `t1HatVals_eq`: at a statement holding a ring's rows (`RowsOf`), the committed
  `â` and `t̂` are the selected key's `Â` and `NTT(2^d · t1)`.
* `muA_eq`: the committed `μ` bits are those of the selected key's `μ`: each limb is a natural
  below `2^22 < q`, so the limbs' equality in the field is their equality as naturals, which gives
  the bits (`Bits.natOfBits_injective`).
-/

namespace GordieHowe.MLDSA44.Ring.Native

open GordieHowe.Bits GordieHowe.Ring RealizedProgram

/-- **A Boolean vector's natural, cast into the field**, is its digit sum. -/
theorem cast_natOfBits {K : Type*} [Field K] [DecidableEq K] {n : ℕ} {w : BitWires K n}
    (hw : AllBool w) : ((natOfBits w : ℕ) : K) = ∑ i : Fin n, (2 : K) ^ (i : ℕ) * w i := by
  unfold natOfBits
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rcases hw i with h | h <;> simp [h]

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaRingEmbed program] [MldsaRingRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaRingFront program]
  {F0 FH : RealizedProgram.FieldInterp} [QField F0]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

set_option hygiene false in
local notation "vMu" => MldsaRingFront.muA program

/-- **The field facts the selection reads in `F_q^m`**: `q − 1` decodes to `−1`, `0` and `1` to
themselves and read back as `0` and `1`. -/
theorem selectField : RealizedProgram.SelectField (interp 0) 8380416 where
  decode_negOne := decode_m1
  decode_zero := (QField.decode_lt (F0 := F0) 0 (by norm_num)).trans Nat.cast_zero
  decode_one := (QField.decode_lt (F0 := F0) 1 (by norm_num)).trans Nat.cast_one
  toNat_zero := by
    have h := QField.toNat_natCast (F0 := F0) (k := 0) (by norm_num)
    rw [Nat.cast_zero] at h
    exact h
  toNat_one := by
    have h := QField.toNat_natCast (F0 := F0) (k := 1) (by norm_num)
    rw [Nat.cast_one] at h
    exact h

/-- The selection's field facts at the table's `−1`. -/
theorem selectField_shape :
    RealizedProgram.SelectField (interp 0) (TableSelect.shape program).mOne := by
  rw [MldsaRingFront.shape.2.2.1]
  exact selectField

/-- The table's domain is field `0`. -/
theorem domainField_shape : program.domainField (TableSelect.shape program).dom = 0 := by
  rw [MldsaRingFront.shape.1, MldsaRingFront.domains.1]

/-! ## The record -/

/-- **Shared expression `0`**: the `μ` bits below `512`, zeros up to `528`. -/
theorem ref0_eq (e : program.Env interp) {t : ℕ} (ht : t < 528) :
    program.evalE (program.reader e) 0 (.ref 0) t =
      if t < 512 then program.evalE (program.reader e) 0 (.leaf vMu) t else 0 := by
  haveI := selectField_shape (program := program) (F0 := F0) (FH := FH)
  have hz : program.evalE (program.reader e) 0 (.leaf 0) 0 = 0 := by
    have := TableSelect.evalE_zero (f := 0) domainField_shape e
    rwa [MldsaRingFront.shape.2.2.2.1] at this
  rw [RealizedProgram.evalE_ref MldsaRingRelation.refsOrdered _ _
      (by have := MldsaRingFront.lt513 (program := program); omega),
    MldsaRingFront.expr0, evalE_reindex, evalE_concat, exprLen_leaf, MldsaRingFront.muSize]
  by_cases h : t < 512
  · have he : IndexMap.entry [(0, 1, 513), (512, 0, 15)] t = t := by
      simp only [IndexMap.entry]
      split_ifs <;> omega
    rw [he, if_pos h, if_pos h]
  · have he : IndexMap.entry [(0, 1, 513), (512, 0, 15)] t = 512 := by
      simp only [IndexMap.entry]
      split_ifs <;> omega
    rw [he, if_neg (lt_irrefl _), if_neg h, Nat.sub_self, hz]

/-- The record expression's first steps: shared expression `1` at a coordinate below `5144`. -/
theorem ref1_eq (rd : program.Valuation interp) {c : ℕ} (hc : c < 5144) :
    program.evalE rd 0 (.ref 1) c =
      if c < 5120 then
        (if c < 4096 then program.evalE rd 0 (.leaf (MldsaRingRelation.aHat program)) c
          else program.evalE rd 0 (.leaf (MldsaRingRelation.t1 program)) (c - 4096))
      else program.evalE rd 0 (.apply (.batched 24 (.fromDigits 22 2)) (.ref 0)) (c - 5120) := by
  rw [RealizedProgram.evalE_ref MldsaRingRelation.refsOrdered _ _
      (by have := MldsaRingFront.lt513 (program := program); omega),
    MldsaRingFront.expr1, evalE_reindex, IndexMap.entry_step_one hc, Nat.zero_add, evalE_concat,
    exprLen_reindex, IndexMap.size_single]
  by_cases h : c < 5120
  · rw [if_pos h, if_pos h, evalE_reindex, IndexMap.entry_step_one h, Nat.zero_add, evalE_concat,
      exprLen_reindex, IndexMap.size_single]
    by_cases h' : c < 4096
    · rw [if_pos h', if_pos h', evalE_reindex, IndexMap.entry_step_one h', Nat.zero_add]
    · rw [if_neg h', if_neg h', evalE_reindex, IndexMap.entry_step_one (by omega), Nat.zero_add]
  · rw [if_neg h, if_neg h, evalE_reindex, IndexMap.entry_step_one (by omega), Nat.zero_add]

/-- **The record's `â`**: coordinate `c < 4096` is `member.a_hat`'s. -/
theorem rec_aHat (rd : program.Valuation interp) {c : ℕ} (hc : c < 4096) :
    program.evalE rd 0 (.ref 1) c =
      program.evalE rd 0 (.leaf (MldsaRingRelation.aHat program)) c := by
  rw [ref1_eq rd (by omega), if_pos (by omega), if_pos hc]

/-- **The record's `t̂`**: coordinate `4096 + c` is `member.t1`'s coordinate `c`. -/
theorem rec_t1 (rd : program.Valuation interp) {c : ℕ} (hc : c < 1024) :
    program.evalE rd 0 (.ref 1) (4096 + c) =
      program.evalE rd 0 (.leaf (MldsaRingRelation.t1 program)) c := by
  rw [ref1_eq rd (by omega), if_pos (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

/-- **The record's limb `l`**: coordinate `5120 + l` is `Σ_b 2^b μ_{22 l + b}` of the
zero-extended `μ` bits. -/
theorem rec_mu (e : program.Env interp) {l : ℕ} (hl : l < 24) :
    program.evalE (program.reader e) 0 (.ref 1) (5120 + l) =
      ∑ b : Fin 22, (2 : (interp 0).K) ^ (b : ℕ) *
        (if l * 22 + (b : ℕ) < 512 then program.evalE (program.reader e) 0 (.leaf vMu) (l * 22 + b)
          else 0) := by
  have h2 : (interp 0).decode 2 = 2 :=
    (QField.decode_lt (F0 := F0) 2 (by norm_num)).trans (by norm_num)
  rw [ref1_eq _ (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
    evalE_apply_batched_fromDigits _ _ (by norm_num), h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ref0_eq e (by have := b.isLt; omega)]

/-! ## The selection -/

/-- **Coordinate `c` of row `j` of the table**, read in field `0` off a statement: `ring.keys`
below `5120`, `ring.mu` after. -/
def rowEntry (x : program.Valuation interp) (j c : ℕ) : (interp 0).K :=
  if c < 5120 then RealizedProgram.castElt (x (MldsaRingStmt.keys program) (j * 5120 + c))
  else RealizedProgram.castElt (x (MldsaRingStmt.mu program) (j * 24 + (c - 5120)))

/-- **The selected index is below `64`** where the source program holds. -/
theorem idxOf_lt64 {e : program.Env interp} (hs : program.SourceSatAt e) :
    TableSelect.idxOf 0 e < 64 := by
  haveI := selectField_shape (program := program) (F0 := F0) (FH := FH)
  have := TableSelect.idxOf_lt domainField_shape (TableSelect.preds_of_source hs)
  rwa [MldsaRingFront.shape.2.2.2.2.2.2.2.2] at this

/-- **The record is the selected row** wherever the source program holds and the selection's
event did not occur (`TableSelect.record_eq_of_not_bad`, the identity row map). -/
theorem record_row {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {c : ℕ} (hc : c < 5144) :
    program.evalE (program.reader e) 0 (.ref 1) c = rowEntry e.stmt (TableSelect.idxOf 0 e) c := by
  haveI := selectField_shape (program := program) (F0 := F0) (FH := FH)
  obtain ⟨-, hchal, -, -, hrec, hparts, hmap, hrows, -⟩ := MldsaRingFront.shape (program := program)
  have h := TableSelect.record_eq_of_not_bad domainField_shape (TableSelect.preds_of_source hs)
    (by rwa [hchal]) (c := c) (by unfold TableSelect.W; rw [hmap, nativeMap_facts.1]; exact hc)
  unfold TableSelect.recOf at h
  rw [hrec] at h
  rw [h]
  unfold TableSelect.mapOf
  rw [hmap, rowApply_id _ _ nativeMap_facts.2 _ (by rw [nativeMap_facts.1]; exact hc)]
  have hidx : TableSelect.rowIdx 0 e = TableSelect.idxOf 0 e := by
    unfold TableSelect.rowIdx
    rw [hrows, if_pos (idxOf_lt64 hs)]
  rw [hidx]
  unfold TableSelect.rowAt rowEntry
  rw [hparts]
  simp only [rowOf]
  by_cases h' : c < 5120
  · rw [if_pos h', if_pos h']
    unfold RealizedProgram.rowRead
    rw [read_of_opaque_nil e TableSelect.values_pos MldsaRingStmt.keysKind]
  · rw [if_neg h', if_neg h', if_pos (by omega)]
    unfold RealizedProgram.rowRead
    rw [read_of_opaque_nil e TableSelect.values_pos MldsaRingStmt.muKind]

variable {len : ℕ}

/-- **The committed `â` is the selected key's `Â`**, at a statement holding a ring's rows. -/
theorem aHatVals_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {x : RStmt len} (hrows : RowsOf x e.stmt) (i j : Fin 4)
    (k : Fin 256) : aHatVals (program.reader e) i j k =
      ((aHatNat (x.keyAt (TableSelect.idxOf 0 e)) i j k : ℕ) : (interp 0).K) := by
  have hi := i.isLt; have hj := j.isLt; have hk := k.isLt
  have hc : ((i : ℕ) * 4 + j) * 256 + k < 4096 := by omega
  unfold aHatVals
  rw [← rec_aHat _ hc, record_row hs hno (by omega), rowEntry, if_pos (by omega),
    hrows.keys _ (idxOf_lt64 hs) _ (by omega), keyEntry_aHat]

/-- **The committed `t̂` is the selected key's `NTT(2^d · t1)`**, at a statement holding a ring's
rows. -/
theorem t1HatVals_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {x : RStmt len} (hrows : RowsOf x e.stmt) (i : Fin 4)
    (k : Fin 256) : t1HatVals (program.reader e) i k =
      ((t1HatNat (x.keyAt (TableSelect.idxOf 0 e)) i k : ℕ) : (interp 0).K) := by
  have hi := i.isLt; have hk := k.isLt
  unfold t1HatVals
  rw [← rec_t1 _ (by omega), record_row hs hno (by omega), rowEntry, if_pos (by omega),
    hrows.keys _ (idxOf_lt64 hs) _ (by omega), keyEntry_t1]

/-- **The `μ` bits are bits** (`member.mu.boolean`). -/
theorem mu_bool {e : program.Env interp} (hs : program.SourceSatAt e) {t : ℕ} (ht : t < 512) :
    program.evalE (program.reader e) 0 (.leaf vMu) t = 0 ∨
      program.evalE (program.reader e) 0 (.leaf vMu) t = 1 := by
  obtain ⟨hc, hl, hsrc⟩ := MldsaRingFront.muBool (program := program)
  have h := RealizedProgram.bool_of_boolCheck hc
    (hs.preds _ (RealizedProgram.predicate_mem hl) hsrc) (i := t)
    (by rw [MldsaRingFront.muSize]; exact ht)
  rwa [MldsaRingFront.domains.1] at h

/-- **The committed `μ` bits are the selected key's `μ`**, at a statement holding a ring's rows:
bit `t` is `1` exactly when bit `t` of `μ = H(H(pk) ‖ M′)` is. -/
theorem muA_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {x : RStmt len} (hrows : RowsOf x e.stmt) {t : ℕ}
    (ht : t < 512) : program.evalE (program.reader e) 0 (.leaf vMu) t =
      if muBitNat (muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg) t = 1 then 1 else 0 := by
  set mu := muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg
  set rd := program.reader e
  have hlimb : ∀ l < 24,
      (fun b : Fin 22 => if l * 22 + (b : ℕ) < 512 then program.evalE rd 0 (.leaf vMu) (l * 22 + b)
        else (0 : (interp 0).K)) =
      fun b : Fin 22 => if muBitNat mu (22 * l + b) = 1 then 1 else 0 := by
    intro l hl
    have hw : AllBool (fun b : Fin 22 => if l * 22 + (b : ℕ) < 512 then
        program.evalE rd 0 (.leaf vMu) (l * 22 + b) else (0 : (interp 0).K)) := fun b => by
      dsimp only
      split_ifs with h
      · exact mu_bool hs h
      · exact .inl rfl
    have hcb : AllBool (fun b : Fin 22 =>
        if muBitNat mu (22 * l + b) = 1 then (1 : (interp 0).K) else 0) := fun b => by
      dsimp only
      split_ifs
      · exact .inr rfl
      · exact .inl rfl
    have hcl : natOfBits (fun b : Fin 22 =>
        if muBitNat mu (22 * l + b) = 1 then (1 : (interp 0).K) else 0) = muLimb mu l := by
      unfold natOfBits muLimb
      refine Finset.sum_congr rfl fun b _ => ?_
      beta_reduce
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (muBitNat_le mu (22 * l + b)) with h | h
      · rw [h, if_neg zero_ne_one, if_neg zero_ne_one, Nat.zero_mul]
      · rw [h, if_pos rfl, if_pos rfl, Nat.one_mul]
    have hrec := rec_mu e hl
    rw [record_row hs hno (by omega), rowEntry, if_neg (by omega), Nat.add_sub_cancel_left,
      hrows.mu _ (idxOf_lt64 hs) _ hl] at hrec
    have hcast := cast_natOfBits hw
    beta_reduce at hcast
    replace hrec := hrec.trans hcast.symm
    have hq : natOfBits (fun b : Fin 22 => if l * 22 + (b : ℕ) < 512 then
        program.evalE rd 0 (.leaf vMu) (l * 22 + b) else (0 : (interp 0).K)) = muLimb mu l :=
      (CharP.natCast_injOn_Iio (interp 0).K 8380417
        (show natOfBits _ < 8380417 from (natOfBits_lt _).trans (by norm_num))
        (show muLimb mu l < 8380417 from (muLimb_lt mu l).trans (by norm_num)) hrec.symm)
    rw [← hcl] at hq
    exact natOfBits_injective hw hcb hq
  have h := congrFun (hlimb (t / 22) (by omega)) ⟨t % 22, Nat.mod_lt _ (by norm_num)⟩
  simp only at h
  rw [show t / 22 * 22 + t % 22 = t by omega, if_pos ht,
    show 22 * (t / 22) + t % 22 = t by omega] at h
  exact h

end GordieHowe.MLDSA44.Ring.Native
