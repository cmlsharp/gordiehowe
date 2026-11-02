-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Readings
public import GordieHowe.Applications.MLDSA44.Ring.Native.Frontend.Select

@[expose] public section

/-!
# GordieHowe frontend: the selected member of the ML-DSA-44 ring carriers

The public table's selection (`select_member`, `lib/gordiehowe/examples/rings/mldsa_ring.h`;
`GordieHowe.RealizedProgram.TableSelect`) read at the ML-DSA-44 ring carriers: without the
selection's event (`TableSelect.SelBad` at `member.table.gamma`), the record (`member.a_hat ‖
member.t1 ‖` the `24` limbs of `member.mu`) is the carriers' row map (`carrierMap`: the
scheme-order transform of length `256` at `ψ = psi512` on each of the `20` key blocks, the
identity on the limbs) applied to row `idx` of the statement, `idx` the natural the index bits
name (`TableSelect.idxOf`, below `64`).

* `selectField`: the field facts the selection reads in a Goldilocks extension (`p − 1` is `−1`).
* `rowApply_ntt256`, `rowApply_carrier_key`, `rowApply_carrier_mu`: the carriers' row map applied
  to a row: a scheme-order transform per key block, the identity on the limbs.
* `ref0_eq`, `rec_aHat`, `rec_t1`, `rec_mu`: the record's coordinates.
* `record_row`: the record is the row map applied to the selected row
  (`TableSelect.record_eq_of_not_bad`).
* `spectraOf_row`: at a statement holding a ring's carrier rows (`RowsOf`), at a selected key whose
  `ExpandA` finishes within the byte budget, the committed `â` and `t̂` are the scheme-order
  transforms of the key's `A = NTT⁻¹(Â)` and `2^d · t1` (`SpectraOf`, the hypothesis of
  `algebra_carrier`).
* `muA_eq`: the committed `μ` bits are those of the selected key's `μ` (the limbs, naturals below
  `2^22 < p`, as in `Native.muA_eq`).
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits GordieHowe.Ring RealizedProgram
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt muLimb muOf muBitNat)

/-! ## The scheme-order transform's reads -/

/-- **The scheme-order transform reads its first `n` coordinates.** -/
theorem nttScheme_congr {K : Type*} [Field K] {n : ℕ} (ψ : K) {x y : ℕ → K}
    (h : ∀ k < n, x k = y k) (m : ℕ) : Ops.nttScheme n ψ x m = Ops.nttScheme n ψ y m := by
  have hxy : Ops.toFin n x = Ops.toFin n y := funext fun i => h i i.isLt
  unfold Ops.nttScheme Ops.nttNatural
  rw [hxy]

/-! ## The carriers' row map -/

section RowMap

variable {K : Type*} [Field K] (dec : ℕ → K)

/-- **A run of scheme-order leaves of length `256` at one root `ψ`, then a rest**, applied to a
row: below `256` per leaf, the transform of the row's block at the cell's offset in the block;
past them, the rest at the shifted row. -/
theorem rowApply_ntt256 (ψ : ℕ) : ∀ (ls : List RowLeaf),
    (∀ l ∈ ls, l.ntt = true ∧ l.natural = false ∧ l.n = 256 ∧ l.psi = ψ) →
    ∀ (rest : List RowLeaf) (row : ℕ → K) (c : ℕ),
    rowApply dec (ls ++ rest) row c =
      if c < 256 * ls.length then
        Ops.nttScheme 256 (dec ψ) (fun k => row (256 * (c / 256) + k)) (c % 256)
      else rowApply dec rest (fun i => row (256 * ls.length + i)) (c - 256 * ls.length)
  | [], _, rest, row, c => by simp
  | l :: ls, hl, rest, row, c => by
    obtain ⟨h1, h2, h3, h4⟩ := hl l (List.mem_cons_self ..)
    have ih := rowApply_ntt256 ψ ls (fun l' hl' => hl l' (List.mem_cons_of_mem _ hl')) rest
      (fun i => row (256 + i)) (c - 256)
    rw [List.cons_append, rowApply, h3]
    by_cases hc : c < 256
    · rw [if_pos hc, if_pos (by simp only [List.length_cons]; omega), RowLeaf.apply, h1, h2, h4, h3,
        if_pos rfl, if_neg Bool.false_ne_true]
      rw [show c / 256 = 0 by omega, show c % 256 = c by omega]
      simp
    · rw [if_neg hc, ih]
      simp only [List.length_cons]
      by_cases hc' : c - 256 < 256 * ls.length
      · rw [if_pos hc', if_pos (by omega), show (c - 256) % 256 = c % 256 by omega]
        refine nttScheme_congr _ (fun k _ => ?_) _
        congr 1
        omega
      · rw [if_neg hc', if_neg (by omega),
          show c - 256 - 256 * ls.length = c - 256 * (ls.length + 1) by omega]
        congr 1
        funext i
        congr 1
        ring

/-- The carriers' key leaves. -/
theorem carrierMap_eq : carrierMap =
    (List.range 20).map (fun i => (⟨true, false, 256, 256 * i, carrierPsi⟩ : RowLeaf)) ++
      [⟨false, false, 24, 5120, 0⟩] := rfl

/-- The carriers' key leaves are scheme-order transforms of length `256` at `carrierPsi`. -/
theorem carrierLeaves_spec : ∀ l ∈ (List.range 20).map
    (fun i => (⟨true, false, 256, 256 * i, carrierPsi⟩ : RowLeaf)),
    l.ntt = true ∧ l.natural = false ∧ l.n = 256 ∧ l.psi = carrierPsi := by
  intro l hl
  obtain ⟨i, -, rfl⟩ := List.mem_map.1 hl
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- **The carriers' row map on a key block**: cell `256 b + m` (`b < 20`, `m < 256`) is the
scheme-order transform at `carrierPsi` of the row's block `b`, at `m`. -/
theorem rowApply_carrier_key (row : ℕ → K) {b m : ℕ} (hb : b < 20) (hm : m < 256) :
    rowApply dec carrierMap row (256 * b + m) =
      Ops.nttScheme 256 (dec carrierPsi) (fun k => row (256 * b + k)) m := by
  rw [carrierMap_eq, rowApply_ntt256 dec carrierPsi _ carrierLeaves_spec, List.length_map,
    List.length_range, if_pos (by omega), show (256 * b + m) / 256 = b by omega,
    show (256 * b + m) % 256 = m by omega]

/-- **The carriers' row map on the limbs**: cell `5120 + l` (`l < 24`) is the row's. -/
theorem rowApply_carrier_mu (row : ℕ → K) {l : ℕ} (hl : l < 24) :
    rowApply dec carrierMap row (5120 + l) = row (5120 + l) := by
  rw [carrierMap_eq, rowApply_ntt256 dec carrierPsi _ carrierLeaves_spec, List.length_map,
    List.length_range, if_neg (by omega), show 5120 + l - 256 * 20 = l by omega]
  simp only [rowApply, RowLeaf.apply, if_pos hl, Bool.false_eq_true, if_false]

/-- The carriers' row map has `5144` cells. -/
theorem carrierMap_width : mapWidth carrierMap = 5144 := by decide +kernel

end RowMap

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [CarrierHEmbed program] [MldsaCarrierRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaCarrierFront program]
  {F0 FH : RealizedProgram.FieldInterp} [MLDSA44.AField F0]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-- **`p − 1` is `−1`** in a field of characteristic `p` (Goldilocks). -/
theorem natCast_pm1 : ((18446744069414584320 : ℕ) : (interp 0).K) = -1 := by
  rw [eq_neg_iff_add_eq_zero, show ((18446744069414584320 : ℕ) : (interp 0).K) + 1 =
    ((pGold : ℕ) : (interp 0).K) by norm_num [pGold]]
  exact CharP.cast_eq_zero _ pGold

/-- **The field facts the selection reads in a Goldilocks extension**: `p − 1` decodes to `−1`,
`0` and `1` to themselves and read back as `0` and `1`. -/
theorem selectField : RealizedProgram.SelectField (interp 0) 18446744069414584320 where
  decode_negOne := (MLDSA44.AField.decode_lt (F0 := F0) _ (by norm_num [pGold])).trans natCast_pm1
  decode_zero := (MLDSA44.AField.decode_lt (F0 := F0) 0 (by norm_num [pGold])).trans Nat.cast_zero
  decode_one := (MLDSA44.AField.decode_lt (F0 := F0) 1 (by norm_num [pGold])).trans Nat.cast_one
  toNat_zero := by
    have h := MLDSA44.AField.toNat_natCast (F0 := F0) 0 (by norm_num [pGold])
    rw [Nat.cast_zero] at h
    exact h
  toNat_one := by
    have h := MLDSA44.AField.toNat_natCast (F0 := F0) 1 (by norm_num [pGold])
    rw [Nat.cast_one] at h
    exact h

/-- The selection's field facts at the table's `−1`. -/
theorem selectField_shape :
    RealizedProgram.SelectField (interp 0) (TableSelect.shape program).mOne := by
  rw [MldsaCarrierFront.shape.2.2.1]
  exact selectField

/-- The table's domain is field `0`. -/
theorem domainField_shape : program.domainField (TableSelect.shape program).dom = 0 := by
  rw [MldsaCarrierFront.shape.1, MldsaCarrierFront.domains.1]

/-- A Goldilocks constant below `p` decodes to its cast. -/
theorem decode_gold {c : ℕ} (hc : c < pGold) : (interp 0).decode c = (c : (interp 0).K) :=
  MLDSA44.AField.decode_lt c hc

/-! ## The record -/

/-- **Shared expression `0`**: the `μ` bits below `512`, zeros up to `528`. -/
theorem ref0_eq (e : program.Env interp) {t : ℕ} (ht : t < 528) :
    program.evalE (program.reader e) 0 (.ref 0) t =
      if t < 512 then program.evalE (program.reader e) 0 (.leaf 57) t else 0 := by
  have := selectField_shape (program := program) (F0 := F0) (FH := FH)
  have hz : program.evalE (program.reader e) 0 (.leaf 0) 0 = 0 := by
    have := TableSelect.evalE_zero (f := 0) domainField_shape e
    rwa [MldsaCarrierFront.shape.2.2.2.1] at this
  rw [RealizedProgram.evalE_ref MldsaCarrierRelation.refsOrdered _ _
      (by have := MldsaCarrierFront.lt505 (program := program); omega),
    MldsaCarrierFront.expr0, evalE_reindex, evalE_concat, exprLen_leaf, MldsaCarrierFront.muSize]
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
        (if c < 4096 then program.evalE rd 0 (.leaf 55) c
          else program.evalE rd 0 (.leaf 56) (c - 4096))
      else program.evalE rd 0 (.apply (.batched 24 (.fromDigits 22 2)) (.ref 0)) (c - 5120) := by
  rw [RealizedProgram.evalE_ref MldsaCarrierRelation.refsOrdered _ _
      (by have := MldsaCarrierFront.lt505 (program := program); omega),
    MldsaCarrierFront.expr1, evalE_reindex, IndexMap.entry_step_one hc, Nat.zero_add, evalE_concat,
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
    program.evalE rd 0 (.ref 1) c = program.evalE rd 0 (.leaf 55) c := by
  rw [ref1_eq rd (by omega), if_pos (by omega), if_pos hc]

/-- **The record's `t̂`**: coordinate `4096 + c` is `member.t1`'s coordinate `c`. -/
theorem rec_t1 (rd : program.Valuation interp) {c : ℕ} (hc : c < 1024) :
    program.evalE rd 0 (.ref 1) (4096 + c) = program.evalE rd 0 (.leaf 56) c := by
  rw [ref1_eq rd (by omega), if_pos (by omega), if_neg (by omega), Nat.add_sub_cancel_left]

/-- **The record's limb `l`**: coordinate `5120 + l` is `Σ_b 2^b μ_{22 l + b}` of the
zero-extended `μ` bits. -/
theorem rec_mu (e : program.Env interp) {l : ℕ} (hl : l < 24) :
    program.evalE (program.reader e) 0 (.ref 1) (5120 + l) =
      ∑ b : Fin 22, (2 : (interp 0).K) ^ (b : ℕ) *
        (if l * 22 + (b : ℕ) < 512 then program.evalE (program.reader e) 0 (.leaf 57) (l * 22 + b)
          else 0) := by
  have h2 : (interp 0).decode 2 = 2 := (decode_gold (by norm_num [pGold])).trans (by norm_num)
  rw [ref1_eq _ (by omega), if_neg (by omega), Nat.add_sub_cancel_left,
    evalE_apply_batched_fromDigits _ _ (by norm_num), h2]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ref0_eq e (by have := b.isLt; omega)]

/-! ## The selection -/

/-- **Coordinate `c` of row `j` of the table**, read in field `0` off a statement: `ring.keys`
below `5120`, `ring.mu` up to `5144`, `0` after. -/
def rowEntry (x : program.Valuation interp) (j c : ℕ) : (interp 0).K :=
  if c < 5120 then RealizedProgram.castElt (x (MldsaRingStmt.keys program) (j * 5120 + c))
  else if c < 5144 then
    RealizedProgram.castElt (x (MldsaRingStmt.mu program) (j * 24 + (c - 5120)))
  else 0

/-- **An opaque statement value reads the statement** at the table's fuel. -/
theorem read_opaque (e : program.Env interp) {v : ℕ} {name : String}
    (hk : (program.value v).kind = .pub (.opaque name [])) (i : ℕ) :
    program.read e program.values.length v i = e.stmt v i := by
  obtain ⟨n, hn⟩ := TableSelect.values_length_succ (program := program)
  rw [hn]
  simp only [RealizedProgram.read, hk, if_true]

/-- **The selected index is below `64`** where the selection's predicates hold. -/
theorem idxOf_lt64_of_preds {e : program.Env interp} (hp : TableSelect.Preds e) :
    TableSelect.idxOf 0 e < 64 := by
  have := selectField_shape (program := program) (F0 := F0) (FH := FH)
  have := TableSelect.idxOf_lt domainField_shape hp
  rwa [MldsaCarrierFront.shape.2.2.2.2.2.2.2.2] at this

/-- **The selected index is below `64`** where the source program holds. -/
theorem idxOf_lt64 {e : program.Env interp} (hs : program.SourceSatAt e) :
    TableSelect.idxOf 0 e < 64 :=
  idxOf_lt64_of_preds (TableSelect.preds_of_source hs)

/-- **The table's selected row is the statement's row `idx`** where the selection's predicates
hold. -/
theorem rowAt_eq_of_preds {e : program.Env interp} (hp : TableSelect.Preds e) :
    TableSelect.rowAt 0 e (TableSelect.rowIdx 0 e) = rowEntry e.stmt (TableSelect.idxOf 0 e) := by
  obtain ⟨-, -, -, -, -, hparts, -, hrows, -⟩ := MldsaCarrierFront.shape (program := program)
  have hidx : TableSelect.rowIdx 0 e = TableSelect.idxOf 0 e := by
    unfold TableSelect.rowIdx
    rw [hrows, if_pos (idxOf_lt64_of_preds hp)]
  rw [hidx]
  funext c
  unfold TableSelect.rowAt rowEntry
  rw [hparts]
  simp only [rowOf]
  by_cases h' : c < 5120
  · rw [if_pos h', if_pos h']
    unfold RealizedProgram.rowRead
    rw [read_opaque e MldsaRingStmt.keysKind]
  · rw [if_neg h', if_neg h']
    by_cases h'' : c < 5144
    · rw [if_pos (by omega), if_pos h'']
      unfold RealizedProgram.rowRead
      rw [read_opaque e MldsaRingStmt.muKind]
    · rw [if_neg (by omega), if_neg h'']

/-- **The record is the row map applied to the selected row** wherever the selection's predicates
hold and the selection's event did not occur (`TableSelect.record_eq_of_not_bad`). -/
theorem record_row_of_preds {e : program.Env interp} (hp : TableSelect.Preds e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {c : ℕ} (hc : c < 5144) :
    program.evalE (program.reader e) 0 (.ref 1) c =
      rowApply (interp 0).decode carrierMap (rowEntry e.stmt (TableSelect.idxOf 0 e)) c := by
  have := selectField_shape (program := program) (F0 := F0) (FH := FH)
  obtain ⟨-, hchal, -, -, hrec, -, hmap, -, -⟩ := MldsaCarrierFront.shape (program := program)
  have h := TableSelect.record_eq_of_not_bad domainField_shape hp
    (by rwa [hchal]) (c := c) (by unfold TableSelect.W; rw [hmap, carrierMap_width]; exact hc)
  unfold TableSelect.recOf at h
  rw [hrec] at h
  rw [h]
  unfold TableSelect.mapOf
  rw [hmap, rowAt_eq_of_preds hp]

/-- **The record is the row map applied to the selected row** wherever the source program holds
and the selection's event did not occur (`record_row_of_preds`). -/
theorem record_row {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {c : ℕ} (hc : c < 5144) :
    program.evalE (program.reader e) 0 (.ref 1) c =
      rowApply (interp 0).decode carrierMap (rowEntry e.stmt (TableSelect.idxOf 0 e)) c :=
  record_row_of_preds (TableSelect.preds_of_source hs) hno hc

variable {len : ℕ}

/-- `ψ` decodes to `psi512`'s cast. -/
theorem decode_psi : (interp 0).decode carrierPsi = ((psi512 : ℕ) : (interp 0).K) :=
  decode_gold (by norm_num [pGold])

/-- **The committed spectra are the selected key's transforms** (`SpectraOf`), at a statement
holding a ring's carrier rows, at a selected key whose `ExpandA` finishes within the byte budget:
the record is the scheme-order transform at `ψ = psi512` of each key block of the selected row,
whose entries are `A = NTT⁻¹(ExpandA(ρ))` (`aNat`, `Rows.aKeyOf` within the budget) and
`2^d · t1` (`tNat`). -/
theorem spectraOf_row {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {x : RStmt len} (hrows : RowsOf x e.stmt)
    (hexp : MLDSA44.ExpandAWithin _root_.MLDSA.mldsa44 (x.keyAt (TableSelect.idxOf 0 e)).rho) :
    SpectraOf (x.keyAt (TableSelect.idxOf 0 e)) (program.reader e) where
  a i j m hm := by
    have hi := i.isLt; have hj := j.isLt
    rw [← rec_aHat _ (by omega), record_row hs hno (by omega),
      show ((i : ℕ) * 4 + j) * 256 + m = 256 * ((i : ℕ) * 4 + j) + m by ring,
      rowApply_carrier_key _ _ (by omega) hm, decode_psi]
    refine nttScheme_congr _ (fun k hk => ?_) _
    rw [rowEntry, if_pos (by omega), hrows.keys _ (idxOf_lt64 hs) _ (by omega),
      show 256 * ((i : ℕ) * 4 + j) + k = ((i : ℕ) * 4 + j) * 256 + (⟨k, hk⟩ : Fin 256) by
        simp only; ring, keyEntry_a]
    simp only [keyPoly, Ops.ofFin_of_lt _ hk]
    congr 2
    unfold aNat Emulated.Rows.aKeyOf MLDSA44.Native.Rows.aEntry MLDSA44.Native.Rows.aHat
    rw [MLDSA44.expandABounded_eq_expandAFull hexp]
  t i m hm := by
    have hi := i.isLt
    rw [← rec_t1 _ (by omega), record_row hs hno (by omega),
      show 4096 + ((i : ℕ) * 256 + m) = 256 * (16 + i) + m by ring,
      rowApply_carrier_key _ _ (by omega) hm, decode_psi]
    refine nttScheme_congr _ (fun k hk => ?_) _
    rw [rowEntry, if_pos (by omega), hrows.keys _ (idxOf_lt64 hs) _ (by omega),
      show 256 * (16 + (i : ℕ)) + k = 4096 + ((i : ℕ) * 256 + (⟨k, hk⟩ : Fin 256)) by
        simp only; ring, keyEntry_t]
    simp only [keyPoly, Ops.ofFin_of_lt _ hk]
    rfl

/-- **The `μ` bits are bits** (`member.mu.boolean`). -/
theorem mu_bool {e : program.Env interp} (hs : program.SourceSatAt e) {t : ℕ} (ht : t < 512) :
    program.evalE (program.reader e) 0 (.leaf 57) t = 0 ∨
      program.evalE (program.reader e) 0 (.leaf 57) t = 1 := by
  obtain ⟨hc, hl, hsrc⟩ := MldsaCarrierFront.muBool (program := program)
  have h := RealizedProgram.bool_of_boolCheck hc
    (hs.preds _ (RealizedProgram.predicate_mem hl) hsrc) (i := t)
    (by rw [MldsaCarrierFront.muSize]; exact ht)
  rwa [MldsaCarrierFront.domains.1] at h

/-- **The committed `μ` bits are the selected key's `μ`**, at a statement holding a ring's carrier
rows: bit `t` is `1` exactly when bit `t` of `μ = H(H(pk) ‖ M′)` is. -/
theorem muA_eq {e : program.Env interp} (hs : program.SourceSatAt e)
    (hno : ¬ TableSelect.SelBad 0 0 e) {x : RStmt len} (hrows : RowsOf x e.stmt) {t : ℕ}
    (ht : t < 512) : program.evalE (program.reader e) 0 (.leaf 57) t =
      if muBitNat (muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg) t = 1 then 1 else 0 := by
  set mu := muOf (x.keyAt (TableSelect.idxOf 0 e)) x.msg
  set rd := program.reader e
  have hlimb : ∀ l < 24,
      (fun b : Fin 22 => if l * 22 + (b : ℕ) < 512 then program.evalE rd 0 (.leaf 57) (l * 22 + b)
        else (0 : (interp 0).K)) =
      fun b : Fin 22 => if muBitNat mu (22 * l + b) = 1 then 1 else 0 := by
    intro l hl
    have hw : AllBool (fun b : Fin 22 => if l * 22 + (b : ℕ) < 512 then
        program.evalE rd 0 (.leaf 57) (l * 22 + b) else (0 : (interp 0).K)) := fun b => by
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
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 (Native.muBitNat_le mu (22 * l + b)) with h | h
      · rw [h, if_neg zero_ne_one, if_neg zero_ne_one, Nat.zero_mul]
      · rw [h, if_pos rfl, if_pos rfl, Nat.one_mul]
    have hrec := rec_mu e hl
    rw [record_row hs hno (by omega), rowApply_carrier_mu _ _ hl, rowEntry, if_neg (by omega),
      if_pos (by omega), Nat.add_sub_cancel_left, hrows.mu _ (idxOf_lt64 hs) _ hl] at hrec
    have hcast := Native.cast_natOfBits hw
    beta_reduce at hcast
    replace hrec := hrec.trans hcast.symm
    have hq : natOfBits (fun b : Fin 22 => if l * 22 + (b : ℕ) < 512 then
        program.evalE rd 0 (.leaf 57) (l * 22 + b) else (0 : (interp 0).K)) = muLimb mu l :=
      (CharP.natCast_injOn_Iio (interp 0).K pGold
        (show natOfBits _ < pGold from (natOfBits_lt _).trans (by norm_num [pGold]))
        (show muLimb mu l < pGold from (Native.muLimb_lt mu l).trans (by norm_num [pGold]))
        hrec.symm)
    rw [← hcl] at hq
    exact natOfBits_injective hw hcb hq
  have h := congrFun (hlimb (t / 22) (by omega)) ⟨t % 22, Nat.mod_lt _ (by norm_num)⟩
  simp only at h
  rw [show t / 22 * 22 + t % 22 = t by omega, if_pos ht,
    show 22 * (t / 22) + t % 22 = t by omega] at h
  exact h

end GordieHowe.MLDSA44.Ring.Carrier
