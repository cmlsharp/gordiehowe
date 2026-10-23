-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Falcon512.Native.ROMParams.HonestAlgebra
public import GordieHowe.Language.Honest.Exec
public import GordieHowe.Language.Completeness.Execution

@[expose] public section

/-!
# GordieHowe: the honest execution of a native Falcon program

The execution of the source program of a native Falcon program (`GordieHowe.RealizedProgram.SourceExecution`): the honest
valuation of the source values (`honestVal`: the hash's inputs `hashVal`, the selection's `selVal`,
domain `A`'s `algVal`), the source predicates and node types at the source environment
(`source_sat`, `source_crossBits`) and the execution (`sourceExecution`), from which
`GordieHowe.RealizedProgram.HonestStrategy.ofCompletionReady` builds the honest strategy. Generic in the program
(`FalconHonestFull`: its MAC with a grouped tail, the predicates' classes, decided per program) and
the fields.
-/

namespace GordieHowe.Falcon512.Native.ROMParams

open Generated.Falcon512.Native.ROMParams.Program hiding program
open GordieHowe.Bits RealizedProgram
open Norm (FalconNorm FalconNormHonest NormIn)

/-! ## The honest valuation -/

/-- **An honest input of a native Falcon program**: a message of at most `32` bytes, its key, nonce,
samples and signature (`Falcon512.PoP.HonestInput`). -/
structure HonestIn where
  /-- The message length. -/
  L : ℕ
  /-- At most `32` bytes. -/
  hL : L ≤ 32
  /-- The input. -/
  y : Falcon512.PoP.HonestInput L
  /-- The input is valid (`HonestInput.Valid`: bytes, the implemented sampler succeeds within its
  `639` candidates, the signature verifies at the key, its payload encodes). -/
  valid : y.Valid

/-- **The Falcon-512 relation at the key, at the supported signatures**: the witness is a message
of some length `L ≤ 32` and a signature on it in `Falcon512.PoP.relSupported L` (the signature
verifies and its `HashToPoint` succeeds within the H circuit's `639` samples). It lies within
the relation at the key `keyWitRel`; the excluded fraction of hash streams is at most `2^-102`
(`Falcon512.unsupportedFraction_le`). -/
abbrev keySupportedRel :
    Set (_root_.Falcon.PublicKey _root_.Falcon.Concrete.params512 × VarWitness) :=
  {p | (p.1, p.2.2) ∈ Falcon512.PoP.relSupported p.2.1}

/-- **The honest input of a pair of `keySupportedRel`**: the witness's message length and the
honest input `Falcon512.PoP.HonestInput.ofWitness` of the key and the witness, valid by
`Falcon512.PoP.HonestInput.valid_ofWitness`.

Running time: that of `Falcon512.PoP.HonestInput.ofWitness`. -/
def HonestIn.ofRel (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512)
    (w : VarWitness) (h : (pk, w) ∈ keySupportedRel) : HonestIn :=
  ⟨w.1, Nat.lt_succ_iff.mp w.1.isLt, Falcon512.PoP.HonestInput.ofWitness pk w.2,
    Falcon512.PoP.HonestInput.valid_ofWitness h⟩

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [FalconACore program] [Norm.FalconNorm program] [Norm.FalconNormHonest program] [FalconAHonest program] {FH FA : FieldInterp} [HField FH]
  [AField FA] [FalconHBase program]

set_option hygiene false in
local notation "interp" => falconInterpOf FH FA

set_option hygiene false in
local notation "vS" => FalconNormHonest.vS program

variable (program FH FA) in
/-- **The honest relation**: the statement is the input's key's (`stmtOf`). -/
def relH : Set (program.Valuation interp × HonestIn) :=
  {p | p.1 = stmtOf p.2.y.pk}

instance (v : ℕ) : Decidable (IsHashValue v) := by unfold IsHashValue; infer_instance

variable [FalconHHonest program] [FalconHSelHonest program] [FalconHConsts program FH]
  [FalconSelField program FH FA]

variable (program FH FA) in
/-- **The honest source values** of an honest input (`hashVal`, `selVal`, `algVal`); `0` for every
other value (the realization's values are generated, `RealizedProgram.genCommitted`).

Running time: computing these values takes ten Keccak-f permutations, one negacyclic product, and a
constant number of digit operations per coefficient. This running time is argued here, not proved in
Lean. -/
-- spec-side
noncomputable def honestVal (i : HonestIn) (v j : ℕ) : (interp (program.valueField v)).K :=
  if IsHashValue v then hashVal i.y v j
  else if v ∈ [539, 541, 542] then selVal program FH FA i.y v j
  else if v ∈ NormValues program then algVal program i.y v j
  else 0

/-- **The selection's and the norm's values are none of the hash's**, and the blind none of the
norm's. -/
class FalconHValues (program : RealizedProgram) [FalconACore program] [Norm.FalconNorm program] [Norm.FalconNormHonest program] [FalconAHonest program] : Prop where
  not_hash_sel : ∀ v ∈ [539, 541, 542], ¬ IsHashValue v
  not_hash_norm : ∀ v ∈ NormValues program, ¬ IsHashValue v ∧ v ∉ [539, 541, 542]
  blind_not : 557 ∉ NormValues program

variable [FalconHValues program]

theorem honestVal_hash (i : HonestIn) : ∀ v, IsHashValue v →
    honestVal program FH FA i v = hashVal i.y v :=
  fun v hv => funext fun j => by unfold honestVal; rw [if_pos hv]

theorem honestVal_sel (i : HonestIn) : ∀ v ∈ [539, 541, 542],
    honestVal program FH FA i v = selVal program FH FA i.y v :=
  fun v hv => funext fun j => by
    unfold honestVal
    rw [if_neg (FalconHValues.not_hash_sel (program := program) v hv), if_pos hv]

theorem honestVal_norm (i : HonestIn) : ∀ v ∈ NormValues program,
    honestVal program FH FA i v = algVal program i.y v :=
  fun v hv => funext fun j => by
    unfold honestVal
    rw [if_neg (FalconHValues.not_hash_norm (program := program) v hv).1,
      if_neg (FalconHValues.not_hash_norm (program := program) v hv).2, if_pos hv]


/-! ## The program facts -/

variable (program) in
/-- **The source predicates of domain `A` and the crossing**, with the field-form signature
equation's row: the selection's four, the norm's, the signature's, the encoding's, the crossing's
type check, the norm's carries' check, the parity, the digit ranges, `mac.equal`. -/
def aPreds : List ℕ :=
  [246, 247, 248, 249, FalconNorm.p0 program, FalconNorm.p0 program + 1, FalconNorm.p0 program + 2,
    FalconNorm.p0 program + 3, FalconNorm.p0 program + 4, FalconNorm.p0 program + 5,
    FalconNorm.p0 program + 6, FalconNorm.p0 program + 7, FalconNorm.p0 program + 8,
    FalconNorm.p0 program + 9,
    FalconAHonest.pSigE program,
    FalconAHonest.pCA program, FalconNorm.pDc program, FalconNorm.pEncB program,
    FalconNorm.pRange program, FalconNorm.pRange program + 1, FalconNorm.pRange program + 2,
    FalconNorm.pRange program + 3, FalconNorm.pRange program + 4, FalconNorm.pRange program + 5,
    FalconNorm.pHigh program, FalconNorm.pSlack program, FalconAAlg.pSig program,
    FalconAHonest.pMac program]

variable (program) in
/-- **The program facts of the honest strategy** (each program instantiates them by `decide`): the
statement bound `hhat < q`, the MAC `mac` with a grouped tail (`mac.equal`, `x_H = 540`, `y_A = 545`) and its role predicates, the
only cross-field `equal` the MAC's, the blind (value `557`, the pad copy of the tag `560`), the
covering of the source predicates and the field-form row (`src_cover`), the committed values'
classes and the node-typed values' classes. -/
class FalconHonestFull (PN : outParam (ℕ → List String)) where
  /-- The program's one statement bound: the key's entries `hhat` (value `544`) below `q`. -/
  bounds : program.declaredRanges = [(544, 12289)] := by decide +kernel
  /-- The MAC. -/
  mac : program.GroupedMac PN
  /-- Its role predicates. -/
  macRolePreds : List ℕ
  /-- The blind's width. -/
  bw : ℕ
  /-- The MAC is `mac.equal` of the raw view and `c_A`. -/
  mac_shape : mac.pid = FalconAHonest.pMac program ∧ mac.dx = 0 ∧ mac.x = .leaf 540 ∧
    mac.dy = 1 ∧ mac.y = .leaf 545 ∧ mac.cdy = 1 ∧ mac.cy = .leaf 545
  /-- The only cross-field `equal` is the MAC's. -/
  crossMac : ∀ p ∈ program.predicates, ∀ dx x dy y k real, p.body = .cross dx x dy y k real →
    (program.predicate mac.pid).body = p.body
  /-- Every other predicate is the hash's or of `aPreds`. -/
  src_cover : ∀ q < program.predicates.length, q ∉ macRolePreds →
    (program.inSource (program.predicate q) = true ∨ program.fieldRowRealB q = true) →
      q < 246 ∨ q ∈ aPreds program
  /-- The statement's one member check: the key below `q`. -/
  checks_list : program.statement.checks = [⟨"hhat", 0, 1024, "falcon_key_canonical", [12289]⟩]
  /-- The blind's cells. -/
  blind_cells : (program.value 557).kind = .padCopy 560 "polynomialBits" ∧
    (program.value 557).domain < program.domains.length ∧
    (∀ j < bw, CellKey.val 557 j ∈ program.cellKeys (program.value 557).domain) ∧
    program.valueField 557 = 1 ∧ (program.value 557).size = bw
  /-- The committed source values' classes. -/
  cell_classes : (List.range program.values.length).all (fun v =>
    !program.isCellValue (program.value v).domain v || !decide (program.IsSourceValue v) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "GF(2^16)" &&
        (v == 96 || (wordsOwner? v).isSome || v == 539 || v == 541)) ||
      (program.valueField v == 0 && (program.value v).node.map (·.name) == some "bit" &&
        [45, 46, 47, 542].contains v) ||
      (program.valueField v == 1 && (program.value v).node.map (·.name) == some "GF(p^1)" &&
        (NormValues program).contains v)) = true
  /-- Only the blind is a pad copy. -/
  padCopy_only : (List.range program.values.length).all (fun w => w == 557 ||
    match (program.value w).kind with
    | .padCopy _ _ => false
    | _ => true) = true
  /-- The node-typed values that are not late. -/
  typed_classes : (List.range program.values.length).all (fun v =>
    !((program.value v).typeSource == .node) || decide (program.IsLate v) ||
      ((match (program.value v).kind with
        | .bits w _ => (match (program.value w).kind with
          | .priv => true
          | _ => false)
        | _ => false) && (program.value v).type == .bit) ||
      (program.privCellB v && program.isCellValue (program.value v).domain v &&
        (match (program.value v).type with
          | .sub S => (program.value v).node.map (·.name) == some S
          | .bit => (program.value v).node.map (·.name) == some "bit" && program.valueField v == 0
          | .field => true))) = true


open FalconHonestFull

variable {PN : ℕ → List String} [hfull : FalconHonestFull program PN]
include hfull

/-! ## The source predicates at the honest values -/

section Holds

variable (i : HonestIn) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **Every source predicate other than the MAC's, and the field-form signature equation's row,
hold** at the source environment of the honest values: the hash (`shake_holds_honest`), the
selection (`select_holds`), the norm, the signature, the encoding and the crossing
(`GordieHowe/Applications/Falcon512/Native/ROMParams/HonestAlgebra.lean`). -/
theorem source_holds (hv : i.y.Valid) (hx : x = stmtOf i.y.pk) {q : ℕ}
    (hq : q < program.predicates.length) (hr : q ∉ FalconHonestFull.macRolePreds (program := program))
    (hs : program.inSource (program.predicate q) = true ∨ program.fieldRowRealB q = true) :
    program.HoldsAt (program.srcEnv interp x (honestVal program FH FA i) c π)
      (program.predicate q).body := by
  have hh := honestVal_hash (program := program) (FH := FH) (FA := FA) i
  have hsel := honestVal_sel (program := program) (FH := FH) (FA := FA) i
  have hn := honestVal_norm (program := program) (FH := FH) (FA := FA) i
  have hk : keyOf x = some i.y.pk := by rw [hx]; exact keyOf_stmtOf _
  rcases src_cover (program := program) (PN := PN) q hq hr hs with h246 | hA
  · exact shake_holds_honest i.hL hh h246
  obtain ⟨s1, s2, s3, s4⟩ := select_holds (x := x) (c := c) (π := π) i.hL hv hh hsel
  have hN := norm_honest (x := x) (c := c) (π := π) hv hn
  simp only [aPreds, List.mem_cons, List.not_mem_nil, or_false] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact s1
  · exact s2
  · exact s3
  · exact s4
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact sig265_honest hv hx hn
  · exact cABool_honest hn
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact hN _ (by simp)
  · exact sig284_honest hv hk hn
  · exact cross_honest hsel hn

end Holds


/-! ## The MAC's source facts -/

section Mac

variable (i : HonestIn) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **The MAC's source facts hold** on the honest values: `mac.equal` holds, the raw view and `c_A`
read the sample bits, `c_A`'s integer reading is its indicator. -/
theorem srcMac_holds :
    (FalconHonestFull.mac (program := program) (PN := PN)).Source
      (program.reader (program.srcEnv interp x (honestVal program FH FA i) c π)) := by
  have hsel := honestVal_sel (program := program) (FH := FH) (FA := FA) i
  have hn := honestVal_norm (program := program) (FH := FH) (FA := FA) i
  obtain ⟨hpid, hdx, hx, hdy, hy, -, -⟩ :=
    mac_shape (program := program) (PN := PN)
  have hsz : program.exprLen (.leaf 540) = 8192 := by
    rw [RealizedProgram.exprLen_leaf]; exact (FalconACore.raw_facts (program := program)).2.1
  have hszy : program.exprLen (.leaf 545) = 8192 := by
    rw [RealizedProgram.exprLen_leaf]; exact FalconAHonest.sizes_H (program := program)
  have hcr := cross_honest (x := x) (c := c) (π := π) hsel hn
  rw [RealizedProgram.HoldsAt, ← hpid, (FalconHonestFull.mac (program := program) (PN := PN)).hb] at hcr
  refine ⟨hcr, fun j hj => ?_, fun j hj => ?_, fun j hj => ?_⟩
  · rw [hx] at hj ⊢
    rw [hsz] at hj
    rw [hdx]
    unfold RealizedProgram.evalWith
    rw [FalconHBase.domainField0 (program := program)]
    rw [raw_honest hsel hj]
    rcases (show hNat program i.y 545 j = 0 ∨ hNat program i.y 545 j = 1 by
      have := hNat545_lt (program := program) (y := i.y) j; omega) with h0 | h0 <;> rw [h0] <;> simp
  · rw [hy] at hj ⊢
    rw [hszy] at hj
    rw [hdy]
    unfold RealizedProgram.evalWith
    rw [FalconACore.domainField1 (program := program)]
    exact rdA545_bool hn hj
  · rw [hy] at hj ⊢
    rw [hszy] at hj
    rw [hdy]
    unfold RealizedProgram.evalWith
    rw [FalconACore.domainField1 (program := program)]
    rw [RealizedProgram.evalIntWith_leaf]
    change ia _ 545 j = if rdA _ 545 j = 1 then 1 else 0
    have hs545 : j < (program.value 545).size := by
      rw [FalconAHonest.sizes_H (program := program)]; exact hj
    rw [ia_algVal hn (by simp [NormValues]) hs545
      (by have := hNat545_lt (program := program) (y := i.y) j; omega),
      rdA_algVal hn (by simp [NormValues]) hs545]
    rcases (show hNat program i.y 545 j = 0 ∨ hNat program i.y 545 j = 1 by
      have := hNat545_lt (program := program) (y := i.y) j; omega) with h0 | h0 <;> rw [h0] <;> simp

end Mac


/-! ## The static histogram -/

section Hists

variable (i : HonestIn) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

end Hists


/-! ## The two-sided digits -/

section Digits

variable (i : HonestIn) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

end Digits


/-! ## The cells' bases and the node types -/

omit hfull in
theorem mem_castElt_of_eq {a b : ℕ} (h : a = b) {S : String} {z : (interp a).K}
    (hz : z ∈ (interp a).node S) : (castElt z : (interp b).K) ∈ (interp b).node S := by
  subst h
  rwa [castElt_self]

omit hfull in
/-- **The naturals lie in `F_q`** in domain `A`'s field. -/
theorem natCast_mem_prime (n : ℕ) : (n : (interp 1).K) ∈ (interp 1).node "GF(p^1)" :=
  (AField.node_prime (FA := FA) _).2
    (natCast_mem (RelativePacking.fixedField FA.K 12289 1).toSubring n)

omit hfull in
/-- The packed words lie in `GF(2^16)`. -/
theorem gf16_mem_pack (bits : Fin (2 ^ 4) → Bool) :
    (PackedClaim.pack (HField.packing (FH := FH)) bits : (interp 0).K) ∈
      (interp 0).node "GF(2^16)" :=
  (HField.node16 (FH := FH) _).2 (HField.pack_mem _)

omit hfull in
/-- The selection's labels lie in `GF(2^16)` of the selection's field. -/
theorem gf16_mem_gpow (k : ℕ) :
    ((selF (program := program) (FH := FH) (FA := FA)).g ^ k :
        (interp (SelectShape.field program selShape)).K) ∈
      (interp (SelectShape.field program selShape)).node "GF(2^16)" :=
  (HField.node16 (FH := SelField program FH FA) _).2
    (Subring.pow_mem _ (HField.g_mem (FH := SelField program FH FA)) k)

omit hfull in
theorem bit_mem {z : (interp 0).K} (hz : z = 0 ∨ z = 1) : z ∈ (interp 0).node "bit" :=
  (HField.nodeBit (FH := FH) z).2 hz

omit hfull in
theorem bit_mem_sel {z : (interp (SelectShape.field program selShape)).K} (hz : z = 0 ∨ z = 1) :
    z ∈ (interp (SelectShape.field program selShape)).node "bit" :=
  (HField.nodeBit (FH := SelField program FH FA) z).2 hz

/-- **An honest committed coordinate lies in its value's node.** -/
theorem honest_cell_mem (i : HonestIn) (π : (program.layout interp).Pads) {v : ℕ}
    (hv : v < program.values.length) (hc : program.isCellValue (program.value v).domain v = true)
    (hsrc : program.IsSourceValue v)
    (j : ℕ) {S : String} (hS : (program.value v).node.map (·.name) = some S) :
    program.copyVal interp (honestVal program FH FA i) π v j ∈
      (interp (program.valueField v)).node S := by
  have hcl := List.all_eq_true.1 (cell_classes (program := program)) v
    (List.mem_range.2 hv)
  simp only [hc, hsrc, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq,
    hS, Option.some.injEq, List.contains_iff_mem] at hcl
  have hbl := blind_cells (program := program)
  have hpriv : v ≠ 557 → program.copyVal interp (honestVal program FH FA i) π v j =
      honestVal program FH FA i v j := by
    intro h557
    unfold RealizedProgram.copyVal
    split
    · rename_i u m hk
      exfalso
      have := List.all_eq_true.1 (padCopy_only (program := program)) v
        (List.mem_range.2 hv)
      simp [hk, h557] at this
    · rfl
  have zero0 : ∀ T, (0 : (interp 0).K) ∈ (interp 0).node T := fun T => zero_mem _
  have hsf := selField (program := program)
  rcases hcl with (⟨⟨hf, rfl⟩, hw⟩ | ⟨⟨hf, rfl⟩, hb⟩) | ⟨⟨hf, rfl⟩, ha⟩
  · have h557 : v ≠ 557 := by
      rintro rfl
      rw [hbl.2.2.2.1] at hf
      exact absurd hf (by norm_num)
    rw [hpriv h557]
    have hw' : (v = 96 ∨ (wordsOwner? v).isSome) ∨ v = 539 ∨ v = 541 := by tauto
    rcases hw' with hh | hs
    · have hH : IsHashValue v := by unfold IsHashValue; tauto
      rw [honestVal_hash i v hH]
      have h45 : v ≠ 45 ∧ v ≠ 46 ∧ v ≠ 47 := by
        obtain ⟨-, w45, w46, w47, -⟩ := wordsOwner_checks
        refine ⟨?_, ?_, ?_⟩ <;> rintro rfl <;> rcases hh with h | h <;> simp_all
      unfold hashVal
      rw [if_neg h45.1, if_neg h45.2.1, if_neg h45.2.2]
      split_ifs with h96
      · exact mem_castElt_of_eq (a := 0) hf.symm (by unfold stateWords; exact gf16_mem_pack _)
      · split
        · exact mem_castElt_of_eq (a := 0) hf.symm (by unfold stateWords; exact gf16_mem_pack _)
        · exact zero_mem _
    · rw [honestVal_sel i v (by rcases hs with rfl | rfl <;> simp)]
      unfold selVal
      rcases hs with rfl | rfl
      · rw [if_pos rfl]
        exact mem_castElt_of_eq (a := 0) hf.symm (gf16_mem_pack _)
      · rw [if_neg (by norm_num), if_pos rfl]
        refine mem_castElt_of_eq (a := SelectShape.field program selShape) (hsf.trans hf.symm) ?_
        by_cases hj : j < 639
        · simp only [hj, ↓reduceDIte]
          unfold hRoute SelectFirstN.Model.hashToPointRoute
          exact gf16_mem_gpow _
        · simp only [hj, ↓reduceDIte]
          exact zero_mem _
  · have h557 : v ≠ 557 := by rintro rfl; simp at hb
    rw [hpriv h557]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl
    · rw [honestVal_hash i 45 (Or.inl rfl)]
      unfold hashVal
      rw [if_pos rfl]
      by_cases hj : j < 320
      · simp only [hj, ↓reduceDIte]
        exact mem_castElt_of_eq (a := 0) hf.symm (bit_mem (hBlock_bool _ _))
      · simp only [hj, ↓reduceDIte]
        exact zero_mem _
    · rw [honestVal_hash i 46 (Or.inr (Or.inl rfl))]
      unfold hashVal
      rw [if_neg (by norm_num), if_pos rfl]
      by_cases hj : j < 768
      · simp only [hj, ↓reduceDIte]
        exact mem_castElt_of_eq (a := 0) hf.symm (bit_mem (hBlock_bool _ _))
      · simp only [hj, ↓reduceDIte]
        exact zero_mem _
    · rw [honestVal_hash i 47 (Or.inr (Or.inr (Or.inl rfl)))]
      unfold hashVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      refine mem_castElt_of_eq (a := 0) hf.symm (bit_mem ?_)
      split_ifs
      · exact Or.inr rfl
      · exact Or.inl rfl
    · rw [honestVal_sel i 542 (by simp)]
      unfold selVal
      rw [if_neg (by norm_num), if_neg (by norm_num), if_pos rfl]
      refine mem_castElt_of_eq (a := SelectShape.field program selShape) (hsf.trans hf.symm) ?_
      by_cases hj : j < 127
      · simp only [hj, ↓reduceDIte]
        refine bit_mem_sel ?_
        unfold hRoute SelectFirstN.Model.hashToPointRoute
        dsimp only
        split_ifs
        · exact Or.inr rfl
        · exact Or.inl rfl
      · simp only [hj, ↓reduceDIte]
        exact zero_mem _
  · have hbN := FalconHValues.blind_not (program := program)
    rw [hpriv (by rintro rfl; exact hbN ha), honestVal_norm i v ha]
    unfold algVal
    rw [if_pos ha]
    exact mem_castElt_of_eq (a := 1) hf.symm (natCast_mem_prime _)

/-- **The node-typed source values lie in their types** at the source environment of the honest
values (`RealizedProgram.SourceSatAt.types`). -/
theorem honest_types (i : HonestIn) (x : program.Valuation interp)
    (c : ∀ k, (program.layout interp).Ch k) (π : (program.layout interp).Pads) (v : ℕ)
    (hv : v < program.values.length) (hts : (program.value v).typeSource = .node)
    (hl : ¬ program.IsLate v) (hsrc : program.IsSourceValue v) (j : ℕ)
    (hj : j < (program.value v).size) :
    (interp (program.valueField v)).InType (program.value v).type
      (program.reader (program.srcEnv interp x (honestVal program FH FA i) c π) v j) := by
  have hcl := List.all_eq_true.1 (typed_classes (program := program)) v
    (List.mem_range.2 hv)
  simp only [hts, beq_self_eq_true, Bool.not_true, Bool.false_or, hl, decide_false,
    Bool.or_eq_true, Bool.and_eq_true] at hcl
  rcases hcl with ⟨hk, hty⟩ | ⟨⟨hp, hc⟩, hty⟩
  · simp only [beq_iff_eq] at hty
    rw [hty]
    revert hk
    rcases hkv : (program.value v).kind with _ | _ | _ | _ | _ | ⟨w, sel⟩ | _ | _ | _ <;>
      simp only [Bool.false_eq_true, IsEmpty.forall_iff]
    rcases hkw : (program.value w).kind <;> simp only [Bool.false_eq_true, IsEmpty.forall_iff]
    intro _
    rw [RealizedProgram.reader_of_bits_of_priv _ hkv hkw]
    unfold FieldInterp.ofBool
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  · rw [RealizedProgram.reader_srcEnv_of_privCellB x _ c π hp hj]
    have hmem : ∀ S, (program.value v).node.map (·.name) = some S →
        honestVal program FH FA i v j ∈ (interp (program.valueField v)).node S := fun S hS => by
      have := honest_cell_mem i π hv hc hsrc j hS
      unfold RealizedProgram.copyVal at this
      split at this
      · rename_i u m hk
        have := kind_of_privCellB hp
        rw [hk] at this
        cases this
      · exact this
    revert hty
    cases hty' : (program.value v).type with
    | sub S =>
      intro hty
      exact hmem S (by simpa using hty)
    | bit =>
      intro hty
      simp only [Bool.and_eq_true, beq_iff_eq] at hty
      have := hmem "bit" hty.1
      revert this
      generalize honestVal program FH FA i v j = z
      revert z
      rw [hty.2]
      intro z hz
      exact (HField.nodeBit (FH := FH) z).1 hz
    | field => intro _; trivial

/-- **A key's statement passes the member check** (`falcon_key_canonical`: `key_hat` below `q`). -/
theorem checks_stmtOf (pk : Emulated.PublicKey) :
    program.StatementOk interp (stmtOf pk : program.Valuation interp) := by
  intro m hm
  rw [checks_list (program := program), List.mem_singleton] at hm
  subst hm
  have hv : program.memberValue? "hhat" = some 544 := FalconACore.hhatValue
  have hq : (MemberCheck.mk "hhat" 0 1024 "falcon_key_canonical" [12289]).entryBound? = some 12289 :=
    by decide
  unfold RealizedProgram.MemberHolds
  rw [hv, hq]
  intro i hi
  rw [FalconACore.hhatSize] at hi
  rw [stmtOf_hhat pk ⟨i, hi⟩, RealizedProgram.toNat_castElt FalconACore.hhatField.symm]
  erw [AField.toNat_natCast (FA := FA) (KeyNTT.keyHat_lt pk ⟨i, hi⟩)]
  exact KeyNTT.keyHat_lt pk ⟨i, hi⟩

/-! ## The execution of the source program -/

omit hfull in
/-- **The nodes of a native Falcon program contain `1`**: `GF(2^16)` and `bit` of field `0`,
`GF(p^1)` of field `1`. -/
theorem one_mem_node {f : ℕ} {S : String}
    (h : (f = 0 ∧ (S = "GF(2^16)" ∨ S = "bit")) ∨ (f = 1 ∧ S = "GF(p^1)")) :
    (1 : (interp f).K) ∈ (interp f).node S := by
  rcases h with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩
  · exact (HField.node16 (FH := FH) 1).2 (one_mem _)
  · exact bit_mem (Or.inr rfl)
  · exact (AField.node_prime (FA := FA) _).2 (one_mem _)

omit hfull in
/-- **The nodes of a native Falcon program contain `1`** (`one_mem_node`). -/
theorem oneNodes : OneNodes interp [(0, "bit"), (0, "GF(2^16)"), (1, "GF(p^1)")] := by
  intro p hp
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact one_mem_node (Or.inl ⟨rfl, Or.inr rfl⟩)
  · exact one_mem_node (Or.inl ⟨rfl, Or.inl rfl⟩)
  · exact one_mem_node (Or.inr ⟨rfl, rfl⟩)

section Exec

variable (i : HonestIn) {x : program.Valuation interp} {c : ∀ k, (program.layout interp).Ch k}
  {π : (program.layout interp).Pads}

/-- **The source program holds at the source environment of the honest values**: its predicates
(`source_holds`, none a MAC role predicate) and its node-typed values' types (`honest_types`, no
source value late). -/
theorem source_sat (hx : x = stmtOf i.y.pk)
    (hsl : ∀ v < program.values.length, program.IsLate v → ¬ program.IsSourceValue v)
    (hsrc : ∀ q < program.predicates.length, program.inSource (program.predicate q) = true →
      q ∉ FalconHonestFull.macRolePreds (program := program)) :
    program.SourceSatAt (program.srcEnv interp x (honestVal program FH FA i) c π) where
  preds p hp hs := by
    obtain ⟨q, hq, rfl⟩ := exists_index_of_mem hp
    exact source_holds i i.valid hx hq (hsrc q hq hs) (Or.inl hs)
  types v hv hs hts j hj :=
    honest_types i x c π v hv hts (fun hl => hsl v hv hl hs) hs j hj

/-- **The source cross-field `equal`s read bits at the source environment of the honest values**:
the only one is the MAC's (`FalconHonestFull.crossMac`), whose operands read bits
(`srcMac_holds`). -/
theorem source_crossBits :
    program.CrossBitsAt interp (program.srcEnv interp x (honestVal program FH FA i) c π) := by
  intro p hp _ dx x' dy y' k real hb
  have hS := srcMac_holds (x := x) (c := c) (π := π) i
  have he := FalconHonestFull.crossMac (program := program) p hp dx x' dy y' k
    real hb
  rw [(FalconHonestFull.mac (program := program)).hb, hb] at he
  cases he
  obtain ⟨-, -, -, hdy, hy, hcdy, hcy⟩ :=
    FalconHonestFull.mac_shape (program := program) (PN := PN)
  refine ⟨hS.xbits, ?_⟩
  rw [hcdy, hcy, ← hdy, ← hy]
  exact hS.ybits

end Exec

variable (program FH FA PN) in
/-- **The execution of a native Falcon program's source program** (`RealizedProgram.SourceExecution`): at the
key's statement, the honest values `honestVal` read off by `execOf`, no late value, no completeness
event. The source program accepts (`source_sat`, `source_crossBits`) and the field-form
`mod_q`'s field equation holds (its row `signature.equation`, a predicate
`source_holds` covers). -/
noncomputable def sourceExecution (hwf : program.WellFormed) (hI : Interp.Registered interp program)
    (hL : Interp.Lawful interp program PN) {Gn : RealizedProgram.Gens} (R : program.CommittedFacts interp Gn)
    (hbc : program.BoundNoCopy)
    (hsl : ∀ v < program.values.length, program.IsLate v → ¬ program.IsSourceValue v)
    (hk : program.KprivTyped)
    (hone : program.BoundOneMem interp)
    (hsrc : ∀ q < program.predicates.length, program.inSource (program.predicate q) = true →
      q ∉ FalconHonestFull.macRolePreds (program := program))
    (hB : program.fieldRowsB = true)
    (hrow : ∀ q < program.predicates.length, program.fieldRowRealB q = true →
      q ∉ FalconHonestFull.macRolePreds (program := program))
    (hng : program.NoGammaTables) :
    program.SourceExecution interp (relH program FH FA) where
  packFree _ _ _ _ _ := RealizedProgram.packFreeAt_of_noGamma hng _
  stmtOf i := stmtOf i.y.pk
  stmt _ _ h := h
  val i := program.execOf interp (honestVal program FH FA i)
  late _ _ := 0
  respects _ _ _ _ _ _ _ := rfl
  bad _ _ _ _ := False
  δ _ := 0
  badBound _ _ _ _ _ := by simp [IOP.probUniform]
  checks x i h := by
    rw [show x = stmtOf i.y.pk from h]
    exact checks_stmtOf _
  bounded x i h := by
    rw [show x = stmtOf i.y.pk from h]
    intro vN hvN j hj
    rw [FalconHonestFull.bounds (program := program), List.mem_singleton] at hvN
    subst hvN
    rw [FalconACore.hhatSize] at hj
    refine ⟨_, KeyNTT.keyHat_lt i.y.pk ⟨j, hj⟩, ?_⟩
    rw [stmtOf_hhat i.y.pk ⟨j, hj⟩]
    exact RealizedProgram.castElt_natCast FalconACore.hhatField.symm _
  accepting x i hx c _ :=
    sourceAcceptingAtC_of_srcEnv (l := 0) (π := 0) hwf hI hL R hbc hk hone
      (by rw [RealizedProgram.srcEnvL_zero]; exact source_sat i hx hsl hsrc)
      (by rw [RealizedProgram.srcEnvL_zero]; exact source_crossBits i)
  fieldEqs x i hx c _ :=
    fieldEqsAtC_of_srcEnv (l := 0) (π := 0) hwf hI hL R hbc hB fun q hq hr => by
      rw [RealizedProgram.srcEnvL_zero]
      exact source_holds i i.valid hx hq (hrow q hq hr) (Or.inr hr)

end GordieHowe.Falcon512.Native.ROMParams
