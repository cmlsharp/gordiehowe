-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Honest.Hash
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Frontend.Shuffle

@[expose] public section

/-!
# GordieHowe: SampleInBall's selection at honest values

The converse of the frontend's selection view (`GordieHowe/Applications/MLDSA44/Native/ROMParams/Frontend/Select.lean`): where the gadget
`SelectFirstTau.run` holds on the program's readings (the candidate bytes, the selected bytes, the
low threshold bits and `δ`), the selection's predicates `h2c.sample.select.start`, `.step` and
`.route` (predicates `264`–`266`) hold (`select_holds_of_run`). The honest values pass the gadget at
every `δ` (`SelectFirstTau.complete`).
-/

namespace GordieHowe.MLDSA44.Native.ROMParams

open Generated.MLDSA44.Native.ROMParams.Program
open GordieHowe.Bits

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [MldsaHHonest program] [MldsaHShuffle program] {F0 FH : RealizedProgram.FieldInterp}
  [HField FH] [MldsaHConsts program FH]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

variable (e : program.Env interp)

/-- **`h2c.sample.select.start` holds** where the first threshold is `256 − 39`
(`SelectFirstTau.initialOk`). -/
theorem sel264_of (h : SelectFirstTau.initialOk 39 (thrBits (program.reader e)) = true) :
    program.HoldsWith (program.reader e) (program.predicate 264).body := by
  rw [(pred264 (program := program))]
  simp only [SelectFirstTau.initialOk, List.all_eq_true, List.mem_finRange, true_implies,
    Bool.or_eq_true, decide_eq_true_eq, ne_eq] at h
  intro b hb
  have hb' : b < 8 := by
    revert hb
    rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex]
    unfold idx52
    simp [RealizedProgram.IndexMap.ofSegs, RealizedProgram.IdxSeg.expand, RealizedProgram.IndexMap.size]
  change program.evalE _ (program.domainField 1) _ b = program.evalE _ (program.domainField 1) _ b
  rw [MldsaHCross.domainField1, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, idx52_eq hb',
    evalE_constH e (stepConsts (program := program)).1 (stepConsts (program := program)).2.2.2.2.2.2.1,
    evalE_constH e (stepConsts (program := program)).2.2.1
      (stepConsts (program := program)).2.2.2.2.2.2.2.1, (stepConsts (program := program)).2.1,
    (stepConsts (program := program)).2.2.2.1, getD_replicate_zero, decode_zero']
  rcases h ⟨0, by norm_num⟩ with h0 | h0
  · exact absurd rfl h0
  have hthr := h0 ⟨b, hb'⟩
  unfold thrBits at hthr
  simp only [Fin.val_zero, Nat.mul_zero, Nat.zero_add] at hthr
  rw [hthr]
  unfold Bits.constBit
  interval_cases b <;> simp [HField.decode_one, HField.decode_zero,
    CharTwo.add_self_eq_zero]

/-- **`h2c.sample.select.step` holds** where the thresholds follow the recurrence
(`SelectFirstTau.stepOk`). -/
theorem sel265_of (h : SelectFirstTau.stepOk 39 (candBits (program.reader e))
      (thrBits (program.reader e)) = true) :
    program.HoldsWith (program.reader e) (program.predicate 265).body := by
  rw [pred265_body]
  intro n hn
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_reindex, stepSizes.2.2.2.2.2.2.2.2] at hn
  obtain ⟨i, b, hb, rfl⟩ : ∃ i b, b < 8 ∧ n = 8 * i + b := ⟨n / 8, n % 8, Nat.mod_lt _ (by norm_num),
    (Nat.div_add_mod n 8).symm⟩
  have hi : i < 263 := by omega
  simp only [SelectFirstTau.stepOk, List.all_eq_true, List.mem_finRange, true_implies] at h
  have hstep := h ⟨i, by omega⟩
  rw [dif_pos (show (i : ℕ) + 1 < 264 by omega)] at hstep
  simp only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] at hstep
  have hs := hstep ⟨b, hb⟩
  rw [← evalE_ref512, thrBits_apply] at hs
  change thrAt (program.reader e) ((i : ℕ) + 1) b = _ at hs
  have hsucc : thrAt (program.reader e) (i + 1) b = thrAt (program.reader e) i b +
      program.evalE (program.reader e) 1 (.ref 512) i *
        ∏ j : Fin 8, if (j : ℕ) < b then thrAt (program.reader e) i j else 1 := by
    rw [hs]
    unfold SelectFirstTau.next SelectScan.mux Bits.increment Bits.bxor
    have h2 : (2 : (interp 1).K) = 0 := CharTwo.two_eq_zero
    simp only [thrBits_apply]
    linear_combination (-(program.evalE (program.reader e) 1 (.ref 512) i *
      thrAt (program.reader e) i b *
        ∏ j : Fin 8, if (j : ℕ) < b then thrAt (program.reader e) i j else 1)) * h2
  have hnext : thrAt (program.reader e) (i + 1) b =
      program.evalE (program.reader e) 1 (.ref 508) (8 + (8 * i + b)) := by
    unfold thrAt
    congr 1
    ring
  change program.evalE _ (program.domainField 1) _ _ =
    program.evalE _ (program.domainField 1) _ _
  rw [MldsaHCross.domainField1, evalE_46, RealizedProgram.evalE_add, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex,
    RealizedProgram.IndexMap.entry_of_toList idx53_toList (by omega), evalE_ref509 e hi hb,
    evalE_chain _ hi (by norm_num) le_rfl hb, ← hnext, hsucc]
  have hsel : program.evalE (program.reader e) 1 (.reindex idx61 (.ref 513)) i =
      program.evalE (program.reader e) 1 (.ref 512) i := by
    rw [RealizedProgram.evalE_reindex, RealizedProgram.IndexMap.entry_of_toList idx61_toList hi, evalE_ref513 e hi]
  by_cases hb0 : b = 0
  · subst hb0
    rw [if_pos rfl, hsel]
    simp only [Nat.not_lt_zero, ite_false, Finset.prod_const_one, mul_one]
    unfold thrAt
    rw [Nat.add_zero]
    ring_nf
    rw [CharTwo.two_eq_zero]
    ring
  · rw [if_neg hb0, evalE_levelCol e hi (by omega) hb]
    unfold thrAt
    rw [Nat.add_comm (8 * i) b] at *
    ring_nf
    rw [CharTwo.two_eq_zero]
    ring

/-- **`h2c.sample.select.route` holds** where the selected positions' tagged product is the
selected bytes' (`SelectFirstTau.fingerprintOk`). -/
theorem sel266_of (h : SelectFirstTau.fingerprintOk selF 39 (candBits (program.reader e))
      (jBits (program.reader e)) (thrBits (program.reader e)) (selDelta (program.reader e)) = true) :
    program.HoldsWith (program.reader e) (program.predicate 266).body := by
  have h36 := fun i => RealizedProgram.reader_of_constant e
    (RealizedProgram.kind_of_isConstant (selConstsA (program := program)).1) i
  rw [(pred266 (program := program))]
  intro n hn
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_prod, RealizedProgram.exprLen_mux, RealizedProgram.exprLen_add,
    (routeLens (program := program))] at hn
  obtain rfl : n = 0 := by omega
  change program.evalE _ (program.domainField 1) (.prod 264 _) 0 +
    program.evalE _ (program.domainField 1) (.prod 39 _) 0 =
      program.evalE _ (program.domainField 1) _ 0
  rw [MldsaHCross.domainField1, RealizedProgram.evalE_prod, RealizedProgram.evalE_prod, List.prod_map_range,
    List.prod_map_range, evalE_36 _ h36]
  unfold SelectFirstTau.fingerprintOk at h
  rw [decide_eq_true_iff, List.finRange_foldl_mul_eq_prod, List.finRange_foldl_mul_eq_prod] at h
  have key : (∏ i : Fin 264, program.evalE (program.reader e) 1 (.mux (.ref 512)
      (.add (.reindex idx76 (.leaf 560)) (.add (.apply (.sum 8) (.mul (.reindex idx77 (.ref 508))
        (.reindex idx78 (.leaf 37)))) (.scale (.const 2) (.apply (.sum 8)
          (.mul (.reindex idx77 (.ref 510)) (.reindex idx78 (.leaf 37)))))))
      (.reindex idx76 (.leaf 7))) (0 * 264 + i)) =
      ∏ i : Fin 264, SelectScan.mux (SelectFirstTau.selected 39 (candBits (program.reader e))
        (thrBits (program.reader e)) i) (selDelta (program.reader e) -
          SelectFirstTau.enc selF (selF.embedBits (by decide) (thrBits (program.reader e) i))
            (candBits (program.reader e) i)) 1 := by
    refine Finset.prod_congr rfl fun i _ => ?_
    have hi := i.isLt
    rw [Nat.zero_mul, Nat.zero_add, RealizedProgram.evalE_mux, evalE_ref512 e i, RealizedProgram.evalE_add,
      RealizedProgram.evalE_reindex, idx76_eq hi, RealizedProgram.evalE_add,
      evalE_embed8 e hi (fun t ht => idx77_eq (by omega)) (fun u hu => idx78_eq hi hu)
        (bits := thrBits (program.reader e) i) (fun u => rfl),
      RealizedProgram.evalE_scale_const,
      evalE_embed8 e hi (fun t ht => idx77_eq (by omega)) (fun u hu => idx78_eq hi hu)
        (bits := candBits (program.reader e) i) (fun u => (candBits_eq e i u).symm),
      RealizedProgram.evalE_reindex, idx76_eq hi, evalE_7, selF_X, SelectScan.mux, SelectFirstTau.enc]
    simp only [CharTwo.sub_eq_add]
    rfl
  rw [key, h]
  have key2 : ∀ (j : Fin 39), program.evalE (program.reader e) 1 (.add (.reindex idx79 (.leaf 560))
      (.add (.leaf 47) (.scale (.const 2) (.apply (.sum 8) (.mul (.reindex idx80 (.leaf 557))
        (.reindex idx81 (.leaf 37))))))) (0 * 39 + j) =
      selDelta (program.reader e) - SelectFirstTau.enc selF (selF.embed (256 - 39 + j))
        (jBits (program.reader e) j) := by
    intro j
    have hj := j.isLt
    rw [Nat.zero_mul, Nat.zero_add, RealizedProgram.evalE_add, RealizedProgram.evalE_reindex, idx79_eq hj,
      RealizedProgram.evalE_add, evalE_47 e hj, RealizedProgram.evalE_scale_const,
      evalE_embed8 e hj (fun t ht => idx80_eq (by omega)) (fun u hu => idx81_eq hj hu)
        (bits := jBits (program.reader e) j) (fun u => rfl),
      selF_X, SelectFirstTau.enc]
    simp only [CharTwo.sub_eq_add]
    rfl
  rw [Finset.prod_congr rfl fun j _ => key2 j]
  exact CharTwo.add_self_eq_zero _

/-- **The selection's predicates hold where the gadget holds** on the program's readings (the
converse of `selectRun`). -/
theorem select_holds_of_run (h : SelectFirstTau.run selF 39 (candBits (program.reader e))
      (jBits (program.reader e)) (lowThr (program.reader e)) (selDelta (program.reader e)) = true)
    {q : ℕ} (hq : q ∈ [264, 265, 266]) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  have hthr : (fun i => SelectFirstTau.decode 39 (lowThr (program.reader e) i)) =
      thrBits (program.reader e) := funext fun i => (thrBits_eq _ i).symm
  unfold SelectFirstTau.run at h
  simp only [hthr, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · exact sel264_of e h1
  · exact sel265_of e h3
  · exact sel266_of e h2

/-! ## The memory check, conversely -/

/-- **`h2c.sample.mem.unit` holds** where every unit is the sign's (`Checks.unitRow`). -/
theorem mem267_of (h : ∀ t : Fin 39, (samLowered e).unit t =
      MemoryShuffle.unit (samM program F0 FH).Θ (signsH (program.reader e) t)) :
    program.HoldsWith (program.reader e) (program.predicate 267).body := by
  obtain ⟨c, hp, -, hc0⟩ := MldsaHConsts.theta (program := program) (FH := FH)
  rw [hp]
  intro t ht
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf,
    (cellFacts (program := program)).2.2.2.2.2.2.1] at ht
  change program.evalE _ (program.domainField 1) _ _ =
    program.evalE _ (program.domainField 1) _ _
  rw [MldsaHCross.domainField1, evalE_48, RealizedProgram.evalE_add, RealizedProgram.evalE_add,
    RealizedProgram.evalE_scale_const, evalE_ref520 e ht, RealizedProgram.evalE_reindex, idx79_eq ht, evalE_7]
  have hc : (interp 1).decode c = (samM program F0 FH).Θ.θ + 1 := hc0
  rw [hc]
  have hu := h ⟨t, ht⟩
  unfold MemoryShuffle.unit samLowered at hu
  dsimp only at hu
  rw [hu]
  linear_combination (1 + ((samM program F0 FH).Θ.θ + 1) * signsH (program.reader e) ⟨t, ht⟩) *
    (CharTwo.two_eq_zero : (2 : (interp 1).K) = 0)

/-- **`h2c.sample.mem.origin` holds** where every origin is its read origin's embedding
(`Checks.originRow`). -/
theorem mem268_of (h : ∀ t : Fin 39, (samLowered e).origin t =
      (samM program F0 FH).originOf ((samLowered e).readOrigin t)) :
    program.HoldsWith (program.reader e) (program.predicate 268).body := by
  rw [(pred268 (program := program))]
  intro t ht
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_leaf, (cellFacts (program := program)).2.2.2.2.2.2.2] at ht
  change program.evalE _ (program.domainField 1) _ _ =
    program.evalE _ (program.domainField 1) _ _
  rw [MldsaHCross.domainField1, evalE_48, RealizedProgram.evalE_add, RealizedProgram.evalE_apply_sum]
  have ho := h ⟨t, ht⟩
  unfold samLowered SampleInBall.originOf SelectionField.embedBits at ho
  dsimp only at ho
  have hsum : (∑ b : Fin 6, program.evalE (program.reader e) 1 (.mul (.reindex idx82 (.leaf 562))
      (.reindex idx83 (.leaf 49))) (t * 6 + b)) =
      program.evalE (program.reader e) 1 (.leaf 566) t := by
    rw [ho]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hb := b.isLt
    rw [RealizedProgram.evalE_mul, RealizedProgram.evalE_reindex, RealizedProgram.evalE_reindex,
      show (t : ℕ) * 6 + b = 6 * t + b by ring, idx82_eq (by omega), idx83_eq ht hb,
      evalE_constH e (memConsts (program := program)).2.2.2.1 (memConsts (program := program)).2.2.2.2.1,
      (memConsts (program := program)).2.2.2.2.2.1 b hb, MldsaHConstsSelect.c37 b (by omega)]
    rfl
  rw [hsum]
  exact CharTwo.add_self_eq_zero _

/-- **`h2c.sample.mem` holds** where the packed reads' and writes' products agree
(`Checks.perm`). -/
theorem mem269_of (h : (((samM program F0 FH).readsPacked (samLowered e)).map
      fun x => memDelta (program.reader e) - x).prod =
    (((samM program F0 FH).writesPacked (samLowered e)).map
      fun x => memDelta (program.reader e) - x).prod) :
    program.HoldsWith (program.reader e) (program.predicate 269).body := by
  have h36 := fun i => RealizedProgram.reader_of_constant e
    (RealizedProgram.kind_of_isConstant (selConstsA (program := program)).1) i
  rw [(pred269_body (program := program))]
  intro n hn
  rw [RealizedProgram.exprLen_add, RealizedProgram.exprLen_prod, (recLens (program := program)).2.2.2.2.2.2.2.2] at hn
  obtain rfl : n = 0 := by omega
  change program.evalE _ (program.domainField 1) (.prod 295 memR) 0 +
    program.evalE _ (program.domainField 1) (.prod 295 memW) 0 =
      program.evalE _ (program.domainField 1) _ 0
  rw [MldsaHCross.domainField1, RealizedProgram.evalE_prod, RealizedProgram.evalE_prod, evalE_36 _ h36]
  have hR : (List.range 295).map (fun t => program.evalE (program.reader e) 1 memR (0 * 295 + t)) =
      (List.range 295).map (readRec (program.reader e)) :=
    List.map_congr_left fun t ht => by
      rw [Nat.zero_mul, Nat.zero_add, evalE_memR e (List.mem_range.1 ht)]
  have hW : (List.range 295).map (fun t => program.evalE (program.reader e) 1 memW (0 * 295 + t)) =
      (List.range 295).map (writeRec (program.reader e)) :=
    List.map_congr_left fun t ht => by
      rw [Nat.zero_mul, Nat.zero_add, evalE_memW e (List.mem_range.1 ht)]
  rw [hR, hW, reads_eq, writes_eq, h]
  exact CharTwo.add_self_eq_zero _

/-- **`h2c.sample.mem.fresh` holds** where every read origin is a Boolean word below its step plus
one (`Checks.fresh`). -/
theorem mem270_of (hbits : ∀ t < 39, ∀ b < 6,
      program.evalE (program.reader e) 1 (.leaf 562) (t * 6 + b) = 0 ∨
        program.evalE (program.reader e) 1 (.leaf 562) (t * 6 + b) = 1)
    (h : ∀ t : Fin 39, Bits.ltConst ((samLowered e).readOrigin t) ((t : ℕ) + 1) = 1) :
    program.HoldsWith (program.reader e) (program.predicate 270).body := by
  rw [(pred270 (program := program))]
  intro t ht
  rw [(freshLen (program := program))] at ht
  change program.evalE _ (program.domainField 1) _ _ =
    program.evalE _ (program.domainField 1) _ _
  rw [MldsaHCross.domainField1, RealizedProgram.evalE_logic,
    evalE_constH e (memConsts (program := program)).2.2.2.2.2.2.2.2.2.1
      (memConsts (program := program)).2.2.2.2.2.2.2.2.2.2.1,
    (memConsts (program := program)).2.2.2.2.2.2.2.2.2.2.2, List.getD_eq_getElem?_getD,
    List.getElem?_replicate, if_pos ht, Option.getD_some, HField.decode_one]
  simp only [RealizedProgram.LogicOp.eval, List.headD_cons, List.getD_cons_succ, List.getD_cons_zero]
  rw [RealizedProgram.Ops.ltWord, RealizedProgram.Ops.ltReduce_congr 6 0 (a' := fun b => program.evalE (program.reader e) 1
    (.leaf 562) (t * 6 + b)) (b' := fun b => Bits.constBit ((t : ℕ) + 1) b)
    (fun b _ => by rw [Nat.zero_add]) (fun b hb => by
      simp only [Nat.zero_add]
      rw [evalE_constH e (memConsts (program := program)).2.2.2.2.2.2.1
          (memConsts (program := program)).2.2.2.2.2.2.2.1,
        show (t : ℕ) * 6 + b = 6 * t + b by ring,
        (memConsts (program := program)).2.2.2.2.2.2.2.2.1 t ht b hb,
        HField.decode_lt_two (Nat.mod_lt _ (by norm_num))]
      rfl), ← RealizedProgram.Ops.ltWord, RealizedProgram.Ops.ltWord_eq_ltConst (fun b hb => hbits t ht b hb) (by omega)]
  have hf : (fun b : Fin 6 => program.evalE (program.reader e) 1 (.leaf 562) (6 * t + b)) =
      fun b : Fin 6 => program.evalE (program.reader e) 1 (.leaf 562) (t * 6 + b) :=
    funext fun b => by rw [Nat.mul_comm]
  have := h ⟨t, ht⟩
  unfold samLowered at this
  dsimp only at this
  exact (congrArg (fun f => Bits.ltConst f ((t : ℕ) + 1)) hf).symm.trans this

/-- **The memory check's predicates hold where its constraints hold** (`SampleInBall.Checks`; the
converse of `checks`), the read origins' coordinates bits. -/
theorem mem_holds_of_checks
    (hc : (samM program F0 FH).Checks (samLowered e) (memDelta (program.reader e)))
    (hbits : ∀ t < 39, ∀ b < 6,
      program.evalE (program.reader e) 1 (.leaf 562) (t * 6 + b) = 0 ∨
        program.evalE (program.reader e) 1 (.leaf 562) (t * 6 + b) = 1)
    {q : ℕ} (hq : q ∈ [267, 268, 269, 270]) :
    program.HoldsWith (program.reader e) (program.predicate q).body := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl
  · exact mem267_of e fun t => by
      rw [hc.unitRow t]
      rfl
  · exact mem268_of e hc.originRow
  · exact mem269_of e hc.perm
  · exact mem270_of e hbits hc.fresh

end GordieHowe.MLDSA44.Native.ROMParams
