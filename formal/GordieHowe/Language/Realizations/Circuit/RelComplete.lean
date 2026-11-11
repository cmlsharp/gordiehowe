-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Circuit.RelCompose
public import GordieHowe.Language.Realizations.Circuit.RelHonest
public import GordieHowe.ProofSystem.GKR.CertificateComplete

@[expose] public section

/-!
# GordieHowe: an accepted certificate accepts the honest input

The completeness direction of a circuit's certificate (`CircuitsAccept`): where every entry of the
circuit holds at the honest reader, every asserted node is zero at the honest input vector.

* **A root's print is zero** where its entry holds
  (`GordieHowe.RealizedProgram.rootZero_of_entryMeaningB`): `X = ±(l − r)` coordinatewise for a
  placed equation or Boolean check, its length the meaning's (the meaning check reads it
  exactly).
* **A family's item is zero** where its realization holds
  (`GordieHowe.RealizedProgram.logupItem_zero`, `GordieHowe.RealizedProgram.macHItem_zero`): the
  cuts give the fraction tree's root, the sum and the chunks, and the meaning closes the item.
* **The circuit** (`GordieHowe.RealizedProgram.circuitAccepts_of_circuitCertB`): at the honest
  input vector every asserted DAG node is zero (each is some entry's assertion, `assertsCoveredB`,
  whose item the entry's kind zeroes), so the scheduling certificate's layered circuit is satisfied
  (`GKR.Certificate.check_complete`) and so is the source circuit
  (`GKR.CertificateBridge.toSource_satisfied_of`). Over all circuits
  (`GordieHowe.RealizedProgram.circuitsAccept_of_certs`), for assignments whose pads are zero off
  the late values' coordinates.
-/

namespace GordieHowe.RealizedProgram

section RootZero

section
variable {ir : RealizedProgram} {I : Interp} {rd : ir.Valuation I}

/-- **A field equation `l = r` zeroes `X = ±(l − r)`** below `X`'s length, `X` no longer than
`l`. -/
theorem rootZero_of_sides {d chr neg1 : ℕ} [CharP (I (ir.domainField d)).K chr]
    (hN : NormModel rd (ir.domainField d) chr) (hneg : (I (ir.domainField d)).decode neg1 = -1)
    {«X» l r : Expr} (hl : ir.exprLen «X» ≤ ir.exprLen l)
    (h : ir.nfUnitEqB d chr neg1 «X» (.sub l r) = true)
    (hs : ∀ i < ir.exprLen l, ir.evalWith rd d l i = ir.evalWith rd d r i) :
    ∀ i < ir.exprLen «X», ir.evalWith rd d «X» i = 0 := by
  intro i hi
  have hz : ir.evalWith rd d (.sub l r) i = 0 := by
    simp only [evalWith, evalE_sub]
    exact sub_eq_zero.2 (hs i (lt_of_lt_of_le hi hl))
  rcases nfUnitEqB_sound hN hneg h with h' | h'
  · rw [h' i hi, hz]
  · rw [h' i hi, hz, neg_zero]

end

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {rd : ir.Valuation I}
  {c chr neg1 : ℕ}

/-- **A placed field equation's meaning gives its sides' agreement** below the left side's length
(the converse of `placedHolds_of_placedSides`). -/
theorem sides_of_placedHolds {b : PredBody} {d : ℕ} {l r : Expr}
    (hb : placedSides? b = some (d, l, r)) (h : ir.PlacedHolds rd b) :
    ∀ i < ir.exprLen l, ir.evalWith rd d l i = ir.evalWith rd d r i := by
  cases b with
  | equal d' l' r' _ =>
    simp only [placedSides?, Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl, rfl⟩ := hb
    exact h
  | mod d' q l' r' real =>
    simp only [placedSides?] at hb
    split_ifs at hb with hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hb
    obtain ⟨rfl, rfl, rfl⟩ := hb
    have hq' : q = 0 ∨ real.form = .field := by
      simpa only [Bool.or_eq_true, Nat.beq_eq, decide_eq_true_eq] using hq
    simpa only [PlacedHolds, hq', ↓reduceIte] using h
  | _ => simp [placedSides?] at hb

/-- **The meaning of an entry zeroes its root's print**: the meaning check reads the print at the
meaning's exact length. -/
theorem rootZero_of_entryMeaningB [CharP (I (ir.circField c)).K chr] (hN : ir.NormModel rd (ir.circField c) chr)
    (hneg : (I (ir.circField c)).decode neg1 = -1) (hB : ir.BoundReads rd)
    {en : CircuitEntry} {«X» : Expr} (h : ir.entryMeaningB c chr neg1 en (some «X») = true)
    (hH : ir.EntryHolds rd en) :
    ∀ i < ir.exprLen «X», ir.evalWith rd (ir.circuit c).domain «X» i = 0 := by
  have _hB := hB
  have hpred : ∀ p : ℕ,
      ir.PlacedHolds rd (ir.predicate p).body →
      (match placedSides? (ir.predicate p).body with
        | some (d, l, r) =>
          Nat.beq d (ir.circuit c).domain && Nat.beq (ir.exprLen l) (ir.exprLen «X») &&
            ir.nfUnitEqB d chr neg1 «X» (.sub l r)
        | none => false) = true →
      ∀ i < ir.exprLen «X», ir.evalWith rd (ir.circuit c).domain «X» i = 0 := by
    intro p hH hm
    split at hm
    · rename_i d l r hs
      simp only [Bool.and_eq_true, Nat.beq_eq] at hm
      obtain ⟨⟨rfl, hl⟩, hu⟩ := hm
      replace hl : ir.exprLen «X» ≤ ir.exprLen l := hl.ge
      exact rootZero_of_sides hN hneg hl hu (sides_of_placedHolds hs hH)
    · cases hm
  cases en with
  | typeCheck p => exact hpred p hH h
  | pred p => exact hpred p hH h
  | alignment _ => simp [entryMeaningB] at h
  | realization _ => simp [entryMeaningB] at h

end RootZero

section FamilyZero

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin GordieHowe.Range
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert Frac FracTree LogupCert MacHCert FamCert relOkE)

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {c : ℕ}
  {ar : CodeArith} {cd : CircuitData}

/-- **A value of a challenge's kind makes `chalNode` some value.** -/
theorem chalNode_isSome_of_kind {u j : ℕ} (hu : u < ir.values.length)
    (hk : (ir.value u).kind = .challenge j) : (ir.chalNode j).isSome = true := by
  unfold chalNode
  rw [List.find?_isSome]
  exact ⟨u, List.mem_range.2 hu, by simp [hk]⟩

theorem logupItem_zero (hM : ir.DerivModel I primeNodes)
    (hC : ir.CircuitFieldOk I c ar cd.chr) (hE : ir.EmitTableOk (cd.env ar) cd.table)
    (hAr : (cd.env ar).ArithOk (I (ir.circField c)).decode) (hcf : ir.chalFieldsB = true)
    {e : ir.Env I} {val : ℕ → (I (ir.circField c)).K}
    {k t g : ℕ} {lc : LogupCert} {as : List Assert}
    (hT : ∀ m < cd.table.size, (cd.table.get m).cut = true →
      ir.WiresOk c (cd.env ar) cd.table (ir.reader e)
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) m)
    (hw : ∀ b a T' : ℕ,
      (ir.circuit c).inputs[b]? = some (InputBlock.realizationPub (.weights t) a T') →
      1 ≤ a → a + T' ≤ (ir.circuit c).publicInputs → ∀ j < T',
        cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val (a + j) =
        ((castElt (e.chal (ir.alphaOf t) 0) : (I (ir.circField c)).K) - j)⁻¹)
    (hg : okB (ir.logupGuardE c ar cd k t g lc as) = true)
    (hc : ∀ q ∈ ir.logupCuts c cd t g lc,
      q.1.val (I (ir.circField c)).decode
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
      q.2.eval (I (ir.circField c)).decode
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val))
    (hH : ir.LogupHoldsAt (ir.reader e) t g) :
    (logupItem cd lc as).2.2.eval (I (ir.circField c)).decode
      (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) = 0 := by
  set α : (I (ir.circField c)).K := castElt (e.chal (ir.alphaOf t) 0) with hαdef
  have hα : ∀ u < ir.values.length, (ir.value u).kind = .challenge (ir.alphaOf t) →
      ir.valueField u = ir.circField c → castElt (ir.reader e u 0) = α :=
    fun u hu hk _ => castElt_reader_challenge hcf e hu hk
  simp only [logupGuardE, okB_seqE, okB_guardE, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq,
    Nat.ble_eq, List.all_eq_true] at hg
  obtain ⟨⟨⟨⟨ht, hgc⟩, hrr⟩, hcf'⟩, hal, ⟨hnl, hnd⟩, ⟨hhl, hhd⟩, hwt, ⟨hdl, htr⟩, has⟩ := hg
  set V := cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val with hV
  set κ := (I (ir.circField c)).decode with hκ
  have h0 : κ 0 = 0 := hC.hom.zero
  have hn1 : κ cd.neg1 = -1 := hAr.neg1
  have h1 : κ 1 = 1 := hC.hom.one
  obtain ⟨hαw, uα, huα, hkα⟩ : (wireAt cd.table lc.alpha 0).val κ V = α ∧
      ∃ u, u < ir.values.length ∧ (ir.value u).kind = .challenge (ir.alphaOf t) := by
    obtain ⟨⟨⟨hak, hacut⟩, halen⟩, hm⟩ := hal
    split at hm
    · rename_i u _ _
      simp only [Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at hm
      obtain ⟨⟨⟨hu, hf⟩, heq⟩, hk⟩ := hm
      have hku : (ir.value u).kind = .challenge (ir.alphaOf t) := by
        split at hk
        · rename_i j hj
          rw [hj, Nat.eq_of_beq_eq_true hk]
        · cases hk
      rw [wire_val_of_eqB hM hE hT hak hacut heq halen, evalE_leaf]
      exact ⟨hα u hu hku hf, u, hu, hku⟩
    · cases hm
  have hN := needleCoords_vals hM hE hT hnl (fun p hp => by
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hnd p hp
    exact ⟨h1, h2, h3, h4⟩)
  have hleaf : lc.tree.dens.map (·.val κ V) =
      (ir.groupNeedles (ir.reader e) (ir.circField c) t g).map (α - ·) := by
    rw [groupNeedles, ← hN, List.map_map]
    refine map_eq_map_of_zip ?_ fun p hp => ?_
    · rw [hdl, ← length_groupNeedles (ir.reader e) (ir.circField c) t g, groupNeedles, ← hN,
        List.length_map]
    · have := hc _ (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inl
        (List.mem_map.2 ⟨p, hp, rfl⟩)))))
      rw [this]
      show TE.eval κ V (teW _) + κ cd.neg1 * TE.eval κ V (teW _) = _
      rw [teW_eval, teW_eval, hαw, hn1, Function.comp_apply]
      ring
  have hroot := GKR.Rel.FracTree.root_eq_fold (κc := κ) (V := V) hC.hom.one htr
    (fun q hq => hc q (List.mem_append.2 (Or.inl (List.mem_append.2 (Or.inr hq)))))
  rw [hleaf, ← FractionTree.balanced_eq_fold] at hroot
  obtain ⟨hwb, hwm⟩ := hwt
  split at hwm
  · rename_i t' a n hblk
    simp only [Bool.and_eq_true, Nat.beq_eq, Nat.ble_eq] at hwm
    obtain ⟨⟨⟨rfl, rfl⟩, ha⟩, hapub⟩ := hwm
    have hbi : (ir.circuit c).inputs[lc.weights]? =
        some (InputBlock.realizationPub (.weights t') a (ir.tableSize t')) := by
      rw [List.getD_eq_getElem _ _ hwb] at hblk
      rw [List.getElem?_eq_getElem hwb, hblk]
    have hwV := hw _ a _ hbi ha hapub
    have hsum : lc.sum.val κ V =
        ∑ j, ir.staticHist (ir.reader e) (ir.circField c) t' g j *
          logupTcoef (ir.tableSize t') α j +
          ∑ j, ir.lateHist (ir.reader e) (ir.circField c) t' g j *
            logupTcoef (ir.tableSize t') α j := by
      have := hc _ (List.mem_append.2 (Or.inr (List.mem_singleton_self _)))
      rw [this, sumL_eval h0, sum_map_flatMap]
      have hmap : (ir.histVals t' g).map (fun u => ∑ j : Fin (ir.tableSize t'),
          ir.histRead (ir.reader e) (ir.circField c) (ir.tableSize t') (some u) j *
            logupTcoef (ir.tableSize t') α j) =
          lc.hists.map (fun h => ((List.range (cd.table.get h).len).map fun j =>
            TE.eval κ V (TE.mul (teW (wireAt cd.table h j))
              (.wire 0 1 (((ir.circuit c).inputs.getD lc.weights default).first + j)))).sum) := by
        refine map_eq_map_of_zip hhl.symm fun p hp => ?_
        obtain ⟨⟨⟨⟨⟨hu, hk⟩, hcut⟩, heq⟩, hlen⟩, hle⟩ := hhd p hp
        refine (sum_histRead_some (w := fun j => (α - (j : (I (ir.circField c)).K))⁻¹) hle).trans ?_
        rw [← hlen]
        refine congrArg List.sum (List.map_congr_left fun j hj => ?_)
        have hj := List.mem_range.1 hj
        show _ = (wireAt cd.table p.2 j).val κ V * (κ 0 + κ 1 * V _)
        rw [wire_val_of_eqB hM hE hT hk hcut heq hj, evalE_leaf, h0, h1, zero_add, one_mul,
          hblk, InputBlock.first, hwV j (by omega)]
      simp only [List.map_map, Function.comp_def]
      rw [← hmap]
      unfold histVals staticHist lateHist
      rcases (ir.groupOf t' g).staticMult with _ | u <;>
        rcases (ir.groupOf t' g).lateMult with _ | u' <;> simp [histRead]
    have hcore : rangeArgument le_rfl (ir.groupNeedles (ir.reader e) (ir.circField c) t' g)
        (logupTcoef (ir.tableSize t') α) (ir.staticHist (ir.reader e) (ir.circField c) t' g)
        (ir.lateHist (ir.reader e) (ir.circField c) t' g) α = true := by
      unfold LogupHoldsAt at hH
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (chalNode_isSome_of_kind huα hkα)
      rw [hv] at hH
      have hp := List.find?_some hv
      have hvl : v < ir.values.length := List.mem_range.1 (List.mem_of_find?_eq_some hv)
      have hk : (ir.value v).kind = .challenge (ir.alphaOf t') := by
        revert hp
        cases (ir.value v).kind <;> simp
      have hαv := hα v hvl hk ((valueField_of_chalFieldsB hcf hvl hk).trans hcf')
      obtain ⟨T', hrows⟩ : ∃ T', (ir.table t').rows = .range T' := by
        unfold rangeRowsB at hrr
        split at hrr
        · exact ⟨_, ‹_›⟩
        · cases hrr
      unfold logupAt at hH
      simp only [hrows] at hH
      rw [← hαv]
      clear_value α
      revert hH
      generalize ir.chalField (ir.alphaOf t') = f at hcf' ⊢
      subst hcf'
      exact id
    rw [rangeArgument_eq_true_iff, fracTree, ← hroot] at hcore
    simp only [show ∀ j : Fin (ir.tableSize t'), Fin.castLE le_rfl j = j from fun _ => rfl] at hcore
    rw [← hsum] at hcore
    simp only [logupItem, TE.eval, teW_eval, hn1]
    linear_combination hcore
  · cases hwm

theorem macHItem_zero (hM : ir.DerivModel I primeNodes)
    (hC : ir.CircuitFieldOk I c ar cd.chr) (hE : ir.EmitTableOk (cd.env ar) cd.table)
    (hAr : (cd.env ar).ArithOk (I (ir.circField c)).decode) (hcf : ir.chalFieldsB = true)
    {e : ir.Env I} {val : ℕ → (I (ir.circField c)).K} {k p : ℕ} {mc : MacHCert} {as : List Assert}
    (hT : ∀ m < cd.table.size, (cd.table.get m).cut = true →
      ir.WiresOk c (cd.env ar) cd.table (ir.reader e)
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) m)
    (hg : okB (ir.macHGuardE c ar cd k p mc as) = true)
    (hc : ∀ q ∈ ir.macHCuts ar cd p mc,
      q.1.val (I (ir.circField c)).decode
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
      q.2.eval (I (ir.circField c)).decode
        (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val))
    (hH : ir.MacHHolds (ir.reader e) p) :
    (macHItem cd mc as).2.2.eval (I (ir.circField c)).decode
      (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) = 0 := by
  have hcs := hc
  unfold macHGuardE at hg
  unfold macHCuts at hcs
  unfold MacHHolds at hH
  split at hg
  · rename_i dx x _ _ _ real hb
    rw [hb] at hcs
    simp only [hb] at hH
    simp only [okB_seqE, okB_guardE, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Nat.ble_eq,
      Option.isNone_iff_eq_none] at hg
    obtain ⟨⟨⟨⟨⟨⟨-, hhp⟩, hdx⟩, hmf⟩, hmfl⟩, hch⟩, hpow, htag, hbits, hchn, -⟩ := hg
    obtain ⟨⟨⟨hpw, hpwc⟩, hpwl⟩, hpwn⟩ := hpow
    obtain ⟨⟨⟨⟨htg, htgc⟩, htgl⟩, htge⟩, -⟩ := htag
    obtain ⟨⟨⟨hbt, hbtc⟩, hbtl⟩, hbtz⟩ := hbits
    split at hpwn
    · rename_i r _ _
      simp only [Bool.and_eq_true] at hpwn
      obtain ⟨hpeq, hpB⟩ := hpwn
      obtain ⟨v, hv, hvf⟩ := chalNode_of_powersB hcf hpB
      have hkf : ir.chalField real.key = real.macField := chalField_of_powersB hpB
      rw [hhp, hv] at hH
      simp only at hH
      have ho := hM.wf.refsOrdered
      have hβ : (castElt (ir.reader e v 0) : (I real.macField).K) =
          castElt (e.chal real.key 0) := by
        rw [castElt_eq_castElt_of_eq hkf, ir.reader_chalNode e hv hvf]
      rw [hβ] at hH
      have hdF : ir.domainField dx < ir.fields.length := by
        rw [hdx]
        show ir.circField c < _
        rw [← hmf]
        exact hmfl
      have hc0 : 0 < ir.charOf (ir.domainField dx) := by
        rw [hdx]
        show 0 < ir.charOf (ir.circField c)
        rw [← hmf]
        omega
      have hpx := padsTo_of_zeroPadB ho hM.registered hM.lawful
        (fun _ _ hk i => reader_of_constant e hk i) hdF hc0 hbtz
      rw [← macHHoldsAt_of_padsTo hpx] at hH
      have hrp : ∀ j < real.chunks, (castElt (ir.reader e r j) : (I real.macField).K) =
          (castElt (e.chal real.key 0) : (I real.macField).K) ^ (j + 1) :=
        fun j hj => reader_powers hM.lawful e hmfl (by omega) hpB hj
      unfold MacHHoldsAt macChunkH at hH
      subst hdx
      generalize real.macField = mf at hmf hrp hH ⊢
      subst hmf
      have hw : ∀ m < cd.table.size, (cd.table.get m).cut = true → ∀ i < (cd.table.get m).len,
          (wireAt cd.table m i).val (I (ir.circField c)).decode
            (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
            ir.nodeSem (cd.env ar) cd.table (ir.reader e) (ir.circuit c).domain m i :=
        fun m hm hc i hi => (hT m hm hc).2 i hi
      have htw : (wireAt cd.table mc.tag 0).val (I (ir.circField c)).decode
          (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
            castElt (ir.reader e real.tag 0) := by
        rw [hw _ htg htgc 0 htgl, ← (eqB_sound ho hE (ir.reader e) _ htge).2]
        rfl
      have hpw' : ∀ j < real.chunks,
          (wireAt cd.table mc.powers j).val (I (ir.circField c)).decode
            (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
              castElt (ir.reader e r j) := by
        intro j hj
        rw [hw _ hpw hpwc j (by omega), ← (eqB_sound ho hE (ir.reader e) _ hpeq).2]
        rfl
      have hbw : ∀ j < real.chunks * real.width, (wireAt cd.table mc.bits j).val
          (I (ir.circField c)).decode
            (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
          castElt (ir.evalPad (ir.reader e) (ir.circuit c).domain
            (cd.table.print (cd.env ar) mc.bits) j) := by
        intro j hj
        rw [hw _ hbt hbtc j (by omega), evalPad,
          ite_eq_left (by rw [(print_spec ho hE (ir.reader e) mc.bits).1]; omega), castElt_self]
        show ir.evalE _ _ (cd.table.treeErase (cd.env ar) mc.bits) j = ir.evalE _ _ _ j
        rw [(print_spec ho hE (ir.reader e) mc.bits).2]
      have hG : ∀ i < real.width,
          (I (ir.circField c)).decode ((PTree.ofList (powList ar 2 real.width 1)).get i) =
            (I (ir.circField c)).decode 2 ^ i := by
        intro i hi
        have hm := map_powList hC.hom 2 real.width 1
        have hl : (powList ar 2 real.width 1).length = real.width := by
          simpa using congrArg List.length hm
        rw [PTree.get_ofList _ (by omega), List.getD_eq_getElem _ _ (by omega)]
        have h1 := congrArg (fun l => l[i]?) hm
        simp only [List.getElem?_map, List.getElem?_range hi, Option.map_some,
          List.getElem?_eq_getElem (by omega : i < (powList ar 2 real.width 1).length),
          Option.some.injEq] at h1
        refine h1.trans ?_
        rw [hC.hom.one, one_mul]
      have hchunk : ∀ j < real.chunks, (mc.chunks.getD j default).val (I (ir.circField c)).decode
            (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
          ∑ i : Fin real.width, (I (ir.circField c)).decode 2 ^ (i : ℕ) *
            castElt (ir.evalPad (ir.reader e) (ir.circuit c).domain
              (cd.table.print (cd.env ar) mc.bits) (j * real.width + i)) := by
        intro j hj
        have h1 := hcs _
          (List.mem_map.2 ⟨_, getD_mem_zipIdx (l := mc.chunks) (i := j) (by omega), rfl⟩)
        rw [h1, sumL_eval hC.hom.zero, List.map_map, sum_range_map_eq_sum_fin]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Function.comp_apply, TE.eval, teW_eval]
        rw [hG i i.2, hbw _ (by have := i.2; nlinarith)]
      have hS : ∑ j : Fin real.chunks,
          (mc.chunks.getD j default).val (I (ir.circField c)).decode
              (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) *
            (wireAt cd.table mc.powers j).val (I (ir.circField c)).decode
              (cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode) val) =
          ∑ j : Fin real.chunks, castElt (e.chal real.key 0) ^ ((j : ℕ) + 1) *
            ∑ i : Fin real.width, (I (ir.circField c)).decode 2 ^ (i : ℕ) *
              castElt (ir.evalPad (ir.reader e) (ir.circuit c).domain
                (cd.table.print (cd.env ar) mc.bits) (j * real.width + i)) :=
        Finset.sum_congr rfl fun j _ => by rw [hchunk j j.2, hpw' j j.2, hrp j j.2, mul_comm]
      have hn1 : (I (ir.circField c)).decode cd.neg1 = -1 := hAr.neg1
      rw [← htw, ← hS] at hH
      simp only [macHItem, TE.eval, teW_eval, sumL_eval hC.hom.zero, List.map_map, hn1,
        sum_map_zipIdx, hchn, sum_range_map_eq_sum_fin, Function.comp_apply, zero_add]
      linear_combination hH
    · cases hpwn
  · simp [okB] at hg

end FamilyZero

end GordieHowe.RealizedProgram

namespace GordieHowe.GKR.Rel

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold

variable {F : Type*} [CommRing F] {ar : CodeArith} {κc : ℕ → F} {w : ℕ} {D : Dag} {Kc : Consts}
  {xs : ℕ → F}

local notation "V" => D.val w (Kc.decode κc) xs

/-- **An accepted relational check's cuts hold**, with no assertion of the DAG assumed. -/
theorem relOk_cuts_sound (hA : ar.Hom κc) (hone : V 0 = 1) {cuts : List (Wire × TE)}
    {zs : List (ℕ × ℕ × TE)} (h : relOk w D Kc ar cuts zs = true) :
    ∀ c ∈ cuts, c.1.val κc V = c.2.eval κc V := by
  unfold relOk at h
  simp only [Bool.and_eq_true, List.all_eq_true] at h
  exact fun c hc => cutOk_sound hA hone (h.1.1 c hc)

/-- **An accepted assertion of a nonzero node** (the converse reading of `zeroOk_sound`): the node
is no input, has the assertion term `0 · 1 · U`, and the tree expression scales `U` or is a cut at
`U`. -/
theorem zeroOk_complete (hA : ar.Hom κc) (hone : V 0 = 1) {z U : ℕ} {e : TE} (hZ : z ≠ 0)
    (h : zeroOk w D Kc ar z U e = true) :
    assertTermB w D z U = true ∧ Nat.ble D.inputs z = true ∧
      (e.scalesNode U = true ∨ V U = e.eval κc V) := by
  have h' := Option.isNone_iff_eq_none.1 h
  unfold zeroR at h'
  have hz : Nat.beq z 0 = false := Bool.eq_false_iff.2 fun h0 => hZ (Nat.eq_of_beq_eq_true h0)
  rw [hz, Bool.cond_false] at h'
  cases ht : assertTermB w D z U
  · simp [ht] at h'
  · rw [ht, Bool.cond_true] at h'
    cases hle : Nat.ble D.inputs z
    · simp [hle] at h'
    · rw [hle, Bool.cond_true] at h'
      refine ⟨rfl, rfl, ?_⟩
      cases hs : e.scalesNode U
      · rw [hs, Bool.cond_false] at h'
        right
        rw [← cutR_sound hA hone h']
        simp [Wire.val, Wire.node, hA.zero, hA.one]
      · exact Or.inl rfl

end GordieHowe.GKR.Rel

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin
open GordieHowe.GKR.CertificateBridge
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert relOkE relOk relOk_eq_okB zeroOk assertTermB
  relOk_cuts_sound zeroOk_complete)

section Items

variable {F : Type*} [Field F] {ar : CodeArith} {κc : ℕ → F} {cd : CircuitData} {xs : ℕ → F}

/-- **An accepted assertion item of a nonzero node zeroes the node its assertion term reads**:
the item passes `unitScaleB` and its tree expression is zero. -/
theorem nodeZero_of_item (hA : ar.Hom κc) (hneg : κc cd.neg1 = -1)
    (hone : cd.dag.val cd.w (cd.consts.decode κc) xs 0 = 1) {z U : ℕ} {e : TE} (hz : z ≠ 0)
    (h : zeroOk cd.w cd.dag cd.consts ar z U e = true) (hu : unitScaleB cd (z, U, e) = true)
    (he : e.eval κc (cd.dag.val cd.w (cd.consts.decode κc) xs) = 0) :
    assertTermB cd.w cd.dag z U = true ∧ Nat.ble cd.dag.inputs z = true ∧
      cd.dag.val cd.w (cd.consts.decode κc) xs U = 0 := by
  obtain ⟨ht, hle, hs | hv⟩ := zeroOk_complete hA hone hz h
  · refine ⟨ht, hle, ?_⟩
    obtain ⟨c0, c1, m⟩ | _ | _ | _ | _ := e <;> simp only [TE.scalesNode,
      Bool.false_eq_true, Bool.and_eq_true, Nat.beq_eq] at hs
    obtain ⟨rfl, rfl⟩ := hs
    have hz' : Nat.beq z 0 = false := Bool.eq_false_iff.2 fun h0 => hz (Nat.eq_of_beq_eq_true h0)
    simp only [unitScaleB, hz', TE.scalesNode, Nat.beq_refl, Bool.and_self, Bool.not_true,
      Bool.or_false, Bool.false_or, Bool.or_eq_true, Nat.beq_eq] at hu
    simp only [TE.eval, hA.zero, zero_add] at he
    rcases hu with rfl | rfl
    · rwa [hA.one, one_mul] at he
    · rw [hneg, neg_one_mul, neg_eq_zero] at he
      exact he
  · exact ⟨ht, hle, hv.trans he⟩

/-- **An asserted node holds** when it is an assertion `0 · 1 · U` (`assertTermsB`) whose read
node `U` is zero. -/
theorem assertHolds_of_term (hT : assertTermsB cd = true) {n U : ℕ} (hn : n ∈ cd.dag.asserts)
    (ht : assertTermB cd.w cd.dag n U = true) (hle : Nat.ble cd.dag.inputs n = true)
    (hU : cd.dag.val cd.w (cd.consts.decode κc) xs U = 0) :
    cd.dag.AssertHolds cd.w (cd.consts.decode κc) xs n := by
  intro t htm _
  have hterms : nodeTerms cd.w cd.dag n = terms cd.w (cd.dag.tree.get n) := nodeTerms_of_le hle
  simp only [assertTermB, List.any_eq_true, Bool.and_eq_true, Nat.beq_eq] at ht
  obtain ⟨t', htm', -, hb⟩ := ht
  rw [← hterms] at htm'
  have h1 := List.all_eq_true.1 hT n hn
  revert htm htm' h1
  cases nodeTerms cd.w cd.dag n with
  | nil => simp
  | cons t0 ts =>
    cases ts with
    | nil =>
      intro htm htm' _
      rw [List.mem_singleton] at htm htm'
      subst htm htm'
      rw [hb, hU, mul_zero]
    | cons _ _ => simp

end Items

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {c : ℕ}
  {ar : CodeArith} {cd : CircuitData}

/-- **Every asserted DAG node is a nonzero asserted node of some entry** (`assertsCoveredB`). -/
theorem exists_entry_of_assert (h : ir.headerB c ar cd = true) {n : ℕ} (hn : n ∈ cd.dag.asserts) :
    ∃ k < cd.entries.length, ∃ a ∈ (cd.entries.getD k default).asserts, a.Z = n ∧ n ≠ 0 := by
  simp only [headerB, headerE, okB_seqE, okB_guardE, Bool.and_eq_true] at h
  obtain ⟨-, -, -, -, -, -, hcov, -⟩ := h
  have hm := mem_of_mem_sortNat (mem_of_subsetSorted hcov n hn)
  simp only [List.mem_filter, List.mem_flatMap, List.mem_map, Bool.not_eq_true',
    beq_eq_false_iff_ne] at hm
  obtain ⟨⟨en, hen, a, ha, rfl⟩, h0⟩ := hm
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hen
  exact ⟨k, hk, a, by rwa [List.getD_eq_getElem _ _ hk], rfl, h0⟩

/-- **A range LogUp entry's guards fix one assertion pair.** -/
theorem logupGuardE_asserts {k t g : ℕ} {lc : GKR.Rel.LogupCert} {as : List Assert}
    (h : okB (ir.logupGuardE c ar cd k t g lc as) = true) : as.length = 1 := by
  simp only [logupGuardE, okB_seqE, okB_guardE, Bool.and_eq_true, Nat.beq_eq] at h
  exact h.2.2.2.2.2.2

/-- **A MAC H entry's guards fix one assertion pair.** -/
theorem macHGuardE_asserts {k p : ℕ} {mc : GKR.Rel.MacHCert} {as : List Assert}
    (h : okB (ir.macHGuardE c ar cd k p mc as) = true) : as.length = 1 := by
  unfold macHGuardE at h
  split at h
  · simp only [okB_seqE, okB_guardE, Bool.and_eq_true, Nat.beq_eq] at h
    exact h.2.2.2.2.2
  · simp [okB] at h

/-- **An accepted circuit certificate accepts the honest input** (the per-circuit core of
`CircuitsAccept`): where every entry of the circuit holds at the honest reader, the bridge's
source circuit is satisfied by the honest input vector (`circuitInput`), where every private block
lies at private positions (`hpriv`) and the committed assignment's pads are zero off the late
values' coordinates (`ha0`). -/
theorem circuitAccepts_of_circuitCertB (hM : ir.DerivModel I primeNodes)
    (hbd : ∀ w < ir.values.length, ir.BoundOk w) (hL : ir.InputLayoutOk c)
    (hpriv : ∀ b ∈ (ir.circuit c).inputs, b.isPublic = false →
        (ir.circuit c).publicInputs ≤ b.first)
    (hC : ir.CircuitFieldOk I c ar cd.chr) (h : ir.circuitCertB c ar cd = true)
    {x : ir.Valuation I} {r : (ir.layout I).Run} {a : ir.Assignment I}
    (ha0 : ir.PadsAgreeOff I ⟨0, 0⟩ a) {d : ℕ} (hfit : (ir.circuit c).inputCount ≤ 2 ^ d)
    (hH : ir.CircuitHolds I c (ir.reader (ir.layoutEnv I x (ir.bindAsg a) r))) :
    (CertificateBridge.toSource cd.layered cd.w
      ((cd.consts.decode (I (ir.circField c)).decode)) d).Satisfied
        (ir.circuitInput I c x r a) := by
  simp only [circuitCertB, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hHd, hE⟩ := h
  have hF := headerFacts_of_headerB hHd
  have := hC.charP
  have hAr : (cd.env ar).ArithOk (I (ir.circField c)).decode :=
    TEnv.arithOk_of_arithB hC.hom hF.arith
  have hx : vecRead (ir.circuitInput I c x r a (d := d)) 0 = 1 := by
    rw [vecRead_circuitInput_pub hL hfit hF.pub]
    simp [publicInput]
  have hκ1 : cd.consts.decode (I (ir.circField c)).decode 1 = 1 := by
    simp only [Consts.decode, hF.one, hC.hom.one]
  have hchk := hF.check
  simp only [GKR.Certificate.check, Bool.and_eq_true, Nat.beq_eq] at hchk
  obtain ⟨⟨⟨⟨honeOk, hin⟩, -⟩, -⟩, -⟩ := hchk
  have hone := val_zero (w := cd.w) (κ := cd.consts.decode (I (ir.circField c)).decode) honeOk hx
  have hval : ∀ q < (ir.circuit c).inputCount,
      cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode)
        (vecRead (ir.circuitInput I c x r a (d := d))) q =
        vecRead (ir.circuitInput I c x r a (d := d)) q := by
    intro q hq
    rw [Dag.val_eq]
    have hb : Nat.blt q cd.dag.inputs = true := by
      rw [← hin, hF.inputs]
      simpa using hq
    rw [hb, Bool.cond_true]
  -- every node's cuts hold
  have hcuts : ∀ m < cd.table.size, ∃ cs, ir.nodeCutsE c (cd.env ar) cd.table m = .ok cs ∧
      CutsHold (ir := ir) (c := c)
        (V := cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode)
          (vecRead (ir.circuitInput I c x r a (d := d)))) cs := by
    intro m hm
    have hn0 : 0 < cd.entries.length := by
      rcases Nat.eq_zero_or_pos cd.entries.length with h0 | h0
      · have := hF.last
        simp [h0] at this
        omega
      · exact h0
    have hhead : ∀ k < cd.entries.length, okB (ir.entryHeadE c ar cd k) = true := fun k hk => by
      have := hE k hk
      simp only [entryCertB, entryCertE, okB_seqE, Bool.and_eq_true] at this
      exact this.1
    have hlast := hF.last
    rw [show Nat.beq cd.entries.length 0 = false from Bool.eq_false_iff.2 fun h' => by
      have := Nat.eq_of_beq_eq_true h'
      omega, Bool.cond_false] at hlast
    obtain ⟨k, hk, hlo, hhi⟩ := exists_block (n := cd.entries.length)
      (lo := fun k => (cd.entries.getD k default).lo)
      (hi := fun k => (cd.entries.getD k default).hi)
      (fun h0 => by simpa using (entryHead_block (hhead 0 h0)).1)
      (fun k hk => by simpa using (entryHead_block (hhead (k + 1) hk)).1)
      (cd.entries.length - 1) (by omega) m (by rw [hlast]; exact hm)
    have hnodes := hE k (by omega)
    simp only [entryCertB, entryCertE, okB_seqE, Bool.and_eq_true] at hnodes
    rw [okB_entryNodesE, List.all_eq_true] at hnodes
    have hmr : m ∈ List.range' (cd.entries.getD k default).lo
        ((cd.entries.getD k default).hi - (cd.entries.getD k default).lo) := by
      rw [List.mem_range'_1]
      exact ⟨hlo, by omega⟩
    obtain ⟨cs, hcs, hrel⟩ := nodeOkE_ok (hnodes.2.1 m hmr)
    exact ⟨cs, hcs, relOk_cuts_sound hC.hom hone hrel⟩
  -- the node table at the honest reader
  have hK : ∀ u es, (ir.value u).kind = .constant es → ∀ i,
      ir.reader (ir.layoutEnv I x (ir.bindAsg a) r) u i =
        (I (ir.valueField u)).decode (es.getD i 0) :=
    fun u es hk i => reader_of_constant _ hk i
  have hR := defReads_reader (e := ir.layoutEnv I x (ir.bindAsg a) r) hM.wf hbd rfl
  have hLeaf := leafReads_circuitInput hL hpriv ha0 hfit hval hAr (E := cd.table)
  have hT := nodeTable_sound hAr hF.table hM.wf.refsOrdered hK hR hLeaf hcuts
  have hB : ir.BoundReads (ir.reader (ir.layoutEnv I x (ir.bindAsg a) r)) := fun u hu e hk =>
    hR u hu e (by simp [valueDef, hk])
  have hN : ir.NormModel (ir.reader (ir.layoutEnv I x (ir.bindAsg a) r)) (ir.circField c) cd.chr :=
    ⟨hM.wf.refsOrdered, hC.pos, hC.dec, hK⟩
  -- the DAG holds
  have hD : cd.dag.Holds cd.w (cd.consts.decode (I (ir.circField c)).decode)
      (vecRead (ir.circuitInput I c x r a (d := d))) := by
    refine ⟨fun n hn => ?_, fun n hn => by simp [hF.noOutputs] at hn⟩
    obtain ⟨k, hk, as0, has0, rfl, hn0⟩ := exists_entry_of_assert hHd hn
    suffices hU : ∃ U, assertTermB cd.w cd.dag as0.Z U = true ∧
        Nat.ble cd.dag.inputs as0.Z = true ∧
        cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode)
          (vecRead (ir.circuitInput I c x r a (d := d))) U = 0 by
      obtain ⟨U, ht, hle, hU⟩ := hU
      exact assertHolds_of_term hF.assertTerms hn ht hle hU
    have hkc : k < (ir.circuit c).entries.length := by rw [← hF.count]; exact hk
    have hHe := hH _ (getD_mem_lt (l := (ir.circuit c).entries) hkc)
    have hh := hE k hk
    simp only [entryCertB, entryCertE, okB_seqE, Bool.and_eq_true] at hh
    have hhead := hh.1
    unfold entryHeadE at hhead
    simp only [okB_seqE, okB_guardE, Bool.and_eq_true] at hhead
    obtain ⟨-, hroot⟩ := hhead
    have hn0' : as0.Z ≠ 0 := hn0
    cases hr : (cd.entries.getD k default).root with
    | some rt =>
      simp only [hr, okB_seqE, okB_guardE, okB_mapE, Bool.and_eq_true, Nat.blt_eq,
        Nat.beq_eq, List.all_eq_true] at hroot
      obtain ⟨⟨⟨⟨hrs, hfl⟩, hal⟩, hus⟩, hrel, hmean⟩ := hroot
      rw [← relOk_eq_okB] at hrel
      unfold relOk at hrel
      simp only [Bool.and_eq_true, List.all_eq_true] at hrel
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem has0
      obtain ⟨hwl, hwv⟩ := hT rt hrs hfl
      have hi' : i < (cd.table.get rt).len := by rw [← hal]; exact hi
      have hmem := mem_rootItems (cd := cd) (r := rt)
        (as := (cd.entries.getD k default).asserts) hi (by rw [hwl]; exact hi')
      rw [List.getD_eq_getElem _ _ hi] at hmem
      refine ⟨_, nodeZero_of_item hC.hom hAr.neg1 hone hn0' (hrel.1.2 _ hmem) (hus _ hmem) ?_⟩
      simp only [Assert.item, TE.eval]
      change Wire.val _ _ _ = 0
      rw [hwv i hi']
      have hps := print_spec hM.wf.refsOrdered hF.table
        (ir.reader (ir.layoutEnv I x (ir.bindAsg a) r)) rt
      have hz := rootZero_of_entryMeaningB hN hAr.neg1 hB hmean hHe i (by rw [hps.1]; exact hi')
      change ir.evalE _ _ _ i = 0 at hz
      rw [congrFun (hps.2 _) i] at hz
      exact hz
    | none =>
      obtain ⟨f, hf, hfam⟩ := famHead_of_entryHeadE ir c ar cd hh.1 hr
      have hs : okB (ir.famSliceE c ar cd k 0 0) = true := hh.2.2
      unfold famHeadE at hfam
      unfold famSliceE famCuts at hs
      rw [hf] at hs
      simp only [Nat.beq_refl, Bool.cond_true, List.drop_zero, okB_mapE, logupCutsT_eq,
        macHCutsT_eq] at hs
      rw [← relOk_eq_okB] at hs
      have hcs := relOk_cuts_sound hC.hom hone hs
      have hw : ∀ (t b a' T' : ℕ),
          (ir.circuit c).inputs[b]? = some (InputBlock.realizationPub (.weights t) a' T') →
          1 ≤ a' → a' + T' ≤ (ir.circuit c).publicInputs → ∀ j < T',
            cd.dag.val cd.w (cd.consts.decode (I (ir.circField c)).decode)
              (vecRead (ir.circuitInput I c x r a (d := d))) (a' + j) =
            ((castElt ((ir.layoutEnv I x (ir.bindAsg a) r).chal (ir.alphaOf t) 0) :
              (I (ir.circField c)).K) - j)⁻¹ := by
        intro t b a' T' hb ha hT' j hj
        have hq : a' + j < (ir.circuit c).publicInputs := by omega
        have hqi : a' + j < (ir.circuit c).inputCount := lt_of_lt_of_le hq hL.pubLe
        rw [hval _ hqi, vecRead_circuitInput_pub hL hfit hq, publicInput_weights hL hb hj]
        rfl
      revert hfam hs hcs hHe
      cases (ir.circuit c).entries.getD k default with
      | alignment n =>
        cases f with
        | alignment b =>
          intro _ hfam _ _
          simp only [okB_seqE, okB_guardE, okB_mapE, Bool.and_eq_true] at hfam
          obtain ⟨hfg, hrel⟩ := hfam
          rw [← relOk_eq_okB] at hrel
          unfold relOk at hrel
          simp only [Bool.and_eq_true, List.all_eq_true] at hrel
          obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem has0
          have hmem : (((cd.entries.getD k default).asserts[i]).Z,
              ((cd.entries.getD k default).asserts[i]).U,
              TE.wire 0 1 ((cd.entries.getD k default).asserts[i]).U) ∈
              (cd.entries.getD k default).asserts.map fun a => (a.Z, a.U, TE.wire 0 1 a.U) :=
            List.mem_map_of_mem (List.getElem_mem hi)
          unfold fillerGuardB at hfg
          simp only [Bool.and_eq_true, Nat.blt_eq] at hfg
          obtain ⟨hbl, hm⟩ := hfg
          have hblk := getD_mem_lt (l := (ir.circuit c).inputs) hbl
          revert hm hblk
          cases (ir.circuit c).inputs.getD b default with
          | filler a0 n' =>
            intro hm hblk
            simp only [Bool.and_eq_true, Nat.beq_eq, List.all_eq_true] at hm
            obtain ⟨⟨rfl, hlen⟩, hU⟩ := hm
            have hUi := hU _ (getD_mem_zipIdx hi)
            rw [List.getD_eq_getElem _ _ hi] at hUi
            simp only at hUi
            have hend := InputBlock.layoutEnd_end_le hL.layout _ hblk
            have hp := hpriv _ hblk rfl
            simp only [InputBlock.first, InputBlock.len] at hend hp
            refine ⟨_, nodeZero_of_item hC.hom hAr.neg1 hone hn0' (hrel.1.2 _ hmem)
              (by simp [unitScaleB]) ?_⟩
            simp only [TE.eval, hC.hom.zero, hC.hom.one, zero_add, one_mul]
            rw [hUi, hval _ (by omega), vecRead_circuitInput_priv hL hfit hblk (by omega)
              (y := 0) (by
                simp only [InputBlock.privValue?, ite_eq_left_iff]
                exact fun h => absurd ⟨by omega, by omega⟩ h)]
          | _ => intro hm; simp at hm
        | _ => intro _ hfam; simp [okB] at hfam
      | typeCheck p => cases f <;> intro _ hfam <;> simp [okB] at hfam
      | pred p => cases f <;> intro _ hfam <;> simp [okB] at hfam
      | realization rc =>
        cases rc with
        | logup t g =>
          cases f with
          | logup lc =>
            intro hHe hfam _ hcs
            simp only [okB_seqE, okB_mapE, Bool.and_eq_true] at hfam
            obtain ⟨hg, hrel⟩ := hfam
            rw [← relOk_eq_okB] at hrel
            unfold relOk at hrel
            simp only [Bool.and_eq_true, List.all_eq_true] at hrel
            have h1 := logupGuardE_asserts hg
            have hz := logupItem_zero hM hC hF.table hAr hF.chal (val := vecRead _) hT
              (hw t) hg hcs hHe
            obtain ⟨a1, ha1⟩ := List.length_eq_one_iff.1 h1
            rw [ha1, List.mem_singleton] at has0
            subst has0
            have hmem := List.mem_singleton_self
              (logupItem cd lc (cd.entries.getD k default).asserts)
            have hZ : (logupItem cd lc (cd.entries.getD k default).asserts).1 = as0.Z := by
              show ((cd.entries.getD k default).asserts.headD default).Z = _
              rw [ha1]
              rfl
            have := nodeZero_of_item hC.hom hAr.neg1 hone (hZ ▸ hn0') (hrel.1.2 _ hmem)
              (by simp [unitScaleB, logupItem, TE.scalesNode]) hz
            rw [hZ] at this
            exact ⟨_, this⟩
          | _ => intro _ hfam; simp [okB] at hfam
        | macH p =>
          cases f with
          | macH mc =>
            intro hHe hfam _ hcs
            simp only [okB_seqE, okB_mapE, Bool.and_eq_true] at hfam
            obtain ⟨hg, hrel⟩ := hfam
            rw [← relOk_eq_okB] at hrel
            unfold relOk at hrel
            simp only [Bool.and_eq_true, List.all_eq_true] at hrel
            have h1 := macHGuardE_asserts hg
            have hz := macHItem_zero hM hC hF.table hAr hF.chal (val := vecRead _) hT
              hg hcs hHe
            obtain ⟨a1, ha1⟩ := List.length_eq_one_iff.1 h1
            rw [ha1, List.mem_singleton] at has0
            subst has0
            have hmem := List.mem_singleton_self
              (macHItem cd mc (cd.entries.getD k default).asserts)
            have hZ : (macHItem cd mc (cd.entries.getD k default).asserts).1 = as0.Z := by
              show ((cd.entries.getD k default).asserts.headD default).Z = _
              rw [ha1]
              rfl
            have := nodeZero_of_item hC.hom hAr.neg1 hone (hZ ▸ hn0') (hrel.1.2 _ hmem)
              (by simp [unitScaleB, macHItem, TE.scalesNode]) hz
            rw [hZ] at this
            exact ⟨_, this⟩
          | _ => intro _ hfam; simp [okB] at hfam
        | _ => cases f <;> intro _ hfam <;> simp [okB] at hfam
  have hsatC := check_complete (K := cd.sched) hF.check hκ1 hx (by rw [hF.width]; exact hD)
  rw [hF.width] at hsatC
  exact toSource_satisfied_of (by rw [hF.inputs]; exact hfit)
    (by have := readsBelow_of_check hF.check; rwa [hF.width] at this) hsatC

/-- **The program's circuits accept honest inputs** (`CircuitsAccept`'s field, at assignments whose
pads are zero off the late values' coordinates): every circuit's certificate checks, its field
meets its codes, every private block lies at private positions, and every source is the bridge's
circuit of its certificate. -/
theorem circuitsAccept_of_certs (hM : ir.DerivModel I primeNodes)
    (hbd : ∀ w < ir.values.length, ir.BoundOk w)
    (hL : ∀ c, ir.InputLayoutOk c)
    (hpriv : ∀ c, ∀ b ∈ (ir.circuit c).inputs, b.isPublic = false →
      (ir.circuit c).publicInputs ≤ b.first)
    (cd : ℕ → CircuitData) (ar : ℕ → CodeArith)
    (hC : ∀ c < ir.circuits.length, ir.CircuitFieldOk I c (ar c) (cd c).chr)
    (h : ∀ c < ir.circuits.length, ir.circuitCertB c (ar c) (cd c) = true)
    (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c)
    (hS : ∀ c : Fin ir.circuits.length, (src c).S = CertificateBridge.toSource (cd c).layered
      (cd c).w ((cd c).consts.decode (I (ir.circField c)).decode) (src c).d) :
    ∀ (c : Fin ir.circuits.length) (x : ir.Valuation I) (r : (ir.layout I).Run)
      (a : ir.Assignment I), ir.PadsAgreeOff I ⟨0, 0⟩ a →
      ir.CircuitHolds I c (ir.reader (ir.layoutEnv I x (ir.bindAsg a) r)) →
      (src c).S.Satisfied (ir.circuitInput I c x r a) := by
  intro c x r a ha0 hH
  rw [hS c]
  exact circuitAccepts_of_circuitCertB hM hbd (hL c) (hpriv c) (hC c c.2) (h c c.2) ha0
    (src c).hfit hH

end GordieHowe.RealizedProgram
