-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkNums
public import GordieHoweNative.ProofSystem.Program.FiguresCheck

/-!
# GordieHowe: the figures' check on numbers is sound

The tests of `FigCheck` (`GordieHoweNative/ProofSystem/Program/FiguresCheck.lean`) on numbers are
the figures' facts: the Chernoff test (`chernoffB_iff`), the samplers' (`samplerOkB_iff`,
`samplerLoadN_eq`), the fractions (`fracSumN_eq`, `dyadicCeilN_eq`, `descFac_eq`), the bytes of a
number (`byteLenN_eq`), the phases' terms (`phaseTermsN_eq`) and errors (`phaseErrorsB_iff`), the
challenges' largest load (`chalLoadN_eq`), the readers' test (`readersB_iff`) and the messages'
bytes (`msgN_eq`).
-/

public section

namespace GordieHowe.RealizedProgram

open Export GordieHowe.SPBCS SPBCS.Configurations

namespace FigCheck

/-! ## Loads and the Chernoff test -/

/-- A load's numbers. -/
abbrev ofLoad (L : Load) : LoadN := (L.draws, L.bytes)

theorem chernoffB_iff (a c E N : ℕ) (L : Load) :
    chernoffB a c E N (ofLoad L) = true ↔ ChernoffOk a c E N L := by
  simp only [chernoffB, Bool.and_eq_true, decide_eq_true_eq, ChernoffOk]
  exact ⟨fun ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ => ⟨h1, h2, h3, h4, h5⟩,
    fun ⟨h1, h2, h3, h4, h5⟩ => ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩⟩

theorem nsmulL_eq (n : ℕ) (L : Load) : nsmulL n (ofLoad L) = ofLoad (L.nsmul n) := rfl

theorem maxL_eq (L L' : Load) : maxL (ofLoad L) (ofLoad L') = ofLoad (L.max L') := rfl

theorem sizeN_eq (n : ℕ) : sizeN n = Nat.size n := by
  unfold sizeN
  split
  · subst_vars; rfl
  · rename_i h
    refine le_antisymm ?_ ?_
    · exact Nat.lt_size.2 (Nat.log2_self_le h)
    · exact Nat.size_le.2 Nat.lt_log2_self

theorem byteLenN_eq (n : ℕ) : byteLenN n = Rejection.byteLen n := by
  rw [byteLenN, sizeN_eq]
  rfl

theorem samplerOkB_iff (rd : Load) (c : ℕ) (s : Sampler) :
    samplerOkB (ofLoad rd) c s = true ↔ samplerOk rd c s := by
  rcases s with _ | _ | (_ | _ | _) <;> simp [samplerOkB, samplerOk]

theorem samplerLoadN_eq (rd : Load) (s : Sampler) :
    samplerLoadN (ofLoad rd) s = ofLoad (samplerLoad rd s) := by
  rcases s with _ | _ | (_ | _ | _) <;> rfl

theorem fracSumN_eq (L : List (ℕ × ℕ)) : fracSumN L = fracSum L := by
  induction L with
  | nil => rfl
  | cons p L ih => simp only [fracSumN, fracSum, ih]

theorem dyadicCeilN_eq (e : ℕ) (p : ℕ × ℕ) : dyadicCeilN e p = dyadicCeil e p := rfl

theorem descFac_eq (n k : ℕ) : descFac n k = n.descFactorial k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [descFac, ih, Nat.descFactorial_succ]

theorem hashBytesN_eq (s : String) : hashBytesN s = Export.hashBytes s := rfl

/-! ## Largest elements -/

theorem le_foldr_max {L : List ℕ} {x : ℕ} (h : x ∈ L) : x ≤ L.foldr max 0 := by
  induction L with
  | nil => cases h
  | cons a L ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

theorem foldr_max_le {L : List ℕ} {m : ℕ} (h : ∀ x ∈ L, x ≤ m) : L.foldr max 0 ≤ m := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons a L ih =>
    exact max_le (h a List.mem_cons_self) (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- **A largest value over `Fin n`** is the list's. -/
theorem sup_fin_eq_foldr (g : ℕ → ℕ) (n : ℕ) :
    (Finset.univ.sup fun j : Fin n => g j) = ((List.range n).map g).foldr max 0 := by
  refine le_antisymm (Finset.sup_le fun j _ => le_foldr_max (List.mem_map.2
    ⟨j, List.mem_range.2 j.2, rfl⟩)) (foldr_max_le fun x hx => ?_)
  obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hx
  exact Finset.le_sup (f := fun j : Fin n => g j) (Finset.mem_univ ⟨j, List.mem_range.1 hj⟩)

theorem foldr_maxL (L : List LoadN) :
    L.foldr maxL (0, 0) = ((L.map Prod.fst).foldr max 0, (L.map Prod.snd).foldr max 0) := by
  induction L with
  | nil => rfl
  | cons a L ih => simp only [List.foldr_cons, ih, maxL, List.map_cons]

variable (ir : RealizedProgram)

/-! ## The phases -/

theorem chalList_idx (k : Fin ir.phases) :
    (ir.chalList k).map (fun j => (j.1 : ℕ)) = chalsOf ir k := by
  rw [chalList, chalsOf, List.map_filterMap, ← List.map_coe_finRange_eq_range, List.filter_map]
  induction (List.finRange ir.challenges.length) with
  | nil => rfl
  | cons b l ih =>
    rw [List.filterMap_cons, List.filter_cons]
    by_cases h : (ir.challenge b).phase = k + 1
    · rw [dite_eq_left_of_eq_true (eq_true h)]
      simp only [Function.comp_apply, h, beq_self_eq_true, ite_true, List.map_cons, ← ih]
      rfl
    · rw [dite_eq_right_of_eq_false (eq_false h)]
      simp only [Option.map_none, Function.comp_apply, h, beq_iff_eq, ite_false, ih]

theorem isSourceChal_eq (j : ℕ) : isSourceChal ir j = decide (ir.IsSourceChal j) := by
  simp only [isSourceChal, IsSourceChal]
  by_cases h1 : j < ir.challenges.length <;> by_cases h2 : 1 ≤ (ir.challenge j).phase <;>
    by_cases h3 : (ir.challenge j).phase ≤ ir.phases <;> simp [h1, h2, h3]

theorem realErrorTermsN_eq (j : ℕ) : realErrorTermsN ir j = ir.realErrorTerms j := rfl

theorem phaseTermsN_eq (cf : ℕ → ℕ) (src : ℕ → ℕ × ℕ) (k : Fin ir.phases) :
    phaseTermsN ir cf src k = ir.phaseTerms cf src k := by
  rw [phaseTermsN, phaseTerms, ← chalList_idx, List.flatMap_map]
  refine List.flatMap_congr fun j _ => ?_
  simp only [isSourceChal_eq, realErrorTermsN_eq, decide_eq_true_eq]

theorem phaseErrorsB_iff (cf : ℕ → ℕ) (src : ℕ → ℕ × ℕ) (num e : ℕ) :
    phaseErrorsB ir cf src num e = true ↔ ir.PhaseErrorsOk cf src num e := by
  simp only [phaseErrorsB, List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq,
    PhaseErrorsOk]
  constructor
  · intro h k
    obtain ⟨h1, h2⟩ := h k k.2
    rw [phaseTermsN_eq ir cf src k, fracSumN_eq] at *
    exact ⟨h1, h2⟩
  · intro h k hk
    obtain ⟨h1, h2⟩ := h ⟨k, hk⟩
    have := phaseTermsN_eq ir cf src ⟨k, hk⟩
    simp only at this
    rw [this, fracSumN_eq]
    exact ⟨h1, h2⟩

/-- **The challenges' largest load** is the reader loads'. -/
theorem chalLoadN_eq (rdl : ℕ → Load) :
    chalLoadN ir (fun f => ofLoad (rdl f)) = ofLoad (ir.stdChalLoad rdl) := by
  rw [chalLoadN, foldr_maxL, stdChalLoad]
  simp only [List.map_map]
  congr 1
  · rw [sup_fin_eq_foldr (fun j => ((samplerLoad (rdl (ir.chalField j)) (ir.challenge j).sampler).nsmul
      (ir.challenge j).size).draws)]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp [samplerLoadN_eq, nsmulL_eq]
  · rw [sup_fin_eq_foldr (fun j => ((samplerLoad (rdl (ir.chalField j)) (ir.challenge j).sampler).nsmul
      (ir.challenge j).size).bytes)]
    congr 1
    refine List.map_congr_left fun j _ => ?_
    simp [samplerLoadN_eq, nsmulL_eq]

/-- **The readers' test** is the reader loads'. -/
theorem readersB_iff (rdl : ℕ → Load) (cf : ℕ → ℕ) :
    readersB ir (fun f => ofLoad (rdl f)) cf = true ↔ ir.ReadersOk rdl cf := by
  simp only [readersB, List.all_eq_true, List.mem_range, samplerOkB_iff, ReadersOk]
  exact ⟨fun h j => h j j.2, fun h j hj => h ⟨j, hj⟩⟩

/-- **Phase `k + 1`'s message bytes** are the reader's, at the fields' element bytes. -/
theorem msgN_eq {I : Interp} (FB : FieldBytesOf I) (k : Fin ir.phases) :
    ir.msgB FB k = @msgN ir (PReader.ofProgram ir) FB.fb k := by
  rw [msgB, msgN, lateList]
  congr 1
  have hn : (PReader.ofProgram ir).nValues = ir.values.length := rfl
  rw [hn, ← List.map_coe_finRange_eq_range, List.map_map, List.map_filterMap]
  simp only [apply_dite (Option.map _), Option.map_some, Option.map_none, dite_eq_ite]
  induction (List.finRange ir.values.length) with
  | nil => rfl
  | cons v l ih =>
    rw [List.filterMap_cons, List.map_cons, List.sum_cons, ← ih]
    have hiff : (decide (PReader.IsLate (r := PReader.ofProgram ir) ir v) &&
        ((PReader.ofProgram ir).value v).phase - 1 == (k : ℕ)) = true ↔
          ir.IsLate v ∧ (ir.value v).phase - 1 = k := by
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      rfl
    by_cases h : ir.IsLate v ∧ (ir.value v).phase - 1 = k
    · simp only [ite_eq_left h, Function.comp_apply, ite_eq_left (hiff.2 h), List.sum_cons]
      rfl
    · simp only [ite_eq_right h, Function.comp_apply, ite_eq_right (fun h' => h (hiff.1 h')), zero_add]

end FigCheck

/-! ## The readers' grants -/

section Grants

theorem piDep_grant {n : ℕ} {β : Fin n → Type} [∀ i, Fintype (β i)]
    (r : ∀ i, SPBCS.CReader (β i)) (L : Load) (hL) : (SPBCS.CReader.piDep r L hL).grant = ∑ i, (r i).grant :=
  rfl

theorem pi_grant_zero {C : Type} [Fintype C] (n : ℕ) (r : SPBCS.CReader C) (h : r.grant = 0) :
    (SPBCS.CReader.pi n r).grant = 0 := by
  simp [SPBCS.CReader.pi, piDep_grant, h]

theorem piList_grant_zero {α : Type} [DecidableEq α] {β : α → Type}
    [∀ a, Fintype (β a)] (l : List α) (hl : l.Nodup) (hall : ∀ a, a ∈ l)
    (r : ∀ a, SPBCS.CReader (β a)) (L : Load) (hL : ∀ a, (r a).load ≤ L) (h : ∀ a, (r a).grant = 0) :
    (SPBCS.CReader.piList l hl hall r L hL).grant = 0 := by
  change (SPBCS.CReader.piDep _ L fun _ => hL _).grant = 0
  rw [piDep_grant]
  exact Finset.sum_eq_zero fun i _ => h _

theorem samplerReader_grant {F : FieldInterp} (rd : SPBCS.CReader F.K) (s : Sampler) (h) :
    (samplerReader rd s h).grant = rd.grant := by
  rcases s with _ | _ | (_ | _ | _)
  · rfl
  · exact h.elim
  · rfl
  · rfl
  · rfl

variable {ir : RealizedProgram} {I : Interp} {P : Export.Plan}

/-- **The application's readers grant nothing** when the fields' readers grant nothing. -/
theorem appReaders_maxGrant (rd : SamplerReaders I ir) (h : ∀ j, (rd j).grant = 0)
    (L : Fin ir.phases → Load) (hL) : (ir.appReaders rd L hL).maxGrant = 0 := by
  refine SpecReaders.Ungranted.maxGrant_eq fun j => ?_
  change ((ir.phaseReader rd L hL _).cast _).grant = 0
  rw [SPBCS.CReader.cast_grant]
  exact piList_grant_zero _ _ _ _ _ _ fun j => pi_grant_zero _ _ (h _)

theorem stdReaders_grant (rd : ∀ f, SPBCS.CReader (I f).K) {cf : ℕ → ℕ}
    (hcard : ∀ f, Fintype.card (I f).K = cf f) (h : ir.ReadersOk (fun f => (rd f).load) cf)
    (hg : ∀ f, (rd f).grant = 0) (j : Fin ir.challenges.length) :
    (stdReaders rd hcard h j).grant = 0 := by
  rw [stdReaders, samplerReader_grant, hg]

theorem runGrant_zero (pos : ℕ) (es : List (ℕ × Option ℕ)) (nc : ℕ) (r : Fin nc → Finset ℕ) :
    PEdge.runGrant (fun _ => 0) pos es nc r = 0 := by
  induction es generalizing pos nc with
  | nil => rfl
  | cons s es ih => simp [PEdge.runGrant, PEdge.stageGrant, ih]

/-- **A run grants nothing** when every stage it visits grants nothing. -/
theorem runGrant_zero_on (gr : ℕ → ℕ) (pos : ℕ) (es : List (ℕ × Option ℕ))
    (nc : ℕ) (r : Fin nc → Finset ℕ)
    (h : ∀ i, pos ≤ i → i < pos + es.length → gr i = 0) :
    PEdge.runGrant gr pos es nc r = 0 := by
  induction es generalizing pos nc with
  | nil => rfl
  | cons s es ih =>
    rw [PEdge.runGrant, ih]
    · simp only [PEdge.stageGrant, h pos le_rfl (by simp), ↓reduceIte, max_self]
    · intro i hlo hhi
      apply h i (by omega)
      simpa only [List.length_cons] using (show i < pos + (es.length + 1) by omega)

/-- **A run's grant is its first stage's grant** when later visited stages grant nothing
and that first stage touches at least two claims whenever it receives a grant. -/
theorem runGrant_first (gr : ℕ → ℕ) (es : List (ℕ × Option ℕ)) (nc : ℕ)
    (r : Fin nc → Finset ℕ)
    (hz : ∀ i, 0 < i → i < es.length → gr i = 0)
    (ht : gr 0 ≠ 0 → es ≠ [] ∧ 2 ≤ (PEdge.routeAt 0 r).nt) :
    PEdge.runGrant gr 0 es nc r = gr 0 := by
  cases es with
  | nil =>
    have : gr 0 = 0 := by by_contra h; exact (ht h).1 rfl
    simpa only [PEdge.runGrant] using this.symm
  | cons e es =>
    rw [PEdge.runGrant, runGrant_zero_on]
    · rw [max_zero, PEdge.stageGrant]
      by_cases h : gr 0 = 0
      · simp only [h, ↓reduceIte]
      · simp only [h, ↓reduceIte, (ht h).2]
    · intro i hlo hhi
      exact hz i (by omega) (by simp only [List.length_cons]; omega)

theorem forkJoinGrant_empty {d : ℕ} {P : Export.Plan} (R : ir.FieldReady I d P) :
    forkJoinGrant R {} = 0 := by
  simp [forkJoinGrant, runGrant_zero]

/-- **The transcript's largest grant is `0`** with no stream grants and readers granting none. -/
theorem fieldForkGrant_zero (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)
    {n : ℕ} {Q : GordieHowe.IOP.ProtocolSpec n} (appR : SpecReaders Q) (h : appR.maxGrant = 0) :
    ProofSystem.fieldForkGrant R (fun _ => {}) appR = 0 := by
  simp [ProofSystem.fieldForkGrant, h, forkJoinGrant_empty]

end Grants

/-! ## A domain's figures -/

section Domain

open FigCheck

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan} (R : ir.FieldReady I d P)
  {D : PackingDesc} {t : TableauNums}

local notation "CR" => CellsReader.ofProgram ir
local notation "N" => @ForkReader.domainNums ir (CR) d P D

theorem rs_length : R.rs.length = (N).degrees.length := by
  change _ = ((ForkReader.es ir d P).map (·.degree)).length
  rw [List.length_map, ForkReader.es, ← R.rs_plan, List.length_map]

/-- **The branches are the numbers'.** -/
theorem nBranch_eq (hbat : ir.batchesB = true) :
    ir.nBranch d R.Pk = (N).batches.length + 1 := by
  rw [nBranch, batches_length R hbat R.batchesOk]

/-- **`forkRoundsConst` is the numbers'.** -/
theorem forkRoundsConst_eq (hbat : ir.batchesB = true) :
    forkRoundsConst R = ((N).batches.map fun b =>
      2 * b.rounds + 5 + (if b.bits then 8 else 0)).sum +
        (N).circuits.length + (2 * (N).degrees.length + 3) := by
  have hB := R.batchesOk
  rw [forkRoundsConst]
  have h1 := sum_fin_idx (cbatches_idx hbat hB) (fun b => 2 * (ir.batch b).rounds + 5)
  have h2 := sum_fin_idx (sumBatches_idx hbat hB) (fun b => 2 * (ir.batch b).rounds + 13)
  have h3 := sum_fin_idx (mbatches_idx hbat hB) (fun b => 2 * (ir.batch b).rounds + 5)
  have h4 := sum_fin_idx (sumMBatches_idx hbat hB) (fun b => 2 * (ir.batch b).rounds + 13)
  erw [h1, h2, h3, h4]
  have hc : (N).circuits.length = (ForkReader.circs ir d).length := List.length_map ..
  rw [hc, ← circs_length, rs_length (D := D) R, batches_eq]
  simp only [List.map_append, List.sum_append, List.map_map]
  congr 1

/-- **`forkRoundsAt` is the numbers'.** -/
theorem forkRoundsAt_eq (hbat : ir.batchesB = true) (x : DomainFig) (hx : x.N = N) :
    forkRoundsAt R = x.rounds := by
  rw [forkRoundsAt, forkRoundsConst_eq R hbat, DomainFig.rounds, hx]
  congr 1
  have h1 : ∑ i : Fin (ir.circs d).length, ((2 + 4 * ir.circW d i) * ir.circL d i + 1) =
      ((ForkReader.circs ir d).map fun c =>
        (2 + 4 * ForkReader.circW ir c) * ForkReader.circL ir c + 1).sum := by
    rw [← sum_fin_idx (circs_idx (ir := ir) d)
      (fun c => (2 + 4 * ForkReader.circW ir c) * ForkReader.circL ir c + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [circW, circuitWidth_eq]
    rfl
  rw [h1]
  change _ = ((ForkReader.circs ir d).map (fun c => (ForkReader.circW ir c, ForkReader.circL ir c))
    |>.map fun c => (2 + 4 * c.1) * c.2 + 1).sum
  rw [List.map_map]
  rfl

theorem batchesNum_eq (hbat : ir.batchesB = true) (x : DomainFig) (hx : x.N = N) :
    ir.batchesNum d R.Pk = x.batchesNum := by
  have hB := R.batchesOk
  have sm : ∀ (L : List ℕ) (f g : ℕ → ℕ), (∀ b, f b = g b) → (L.map f).sum = (L.map g).sum :=
    fun L f g h => congrArg List.sum (List.map_congr_left fun b _ => h b)
  rw [batchesNum, DomainFig.batchesNum, hx, batches_eq]
  simp only [List.map_append, List.sum_append, List.map_map]
  rw [show (ir.cbatches d R.Pk).map (fun cb => ir.batchNum cb.idx) =
      ((ir.cbatches d R.Pk).map fun cb => (cb.idx : ℕ)).map ir.batchNum by rw [List.map_map]; rfl,
    show (ir.sumBatches d R.Pk).map (fun sb => ir.batchNum sb.cb.idx + 2 * 4) =
      ((ir.sumBatches d R.Pk).map fun sb => (sb.cb.idx : ℕ)).map (fun b => ir.batchNum b + 2 * 4)
      by rw [List.map_map]; rfl,
    show (ir.mbatches d R.Pk).map (fun cb => ir.mergedNum cb.idx) =
      ((ir.mbatches d R.Pk).map fun cb => (cb.idx : ℕ)).map ir.mergedNum by rw [List.map_map]; rfl,
    show (ir.sumMBatches d R.Pk).map (fun sb => ir.mergedNum sb.mb.idx + 2 * 4) =
      ((ir.sumMBatches d R.Pk).map fun sb => (sb.mb.idx : ℕ)).map (fun b => ir.mergedNum b + 2 * 4)
      by rw [List.map_map]; rfl,
    cbatches_idx hbat hB, sumBatches_idx hbat hB, mbatches_idx hbat hB, sumMBatches_idx hbat hB]
  congr 1
  congr 1
  congr 1
  all_goals first
    | exact sm _ _ _ fun b => by
        simp [RealizedProgram.batchNum, RealizedProgram.mergedNum]
        try omega
    | exact List.map_congr_left fun b _ => by
        simp [RealizedProgram.batchNum, RealizedProgram.mergedNum]
        try omega

theorem gkrWidth_eq (x : DomainFig) (hx : x.N = N) : ir.gkrWidth d = x.gkrWidth := by
  rw [gkrWidth, DomainFig.gkrWidth, hx]
  change _ = (((ForkReader.circs ir d).map fun c => (ForkReader.circW ir c, ForkReader.circL ir c)).map
    (·.1)).foldr max 0
  rw [List.map_map, ← circs_idx, List.map_map, List.foldr_map]
  congr 1
  funext c m
  simp [circuitWidth_eq]

/-! ### The certificate's numbers with the mask test -/

theorem cert_split (ht : R.cert.nums = t) (hs : t.split = true) : R.cert.masking = .split := by
  have : (R.cert.masking.kind == .split) = true := by rw [← hs, ← ht]; rfl
  revert this
  generalize R.cert.masking = m
  cases m <;> simp [LigeroCert.Masking.kind]

theorem cert_testNum (ht : R.cert.nums = t) (hs : t.split = true) : R.cert.testNum = 1 := by
  rw [LigeroCert.testNum, cert_split R ht hs]

theorem cert_columnNum (ht : R.cert.nums = t) (hs : t.split = true) (x : DomainFig) (hx : x.t = t) :
    R.cert.columnNum = x.columnNum := by
  rw [LigeroCert.columnNum, LigeroCert.maskCount, cert_split R ht hs, DomainFig.columnNum, hx,
    descFac_eq, descFac_eq]
  subst ht
  rfl

theorem cert_jointNum (ht : R.cert.nums = t) (x : DomainFig) (hx : x.t = t) :
    R.cert.jointNum = x.jointNum := by
  rw [LigeroCert.jointNum, DomainFig.jointNum, hx, descFac_eq]
  subst ht
  rfl

theorem cert_columnDen (ht : R.cert.nums = t) (x : DomainFig) (hx : x.t = t) :
    R.cert.columnDen = x.columnDen := by
  rw [LigeroCert.columnDen, DomainFig.columnDen, hx, descFac_eq]
  subst ht
  rfl

/-- **The round charges are the numbers'.** -/
theorem chargeFracs_eq (hbat : ir.batchesB = true) (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) (ht : R.cert.nums = t) (hs : t.split = true)
    (x : DomainFig) (hx : x.N = N) (hxt : x.t = t) :
    R.chargeFracs x.q = x.chargeFracs := by
  rw [FieldReady.chargeFracs, DomainFig.chargeFracs, cert_testNum R ht hs,
    cert_columnNum R ht hs x hxt, cert_jointNum R ht x hxt, cert_columnDen R ht x hxt,
    R.np_eq hD hc, batchesNum_eq R hbat x hx, gkrWidth_eq x hx, rs_length (D := D) R, hx, hxt]
  subst ht
  rfl

/-- **The round charges' bounds from the numbers.** -/
theorem fieldRoundsOk_of (hbat : ir.batchesB = true) (hD : R.Pk.desc D = D)
    (hc : MasksCover D (ir.planPacking P d)) (ht : R.cert.nums = t) (x : DomainFig) (hx : x.N = N)
    (hxt : x.t = t) {num e : ℕ} (h : x.fieldRoundsB num e = true) :
    FieldRoundsOk R x.q num e := by
  simp only [DomainFig.fieldRoundsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hs, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  rw [hxt] at hs
  rw [fieldRoundsOk_iff, cert_testNum R ht hs, cert_columnNum R ht hs x hxt,
    cert_jointNum R ht x hxt, cert_columnDen R ht x hxt, R.np_eq hD hc, batchesNum_eq R hbat x hx,
    gkrWidth_eq x hx, rs_length (D := D) R, ← hx]
  have he : R.cert.exceptions = x.t.exceptions := by rw [hxt, ← ht]; rfl
  have hn : R.cert.Sh.nrep = x.t.nrep := by rw [hxt, ← ht]; rfl
  have hnp : x.N.np = ForkReader.npN ir d P D := by rw [hx]; rfl
  rw [he, hn, ← hnp]
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- **At least two first-stage claims touch** whenever the total exceeds the certified
bound on passing claims by at least two. -/
theorem firstStage_touches (hbat : ir.batchesB = true)
    (h : 2 + (N).later ≤ (N).claims) :
    2 ≤ (PEdge.routeAt 0 (claimReads R.rs)).nt := by
  have hp := card_passing_le (ir := ir) R.rs
  rw [← PEdge.routeAt_np] at hp
  have hn := PEdge.routeAt_nt_le 0 (claimReads R.rs)
  rw [laterBound_eq (D := D) R hbat] at hp
  have hn' := hn.trans (claimCount_eq (D := D) R hbat)
  omega

/-- **The descriptor's checked grants give the join's exact largest grant.** -/
theorem forkJoinGrant_eq (hbat : ir.batchesB = true) (x : DomainFig) (hx : x.N = N)
    (h : x.grantsB = true) : forkJoinGrant R x.grants = x.joinGrant := by
  simp only [DomainFig.grantsB, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq,
    decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  rw [forkJoinGrant, DomainFig.joinGrant]
  congr 1
  apply runGrant_first
  · intro i hi hlt
    have hlen : (edgeShapes R.rs).length = (x.N.degrees).length := by
      rw [edgeShapes, List.length_mapIdx, rs_length (D := D) R, ← hx]
    rcases h.1 i (by omega) with heq | heq
    · omega
    · exact heq
  · intro hg
    obtain ⟨hne, htouch⟩ := h.2.resolve_left hg
    constructor
    · have hlen : (edgeShapes R.rs).length = (x.N.degrees).length := by
        rw [edgeShapes, List.length_mapIdx, rs_length (D := D) R, ← hx]
      intro he
      simp only [he, List.length_nil] at hlen
      omega
    · rw [hx] at htouch
      exact firstStage_touches R hbat htouch

end Domain

/-! ## The figures of all domains -/

section Domains

open FigCheck

variable {ir : RealizedProgram} {I : Interp} {P : Export.Plan}
  (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)
  (x : ℕ → DomainFig) (D : ℕ → PackingDesc)

private theorem sum_indexed {n : ℕ} {α : Type} (x : ℕ → α) (f : α → ℕ)
    (g : Fin n → ℕ) (h : ∀ i, g i = f (x i)) :
    (∑ i, g i) = (((List.range n).map x).map f).sum := by
  rw [List.map_map, ← sum_fin_eq_list]
  exact Finset.sum_congr rfl fun i _ => h i

private theorem sup_indexed {n : ℕ} {α : Type} (x : ℕ → α) (f : α → ℕ)
    (g : Fin n → ℕ) (h : ∀ i, g i = f (x i)) :
    (Finset.univ.sup g) = (((List.range n).map x).map f).foldr max 0 := by
  rw [List.map_map, ← sup_fin_eq_foldr]
  exact Finset.sup_congr rfl fun i _ => h i

variable (hbat : ir.batchesB = true)
  (hN : ∀ i : Fin ir.domains.length,
    (x i).N = @ForkReader.domainNums ir (CellsReader.ofProgram ir) i P (D i))
  (ht : ∀ i : Fin ir.domains.length, (R i).cert.nums = (x i).t)

include hbat hN in
/-- **The total round count is the descriptor count.** -/
theorem figRounds_eq :
    figRounds R = roundsTotal ir ((List.range ir.domains.length).map x) := by
  rw [figRounds, forkRoundsTotal, roundsTotal, List.length_map, List.length_range]
  congr 1
  exact sum_indexed x _ _ fun i => forkRoundsAt_eq (R i) hbat (x i) (hN i)

include ht in
/-- **The largest leaf count is the descriptor count.** -/
theorem figLeaves_eq : figLeaves R = leaves ((List.range ir.domains.length).map x) := by
  rw [figLeaves, leaves]
  exact sup_indexed x _ _ fun i => sh_N (R i) (ht i)

include ht in
/-- **The query count is the descriptor count.** -/
theorem figQueries_eq : figQueries R = queries ((List.range ir.domains.length).map x) := by
  rw [figQueries, queries]
  exact sum_indexed x _ _ fun i => congrArg TableauNums.nreq (ht i)

include hbat hN ht in
/-- **The verifier query count is the descriptor count.** -/
theorem figKq_eq : figKq R = kqN ir ((List.range ir.domains.length).map x) := by
  rw [figKq, kqN, figRounds_eq R x D hbat hN, figQueries_eq R x ht, figLeaves_eq R x ht,
    Nat.log2_eq_log_two]
  congr 2
  exact sum_indexed x _ _ fun i => (nBranch_eq (D := D i) (R i) hbat).trans
    (congrArg (fun n => n.batches.length + 1) (hN i).symm)

include hbat hN in
/-- **The digest count is the descriptor count.** -/
theorem figDigests_eq : figDigests R = digestsN ir ((List.range ir.domains.length).map x) := by
  rw [figDigests, digestsN, figRounds_eq R x D hbat hN, List.length_map, List.length_range]
  congr 2
  exact sup_indexed x _ _ fun i => (nBranch_eq (D := D i) (R i) hbat).trans
    (congrArg (fun n => n.batches.length + 1) (hN i).symm)

include ht in
/-- **The total position count is the descriptor count.** -/
theorem figPos_eq : figPos R = posN ((List.range ir.domains.length).map x) := by
  rw [figPos, posN]
  exact sum_indexed x _ _ fun i => sh_N (R i) (ht i)

include hbat hN ht in
/-- **The largest round error is the descriptor calculation**, including the phase errors. -/
theorem figErrorMax_eq
    (hD : ∀ i : Fin ir.domains.length, (R i).Pk.desc (D i) = D i)
    (hc : ∀ i : Fin ir.domains.length, MasksCover (D i) (ir.planPacking P i))
    (hs : ∀ i : Fin ir.domains.length, (x i).t.split = true)
    (hq : ∀ i : Fin ir.domains.length, (x i).q = I.specCard (ir.domainField i))
    (src : ℕ → ℕ × ℕ) (e : ℕ) :
    figErrorMax R src e = errorMaxN ir ((List.range ir.domains.length).map x) I.specCard src e := by
  rw [figErrorMax, errorMaxN]
  congr 1
  · exact sup_indexed x _ _ fun i => by
      rw [← hq i, chargeFracs_eq (R i) hbat (hD i) (hc i) (ht i) (hs i) (x i) (hN i) rfl]
      rfl
  · rw [← sup_fin_eq_foldr]
    exact Finset.sup_congr rfl fun i _ => by
      rw [phaseTermsN_eq ir _ _ i, fracSumN_eq, dyadicCeilN_eq]

include hbat hN in
/-- **The transcript's largest grant is the largest checked join grant** when its application
readers grant no bytes. -/
theorem fieldForkGrant_eq (hg : ∀ i : Fin ir.domains.length, (x i).grantsB = true)
    {n : ℕ} {Q : GordieHowe.IOP.ProtocolSpec n} (appR : SpecReaders Q) (ha : appR.maxGrant = 0) :
    ProofSystem.fieldForkGrant R (fun i => (x i).grants) appR =
      (((List.range ir.domains.length).map x).map (·.joinGrant)).foldr max 0 := by
  rw [ProofSystem.fieldForkGrant, ha, zero_max]
  exact sup_indexed x _ _ fun i => forkJoinGrant_eq (R i) hbat (x i) (hN i) (hg i)

end Domains

end GordieHowe.RealizedProgram
