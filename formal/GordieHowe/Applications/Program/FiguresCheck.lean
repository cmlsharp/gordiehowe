-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Program.Conditions
public import GordieHowe.ProofSystem.Program.FiguresCheck
public import GordieHowe.Language.FiguresCheck

/-!
# Soundness of the figures part

The numeric figures checker reads finite descriptors and a shared cells reader. Its soundness
transports the checked numbers through `PackingsOk`; the full statement `FiguresOk` remains at
the ready data. Mask-query coverage, batch validity, split masking and the supported stream-grant
distribution are checked by this part. The grant proof ignores unvisited stage values and
establishes the unchanged exact largest-grant equation.
-/

public section

namespace GordieHowe.ProgramData

open RealizedProgram RealizedProgram.FigCheck SPBCS SPBCS.Configurations

variable (d : ProgramData)

local notation "CR" => CellsReader.ofProgram d.program
local notation "X" => @figuresDomain d CR

/-- **The fields' reader loads are the registry numbers.** -/
theorem fieldReader_loadN (hc : d.CodedOk) (f : ℕ) :
    ofLoad (d.fieldReader hc f).load = d.fieldTable.interp.loadN f :=
  Prod.ext (d.fieldTable.interp.load_eq hc f).1 (d.fieldTable.interp.load_eq hc f).2

/-- **The fields' readers grant no bytes.** -/
theorem fieldReader_grant_zero (hc : d.CodedOk) (f : ℕ) :
    (d.fieldReader hc f).grant = 0 := d.fieldTable.interp.grant_eq hc f

/-- **The field-table index of a ready domain is its program index.** -/
theorem figures_domainField (h : CoreConditions d) (i : Fin d.program.domains.length) :
    d.program.domainField i = d.fieldTable.domainField i :=
  h.fieldTable.domainField_eq i (h.fieldTable.domains_length ▸ i.2)

/-- **The numeric tableau is the ready domain's tableau.** -/
theorem figures_tableau (h : CoreConditions d) (i : Fin d.program.domains.length) :
    (d.ready h.readyFacts i).cert.nums = (X i).t := TableauDesc.cert_nums _ _

/-- **The numeric codec bytes are the ready domain's codec bytes.** -/
theorem figures_fb (h : CoreConditions d) (hc : d.CodedOk) (i : Fin d.program.domains.length) :
    (d.cod hc i).fb = (X i).fb := by
  rw [show (d.cod hc i).fb = d.fieldTable.interp.fbN (d.program.domainField i) from
    d.fieldTable.interp.fb_eq hc _, d.figures_domainField h i]
  rfl

/-- **The numeric reader load is the ready domain's reader load.** -/
theorem figures_load (h : CoreConditions d) (hc : d.CodedOk) (i : Fin d.program.domains.length) :
    ofLoad (d.cod hc i).rd.load = (X i).load := by
  change ofLoad (d.fieldReader hc (d.program.domainField i)).load = _
  rw [d.fieldReader_loadN hc, d.figures_domainField h i]
  rfl

/-- **The numeric field size is the interpretation's specification size.** -/
theorem figures_q (h : CoreConditions d) (i : Fin d.program.domains.length) :
    (X i).q = d.interp.specCard (d.program.domainField i) := by
  rw [show d.interp.specCard (d.program.domainField i) =
    d.fieldTable.interp.cardN (d.program.domainField i) from d.fieldTable.interp.specCard_eq _,
    d.figures_domainField h i]
  rfl

/-- **The checked descriptor figures imply the full figures statement**. The part supplies
batch validity and mask-query coverage; `PackingsOk` supplies the registry's answers to those
queries. Application certificates must explicitly establish that figures are present. -/
theorem FiguresOk.of_descs (hp : d.PackingsOk) (hpresent : d.figures.present = true)
    (hfig : d.figuresPartB = true) : d.FiguresOk := by
  intro h hc
  simp only [figuresPartB, hpresent, Bool.not_true, Bool.false_or, figuresReaderB,
    Bool.and_eq_true] at hfig
  obtain ⟨⟨hbat, hmasks⟩, hfig⟩ := hfig
  have hb : d.program.batchesB = true := by
    rw [batchesB, batchesE_eq_reader, ← CellsReader.batchesK_eq]
    exact hbat
  have hlen := h.fieldTable.domains_length
  have hi (i : Fin d.program.domains.length) : (i : ℕ) < d.fieldTable.domainFields.length :=
    hlen ▸ i.2
  have hD (i : Fin d.program.domains.length) :
      (d.ready h.readyFacts i).Pk.desc (d.packingDesc i) = d.packingDesc i := by
    change (d.fieldTable.interp.packing (d.program.domainField i)).desc _ = _
    rw [d.figures_domainField h i]
    exact hp i (hi i)
  have hmask (i : Fin d.program.domains.length) :
      MasksCover (d.packingDesc i) (d.program.planPacking d.plan i) := by
    apply (masksCoverB_iff _ _).1
    exact (List.all_eq_true.1 hmasks) i (List.mem_range.2 (hi i))
  have ht := d.figures_tableau h
  have hN (i : Fin d.program.domains.length) :
      (X i).N = @ForkReader.domainNums d.program CR i d.plan (d.packingDesc i) := rfl
  have hrload : (fun f => ofLoad (d.fieldReader hc f).load) = d.fieldTable.interp.loadN :=
    funext (d.fieldReader_loadN hc)
  have hcard : d.interp.specCard = d.fieldTable.interp.cardN :=
    funext d.fieldTable.interp.specCard_eq
  change @FigCheck.figuresB d.program ((List.range d.fieldTable.domainFields.length).map X)
    (CellsReader.ofProgram d.program).toPReader d.plan.hash d.fieldTable.interp.loadN d.fieldTable.interp.cardN d.fieldTable.interp.fbN
    d.figures = true at hfig
  rw [← hlen] at hfig
  simp only [FigCheck.figuresB, Bool.and_eq_true, and_assoc, decide_eq_true_eq, beq_iff_eq] at hfig
  obtain ⟨hread, hfits, hmsg, hround, hleaf, hquery, hkq, hdigest, hpos, hkqle, hhash, hkpos,
    hkle, hdomains, hbranches, hbytes, hroundle, hgrzero, hgrants, hgrantmax, hrest,
    hrestgood, hstagegood, hphasegood, herrors, hphases, herrmax, hdefault⟩ := hfig
  have hall (b : DomainFig → Bool)
      (hs : ((List.range d.program.domains.length).map X).all b = true)
      (i : Fin d.program.domains.length) : b (X i) = true :=
    List.all_eq_true.1 hs _ (List.mem_map.2 ⟨i, List.mem_range.2 i.2, rfl⟩)
  have readers : d.ReadersOk hc := by
    rw [← hrload, ← hcard, readersB_iff] at hread
    exact hread
  have fits : d.FitsOk h.readyFacts hc := by
    intro i
    have hf := fitsOk_of (d.ready h.readyFacts i) hb (hD i) (hmask i) (ht i) (hall _ hfits i)
    rw [← d.figures_fb h hc i] at hf
    exact hf
  have hrounds := figRounds_eq (d.ready h.readyFacts) X d.packingDesc hb hN
  have hleaves := figLeaves_eq (d.ready h.readyFacts) X ht
  have hqueries := figQueries_eq (d.ready h.readyFacts) X ht
  have hsplit (i : Fin d.program.domains.length) : (X i).t.split = true := by
    have he := hall _ herrors i
    simp only [DomainFig.fieldRoundsB, Bool.and_eq_true] at he
    exact he.1.1.1.1.1.1.1.1
  refine ⟨readers, fits, ?_, ?_, ?_⟩
  · intro k
    have hm := List.all_eq_true.1 hmsg k (List.mem_range.2 k.2)
    rw [decide_eq_true_eq] at hm
    rw [msgN_eq]
    have hfb : (d.fieldBytes hc).fb = d.fieldTable.interp.fbN :=
      funext (d.fieldTable.interp.fb_eq hc)
    rw [hfb]
    exact hm
  · refine {
      rounds_eq := hround.trans hrounds.symm
      leaves_eq := hleaf.trans hleaves.symm
      queries_eq := hquery.trans hqueries.symm
      kq_eq := hkq.trans (figKq_eq (d.ready h.readyFacts) X d.packingDesc hb hN ht).symm
      digests_eq := hdigest.trans (figDigests_eq (d.ready h.readyFacts) X d.packingDesc hb hN).symm
      pos_eq := hpos.trans (figPos_eq (d.ready h.readyFacts) X ht).symm
      kq_le := hkqle
      k_eq := hhash
      k_pos := hkpos
      k_le := hkle
      bounds := ?_
      grant := ?_
      rest := fun i => forkRestNumbers_of (d.ready h.readyFacts i) hb (hD i) (hmask i) (ht i)
        (hall _ hrest i)
      restGood := ?_
      stageGood := ?_
      phaseGood := ?_
      errors := ?_
      phases := ?_
      errorMax_eq := ?_ }
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.length_map, List.length_range] using hdomains
      · intro i
        have hbnd := of_decide_eq_true (hall _ hbranches i)
        rw [nBranch_eq (D := d.packingDesc i) (d.ready h.readyFacts i) hb]
        exact hbnd
      · intro i
        have hbnd := of_decide_eq_true (hall _ hbytes i)
        change (9 + ((d.ready h.readyFacts i).cert.Sh.nrep + d.maxRead i) * (d.cod hc i).fb) +
          ((1 + (d.cod hc i).fb) + (1 + (d.cod hc i).fb)) ≤ _
        rw [d.figures_fb h hc i]
        have hn := congrArg TableauNums.nrep (ht i)
        change (d.ready h.readyFacts i).cert.Sh.nrep = (X i).t.nrep at hn
        rw [hn]
        exact hbnd
      · exact hrounds.trans_le hroundle
      · intro i
        exact d.fieldReader_grant_zero hc _
    · have happ : (d.program.appReaders (d.samplerReaders hc readers)
          (fun _ => d.chalLoadMax hc)
          (chalLoad_stdReaders_le_std (d.fieldReader hc) d.fieldTable.interp.card readers)).maxGrant = 0 :=
        appReaders_maxGrant _ (stdReaders_grant _ _ _ (d.fieldReader_grant_zero hc)) _ _
      exact hgrantmax.trans (fieldForkGrant_eq (d.ready h.readyFacts) X d.packingDesc hb hN
        (hall _ hgrants) _ happ).symm
    · intro i
      have hg := hall _ hrestgood i
      rw [DomainFig.restGoodB, ← d.figures_load h hc i, nsmulL_eq,
        ← sh_N (d.ready h.readyFacts i) (ht i), byteLenN_eq] at hg
      have hn := congrArg TableauNums.nreq (ht i)
      change (d.ready h.readyFacts i).cert.Sh.nreq = (X i).t.nreq at hn
      rw [← hn] at hg
      exact (chernoffB_iff _ _ _).1 hg
    · intro i
      have hg := hall _ hstagegood i
      rw [DomainFig.stageGoodB, ← d.figures_load h hc i, nsmulL_eq, hN i,
        ← claimCount_eq (D := d.packingDesc i) (d.ready h.readyFacts i) hb] at hg
      exact (chernoffB_iff _ _ _).1 hg
    · intro k
      have hg := List.all_eq_true.1 hphasegood k (List.mem_range.2 k.2)
      rw [← hrload, chalLoadN_eq, nsmulL_eq] at hg
      have hl := congrArg List.length (chalList_idx d.program k)
      rw [List.length_map] at hl
      rw [← hl] at hg
      exact (chernoffB_iff _ _ _).1 hg
    · intro i
      rw [← d.figures_q h i]
      exact fieldRoundsOk_of (d.ready h.readyFacts i) hb (hD i) (hmask i) (ht i) (X i) (hN i) rfl
        (hall _ herrors i)
    · rw [← hcard, phaseErrorsB_iff] at hphases
      exact hphases
    · rw [← hcard] at herrmax
      exact herrmax.trans (figErrorMax_eq (d.ready h.readyFacts) X d.packingDesc hb hN ht hD hmask
        hsplit (d.figures_q h) _ _).symm
  · intro hd
    rw [hd, Bool.not_true, Bool.false_or] at hdefault
    intro i
    have hg := hall _ hdefault i
    rw [DomainFig.defaultGoodB, ← d.figures_load h hc i, nsmulL_eq,
      ← sh_N (d.ready h.readyFacts i) (ht i), byteLenN_eq] at hg
    have hn := congrArg TableauNums.nreq (ht i)
    change (d.ready h.readyFacts i).cert.Sh.nreq = (X i).t.nreq at hn
    rw [← hn] at hg
    exact (chernoffB_iff _ _ _).1 hg

end GordieHowe.ProgramData
