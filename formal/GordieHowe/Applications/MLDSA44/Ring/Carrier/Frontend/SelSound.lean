-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.MLDSA44.Ring.Carrier.Frontend.Select

@[expose] public section

/-!
# GordieHowe frontend: the selection's error of the ML-DSA-44 ring carriers

The ML-DSA-44 ring carriers' signature relation is a product form (`signature.relation`, the
spectral product of `member.a_hat` and `member.t1`), whose kernel reads the selected member's
committed spectra. The realization's selection event (`GordieHowe.RealizedProgram.SelEvent`: the
records the kernel reads are no row's transforms) is bounded by the proof system through
`GordieHowe.RealizedProgram.SelSound`, proved here from the public table's selection
(`GordieHowe.RealizedProgram.TableSelect`):

* `carrierSel`: the one selection a carrier's product form reads (decided per carrier): the
  records `member.a_hat`, `member.t1` (values `55`, `56`) as the scheme-order transforms of length
  `256` at `ψ = psi512` of a row of `ring.keys` (value `53`, `64` rows of `5120`), fingerprinted at
  `member.table.gamma` (challenge `0`) with the exported degree `10240`.
* `selExact_of_not_selBad`: where the selection's predicates hold and the table's event
  (`TableSelect.SelBad`) did not occur, the records are the selected row's transforms
  (`record_row_of_preds`, `rowApply_carrier_key`).
* `selBad_of_selEvent`: the selection event implies the table's event.
* `selSound_carrier`: so the selection event's probability is at most the table's `5143/|F|`
  (`TableSelect.selBad_bound`), below the selection error `10240/|F|` at challenge `0`; at any
  other challenge there is no selection event.
-/

namespace GordieHowe.MLDSA44.Ring.Carrier

open GordieHowe.Bits RealizedProgram IOP
open GordieHowe.MLDSA44.Ring.Native (MldsaRingStmt)
open scoped NNReal ENNReal

/-- **The selection a carrier's product form reads**: the committed spectra `member.a_hat`,
`member.t1` (values `55`, `56`) as the scheme-order transforms of length `256` at `ψ = psi512` of a
row of `ring.keys` (value `53`, `64` rows of `5120` entries), fingerprinted at `member.table.gamma`
(challenge `0`) with the exported degree `10240`. -/
def carrierSel : SelShape := ⟨0, [55, 56], 53, 64, 5120, 256, carrierPsi, false, 0, 10240⟩

set_option linter.unusedSectionVars false

variable {program : RealizedProgram} [CarrierHEmbed program] [MldsaCarrierRelation program]
  [MldsaRingStmt program] [TableSelect program] [MldsaCarrierFront program]
  {F0 FH : RealizedProgram.FieldInterp} [MLDSA44.AField F0]

set_option hygiene false in
local notation "interp" => RealizedProgram.mldsaInterpOf F0 FH

/-- **The records are the selected row's transforms** (`SelExact` at `carrierSel`) where the
selection's predicates hold and the table's event did not occur: coordinate `256 b + m` of
`member.a_hat` is the record's (`rec_aHat`), the transform of block `b` of the selected row
(`record_row_of_preds`, `rowApply_carrier_key`), and coordinate `256 b + m` of `member.t1` the
record's at `4096 + 256 b + m`, the transform of block `16 + b`. -/
theorem selExact_of_not_selBad (hkeys : MldsaRingStmt.keys program = 53) {e : program.Env interp}
    (hp : TableSelect.Preds e) (hno : ¬ TableSelect.SelBad 0 0 e) :
    program.SelExact (program.reader e) carrierSel := by
  have hd := (MldsaCarrierFront.domains (program := program)).1
  have hr53 : program.reader e 53 = e.stmt 53 :=
    RealizedProgram.reader_of_opaque_nil e (hkeys ▸ MldsaRingStmt.keysKind (program := program))
  have h55 := MldsaCarrierRelation.size55 (program := program)
  have h56 := MldsaCarrierRelation.size56 (program := program)
  set idx := TableSelect.idxOf 0 e
  have hrow : ∀ {b m : ℕ}, b < 20 → m < 256 → ∀ {c : ℕ}, c = 256 * b + m → c < 5144 →
      program.evalE (program.reader e) 0 (.ref 1) c =
        Ops.nttScheme 256 ((interp 0).decode carrierPsi)
          (fun k => (castElt (e.stmt 53 (idx * 5120 + (b * 256 + k))) : (interp 0).K)) m := by
    intro b m hb hm c hc hc'
    rw [record_row_of_preds hp hno hc', hc, rowApply_carrier_key _ _ hb hm]
    refine nttScheme_congr _ (fun k hk => ?_) _
    rw [rowEntry, if_pos (by omega), hkeys, show 256 * b + k = b * 256 + k by ring]
  refine ⟨idx, idxOf_lt64_of_preds hp, fun i hi b hb m hm => ?_⟩
  simp only [carrierSel, List.length_cons, List.length_nil] at hi
  have key : ∀ f, f = 0 →
      (castElt (program.reader e (carrierSel.records.getD i 0) (b * carrierSel.n + m)) :
        (interp f).K) =
      Ops.nttOf carrierSel.natural carrierSel.n ((interp f).decode carrierSel.psi)
        (fun c => castElt (program.reader e carrierSel.table (idx * carrierSel.width +
          (program.blockStart carrierSel i + b) * carrierSel.n + c))) m := by
    rintro f rfl
    have hm' : m < 256 := hm
    interval_cases i
    · have hb' : b < 16 := by
        simp only [RealizedProgram.recBlocks, carrierSel, List.getD_cons_zero, h55] at hb
        omega
      show program.evalE (program.reader e) 0 (.leaf 55) (b * 256 + m) =
        Ops.nttScheme 256 ((interp 0).decode carrierPsi)
          (fun c => castElt (program.reader e 53 (idx * 5120 + (0 + b) * 256 + c))) m
      rw [hr53, ← rec_aHat _ (by omega),
        hrow (b := b) (m := m) (by omega) hm' (by ring) (by omega)]
      refine nttScheme_congr _ (fun k _ => ?_) _
      rw [Nat.zero_add, Nat.add_assoc]
    · have hb' : b < 4 := by
        simp only [RealizedProgram.recBlocks, carrierSel, List.getD_cons_succ,
          List.getD_cons_zero, h56] at hb
        omega
      have hbs : program.blockStart carrierSel 1 = 16 := by
        simp [RealizedProgram.blockStart, RealizedProgram.recBlocks, carrierSel, h55]
      show program.evalE (program.reader e) 0 (.leaf 56) (b * 256 + m) =
        Ops.nttScheme 256 ((interp 0).decode carrierPsi)
          (fun c => castElt (program.reader e 53 (idx * 5120 +
            (program.blockStart carrierSel 1 + b) * 256 + c))) m
      rw [hr53, ← rec_t1 _ (by omega),
        hrow (b := 16 + b) (m := m) (by omega) hm' (by ring) (by omega),
        hbs]
      refine nttScheme_congr _ (fun k _ => ?_) _
      rw [Nat.add_assoc]
  exact key _ hd

/-- **The selection event implies the table's event** (`TableSelect.SelBad` at
`member.table.gamma`): the event's equalities that read only what is fixed when `γ` is drawn
include the selection's predicates (`member.select` and the index bits' check), so without the
table's event the records are the selected row's transforms (`selExact_of_not_selBad`). -/
theorem selBad_of_selEvent
    (hk : ∀ q < program.predicates.length,
      program.kernelSel? q = if q = 0 then some carrierSel else none)
    (hwf : program.WellFormed) (hkeys : MldsaRingStmt.keys program = 53)
    (hfix : ∀ p ∈ [(TableSelect.shape program).pred, (TableSelect.shape program).idxPred],
      (program.predicate p).body.isEqual = true ∧
        (program.predNodes (program.predicate p).body).all (program.readsFixedB 0) = true)
    {j : ℕ} {e : program.Env interp} (h : program.SelEvent j e) :
    j = 0 ∧ TableSelect.SelBad 0 0 e := by
  obtain ⟨q, hq, sh, hsh, hj, -, heqs, hx⟩ := h
  rw [hk q hq] at hsh
  split_ifs at hsh with hq0
  cases hsh
  subst hj
  refine ⟨rfl, ?_⟩
  have hp : TableSelect.Preds e := fun p hp =>
    heqs p (TableSelect.inSource p hp).1 (hfix p hp).1
      (RealizedProgram.predReads_fixed_of_readsFixedB hwf (hfix p hp).2)
  by_contra hno
  exact hx (selExact_of_not_selBad hkeys hp hno)

/-- The table's width is `5144`. -/
theorem width_eq : TableSelect.W program = 5144 := by
  unfold TableSelect.W
  rw [MldsaCarrierFront.shape.2.2.2.2.2.2.1, carrierMap_width]

/-- **The selections of an ML-DSA-44 ring carrier have error at most their fingerprint's**
(`RealizedProgram.SelSound`): the one selection a product form reads is `carrierSel` (`hk`),
whose event implies the table's event (`selBad_of_selEvent`), of probability at most `5143/|F|`
at `member.table.gamma` (`TableSelect.selBad_bound`), below the selection error `10240/|F|`
there (`hterms`); at any other challenge there is no selection event. -/
theorem selSound_carrier
    (hk : ∀ q < program.predicates.length,
      program.kernelSel? q = if q = 0 then some carrierSel else none)
    (hwf : program.WellFormed) (hkeys : MldsaRingStmt.keys program = 53)
    (hfix : ∀ p ∈ [(TableSelect.shape program).pred, (TableSelect.shape program).idxPred],
      (program.predicate p).body.isEqual = true ∧
        (program.predNodes (program.predicate p).body).all (program.readsFixedB 0) = true)
    (hchalF : program.chalField 0 = 0)
    (hterms : program.selErrorTerms 0 = [(10240, 0)]) : program.SelSound interp := by
  intro j e
  by_cases hj : j = 0
  · subst hj
    have hchal := (MldsaCarrierFront.shape (program := program)).2.1
    have hb := TableSelect.selBad_bound (f := 0) domainField_shape e
    rw [hchal, width_eq] at hb
    have hsub : Pr[c ← program.ChalVal interp 0 : program.SelEvent 0 (e.setChal 0 c)] ≤
        Pr[c ← program.ChalVal interp 0 : TableSelect.SelBad 0 0 (e.setChal 0 c)] :=
      (PMF.uniformOfFintype _).toOuterMeasure.mono fun c hc =>
        (selBad_of_selEvent hk hwf hkeys hfix hc).2
    refine hsub.trans (hb.trans ?_)
    rw [RealizedProgram.selError, hterms, hchalF]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, Nat.sub_zero]
    exact_mod_cast div_le_div_of_nonneg_right (by norm_num) (by positivity)
  · have hn : ∀ c, ¬ program.SelEvent j (e.setChal j c) := fun c h =>
      hj (selBad_of_selEvent hk hwf hkeys hfix h).1
    have : {c : program.ChalVal interp j | program.SelEvent j (e.setChal j c)} = ∅ :=
      Set.eq_empty_of_forall_notMem hn
    simp only [IOP.probUniform, this, MeasureTheory.measure_empty]
    exact zero_le

end GordieHowe.MLDSA44.Ring.Carrier
