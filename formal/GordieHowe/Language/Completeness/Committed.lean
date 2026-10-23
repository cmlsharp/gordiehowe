-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Completeness.Bound

@[expose] public section

/-!
# GordieHowe: completeness certificates, the honest committed values

What the honest committed values of a certificate (`genCommitted`) satisfy at the source environment
`srcEnvL x (genCommitted G x s) (padSpaceLate l) c π` where the execution accepts: it agrees with
the environment of the execution on the source values (`agreeOnSourceVals_srcEnvC`), so the source
program holds there (`sourceSatAt_srcEnvC`); every static histogram counts its group's needles
(`staticHistsCount_srcEnvC`), and one beside a late histogram its static members' needles
(`mixedStatic_srcEnvC`); the committed cells lie in their bases (`honestCellsC_base`); the
quotient of a one-digit `mod_q` lies in its range (`holds_oneDigitQuot_srcEnvC`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP Range

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-- **The honest committed values off the source values are naturals**: committed generators'
values, static histograms, or `0`. -/
theorem genCommitted_natCast_of_not_source (G : Gens) (x s : ir.Valuation I) {v : ℕ}
    (hv : ¬ ir.IsSourceValue v) (i : ℕ) :
    ∃ n : ℕ, ir.genCommitted I G x s v i = (n : (I (ir.valueField v)).K) := by
  unfold genCommitted
  rw [if_neg hv]
  split
  · split_ifs
    · exact ⟨_, rfl⟩
    · exact ⟨0, by simp⟩
  · unfold withGens
    rw [if_neg hv]
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · split
      · exact ⟨_, rfl⟩
      · exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩

variable (ir) in
/-- **The facts of group `g` of table `t` with the static histogram `h`** at the
certificate's generators `G`: a committed cell of the table's size in the field of the table's challenge,
no source value, generated as the group's static histogram; the needles and the rows read no
challenge and no late value, and no value they read is a static histogram or a pad copy; a table
packed at a value has its members packed alike. -/
structure StaticGroupFactsC (G : Gens) (t g h : ℕ) : Prop where
  /-- A committed cell. -/
  cell : ir.privCellB h = true
  /-- The table's size. -/
  size : (ir.value h).size = ir.tableSize t
  /-- The field of the table's challenge. -/
  field : ir.valueField h = ir.chalField (ir.alphaOf t)
  /-- No source value. -/
  notSource : ¬ ir.IsSourceValue h
  /-- Generated as the group's static histogram. -/
  own : G.at h = .staticHist t g
  /-- The needles read no challenge, no late value, no static histogram and no pad copy. -/
  needles : ∀ m ∈ ir.staticMembers t g, ∀ w ∈ ir.histNodes t m,
    (ir.readsT.getD w []).isEmpty = true ∧
      ∀ u ∈ ir.valReads ir.fuel w, (∀ t' g', G.at u ≠ .staticHist t' g') ∧
        (ir.value u).kind.isPadCopy = false
  /-- The rows read no challenge, no late value, no static histogram and no pad copy. -/
  rows : ∀ w ∈ ir.histRowNodes t, (ir.readsT.getD w []).isEmpty = true ∧
    ∀ u ∈ ir.valReads ir.fuel w, (∀ t' g', G.at u ≠ .staticHist t' g') ∧
      (ir.value u).kind.isPadCopy = false
  /-- A table packed at a value has its members packed alike. -/
  packed : ir.packGroupB t g = true

variable (ir I) in
/-- **The facts the honest committed values need** at the certificate's generators `G`: the source
part well formed, no source value a pad copy or a message, each source late value's pad space
containing its type; every value bound to its digits a source value and the record of a two-sided
or digit lookup, and every such lookup with its facts; every
group with no late histogram, with its static histogram's facts or no members; every committed cell
at a node of its source value's type whose subgroup contains `1`; every node-typed value that is no
source value and no late value a committed cell whose type contains the naturals. -/
structure CommittedFacts (G : Gens) : Prop where
  /-- The source part is well formed. -/
  sourceValid : ir.SourceValid
  /-- No source value is a pad copy. -/
  srcNoPadCopy : ∀ u < ir.values.length, ir.IsSourceValue u → (ir.value u).kind.isPadCopy = false
  /-- No source value is a message. -/
  srcNoMessage : ir.SrcNoMessage
  /-- The pad space of every source late value contains its type. -/
  srcLatePads : ∀ v < ir.values.length, ir.IsSourceValue v → ir.IsLate v → ir.latePadTypeB v = true
  /-- The predicates the source values' intervals read are source predicates. -/
  ivlSource : ∀ q < ir.predicates.length, ir.ivlSourceB q = true
  /-- Every value bound to its digits is a source value and the record of a two-sided or digit
  lookup. -/
  boundRecs : ir.BoundRecs
  /-- Every two-sided and digit lookup has its facts, its digits generated as its digits. -/
  digitLookups : ir.DigitLookupsC G
  /-- A group with no late histogram has its static histogram with its facts, or no members. -/
  groups : ∀ t < ir.tables.length, ∀ g < ir.groupCountOf t, (ir.groupOf t g).lateMult = none →
    ((ir.groupOf t g).staticMult = none ∧ ir.members t g = []) ∨
      ∃ h, (ir.groupOf t g).staticMult = some h ∧ ir.StaticGroupFactsC G t g h
  /-- Every committed cell is at a node of its source value's type. -/
  cellNodes : ∀ v < ir.values.length, ir.isCellValue (ir.value v).domain v = true →
    ir.cellNodeB v = true
  /-- The subgroup of every committed cell's node contains `1`. -/
  oneMem : ∀ v < ir.values.length, ir.isCellValue (ir.value v).domain v = true →
    ir.oneMemB I v = true
  /-- Every node-typed value that is no source value and no late value is a committed cell whose
  type contains the naturals. -/
  realTypes : ∀ v < ir.values.length, (ir.value v).typeSource = .node → ¬ ir.IsLate v →
    ¬ ir.IsSourceValue v → ir.privCellB v = true ∧ ir.NatTyped I v

variable (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
  {G : Gens} (R : ir.CommittedFacts I G) {x s l : ir.Valuation I} {c : ∀ k, (ir.layout I).Ch k}
  (hA : ir.SourceAcceptingAt I (ir.execEnv I x s l c)) (π : (ir.layout I).Pads)

set_option hygiene false in
/-- The source environment of the honest committed values of the execution. -/
local notation "SE" => ir.srcEnvL I x (ir.genCommitted I G x s) (ir.padSpaceLate I l) c π

include R hA in
/-- **An accepting execution's source late values lie in their pad spaces**
(`CommittedFacts.srcLatePads`): `padSpaceLate` keeps them. -/
theorem padSpaceLate_of_acceptingC :
    ∀ u, ir.IsSourceValue u → ir.IsLate u → ∀ i < (ir.value u).size,
      ir.padSpaceLate I l u i = l u i := by
  intro u hu hl i hi
  have hlt := lt_of_isLate hl
  have ht := hA.types u hlt hu (by rw [kind_of_isLate hl]; rfl) i hi
  rw [reader_of_late _ (kind_of_isLate hl)] at ht
  have hr : (ir.execEnv I x s l c).late u i = l u i := by
    simp only [execEnv, hlt, hl, hi, and_self, ite_true]
  rw [hr] at ht
  unfold padSpaceLate
  rw [if_pos (mem_space_of_latePadTypeB (R.srcLatePads u hlt hu hl) ht)]

include hwf hI hL R hA in
/-- **The source environment of the honest committed values agrees with the environment of the
execution on the source values** (`agreeOnSourceVals_srcEnv_of`; the values bound to their digits by
`bindAsgC_bound_honest`, the source late values by `padSpaceLate`). -/
theorem agreeOnSourceVals_srcEnvC : Env.AgreeOnSourceVals SE (ir.execEnv I x s l c) :=
  agreeOnSourceVals_srcEnv_of c π (padSpaceLate_of_acceptingC R hA) R.srcNoPadCopy
    (fun _ _ hb => bindAsgC_bound_honest hwf hI hL R.boundRecs R.digitLookups hA π
      (lt_of_isBound hb) hb)
    fun _ hu _ => genCommitted_of_source G x s hu

include hwf hI hL R hA in
/-- **The source program holds at the source environment of the honest committed values.** -/
theorem sourceSatAt_srcEnvC : ir.SourceSatAt SE :=
  ((agreeOnSourceVals_srcEnvC hwf hI hL R hA π).sourceSatAt_congr R.sourceValid
    R.srcNoMessage).2 hA.sat

include hwf hI hL R hA in
/-- **A value reading no challenge, no late value, no static histogram and no pad copy** reads at
the source environment of the honest committed values as in the environment of the execution of
the committed generators' values (`withGens`) at the default challenges: there the honest
committed values are those values, and a value bound to its digits, a source value, reads its
phase-`0` value in both (`bindAsgC_bound_honest`). -/
theorem reader_srcEnvC_eq_exec1 {w : ℕ}
    (he : (ir.readsT.getD w []).isEmpty = true)
    (hv : ∀ u ∈ ir.valReads ir.fuel w, (∀ t' g', G.at u ≠ .staticHist t' g') ∧
      (ir.value u).kind.isPadCopy = false) :
    ir.reader SE w =
      ir.reader (ir.execEnv I x (ir.withGens I G x s) 0 (ir.chal0 I)) w := by
  have hn := notMem_nodeReads_of_isEmpty hwf he
  refine read_congr_vals (e := SE)
    (e' := ir.execEnv I x (ir.withGens I G x s) 0 (ir.chal0 I)) rfl _ w
    (fun c hc => absurd hc (hn _)) (fun u hu => absurd hu (hn _)) fun u hu => ?_
  obtain ⟨hh, hpc⟩ := hv u hu
  rcases hb : (ir.value u).kind.isBound
  swap
  · have hs := (R.boundRecs u (lt_of_isBound hb) hb).1
    change (ir.bindAsg (ir.honestAsg I (ir.genCommitted I G x s) π)).val u = _
    rw [bindAsgC_bound_honest hwf hI hL R.boundRecs R.digitLookups hA π (lt_of_isBound hb) hb,
      execEnv_asg_val_of_isBound x _ 0 (ir.chal0 I) hb]
    funext i
    simp only [withGens, hs, ite_true]
  have hpc' : ∀ w m, (ir.value u).kind ≠ .padCopy w m := fun w m hk => by
    rw [hk] at hpc
    cases hpc
  have hval : ir.genCommitted I G x s u = ir.withGens I G x s u := by
    funext i
    unfold genCommitted
    by_cases hs : ir.IsSourceValue u
    · simp only [withGens, hs, ite_true]
    · rw [if_neg hs]
      split
      · rename_i t g hg
        exact absurd hg (hh t g)
      · rfl
  change (ir.bindAsg (ir.honestAsg I (ir.genCommitted I G x s) π)).val u = _
  rw [ir.bindAsg_val_of_isBound _ hb, honestAsg_val_eq_ite hpc', hval,
    execEnv_asg_val_of_not_bound x _ 0 (ir.chal0 I) hb]

include hwf hI hL R hA in
/-- **A static histogram reads its honest counts** (`staticHistNat`) at the source environment of
the honest committed values: the honest committed value is the honest counts read where the
committed generators' values are (`genCommitted`), and the values they read read alike there
(`reader_srcEnvC_eq_exec1`, `staticHistNat_congr`). -/
theorem reader_srcEnvC_staticHist {t g h : ℕ} (hF : ir.StaticGroupFactsC G t g h)
    (j : Fin (ir.tableSize t)) :
    (castElt (ir.reader SE h j) : (I (ir.chalField (ir.alphaOf t))).K) =
      ((ir.staticHistNat (ir.reader SE) t g j : ℕ) : (I (ir.chalField (ir.alphaOf t))).K) := by
  have hj : (j : ℕ) < (ir.value h).size := by rw [hF.size]; exact j.isLt
  rw [reader_srcEnvL_of_privCellB x _ _ c π hF.cell hj, staticHistNat_congr (fun m hm w hw =>
    reader_srcEnvC_eq_exec1 hwf hI hL R hA π (hF.needles m hm w hw).1 (hF.needles m hm w hw).2)
    fun w hw => reader_srcEnvC_eq_exec1 hwf hI hL R hA π (hF.rows w hw).1 (hF.rows w hw).2]
  unfold genCommitted
  rw [if_neg hF.notSource, hF.own]
  simp only [if_pos hj]
  have hf := hF.field
  revert hf
  generalize ir.valueField h = a
  intro hf
  subst hf
  simp

include hwf hI hL R hA in
/-- **A static histogram beside a late one counts its static members' needles** at the source
environment of the honest committed values, its table a range (`reader_srcEnvC_staticHist`). -/
theorem mixedStatic_srcEnvC {t g h : ℕ} (hF : ir.StaticGroupFactsC G t g h) (hr : ir.IsRange t)
    (hl : (ir.groupOf t g).lateMult.isSome = true) (j : Fin (ir.tableSize t)) :
    (castElt (ir.reader SE h j) : (I (ir.chalField (ir.alphaOf t))).K) =
      (((ir.staticNeedles (ir.reader SE) (ir.chalField (ir.alphaOf t)) t g).count
        (j : (I (ir.chalField (ir.alphaOf t))).K) : ℕ) : (I (ir.chalField (ir.alphaOf t))).K) := by
  rw [reader_srcEnvC_staticHist hwf hI hL R hA π hF j,
    staticHistNat_of_none (gammaPack_of_isRange hr), rowCountNat_of_isRange hr]
  simp only [staticHistNeedles, hl, ite_true]

include hwf hI hL R hA in
/-- **The records' counts of a table packed at a value are its honest counts** at the source
environment of the honest committed values, where the packing is injective on the table's records
in the environment of the execution (`PackFreeAt`). -/
theorem tupleCount_srcEnvC {t g P A : ℕ} {b : Expr} (ht : t < ir.tables.length)
    (hg : g < ir.groupCountOf t) (hl : (ir.groupOf t g).lateMult = none)
    (hp : ir.gammaPack? t = some (P, A, b)) (hB : ir.packGroupB t g = true)
    (hP : ir.PackFreeAt I (ir.execEnv I x s l c)) (j : Fin (ir.tableSize t)) :
    ((ir.tupleCountNat (ir.reader SE) t P A b (ir.staticMembers t g) j : ℕ) :
        (I (ir.chalField (ir.alphaOf t))).K) = ir.honestCounts (ir.reader SE) t g j := by
  set f := ir.chalField (ir.alphaOf t)
  have hrd : ∀ w, ir.IsSourceValue w → ir.reader SE w = ir.reader (ir.execEnv I x s l c) w :=
    fun w hw =>
      (agreeOnSourceVals_srcEnvC hwf hI hL R hA π).reader_eq R.sourceValid R.srcNoMessage hw
  unfold packGroupB at hB
  rw [hp] at hB
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hB
  obtain ⟨⟨hPs, hbs⟩, hms⟩ := hB
  have hsm : ir.staticMembers t g = ir.members t g := by simp [staticMembers, hl]
  rw [hsm] at hms ⊢
  obtain ⟨e', hr⟩ : ∃ e', (ir.table t).rows = .expr e' := by
    unfold gammaPack? at hp
    split at hp
    · exact ⟨_, ‹_›⟩
    · cases hp
  have hneed : ir.groupNeedles (ir.reader SE) f t g =
      ((ir.members t g).flatMap (ir.memberTuples (ir.reader SE) f P A)).map
        (packWith fun i => (castElt (ir.reader SE P i) : (I f).K)) := by
    unfold groupNeedles
    rw [List.map_flatMap]
    refine List.flatMap_congr fun m hm => ?_
    have hmB := hms m hm
    unfold packMemberB at hmB
    split at hmB
    · rename_i b' hb'
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hmB
      exact memberVals_of_memberBase hb' hmB.1 _ _
    · cases hmB
  have hhc : ir.honestCounts (ir.reader SE) t g =
      rowHistogram (ir.tableRow (ir.reader SE) f t) (ir.groupNeedles (ir.reader SE) f t g) := by
    unfold honestCounts
    simp only [hr]
    rfl
  -- The records and the powers read alike in the environment of the execution.
  have hT : ∀ k, ir.tupleOf (ir.reader SE) f A b k =
      ir.tupleOf (ir.reader (ir.execEnv I x s l c)) f A b k :=
    fun k => by simp only [tupleOf, evalE_congr fun w hw => hrd w (hbs w hw)]
  have hMT : ∀ m ∈ ir.members t g, ir.memberTuples (ir.reader SE) f P A m =
      ir.memberTuples (ir.reader (ir.execEnv I x s l c)) f P A m := by
    intro m hm
    have hmB := hms m hm
    unfold packMemberB at hmB
    unfold memberTuples
    split
    · rename_i b' hb'
      rw [hb'] at hmB
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hmB
      simp only [tupleOf, evalE_congr fun w hw => hrd w (hmB.2 w hw)]
    · rfl
  have hpw : (fun i => (castElt (ir.reader SE P i) : (I f).K)) =
      fun i => (castElt (ir.reader (ir.execEnv I x s l c) P i) : (I f).K) := by
    rw [hrd P hPs]
  have hmem : ∀ a, (a ∈ (ir.members t g).flatMap (ir.memberTuples (ir.reader SE) f P A) ∨
      ∃ k : Fin (ir.tableSize t), ir.tupleOf (ir.reader SE) f A b k = a) →
      a ∈ ir.packTuples (ir.reader (ir.execEnv I x s l c)) t := by
    intro a ha
    unfold packTuples
    rw [hp]
    rcases ha with ha | ⟨k, rfl⟩
    · rw [List.flatMap_congr hMT] at ha
      exact List.mem_append_right _ (List.mem_flatMap.2 ⟨g, List.mem_range.2 hg, ha⟩)
    · rw [hT]
      exact List.mem_append_left _ (List.mem_map.2 ⟨k, List.mem_range.2 k.isLt, rfl⟩)
  rw [hhc, funext (tableRow_of_gammaPack hp (ir.reader SE) f), hneed,
    rowHistogram_map_of_injOn (packWith fun i => (castElt (ir.reader SE P i) : (I f).K))
      (fun k => ir.tupleOf (ir.reader SE) f A b k) _
      (fun a ha a' ha' he => hP t ht P A b hp a (hmem a ha) a' (hmem a' ha')
        (by rw [hpw] at he; exact he)) j]
  unfold tupleCountNat
  split_ifs <;> rfl

include hwf hI hL R hA in
/-- **The groups with no late histogram count their needles at the source environment** of the
honest committed values, where the packings are injective in the environment of the execution. -/
theorem staticHistsCount_srcEnvC (hP : ir.PackFreeAt I (ir.execEnv I x s l c)) :
    ir.StaticHistsCount SE := by
  intro t ht g hg hl
  rcases R.groups t ht g hg hl with ⟨hs, hm⟩ | ⟨h, hs, hF⟩
  · funext j
    rw [← rowCountNat_groupNeedles]
    unfold Range.combined staticHist lateHist histRead groupNeedles
    rw [hs, hl, hm]
    simp [rowCountNat_nil]
  · funext j
    unfold Range.combined staticHist lateHist histRead
    rw [hs, hl]
    simp only [dite_eq_ite, ite_self, add_zero]
    have hj : (j : ℕ) < (ir.value h).size := by rw [hF.size]; exact j.isLt
    rw [if_pos hj, reader_srcEnvC_staticHist hwf hI hL R hA π hF j]
    rcases hp : ir.gammaPack? t with _ | ⟨P, A, b⟩
    · rw [staticHistNat_of_none hp, ← rowCountNat_groupNeedles]
      simp [staticHistNeedles, hl]
    · rw [staticHistNat_of_some hp]
      exact tupleCount_srcEnvC hwf hI hL R hA π ht hg hl hp hF.packed hP j

include hwf hI hL R hA in
/-- **The node-typed values other than the generated late values lie in their types at the source
environment** of the honest committed values. -/
theorem srcTypesHold_srcEnvC : ir.SrcTypesHold SE := by
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  intro v hv hts hgen i hi
  by_cases hsrc : ir.IsSourceValue v
  · exact hsat.types v hv hsrc hts i hi
  · obtain ⟨hc, hnat⟩ := R.realTypes v hv hts (fun hl => hsrc (hgen hl)) hsrc
    rw [reader_srcEnvL_of_privCellB x _ _ c π hc hi]
    obtain ⟨n, hn⟩ := genCommitted_natCast_of_not_source G x s hsrc i
    rw [hn]
    exact hnat.inType n

include hwf hL R hA in
/-- **The honest committed values and their pad copies lie in their cells' bases** where the
execution accepts. -/
theorem honestCellsC_base {d v i : ℕ} (h : CellKey.val v i ∈ ir.cellKeys d) :
    (castElt (ir.copyVal I (ir.genCommitted I G x s) π v i) : (I (ir.domainField d)).K) ∈
      ir.cellBase I d ⟨_, h⟩ := by
  obtain ⟨hv, hc, hi⟩ := (ir.mem_cellKeys_val).1 h
  have hfd := ir.isCellValue_valueField hc
  have hdd : (ir.value v).domain = d := by
    unfold isCellValue at hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact hc.1
  have hB := R.cellNodes v hv (by rw [hdd]; exact hc)
  unfold cellNodeB at hB
  rcases hnode : (ir.value v).node with _ | nr
  · rw [hnode] at hB
    cases hB
  rw [hnode] at hB
  have h1 : (1 : (I (ir.domainField d)).K) ∈ (I (ir.domainField d)).node nr.name := by
    have := one_mem_of_oneMemB (R.oneMem v hv (by rw [hdd]; exact hc)) hnode
    rwa [hdd] at this
  have hnat : ∀ n : ℕ, ((n : ℕ) : (I (ir.domainField d)).K) ∈ (I (ir.domainField d)).node nr.name :=
    fun n => by simpa using AddSubgroup.nsmul_mem _ h1 n
  simp only [cellBase, hnode]
  have hbit : ∀ b : Bool, (castElt ((I (ir.valueField v)).ofBool b) : (I (ir.domainField d)).K) ∈
      (I (ir.domainField d)).node nr.name := fun b => by
    cases b
    · simpa [FieldInterp.ofBool] using AddSubgroup.zero_mem _
    · simpa [FieldInterp.ofBool, castElt_one_of_eq hfd] using h1
  unfold copyVal
  split
  · exact hbit _
  · rename_i hk
    by_cases hsrc : ir.IsSourceValue v
    · rw [genCommitted_of_source G x s hsrc]
      have hpriv : (ir.value v).kind = .priv := by
        unfold isCellValue at hc
        simp only [Bool.and_eq_true] at hc
        revert hc hk
        cases (ir.value v).kind <;> simp
      have ht := hA.types v hv hsrc (by rw [hpriv]; rfl) i hi
      rw [reader_execEnv_priv x s l c hpriv (hwf.values v hv).1 (by rw [hdd]; exact h)] at ht
      simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
        beq_iff_eq] at hB
      rcases hB with hB | (hB | hB) | ⟨-, hB⟩
      · exact absurd hsrc hB
      · rw [hB] at ht
        exact castElt_mem_node hfd ht
      · rw [hB] at ht
        rcases ht with ht | ht
        · rw [ht, castElt_zero]
          exact AddSubgroup.zero_mem _
        · rw [ht, castElt_one_of_eq hfd]
          exact h1
      · rw [hB, hdd, hL.rootNode _ (domainField_lt hwf (hdd ▸ (hwf.values v hv).1))]
        exact AddSubgroup.mem_top _
    · obtain ⟨n, hn⟩ := genCommitted_natCast_of_not_source G x s hsrc i
      rw [hn, castElt_natCast hfd]
      exact hnat n

include hwf hI hL R hA in
/-- **The intervals' facts of the source values hold at the source environment** of the honest
committed values where the execution accepts: the predicates they read are source predicates
(`CommittedFacts.ivlSource`), which hold there by the agreement on the source values. -/
theorem ivlFacts_srcEnvC (hbd : ir.StmtBounded I x) :
    ir.IvlFacts (ir.reader SE) ir.declaredRanges
      (fun v => v < ir.values.length ∧ ir.IsSourceValue v) := by
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  refine ⟨fun v es hk i => reader_of_constant _ hk i,
    fun v name args hk hne i => reader_opaque _ hk hne i,
    fun v hv hS hts i hi => hsat.types v hv hS.2 hts i hi, ?_, ?_, ?_,
    fun vN hvN i hi => by
      rw [reader_of_declared _ hvN]
      exact hbd vN hvN i hi⟩
  · intro v hS q hq hts he
    exact hsat.preds _ (predicate_mem hq)
      (inSource_of_ivlSourceB_equal (R.ivlSource q hq) he hS.1 hS.2 (.inr hts))
  · intro v hS q hq d rec set r hb hk hrec
    exact hsat.preds _ (predicate_mem hq) (inSource_of_ivlSourceB_lookup (R.ivlSource q hq) hb hk
      hrec hS.2)
  · intro v hS q hq he hr
    have hsrc := inSource_of_ivlSourceB_equal (R.ivlSource q hq) he hS.1 hS.2 (.inl hr)
    refine ⟨hsat.preds _ (predicate_mem hq) hsrc, fun w hw => ⟨?_, R.sourceValid.preds _
      (predicate_mem hq) hsrc w hw⟩⟩
    have hpo := hwf.predicates _ (predicate_mem hq)
    unfold predNodes at hw
    rcases List.mem_append.1 hw with hw | hw
    · obtain ⟨de, hde, hw⟩ := List.mem_flatMap.1 hw
      exact ((hpo.1 de hde).2.range w hw)
    · revert hw he
      cases (ir.predicate q).body <;> simp [tableCols, PredBody.isEqual]

include hwf hI hL R hA in
/-- **The quotient of a one-digit `mod_q` lies in its range at the source environment** of the
honest committed values, at value intervals `L` justified by the source program (`hLok`). -/
theorem holds_oneDigitQuot_srcEnvC (hbd : ir.StmtBounded I x) {m rid : ℕ}
    (h : ir.oneDigitQuotAtB (ir.srcLeafIvl primeNodes) m rid = true) :
    ir.HoldsWith (ir.reader SE) (ir.predicate rid).body := by
  have hsat := sourceSatAt_srcEnvC hwf hI hL R hA π
  have hIF := ivlFacts_srcEnvC hwf hI hL R hA π hbd
  have hlok := ir.leafIvl_justified primeNodes ir.declaredRanges
  have hm : m < ir.predicates.length := by
    by_contra hm
    have hd : ir.predicate m = default := List.getD_eq_default _ _ (Nat.le_of_not_lt hm)
    unfold oneDigitQuotAtB at h
    rw [hd] at h
    change false = true at h
    cases h
  have hB := h
  unfold oneDigitQuotAtB at hB
  split at hB
  · rename_i d q e e' real hbody
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hB
    obtain ⟨⟨⟨⟨⟨⟨hsrc, -⟩, hq⟩, h2⟩, hder⟩, hqr⟩, hiv⟩ := hB
    have hmod := hsat.preds _ (predicate_mem hm) hsrc
    rw [hbody] at hmod
    have hpo := hwf.predicates _ (predicate_mem hm)
    rw [hbody] at hpo
    have he := hpo.1 (d, e) (by simp [PredBody.exprs])
    have he' := hpo.1 (d, e') (by simp [PredBody.exprs])
    have hlen : ir.exprLen e = ir.exprLen e' := hpo.2
    have hf := domainField_lt hwf he.1
    have hchar := charP_field hI hf
    unfold quotRangeB at hqr
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hqr
    obtain ⟨hrid, hqr⟩ := hqr
    split at hqr
    · rename_i d' Q' N r hbr
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hqr
      obtain ⟨⟨⟨⟨⟨hd', -⟩, hQ⟩, hQlen⟩, hN0⟩, -⟩ := hqr
      subst d'
      rw [hbr] at hiv ⊢
      split at hiv
      · rename_i J J' _ _ N' r' hJ hJ' hbr'
        simp only [PredBody.mem.injEq, List.cons.injEq, and_true, InSet.range.injEq] at hbr'
        obtain ⟨-, -, rfl, -⟩ := hbr'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hiv
        obtain ⟨hlo, hhi⟩ := hiv
        intro i hi
        simp only [List.headD_cons] at hi
        rw [hQlen] at hi
        refine (inRows_range_iff _ d Q' i N).2 ?_
        have hwe : IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes) (ir.domainField d) e)
            J.lo J.hi := by
          rw [hJ]; exact ⟨le_rfl, le_rfl⟩
        have hwe' : IvlWithin (ir.srcIvl (ir.srcLeafIvl primeNodes) (ir.domainField d) e')
            J'.lo J'.hi := by
          rw [hJ']; exact ⟨le_rfl, le_rfl⟩
        obtain ⟨⟨h1, h2'⟩, hc⟩ := exprIvl_within_of hwf hI hL hIF hlok he.1 h2 he.2 hwe hi
        obtain ⟨⟨h3, h4⟩, hc'⟩ := exprIvl_within_of hwf hI hL hIF hlok
          he'.1 h2 he'.2 hwe' (by rw [← hlen]; exact hi)
        simp only at h1 h2' h3 h4 hc hc'
        obtain ⟨z, hz⟩ := hmod i hi
        have hq0 : (0 : ℤ) < q := by exact_mod_cast hq
        have hz0 : real.quotientLo ≤ z := by
          by_contra hneg
          have : (q : ℤ) * z ≤ q * (real.quotientLo - 1) :=
            mul_le_mul_of_nonneg_left (by omega) hq0.le
          nlinarith
        have hzN : z - real.quotientLo < N := by
          have hle : (q : ℤ) * z ≤ J.hi - J'.lo := by omega
          have : z ≤ (J.hi - J'.lo) / q := Int.le_ediv_of_mul_le hq0 (by linarith)
          omega
        have hQf := fieldEq_of_quotDerived (rd := ir.reader SE)
          (fun v es hk i => reader_of_constant SE hk i) hwf hI hL he.1 hder hi
        rw [← hc, ← hc', ← Int.cast_sub, hz, Int.cast_mul, Int.cast_natCast] at hQf
        have hqa := quot_ne_zero_of_quotDerivedB hwf hI he.1 hder
        have hQz : ir.evalWith (ir.reader SE) d Q' i =
            ((z - real.quotientLo : ℤ) : (I (ir.domainField d)).K) := by
          rw [show ir.evalWith (ir.reader SE) d Q' = ir.evalWith (ir.reader SE) d real.quotExpr by
            rw [Expr.eq_of_beq hQ]]
          have := mul_left_cancel₀ hqa hQf
          push_cast
          linear_combination -this
        refine ⟨(z - real.quotientLo).toNat, by omega, ?_⟩
        rw [hQz, ← Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ z - real.quotientLo), Int.cast_natCast,
          Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ z - real.quotientLo)]
      · cases hiv
    · cases hqr
  · cases hB

end

end GordieHowe.RealizedProgram
