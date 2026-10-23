-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.PlanTree
public import GordieHowe.ProofSystem.FieldProof.MaskedReductionList
public import GordieHowe.ProofSystem.Program.Transcript.CircuitCodecs
public import GordieHowe.ProofSystem.Program.Transcript.Readers
public import GordieHowe.ProofSystem.Program.Transcript.GrantedLoads

@[expose] public section

/-!
# The codecs and challenge readers of a planned packing tree and of a list of masked reductions

The write codecs and challenge readers of two constructions with any number of parts:

* **a list of masked reductions** (`MaskedReduction.ofList`): every entry's in order (`ofListWrites`,
  `ofListReaders`), the readers' loads within every entry's bound (`ofListReaders_allLoads`), the
  rounds the entries' (`ofList_n`);
* **the touching claims' combination** (`MaskedReduction.touch`): the masked reduction's, then the
  combination challenge (`nt` elements, no codec) when two or more claims touch (`touchWrites`,
  `touchReaders`);
* **the run of a planned packing tree** (`PEdge.path`, `GordieHowe.RingSwitching.Tree.run`): after the
  masked reduction's, every stage's combination challenge, if any, and its `d` measurements (one
  array) (`PEdge.runWrites`, `PEdge.runReaders`), the readers' loads within a bound on every
  stage's touching claims (`PEdge.StagesOk`, `PEdge.runReaders_allLoads`), at most two rounds per
  stage (`PEdge.run_n_le`); every stage touches at most the claims entering the tree and two more
  per earlier edge's relative degree (`PEdge.stagesOk_le`).
-/

namespace GordieHowe

open IOP GordieHowe.QROM GordieHowe.SPBCS SPBCS.Configurations

/-! ## A list of masked reductions -/

section List

variable {F : Type} {ι : Type} {PubT : Type} {WitT : Type} {Zc : Type} [Field F] [Fintype ι] {cells : WitT → ι → F} {β : Type}
  {ncOf : β → ℕ} {M : (b : β) → FieldProof.MaskedReduction F ι PubT WitT cells Zc (ncOf b)} {B : ℕ}

/-- **The codecs of a list of masked reductions**: every entry's in order, none for the empty list. -/
def ofListWrites (W : ∀ b, SpecWrites (M b).spec B) :
    (l : List β) → SpecWrites (FieldProof.MaskedReduction.ofList M l).spec B
  | [] => SpecWrites.ofNone fun i => i.elim0
  | b :: l => W b ++ ofListWrites W l

/-- **The challenge readers of a list of masked reductions**: every entry's in order. -/
def ofListReaders (Rd : ∀ b, SpecReaders (M b).spec) :
    (l : List β) → SpecReaders (FieldProof.MaskedReduction.ofList M l).spec
  | [] => fun i => i.1.elim0
  | b :: l => Rd b ++ ofListReaders Rd l

/-- **The loads of a list's readers** satisfy `good` when every entry's do. -/
theorem ofListReaders_allLoads {Rd : ∀ b, SpecReaders (M b).spec} {good : Load → Prop}
    (h : ∀ b, (Rd b).AllLoads good) : ∀ l, (ofListReaders Rd l).AllLoads good
  | [] => fun i => i.1.elim0
  | b :: l => SpecReaders.append_allLoads (h b) (ofListReaders_allLoads h l)

/-- **The rounds of a list of masked reductions** are its entries'. -/
theorem ofList_n : (l : List β) → (FieldProof.MaskedReduction.ofList M l).n = (l.map fun b => (M b).n).sum
  | [] => rfl
  | b :: l => by
    change (M b).n + (FieldProof.MaskedReduction.ofList M l).n = _
    rw [ofList_n l, List.map_cons, List.sum_cons]

/-- **The linear rows of a list of masked reductions** are its entries'. -/
theorem ofList_card_Lin : (l : List β) →
    Fintype.card (FieldProof.MaskedReduction.ofList M l).Lin = (l.map fun b => Fintype.card (M b).Lin).sum
  | [] => by
    change Fintype.card Empty = 0
    simp
  | b :: l => by
    change Fintype.card ((M b).Lin ⊕ (FieldProof.MaskedReduction.ofList M l).Lin) = _
    rw [Fintype.card_sum, ofList_card_Lin l, List.map_cons, List.sum_cons]

/-- **The product triples of a list of masked reductions** are its entries'. -/
theorem ofList_card_Q : (l : List β) →
    Fintype.card (FieldProof.MaskedReduction.ofList M l).Q = (l.map fun b => Fintype.card (M b).Q).sum
  | [] => by
    change Fintype.card Empty = 0
    simp
  | b :: l => by
    change Fintype.card ((M b).Q ⊕ (FieldProof.MaskedReduction.ofList M l).Q) = _
    rw [Fintype.card_sum, ofList_card_Q l, List.map_cons, List.sum_cons]

end List

/-! ## The touching claims' combination -/

section Touch

variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K] [Fintype ι] {PubT WitT Zt : Type}
  {cells : WitT → ι → K} {B nc nt np : ℕ}

/-- **The codecs of the touching claims' combination**: the masked reduction's `W`, then the
combination challenge (no codec) when two or more claims touch. -/
def touchWrites (M : FieldProof.MaskedReduction K ι PubT WitT cells Zt nc) (R : StageRouting nc nt np)
    (W : SpecWrites M.spec B) : SpecWrites (M.touch R).spec B :=
  match R with
  | .none _ => W
  | .single _ => W
  | .combine _ _ => W ++ SpecWrites.oneV (M := Fin nt → K) (B := B)

/-- **The challenge readers of the touching claims' combination**: the masked reduction's `Rd`,
then the combination's `nt` elements granted `g` stream bytes when two or more claims touch. -/
def touchReaders (rd : CReader K) (g : ℕ) (M : FieldProof.MaskedReduction K ι PubT WitT cells Zt nc)
    (R : StageRouting nc nt np) (Rd : SpecReaders M.spec) : SpecReaders (M.touch R).spec :=
  match R with
  | .none _ => Rd
  | .single _ => Rd
  | .combine _ _ => Rd ++ SpecReaders.one (Fin nt → K) ((CReader.pi nt rd).extend g)

/-- **The loads of the combination's readers** are at most `L` when the masked reduction's are and
the `nt` touching claims' elements are. -/
theorem touchReaders_allLoads (rd : CReader K) (g : ℕ)
    (M : FieldProof.MaskedReduction K ι PubT WitT cells Zt nc) (R : StageRouting nc nt np)
    {Rd : SpecReaders M.spec} {L : Load} (hR : Rd.AllLoads (· ≤ L)) (hnt : rd.load.nsmul nt ≤ L) :
    (touchReaders rd g M R Rd).AllLoads (· ≤ L) :=
  match R with
  | .none _ => hR
  | .single _ => hR
  | .combine _ _ => SpecReaders.append_allLoads hR
      (SpecReaders.one_allLoads _ (by rw [CReader.extend_load, CReader.pi_load]; exact hnt))

/-- **The combination's readers at their grants**: `good` holds at every round when it holds for
the masked reduction's readers and for the `nt` touching claims' elements at their grant. -/
theorem touchReaders_allGranted (rd : CReader K) (g : ℕ)
    (M : FieldProof.MaskedReduction K ι PubT WitT cells Zt nc) (R : StageRouting nc nt np)
    {Rd : SpecReaders M.spec} {good : ℕ → Load → Prop} (hR : Rd.AllGranted good)
    (hnt : good ((CReader.pi nt rd).extend g).grant (rd.load.nsmul nt)) :
    (touchReaders rd g M R Rd).AllGranted good :=
  match R with
  | .none _ => hR
  | .single _ => hR
  | .combine _ _ => SpecReaders.AllGranted.append hR
      (SpecReaders.AllGranted.one _ (by rw [CReader.extend_load, CReader.pi_load]; exact hnt))

/-- **The combination adds a round** exactly when two or more claims touch. -/
theorem touch_n (M : FieldProof.MaskedReduction K ι PubT WitT cells Zt nc) (R : StageRouting nc nt np) :
    (M.touch R).n = M.n + R.combinations := by
  cases R <;> rfl

/-- The combination keeps the masked reduction's linear rows. -/
theorem touch_card_Lin (M : FieldProof.MaskedReduction K ι PubT WitT cells Zt nc)
    (R : StageRouting nc nt np) : Fintype.card (M.touch R).Lin = Fintype.card M.Lin := by
  cases R <;> rfl

/-- The combination keeps the masked reduction's product triples. -/
theorem touch_card_Q (M : FieldProof.MaskedReduction K ι PubT WitT cells Zt nc)
    (R : StageRouting nc nt np) : Fintype.card (M.touch R).Q = Fintype.card M.Q := by
  cases R <;> rfl

end Touch

/-! ## The run of a planned packing tree -/

namespace PEdge

variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K] {p : ℕ} [ExpChar K p]
  {S0 : Subfield K} [Fintype ι] {PubT WitT : Type} {cells : WitT → ι → K} {fb B : ℕ}

/-- **A property of every stage's touching claims** from absolute position `pos` on: `P pos nt`
for the stage at `pos` and its `nt` touching claims. -/
def StagesOk (P : ℕ → ℕ → Prop) (fc : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (Fin nc → Finset ℕ) → Prop
  | _, [], _, _ => True
  | pos, e :: es, _, r => P pos (routeAt pos r).nt ∧ StagesOk P fc (pos + 1) es _ (nextReads pos e r)

theorem StagesOk.mono {P Q : ℕ → ℕ → Prop} (hPQ : ∀ pos n, P pos n → Q pos n) (fc : ι) :
    (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) → (r : Fin nc → Finset ℕ) →
      StagesOk P fc pos es nc r → StagesOk Q fc pos es nc r
  | _, [], _, _, _ => trivial
  | pos, e :: es, _, r, h => ⟨hPQ _ _ h.1, StagesOk.mono hPQ fc (pos + 1) es _ (nextReads pos e r) h.2⟩

/-- **A stage touches at most its claims.** -/
theorem routeAt_nt_le {nc : ℕ} (pos : ℕ) (r : Fin nc → Finset ℕ) :
    (routeAt pos r).nt + (routeAt pos r).np = nc := by
  have h := Fintype.card_congr (routeAt pos r).route.split
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin, Fintype.card_fin] at h
  omega

/-- **Every stage touches at most the claims entering the tree and `d + 1` more per earlier
edge.** -/
theorem stagesOk_le (fc : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) →
      StagesOk (fun _ n => n ≤ nc + (es.map fun e => e.d + 1).sum) fc pos es nc r
  | _, [], _, _ => trivial
  | pos, e :: es, nc, r => by
    have hn := routeAt_nt_le pos r
    refine ⟨by simp only [List.map_cons, List.sum_cons]; omega, ?_⟩
    refine StagesOk.mono (fun _ n hn' => ?_) fc (pos + 1) es _ _
      (stagesOk_le fc (pos + 1) es _ (nextReads pos e r))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- **The tree's output claims** are at most the claims entering it and `d + 1` per edge. -/
theorem outClaims_le (fc : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) →
      (path fc pos es nc r).outClaims ≤ nc + (es.map fun e => e.d + 1).sum
  | _, [], _, _ => le_rfl
  | pos, e :: es, nc, r => by
    have h := outClaims_le fc (pos + 1) es _ (nextReads pos e r)
    have hn := routeAt_nt_le pos r
    change (path fc (pos + 1) es _ (nextReads pos e r)).outClaims ≤ _
    simp only [List.map_cons, List.sum_cons]
    omega

/-- **The output claims of a tree with an edge** are at most the first stage's passing claims and
`d + 1` per edge. -/
theorem outClaims_cons_le (fc : ι) (pos : ℕ) (e : PEdge K ι p S0) (es : List (PEdge K ι p S0))
    (nc : ℕ) (r : Fin nc → Finset ℕ) :
    (path fc pos (e :: es) nc r).outClaims ≤
      (routeAt pos r).np + ((e :: es).map fun e => e.d + 1).sum := by
  have h := outClaims_le fc (pos + 1) es _ (nextReads pos e r)
  change (path fc (pos + 1) es _ (nextReads pos e r)).outClaims ≤ _
  simp only [List.map_cons, List.sum_cons]
  omega

/-- **The touching claims of every stage from the first edge's**: the first stage's at most its
bound, every later stage's at most the first stage's passing claims and `d + 1` per edge
(`stagesOk_le` after the first stage). -/
theorem stagesOk_cons_of {P : ℕ → ℕ → Prop} (fc : ι) (pos : ℕ) (e : PEdge K ι p S0)
    (es : List (PEdge K ι p S0)) (nc : ℕ) (r : Fin nc → Finset ℕ)
    (h0 : P pos (routeAt pos r).nt)
    (h1 : ∀ q n, n ≤ (routeAt pos r).np + ((e :: es).map fun e => e.d + 1).sum → P q n) :
    StagesOk P fc pos (e :: es) nc r :=
  ⟨h0, StagesOk.mono (fun q n hn => h1 q n (by simp only [List.map_cons, List.sum_cons]; omega))
    fc (pos + 1) es _ _ (stagesOk_le fc (pos + 1) es _ (nextReads pos e r))⟩

/-- **The touching claims of every stage from bounds**: the first stage's at most the `nc`
claims, every later stage's at most the first stage's passing claims and `d + 1` per edge. -/
theorem stagesOk_of_bound {P : ℕ → ℕ → Prop} (fc : ι) (pos : ℕ) :
    (es : List (PEdge K ι p S0)) → (nc : ℕ) → (r : Fin nc → Finset ℕ) →
    (∀ n ≤ nc, P pos n) →
    (∀ q n, n ≤ (routeAt pos r).np + (es.map fun e => e.d + 1).sum → P q n) →
      StagesOk P fc pos es nc r
  | [], _, _, _, _ => trivial
  | e :: es, nc, r, h0, h1 => by
    have hn := routeAt_nt_le pos r
    exact stagesOk_cons_of fc pos e es nc r (h0 _ (by omega)) h1

/-- **The passing claims at the edge at position `pos`**: the claims whose nodes do not hold
`pos`. -/
theorem routeAt_np {nc : ℕ} (pos : ℕ) (r : Fin nc → Finset ℕ) :
    (routeAt pos r).np = (Finset.univ.filter fun c => pos ∉ r c).card := by
  unfold routeAt
  rw [StageRouting.Routing.ofTouch_np]
  simp only [decide_eq_true_eq]

/-- **The codecs of the run of the tree** from absolute position `pos` on: the masked reduction's `W`, then
every stage's combination challenge, if any (no codec), and its `d` measurements (one array). -/
def runWrites (FB : SPBCS.Codec.FieldBytes K fb) (fc : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) →
    (nc : ℕ) → (r : Fin nc → Finset ℕ) →
    (M : FieldProof.MaskedReduction K ι PubT WitT cells (Logical ι es) nc) → SpecWrites M.spec B →
    (∀ e ∈ es, 9 + e.d * fb ≤ B) → SpecWrites ((path fc pos es nc r).run M).spec B
  | _, [], _, _, _, W, _ => W
  | pos, e :: es, _, r, M, W, h =>
    let _ := e.kit.order
    runWrites FB fc (pos + 1) es _ (nextReads pos e r)
      (M.routedStage (routeAt pos r).route (stage fc pos e es)
        (path fc (pos + 1) es _ (nextReads pos e r)).level)
      (touchWrites M (routeAt pos r).route W ++
        SpecWrites.one (WriteCodec.fieldArray FB e.d)
          ((WriteCodec.fieldArray_B FB _).trans_le (h e List.mem_cons_self)))
      fun e' he' => h e' (List.mem_cons_of_mem _ he')

/-- **The challenge readers of the run of the tree**: the masked reduction's `Rd`, then every
stage's combination challenge, if any (`nt` elements), the stage at position `pos` granted
`gr pos` stream bytes; the measurements have no challenge. -/
def runReaders (rd : CReader K) (gr : ℕ → ℕ) (fc : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) →
    (nc : ℕ) → (r : Fin nc → Finset ℕ) →
    (M : FieldProof.MaskedReduction K ι PubT WitT cells (Logical ι es) nc) → SpecReaders M.spec →
    SpecReaders ((path fc pos es nc r).run M).spec
  | _, [], _, _, _, Rd => Rd
  | pos, e :: es, _, r, M, Rd =>
    let _ := e.kit.order
    runReaders rd gr fc (pos + 1) es _ (nextReads pos e r)
      (M.routedStage (routeAt pos r).route (stage fc pos e es)
        (path fc (pos + 1) es _ (nextReads pos e r)).level)
      (touchReaders rd (gr pos) M (routeAt pos r).route Rd ++ SpecReaders.oneP (Fin e.d → K))

/-- **The loads of the run's readers** are at most `L` when the masked reduction's are and every
stage's touching claims' elements are. -/
theorem runReaders_allLoads (rd : CReader K) (gr : ℕ → ℕ) (fc : ι) {L : Load} : (pos : ℕ) →
    (es : List (PEdge K ι p S0)) → (nc : ℕ) → (r : Fin nc → Finset ℕ) →
    (M : FieldProof.MaskedReduction K ι PubT WitT cells (Logical ι es) nc) →
    (Rd : SpecReaders M.spec) → Rd.AllLoads (· ≤ L) →
    StagesOk (fun _ n => rd.load.nsmul n ≤ L) fc pos es nc r →
      (runReaders rd gr fc pos es nc r M Rd).AllLoads (· ≤ L)
  | _, [], _, _, _, _, hR, _ => hR
  | pos, e :: es, _, r, M, Rd, hR, hst => by
    let _ := e.kit.order
    exact runReaders_allLoads rd gr fc (pos + 1) es _ (nextReads pos e r) _ _
      (SpecReaders.append_allLoads (touchReaders_allLoads rd (gr pos) M _ hR hst.1)
        (SpecReaders.oneP_allLoads _ _)) hst.2

/-- **The run's readers at their grants**: a predicate `good` that larger grants keep holds at
every round when the masked reduction's readers satisfy it and every stage's touching claims'
elements satisfy it at the stage's grant. -/
theorem runReaders_allGranted (rd : CReader K) (gr : ℕ → ℕ) (fc : ι) {good : ℕ → Load → Prop}
    (hg : ∀ g L, good 0 L → good g L) : (pos : ℕ) →
    (es : List (PEdge K ι p S0)) → (nc : ℕ) → (r : Fin nc → Finset ℕ) →
    (M : FieldProof.MaskedReduction K ι PubT WitT cells (Logical ι es) nc) →
    (Rd : SpecReaders M.spec) → Rd.AllGranted good →
    StagesOk (fun pos n => good ((CReader.pi n rd).extend (gr pos)).grant (rd.load.nsmul n)) fc pos
      es nc r →
      (runReaders rd gr fc pos es nc r M Rd).AllGranted good
  | _, [], _, _, _, _, hR, _ => hR
  | pos, e :: es, _, r, M, Rd, hR, hst => by
    let _ := e.kit.order
    exact runReaders_allGranted rd gr fc hg (pos + 1) es _ (nextReads pos e r) _ _
      (SpecReaders.AllGranted.append (touchReaders_allGranted rd (gr pos) M _ hR hst.1)
        (SpecReaders.AllGranted.of_allLoads hg (SpecReaders.oneP_allLoads _ _))) hst.2

/-- **The run of the tree has at most two rounds per stage** after the masked reduction's: the
combination, if any, and the measurement. -/
theorem run_n_le (fc : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) →
    (M : FieldProof.MaskedReduction K ι PubT WitT cells (Logical ι es) nc) →
      ((path fc pos es nc r).run M).n ≤ M.n + 2 * es.length
  | _, [], _, _, _ => le_rfl
  | pos, e :: es, nc, r, M => by
    let _ := e.kit.order
    have h := run_n_le fc (pos + 1) es _ (nextReads pos e r)
      (M.routedStage (routeAt pos r).route (stage fc pos e es)
        (path fc (pos + 1) es _ (nextReads pos e r)).level)
    have hc := StageRouting.Routing.combinations_ofTouch_le fun c => decide (pos ∈ r c)
    have ht := touch_n M (routeAt pos r).route
    change ((path fc (pos + 1) es _ (nextReads pos e r)).run
      (M.routedStage (routeAt pos r).route (stage fc pos e es)
        (path fc (pos + 1) es _ (nextReads pos e r)).level)).n ≤ _
    refine h.trans ?_
    change (M.touch (routeAt pos r).route).n + 1 + 2 * es.length ≤ M.n + 2 * (es.length + 1)
    unfold routeAt at ht ⊢
    omega

/-- **The run of the tree keeps the masked reduction's linear rows.** -/
theorem run_card_Lin (fc : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) →
    (M : FieldProof.MaskedReduction K ι PubT WitT cells (Logical ι es) nc) →
      Fintype.card ((path fc pos es nc r).run M).Lin = Fintype.card M.Lin
  | _, [], _, _, _ => rfl
  | pos, e :: es, _, r, M => by
    let _ := e.kit.order
    refine (run_card_Lin fc (pos + 1) es _ (nextReads pos e r) _).trans ?_
    exact touch_card_Lin M (routeAt pos r).route

/-- **The run of the tree adds every stage's masks' product triples**, at most its own cells
(`MaskKit.card_Q_le`). -/
theorem run_card_Q_le (fc : ι) : (pos : ℕ) → (es : List (PEdge K ι p S0)) → (nc : ℕ) →
    (r : Fin nc → Finset ℕ) →
    (M : FieldProof.MaskedReduction K ι PubT WitT cells (Logical ι es) nc) →
      Fintype.card ((path fc pos es nc r).run M).Q ≤
        Fintype.card M.Q + (es.map fun e => e.kit.masks.nOwn).sum
  | _, [], _, _, _ => by simp only [List.map_nil, List.sum_nil, add_zero]; exact le_rfl
  | pos, e :: es, nc, r, M => by
    let _ := e.kit.order
    have h := run_card_Q_le fc (pos + 1) es _ (nextReads pos e r)
      (M.routedStage (routeAt pos r).route (stage fc pos e es)
        (path fc (pos + 1) es _ (nextReads pos e r)).level)
    have hq : Fintype.card (M.routedStage (routeAt pos r).route (stage fc pos e es)
        (path fc (pos + 1) es _ (nextReads pos e r)).level).Q =
        Fintype.card M.Q + Fintype.card (e.kit.masks.scheme e.maskPre e.maskOwn).Q := by
      change Fintype.card ((M.touch (routeAt pos r).route).Q ⊕
        (e.kit.masks.scheme e.maskPre e.maskOwn).Q) = _
      rw [Fintype.card_sum, touch_card_Q]
    have hm := e.kit.masks.card_Q_le e.maskPre e.maskOwn
    change Fintype.card ((path fc (pos + 1) es _ (nextReads pos e r)).run
      (M.routedStage (routeAt pos r).route (stage fc pos e es)
        (path fc (pos + 1) es _ (nextReads pos e r)).level)).Q ≤ _
    rw [List.map_cons, List.sum_cons]
    omega

end PEdge

end GordieHowe
