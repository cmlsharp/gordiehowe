-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldPacking
public import GordieHowe.Foundations.Algebra.FiniteFieldStages
public import GordieHowe.Headline

@[expose] public section

/-!
# GordieHowe: every finite field is a member of the packing class

The class `FieldInterp.Packing` holds the packing facts of a field interpretation. It is no
restriction on the field: every finite field `K` of `p^n` elements has a member
(`FieldInterp.genericPacking`) that realizes every edge, node, evaluation point count and skip
domain the field's size allows (`FieldInterp.Packing.Realizes`, `genericPacking_realizes`):

* **the edges** `F_{p^m} <d F_{p^(m d)}`, for `m d ∣ n`: the stage basis is any basis
  of the stage with its trace-dual basis, which exists because the extension of finite fields is
  separable (`StageIndependent.stageBasis`); the relative Frobenius order of `K` over `F_{p^m}` is
  `n / m`. Subfield masks need `S0 = F_{p^s0} ⊆ F_{p^m}` (`s0 ∣ m`) and a basis of `K` over `S0`,
  again a stage basis; squaring-chain masks need characteristic two and `m = 1`, and the bit
  stage's basis is the basis in which the interpretation reads its bit coordinates
  (`FieldInterp.BitBases`), so the bit coordinates agree (`coord_eq`);
* **the nodes**: a name whose node is the subfield `F_{p^m}` for some `m ∣ n` has degree `m`, unique
  because subfields of distinct dividing degrees differ (`fixedField_injOn_dvd`);
* **the evaluation points**: any `q ≤ p^s0` distinct points of `S0`;
* **the skip domains**: `w + (D − 1)(w − 1)` distinct points whenever `K` has that many elements.

The size conditions of the class are those two: `S0` has at least `q` elements, and `K` has at least
`D (w − 1) + 1` elements for every batch's skip domain (`GordieHowe.RealizedProgram.batchesOkB` tests the latter).

The construction is noncomputable (dual bases of a nondegenerate form, enumerations of finite
types); it shows that the class is not a restriction. The fields of the exported programs register
computable instances (`Plan/FieldPackings.lean`).
-/

namespace GordieHowe.RealizedProgram

open Export PackingStage RelativePacking

/-! ## The bit bases of an interpretation -/

/-- **The bit bases of a field interpretation**: for some degrees `dd`, a basis `β` of `F_{p^dd}`
over `F_p` (`StageIndependent`) in whose coordinates every node that is `F_{p^dd}` reads its bits:
the bit coordinates of `Σ_i β_i c_i` are the coefficients `c`. The squaring-chain edges of the
generic member are those at the degrees of the bit bases. -/
structure FieldInterp.BitBases (F : FieldInterp) (p : ℕ) [ExpChar F.K p] where
  /-- The basis at each degree, if any. -/
  basis : (dd : ℕ) → Option {β : Fin dd → F.K // StageIndependent p 1 dd β}
  /-- The nodes that are `F_{p^dd}` read their bits in the basis. -/
  coord : ∀ dd β, basis dd = some β → ∀ s,
    ((F.node s : AddSubgroup F.K) : Set F.K) = fixedField F.K p dd →
      ∀ (c : Fin dd → fixedField F.K p 1) (j : Fin dd),
        F.ofBool (F.coord s (∑ i, β.1 i * (c i : F.K)) j) = c j

/-- **No bit bases**: no squaring-chain edge (an odd field, or a binary field with subfield masks
only). -/
def FieldInterp.BitBases.none (F : FieldInterp) (p : ℕ) [ExpChar F.K p] : F.BitBases p where
  basis _ := Option.none
  coord _ _ h := by cases h

/-! ## The realized shape of a member -/

/-- **A member realizes everything a field of `p^n` elements allows** (see the module docstring):
its degree `n`, masking degree `s0` and point count `q`; an edge `F_{p^m} <d` with subfield masks
exactly when `m d ∣ n` and `s0 ∣ m`; one with squaring-chain masks exactly when
`p = 2`, `m = 1`, `d ∣ n` and the interpretation reads bits at degree `d` (`bits d`);
node degree `m` exactly for the names whose node is `F_{p^m}` with `m ∣ n`; and a skip domain
exactly when `K` has `w + (D − 1)(w − 1)` elements. -/
structure FieldInterp.Packing.Realizes {F : FieldInterp} (Pk : F.Packing) (n s0 q : ℕ)
    (bits : ℕ → Prop) : Prop where
  /-- The degree. -/
  n_eq : Pk.n = n
  /-- The masking degree. -/
  s0_eq : Pk.s0 = s0
  /-- The number of evaluation points. -/
  q_eq : Pk.q = q
  /-- The edges with subfield masks. -/
  subfield : ∀ m d, (Pk.edge m d .subfieldMasks).isSome ↔ m * d ∣ n ∧ s0 ∣ m
  /-- The edges with squaring-chain masks. -/
  squaring : ∀ m d,
    (Pk.edge m d .squaringChain).isSome ↔ Pk.p = 2 ∧ m = 1 ∧ d ∣ n ∧ bits d
  /-- The node degrees. -/
  nodeDeg : ∀ s m, Pk.nodeDeg s = some m ↔
    m ∣ n ∧ ((F.node s : AddSubgroup F.K) : Set F.K) = fixedField F.K Pk.p m
  /-- The skip domains. -/
  skip : ∀ w D, (Pk.skip w D).isSome ↔ w + (D - 1) * (w - 1) ≤ Fintype.card F.K

/-! ## The generic edges -/

section Edges

variable {K : Type} [Field K] [Fintype K] {p n : ℕ} [ExpChar K p]

omit [ExpChar K p] in
/-- A field of `p^n` elements has `n ≠ 0`. -/
theorem ne_zero_of_card_eq_pow (hK : Fintype.card K = p ^ n) : n ≠ 0 := by
  rintro rfl
  rw [pow_zero] at hK
  exact absurd hK (ne_of_gt Fintype.one_lt_card)

omit [ExpChar K p] in
/-- A field of `p^n` elements has `1 < p`. -/
theorem one_lt_of_card_eq_pow (hK : Fintype.card K = p ^ n) : 1 < p := by
  have h1 : 1 < p ^ n := hK ▸ Fintype.one_lt_card
  by_contra hp
  have : p ^ n ≤ 1 := (Nat.pow_le_pow_left (show p ≤ 1 by omega) n).trans (by rw [one_pow])
  omega

omit [ExpChar K p] in
/-- **The relative Frobenius order** `n / m` of `K` over `F_{p^m}`, for `m ∣ n`. -/
theorem relFrobeniusOrder_div (hK : Fintype.card K = p ^ n) {m : ℕ} (hm : m ∣ n) :
    RelFrobeniusOrder K p m (n / m) := by
  have hn := ne_zero_of_card_eq_pow hK
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hn (zero_dvd_iff.mp hm)
  refine RelFrobeniusOrder.of_card (by rw [hK, Nat.mul_div_cancel' hm]) ?_
  exact Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hm) (Nat.pos_of_ne_zero hm0)

/-- **A basis of `K` over `F_{p^s0}`** with its trace dual, for `s0 ∣ n`. -/
noncomputable def maskBasis (hK : Fintype.card K = p ^ n) {s0 : ℕ} (hs0 : s0 ∣ n) :
    RelativeBasis K p s0 (n / s0) :=
  have hmd : s0 * (n / s0) ∣ n := by rw [Nat.mul_div_cancel' hs0]
  RelativeBasis.traceDualOf hK (ne_zero_of_card_eq_pow hK) (one_lt_of_card_eq_pow hK) hmd
    (Classical.choose_spec (exists_stageIndependent hK (ne_zero_of_card_eq_pow hK)
      (one_lt_of_card_eq_pow hK) hmd))

/-- **The stage basis of `F_{p^m} <d F_{p^(m d)}`**, for `m d ∣ n`: a basis of the stage and its
trace dual. -/
noncomputable def genericStageBasis (hK : Fintype.card K = p ^ n) {m d : ℕ} (hmd : m * d ∣ n) :
    StageBasis K p m d :=
  (Classical.choose_spec (exists_stageIndependent hK (ne_zero_of_card_eq_pow hK)
    (one_lt_of_card_eq_pow hK) hmd)).stageBasis hK (ne_zero_of_card_eq_pow hK)
      (one_lt_of_card_eq_pow hK) hmd

/-- **The edge `F_{p^m} <d F_{p^(m d)}` with subfield masks over `F_{p^s0}`**, for `m d ∣ n` and
`s0 ∣ m`: the stage basis `genericStageBasis`, the order `n / m`, and the masks in the basis
`maskBasis` of `K` over `F_{p^s0}`. -/
noncomputable def subfieldEdgeKit (hK : Fintype.card K = p ^ n) {s0 m d : ℕ} (hmd : m * d ∣ n)
    (hs0 : s0 ∣ m) : EdgeKit K p (fixedField K p s0) m d :=
  have hm : m ∣ n := Dvd.dvd.trans (Dvd.intro d rfl) hmd
  have hs0n : s0 ∣ n := hs0.trans hm
  letI := relFrobeniusOrder_div hK hs0n
  letI : Fintype (fixedField K p s0) := Fintype.ofFinite _
  { e := n / m
    order := relFrobeniusOrder_div hK hm
    basis := genericStageBasis hK hmd
    top_eq := rfl
    masks := MaskKit.subfield (maskBasis hK hs0n).β (fixedField_le_of_dvd hs0)
      (packSub_bijective (maskBasis hK hs0n)) }

/-- **The bit edge `F_p <d F_{p^d}` with squaring-chain masks**, in characteristic two, for
`d ∣ n`, in the basis `β` of the stage. -/
noncomputable def squaringEdgeKit (hK : Fintype.card K = p ^ n) (h2 : p = 2) {S0 : Subfield K}
    {d : ℕ} (hd : d ∣ n) {β : Fin d → K} (hβ : StageIndependent p 1 d β) : EdgeKit K p S0 1 d where
  e := n
  order := RelFrobeniusOrder.of_card (by rw [hK, one_mul]) (Nat.pos_of_ne_zero
    (ne_zero_of_card_eq_pow hK))
  basis := hβ.stageBasis hK (ne_zero_of_card_eq_pow hK) (one_lt_of_card_eq_pow hK)
    (by rwa [one_mul])
  top_eq := rfl
  masks := by
    subst h2
    exact MaskKit.bitChain

/-- **The coordinates of the bit edge** are the coefficients in its basis. -/
theorem squaringEdgeKit_coord (hK : Fintype.card K = p ^ n) (h2 : p = 2) {S0 : Subfield K}
    {d : ℕ} (hd : d ∣ n) {β : Fin d → K} (hβ : StageIndependent p 1 d β)
    (c : Fin d → fixedField K p 1) (j : Fin d) :
    (squaringEdgeKit (S0 := S0) hK h2 hd hβ).basis.coord (∑ i, β i * (c i : K)) j = c j :=
  hβ.coord_stageBasis _ _ _ _ c j

end Edges

/-! ## The generic member -/

section Generic

variable (F : FieldInterp) {p : ℕ} [ExpChar F.K p] {n : ℕ} (s0 q : ℕ)

/-- **The generic edges** (see the module docstring). -/
noncomputable def genericEdges (hK : Fintype.card F.K = p ^ n) (bb : F.BitBases p) :
    (m d : ℕ) → PackingMode → Option (EdgeKit F.K p (fixedField F.K p s0) m d)
  | m, d, .subfieldMasks =>
    if h : m * d ∣ n ∧ s0 ∣ m then some (subfieldEdgeKit hK h.1 h.2) else Option.none
  | 1, d, .squaringChain =>
    if h : p = 2 ∧ d ∣ n then
      (bb.basis d).map fun β => squaringEdgeKit hK h.1 h.2 β.2
    else Option.none
  | _, _, .squaringChain => Option.none

open Classical in
/-- **The generic node degrees**: `m` for a name whose node is `F_{p^m}` with `m ∣ n`. -/
noncomputable def genericNodeDeg (s : String) : Option ℕ :=
  if h : ∃ m, m ∣ n ∧ ((F.node s : AddSubgroup F.K) : Set F.K) = fixedField F.K p m then
    some (Nat.find h)
  else Option.none

/-- **`q` distinct points of a finite subfield** `S`, for `q ≤ |S|`: an enumeration of `S`. -/
noncomputable def subfieldPoints (S : Subfield F.K) (hq : q ≤ Nat.card S) :
    Ligero.Relative.Shape.Points F.K q where
  pt a := if h : a < Nat.card S then ((Finite.equivFin S).symm ⟨a, h⟩ : F.K) else 0
  inj {a b} ha hb hab := by
    have ha' : a < Nat.card S := lt_of_lt_of_le ha hq
    have hb' : b < Nat.card S := lt_of_lt_of_le hb hq
    simp only [ha', hb', dite_true] at hab
    have := (Finite.equivFin S).symm.injective (Subtype.ext hab)
    exact congrArg Fin.val this

theorem subfieldPoints_mem (S : Subfield F.K) (hq : q ≤ Nat.card S) (a : ℕ) :
    (subfieldPoints F q S hq).pt a ∈ S := by
  simp only [subfieldPoints]
  split
  · exact Subtype.property _
  · exact S.zero_mem

/-- **An enumeration of `K`**: the `i`-th element for `i < |K|`. -/
noncomputable def enumField (i : ℕ) : F.K :=
  if h : i < Fintype.card F.K then (Fintype.equivFin F.K).symm ⟨i, h⟩ else 0

theorem enumField_injOn : Set.InjOn (enumField F) (Set.Iio (Fintype.card F.K)) := by
  intro a ha b hb hab
  simp only [Set.mem_Iio] at ha hb
  simp only [enumField, ha, hb, dite_true] at hab
  exact congrArg Fin.val ((Fintype.equivFin F.K).symm.injective hab)

/-- **The generic skip domains**: the enumeration of `K` on `w + (D − 1)(w − 1)` points. -/
noncomputable def genericSkip (w D : ℕ) : Option (Sumcheck.FieldSkip.SkipPoints F.K w D) :=
  if h : w + (D - 1) * (w - 1) ≤ Fintype.card F.K then
    some (Sumcheck.FieldSkip.SkipPoints.ofEmbed (enumField F)
      ((enumField_injOn F).mono (Set.Iio_subset_Iio h)))
  else Option.none

variable {F s0 q}

theorem genericNodeDeg_eq_some_iff (hK : Fintype.card F.K = p ^ n) (s : String) (m : ℕ) :
    genericNodeDeg F (p := p) (n := n) s = some m ↔
      m ∣ n ∧ ((F.node s : AddSubgroup F.K) : Set F.K) = fixedField F.K p m := by
  classical
  unfold genericNodeDeg
  split
  · rename_i h
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact Nat.find_spec h
    · rintro ⟨hm, hs⟩
      have hspec := Nat.find_spec h
      apply fixedField_injOn_dvd hK (ne_zero_of_card_eq_pow hK) (one_lt_of_card_eq_pow hK)
        hspec.1 hm
      exact SetLike.coe_injective (hspec.2.symm.trans hs)
  · rename_i h
    simp only [reduceCtorEq, false_iff]
    exact fun hm => h ⟨m, hm⟩

/-- **The generic member of the packing class** of a field of `p^n` elements with masking subfield
`F_{p^s0}` (`s0 ∣ n`), `q ≤ p^s0` evaluation points, the bit bases `bb` and additive bit
coordinates (see the module docstring). Noncomputable: it shows that the class is not a
restriction. -/
@[instance_reducible]
noncomputable def FieldInterp.genericPacking (hK : Fintype.card F.K = p ^ n) (hs0 : s0 ∣ n)
    (hq : q ≤ p ^ s0) (bb : F.BitBases p) (hbits : F.BitsAdditive) (nodes : Option (Sumcheck.Nodes F.K)) :
    F.Packing where
  p := p
  n := n
  top_eq := fixedField_eq_top hK
  s0 := s0
  decS0 := Classical.decPred _
  edge := genericEdges F s0 hK bb
  nodeDeg := genericNodeDeg F (p := p) (n := n)
  node_eq s m h := ((genericNodeDeg_eq_some_iff hK s m).mp h).2
  q := q
  points := subfieldPoints F q (fixedField F.K p s0)
    (by rwa [card_fixedField_of_dvd hK (ne_zero_of_card_eq_pow hK) hs0 (one_lt_of_card_eq_pow hK)])
  points_mem a := subfieldPoints_mem F q _ _ a
  coord_eq s m dd mode EB hEB hm hmode hs x hx j := by
    subst hm
    subst hmode
    simp only [genericEdges] at hEB
    split_ifs at hEB with h
    obtain ⟨β, hβ, rfl⟩ := Option.map_eq_some_iff.mp hEB
    have hnode := ((genericNodeDeg_eq_some_iff hK s dd).mp hs).2
    obtain ⟨c, rfl⟩ := β.2.exists_eq_sum hK (ne_zero_of_card_eq_pow hK) (one_lt_of_card_eq_pow hK)
      (by rw [one_mul]; exact h.2) (by rwa [one_mul])
    rw [squaringEdgeKit_coord]
    exact bb.coord dd β hβ s hnode c j
  bitsAdditive := hbits
  skip := genericSkip F
  nodes := nodes

/-- **The generic member realizes everything the field allows** (`Packing.Realizes`), with
squaring-chain edges at the degrees of the bit bases. -/
theorem FieldInterp.genericPacking_realizes (hK : Fintype.card F.K = p ^ n) (hs0 : s0 ∣ n)
    (hq : q ≤ p ^ s0) (bb : F.BitBases p) (hbits : F.BitsAdditive) (nodes : Option (Sumcheck.Nodes F.K)) :
    (F.genericPacking hK hs0 hq bb hbits nodes).Realizes n s0 q fun d => (bb.basis d).isSome where
  n_eq := rfl
  s0_eq := rfl
  q_eq := rfl
  subfield m d := by
    change (genericEdges F s0 hK bb m d .subfieldMasks).isSome ↔ _
    simp only [genericEdges]
    split_ifs with h
    · simp [h]
    · simp [h]
  squaring m d := by
    change (genericEdges F s0 hK bb m d .squaringChain).isSome ↔ p = 2 ∧ _
    rcases m with _ | _ | m
    · simp [genericEdges]
    · simp only [genericEdges]
      split_ifs with h
      · simp [h]
      · simp only [Option.isSome_none, Bool.false_eq_true, false_iff]
        rintro ⟨h2, -, hdn, -⟩
        exact h ⟨h2, hdn⟩
    · simp [genericEdges]
  nodeDeg s m := genericNodeDeg_eq_some_iff hK s m
  skip w D := by
    change (genericSkip F w D).isSome ↔ _
    simp only [genericSkip]
    split_ifs with h
    · simp [h]
    · simp [h]

/-- **Every finite field is a member of the packing class**: a field of `p^n` elements with an
interpretation whose bit coordinates are additive has a member that realizes everything the field
allows, at every masking degree `s0 ∣ n` and point count `q ≤ p^s0`, with squaring-chain edges at
the degrees of the bit bases `bb`. -/
@[headline]
theorem FieldInterp.exists_packing_realizes (hK : Fintype.card F.K = p ^ n) (hs0 : s0 ∣ n)
    (hq : q ≤ p ^ s0) (bb : F.BitBases p) (hbits : F.BitsAdditive) :
    ∃ Pk : F.Packing, Pk.p = p ∧ Pk.Realizes n s0 q fun d => (bb.basis d).isSome :=
  ⟨F.genericPacking hK hs0 hq bb hbits none, rfl, F.genericPacking_realizes hK hs0 hq bb hbits none⟩

end Generic

/-! ## The generic member at a given member's numbers -/

section OfPacking

variable {F : FieldInterp}

/-- **A stage basis packs injectively**: coordinates in the base field are recovered by decoding
(`StageBasis.coord_pack`). -/
theorem _root_.GordieHowe.PackingStage.StageBasis.pack_injective {K : Type} [Field K] {p m d : ℕ}
    [ExpChar K p] (S : StageBasis K p m d) :
    Function.Injective fun c : Fin d → fixedField K p m => ∑ i, S.β i * (c i : K) := by
  intro c c' h
  funext i
  apply Subtype.ext
  have h1 := S.coord_pack (c := fun i => (c i : K)) (fun i => (c i).2) i
  have h2 := S.coord_pack (c := fun i => (c' i : K)) (fun i => (c' i).2) i
  change S.coord (∑ i, S.β i * (c i : K)) i = _ at h1
  change S.coord (∑ i, S.β i * (c' i : K)) i = _ at h2
  rw [← h1, ← h2]
  exact congrArg (fun x => S.coord x i) h

/-- **A member has at most `|S0|` evaluation points**: its points are distinct elements of
`S0`. -/
theorem FieldInterp.Packing.q_le_card (Pk : F.Packing) : Pk.q ≤ Nat.card Pk.S0 := by
  have hinj : Function.Injective fun a : Fin Pk.q => (⟨Pk.points.pt a, Pk.points_mem a⟩ : Pk.S0) :=
    fun a b h => Fin.ext (Pk.points.inj a.2 b.2 (congrArg Subtype.val h))
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_eq_fintype_card (α := Fin Pk.q), Fintype.card_fin] at this

/-- **A member's skip domain has at most `|K|` points**: its points are distinct. -/
theorem FieldInterp.Packing.skip_le (Pk : F.Packing) {w D : ℕ} (h : (Pk.skip w D).isSome) :
    w + (D - 1) * (w - 1) ≤ Fintype.card F.K := by
  obtain ⟨dom, -⟩ := Option.isSome_iff_exists.mp h
  have := Fintype.card_le_of_injective dom.point dom.injective
  simpa [Fintype.card_sum] using this

/-- **The tops of a member's bit edges are named by their degree**: a node that is the top
`F_{p^dd}` of a bit edge `F_p <dd` with squaring-chain masks has node degree `dd`. A fact about the
field interpretation's names. -/
def FieldInterp.Packing.BitNodesNamed (Pk : F.Packing) : Prop :=
  ∀ dd EB, Pk.edge 1 dd .squaringChain = some EB → ∀ s,
    ((F.node s : AddSubgroup F.K) : Set F.K) = fixedField F.K Pk.p dd → Pk.nodeDeg s = some dd

/-- **The bit bases of a member**: the bases of its bit edges, in which its nodes read their bits
(`coord_eq`), when the tops of its bit edges are named by their degree. -/
def FieldInterp.BitBases.ofPacking (Pk : F.Packing) (hcov : Pk.BitNodesNamed) :
    F.BitBases Pk.p where
  basis dd := (Pk.edge 1 dd .squaringChain).map fun EB =>
    ⟨EB.basis.β, { mem := fun i => EB.top_eq ▸ EB.basis.β_mem i
                   injective := EB.basis.pack_injective }⟩
  coord dd β hβ s hs c j := by
    obtain ⟨EB, hEB, rfl⟩ := Option.map_eq_some_iff.mp hβ
    have hdeg := hcov dd EB hEB s hs
    have hx : (∑ i, EB.basis.β i * (c i : F.K)) ∈ fixedField F.K Pk.p dd := by
      have := EB.basis.pack_mem (c := fun i => (c i : F.K)) (fun i => (c i).2)
      rw [EB.top_eq, one_mul] at this
      exact this
    rw [Pk.coord_eq s .squaringChain EB hEB rfl rfl hdeg _ hx j]
    exact EB.basis.coord_pack (fun i => (c i).2) j

theorem FieldInterp.BitBases.ofPacking_isSome (Pk : F.Packing) (hcov : Pk.BitNodesNamed)
    (dd : ℕ) :
    ((FieldInterp.BitBases.ofPacking Pk hcov).basis dd).isSome =
      (Pk.edge 1 dd .squaringChain).isSome := by
  simp [FieldInterp.BitBases.ofPacking]

/-- **A member of a field of `p^n` elements has at most `p^s0` evaluation points**, for
`s0 ∣ n`. -/
theorem FieldInterp.Packing.q_le_pow (Pk : F.Packing) (hK : Fintype.card F.K = Pk.p ^ Pk.n)
    (hs0 : Pk.s0 ∣ Pk.n) : Pk.q ≤ Pk.p ^ Pk.s0 := by
  have := Pk.q_le_card
  rwa [card_fixedField_of_dvd hK (ne_zero_of_card_eq_pow hK) hs0 (one_lt_of_card_eq_pow hK)] at this

/-- **The generic member at a member's numbers**: the same characteristic, degree `n`, masking
degree `s0` and point count `q`, the bit bases of the member's bit edges and its additive bit
coordinates (`genericPacking`), for a field of `p^n` elements with `s0 ∣ n`. -/
@[instance_reducible]
noncomputable def FieldInterp.Packing.generic (Pk : F.Packing)
    (hK : Fintype.card F.K = Pk.p ^ Pk.n) (hs0 : Pk.s0 ∣ Pk.n) (hcov : Pk.BitNodesNamed) :
    F.Packing :=
  F.genericPacking hK hs0 (Pk.q_le_pow hK hs0) (FieldInterp.BitBases.ofPacking Pk hcov)
    Pk.bitsAdditive Pk.nodes

theorem FieldInterp.Packing.generic_realizes (Pk : F.Packing)
    (hK : Fintype.card F.K = Pk.p ^ Pk.n) (hs0 : Pk.s0 ∣ Pk.n) (hcov : Pk.BitNodesNamed) :
    (Pk.generic hK hs0 hcov).Realizes Pk.n Pk.s0 Pk.q
      fun d => (Pk.edge 1 d .squaringChain).isSome := by
  have h := F.genericPacking_realizes hK hs0 (Pk.q_le_pow hK hs0)
    (FieldInterp.BitBases.ofPacking Pk hcov) Pk.bitsAdditive Pk.nodes
  simp only [FieldInterp.BitBases.ofPacking_isSome] at h
  exact h

end OfPacking

end GordieHowe.RealizedProgram
