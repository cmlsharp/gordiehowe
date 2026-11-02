-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.GKR.Certificate
public import GordieHowe.Language.Assumptions

@[expose] public section

/-!
# From the certificate's layered circuit to the GKR source circuit

The scheduling certificate (`GordieHowe.GKR.Certificate`) is about the layered circuit `Layered`:
per layer, the quad terms grouped by gate, the layers listed from the inputs up, the wire values
`ℕ → F`, and satisfaction `Layered.Satisfied` asking every assertion product (a term with constant
index `0`) to vanish and every output wire to be zero. The GKR protocol is proved sound for a source
circuit `GordieHowe.GKR.LayeredCircuit` (`GKR/Circuit.lean`, `GKR/Layer.lean`): layers from the
output down, every layer's gates and input wires padded to powers of two, a layer a list of corners
`(gate, left, right, coefficient)`, and satisfaction asking every output to be zero and, at every
gate, the sum of its assertion products (corners of coefficient `0`, `Layer.assertions`) to vanish.

`toSource C w κ d` is the source circuit of `C`: the layers in reverse order, the gates of a layer
of `n` gates padded to `2 ^ ⌈log₂ n⌉` and the input to `2 ^ d`, and each term `(k, a, b)` of gate
`g` the corner `(g, a, b, κ k)`, an assertion term (`k = 0`) the corner of coefficient `0`. A term
with `k ≠ 0` whose constant is `0` contributes nothing to its gate and is left out, so that the
corners of coefficient `0` are exactly the assertion terms. A circuit without layers becomes one
layer squaring each input.

**Soundness** (`toSource_satisfied`): if the source circuit is satisfied by `v`, the layered
circuit is satisfied by `vecRead v`. It needs two properties of `C`: every term reads wires of the
layer below it (`ReadsBelow`, implied by the certificate checker, `readsBelow_of_check`), and every
gate has at most one assertion term (`uniqueAssertsB`, decided separately), which makes the source's
per-gate sum of assertion products the single product the layered circuit asks to vanish.

**Shape** (`toSource_shape`): the source has at most `2 ^ width` wires per layer and at most
`depth` layers when `C` has at least one and at most `depth` layers of at most `2 ^ width` gates
(`shapeB`, decided) and the input dimension is at most `width`.
-/

namespace GordieHowe.GKR.CertificateBridge

open Certificate RealizedProgram

/-! ## The checks on the layered circuit -/

/-- A gate's terms have at most one assertion term (constant index `0`). -/
def atMostOneAssert : List Term → Bool
  | [] => true
  | t :: ts => cond (Nat.beq t.k 0) (!hasAssert ts) (atMostOneAssert ts)

/-- Every gate of the layer `l` has at most one assertion term. -/
def layerUniqueB (w : ℕ) (l : List ℕ) : Bool := l.all fun c => atMostOneAssert (gateTerms w c)

/-- **Every gate of `C` has at most one assertion term.** -/
def uniqueAssertsB (w : ℕ) (C : Layered) : Bool := C.layers.all (layerUniqueB w)

/-- A layer's check from its blocks' (one kernel check per block, as `gatesOk_append`). -/
theorem layerUniqueB_append {w : ℕ} {l₁ l₂ : List ℕ} (h₁ : layerUniqueB w l₁ = true)
    (h₂ : layerUniqueB w l₂ = true) : layerUniqueB w (l₁ ++ l₂) = true := by
  simp only [layerUniqueB, List.all_append, Bool.and_eq_true] at h₁ h₂ ⊢
  exact ⟨h₁, h₂⟩

/-- The check from the first layer's and the rest's (one kernel check per layer). -/
theorem uniqueAssertsB_cons {w n : ℕ} {l : List ℕ} {ls : List (List ℕ)}
    (h₁ : layerUniqueB w l = true) (h₂ : uniqueAssertsB w ⟨n, ls⟩ = true) :
    uniqueAssertsB w ⟨n, l :: ls⟩ = true := by
  simp only [uniqueAssertsB, List.all_cons, Bool.and_eq_true] at h₂ ⊢
  exact ⟨h₁, h₂⟩

/-- The check on a circuit without layers. -/
theorem uniqueAssertsB_nil {w n : ℕ} : uniqueAssertsB w ⟨n, []⟩ = true := rfl

/-- **The shape of `C`**: at least one and at most `depth` layers, each of at most `2 ^ width`
gates. -/
def shapeB (C : Layered) (width depth : ℕ) : Bool :=
  Nat.blt 0 C.layers.length && Nat.ble C.layers.length depth &&
    C.layers.all fun l => Nat.ble l.length (2 ^ width)

/-- The shape check from its parts, so that a layer's length can be bounded block by block. -/
theorem shapeB_intro {C : Layered} {width depth : ℕ} (h0 : 0 < C.layers.length)
    (hd : C.layers.length ≤ depth) (hl : ∀ l ∈ C.layers, l.length ≤ 2 ^ width) :
    shapeB C width depth = true := by
  simp only [shapeB, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, List.all_eq_true]
  exact ⟨⟨h0, hd⟩, hl⟩

/-- **A slice of the layer `l`** (`sliceL l s n`): every gate has at most one assertion term,
there are `m` gates, and `c` of them are non-copy gates with an assertion term. A large layer is
checked slice by slice, one theorem each, so no kernel check grows with the layer. -/
def infoSliceB (w : ℕ) (l : List ℕ) (s n m c : ℕ) : Bool :=
  layerUniqueB w (sliceL l s n) && Nat.beq (sliceL l s n).length m &&
    Nat.beq (countGates w (sliceL l s n)) c

/-- A slice and the rest after it, as the rest from the slice's start. -/
theorem infoSliceB_cons {w : ℕ} {l : List ℕ} {s n m₁ c₁ m₂ c₂ : ℕ} (hn : 0 < n)
    (h₁ : infoSliceB w l s n m₁ c₁ = true) (h₂ : infoSliceB w l (s + n) 0 m₂ c₂ = true) :
    infoSliceB w l s 0 (m₁ + m₂) (c₁ + c₂) = true := by
  simp only [infoSliceB, Bool.and_eq_true, Nat.beq_eq] at h₁ h₂ ⊢
  rw [← sliceL_append hn, List.length_append, countGates_append]
  exact ⟨⟨layerUniqueB_append h₁.1.1 h₂.1.1, by omega⟩, by omega⟩

/-- **Per layer, the slice from `0` on**: its gates' unique assertion terms and its counts. -/
def layersInfoB (w : ℕ) : List (List ℕ) → List ℕ → List ℕ → Bool
  | [], [], [] => true
  | l :: ls, m :: ms, c :: cs => infoSliceB w l 0 0 m c && layersInfoB w ls ms cs
  | _, _, _ => false

/-- The layers' check from the first layer's and the rest's. -/
theorem layersInfoB_cons {w m c : ℕ} {l : List ℕ} {ls : List (List ℕ)} {ms cs : List ℕ}
    (h₁ : infoSliceB w l 0 0 m c = true) (h₂ : layersInfoB w ls ms cs = true) :
    layersInfoB w (l :: ls) (m :: ms) (c :: cs) = true := by
  simp [layersInfoB, h₁, h₂]

/-- The layers' check on no layers. -/
theorem layersInfoB_nil {w : ℕ} : layersInfoB w [] [] [] = true := rfl

/-- The counts of the layers' check. -/
theorem layersCountB_of_info {w : ℕ} :
    ∀ {ls : List (List ℕ)} {ms cs : List ℕ}, layersInfoB w ls ms cs = true →
      layersCountB w ls ms cs = true
  | [], [], [], _ => rfl
  | l :: ls, m :: ms, c :: cs, h => by
    simp only [layersInfoB, infoSliceB, sliceL_zero, Bool.and_eq_true] at h
    simp only [layersCountB, Bool.and_eq_true]
    exact ⟨⟨h.1.1.2, h.1.2⟩, layersCountB_of_info h.2⟩
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [layersInfoB] at h

/-- The unique assertion terms of the layers' check. -/
theorem uniqueAssertsB_of_info {w n : ℕ} :
    ∀ {ls : List (List ℕ)} {ms cs : List ℕ}, layersInfoB w ls ms cs = true →
      uniqueAssertsB w ⟨n, ls⟩ = true
  | [], [], [], _ => uniqueAssertsB_nil
  | l :: ls, m :: ms, c :: cs, h => by
    simp only [layersInfoB, infoSliceB, sliceL_zero, Bool.and_eq_true] at h
    exact uniqueAssertsB_cons h.1.1.1 (uniqueAssertsB_of_info h.2)
  | [], _ :: _, _, h | [], [], _ :: _, h | _ :: _, [], _, h | _ :: _, _ :: _, [], h => by
    simp [layersInfoB] at h

/-- **The shape from the layers' gate counts `ms`**: at least one and at most `depth` layers,
each of at most `2 ^ width` gates. -/
def shapeLensB (ms : List ℕ) (width depth : ℕ) : Bool :=
  Nat.blt 0 ms.length && Nat.ble ms.length depth && ms.all fun m => Nat.ble m (2 ^ width)

/-- **The bridge's checks from the layers' check** and the shape of the gate counts. -/
theorem uniqueAssertsB_shapeB_of_info {w width depth : ℕ} {C : Layered} {ms cs : List ℕ}
    (h : layersInfoB w C.layers ms cs = true) (hs : shapeLensB ms width depth = true) :
    (uniqueAssertsB w C && shapeB C width depth) = true := by
  have hu : uniqueAssertsB w C = true := uniqueAssertsB_of_info (n := C.inputs) h
  have hm := map_length_of_layersCountB (layersCountB_of_info h)
  simp only [shapeLensB, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, List.all_eq_true] at hs
  rw [← hm] at hs
  simp only [List.length_map, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂] at hs
  rw [hu, shapeB_intro hs.1.1 hs.1.2 hs.2]
  rfl

/-- Every term of the layer `l`'s gates reads wires below `wp`. -/
def LayerReads (w : ℕ) (l : List ℕ) (wp : ℕ) : Prop :=
  ∀ c ∈ l, ∀ t ∈ gateTerms w c, t.a < wp ∧ t.b < wp

/-- Every layer from `ls` on reads wires of the layer below it, the first one wires below `wp`. -/
def ReadsFrom (w : ℕ) : ℕ → List (List ℕ) → Prop
  | _, [] => True
  | wp, l :: ls => LayerReads w l wp ∧ ReadsFrom w l.length ls

/-- **Every term of `C` reads wires of the layer below it** (the inputs, for the first layer). -/
def _root_.GordieHowe.GKR.Certificate.Layered.ReadsBelow (w : ℕ) (C : Layered) : Prop :=
  ReadsFrom w C.inputs C.layers

/-! ## The source circuit -/

section Source

variable {F : Type} [Field F] [DecidableEq F]

/-- The wire `a` of a layer of `2 ^ n` wires (`a` modulo `2 ^ n`; `a` itself for the wires the
layered circuit reads). -/
def wire (n a : ℕ) : Fin (2 ^ n) := ⟨a % 2 ^ n, Nat.mod_lt _ (Nat.two_pow_pos n)⟩

/-- A term is kept in the source: an assertion term, or a term whose constant is not `0`. -/
def keep (κ : ℕ → F) (t : Term) : Bool := Nat.beq t.k 0 || !decide (κ t.k = 0)

/-- A term's coefficient in the source: `0` for an assertion term, its constant otherwise. -/
def coef (κ : ℕ → F) (t : Term) : F := if t.k = 0 then 0 else κ t.k

/-- The corners of gate `g` of the layer `l` over `2 ^ n` input wires: its kept terms. -/
def gateCorners (w : ℕ) (κ : ℕ → F) (l : List ℕ) (m n : ℕ) (g : Fin (2 ^ m)) :
    List (Layer.Corner F (2 ^ m) (2 ^ n)) :=
  ((gateTerms w (l.getD g 0)).filter (keep κ)).map fun t => ⟨g, wire n t.a, wire n t.b, coef κ t⟩

/-- The corners of the layer `l` with `2 ^ m` gates over `2 ^ n` input wires, gate by gate. -/
def layerCorners (w : ℕ) (κ : ℕ → F) (l : List ℕ) (m n : ℕ) :
    List (Layer.Corner F (2 ^ m) (2 ^ n)) :=
  (List.finRange (2 ^ m)).flatMap (gateCorners w κ l m n)

/-- The dimension of a layer of `l.length` gates: `⌈log₂⌉` of its length. -/
def dim (l : List ℕ) : ℕ := Nat.clog 2 l.length

/-- The source layer of the layer `l` over `2 ^ n` input wires. -/
def layerOf (w : ℕ) (κ : ℕ → F) (l : List ℕ) (n : ℕ) :
    GKR.Layer F (2 ^ dim l) (2 ^ n) (layerCorners w κ l (dim l) n).length :=
  fun i => (layerCorners w κ l (dim l) n).get i

/-- The dimension of the wires below the layers `rs` (listed from the output down): the first
layer's, or `d` for the input. -/
def lowDim (d : ℕ) : List (List ℕ) → ℕ
  | [] => d
  | l :: _ => dim l

/-- The source circuit of the layers `rs`, listed from the output down, over an input of
dimension `d`. -/
def build (w : ℕ) (κ : ℕ → F) (d : ℕ) : (rs : List (List ℕ)) → GKR.Circuit F (lowDim d rs)
  | [] => .input d
  | l :: rs => .layer (layerOf w κ l (lowDim d rs)) (build w κ d rs)

/-- The source circuit's input has dimension `d`. -/
theorem build_inputDim (w : ℕ) (κ : ℕ → F) (d : ℕ) :
    ∀ rs : List (List ℕ), (build w κ d rs).inputDim = d
  | [] => rfl
  | _ :: rs => build_inputDim w κ d rs

/-- The layer squaring each of `2 ^ d` inputs: the source of a circuit without layers. -/
def squares (d : ℕ) : GKR.Layer F (2 ^ d) (2 ^ d) (2 ^ d) := fun i => ⟨i, i, i, 1⟩

/-- The source circuit of the layers `rs`, listed from the output down. -/
def ofLayers (w : ℕ) (κ : ℕ → F) (d : ℕ) : List (List ℕ) → LayeredCircuit F d
  | [] => ⟨d, d, 2 ^ d, squares d, .input d, rfl⟩
  | l :: rs => ⟨dim l, lowDim d rs, _, layerOf w κ l (lowDim d rs), build w κ d rs,
      build_inputDim w κ d rs⟩

/-- **The GKR source circuit of the layered circuit `C`** at the constants `κ`, over an input
of dimension `d`: the layers from the output down, padded to powers of two, a term `(k, a, b)`
of gate `g` the corner `(g, a, b, κ k)`, an assertion term the corner of coefficient `0`, and a
term of constant `0` left out. -/
def toSource (C : Layered) (w : ℕ) (κ : ℕ → F) (d : ℕ) : LayeredCircuit F d :=
  ofLayers w κ d C.layers.reverse

end Source

/-! ## Soundness -/

section Soundness

variable {F : Type} [Field F] [DecidableEq F]

/-- The wire values after the layers `ls` (listed from the inputs up), from the values `v`. -/
def run (w : ℕ) (κ : ℕ → F) : List (List ℕ) → (ℕ → F) → ℕ → F
  | [], v => v
  | l :: ls, v => run w κ ls (layerValue w κ l v)

omit [DecidableEq F] in
/-- The values after one more layer on top. -/
theorem run_append_singleton (w : ℕ) (κ : ℕ → F) (l : List ℕ) :
    ∀ (ls : List (List ℕ)) (v : ℕ → F), run w κ (ls ++ [l]) v = layerValue w κ l (run w κ ls v)
  | [], _ => rfl
  | _ :: ls, _ => run_append_singleton w κ l ls _

/-- The zero chunk is a gate without terms. -/
@[simp] theorem gateTerms_zero (w : ℕ) : gateTerms w 0 = [] := by
  simp [gateTerms, decodeTerms]

/-- A layer's gates past its length have no terms. -/
theorem gateTerms_getD_of_le {w : ℕ} {l : List ℕ} {g : ℕ} (h : l.length ≤ g) :
    gateTerms w (l.getD g 0) = [] := by
  rw [List.getD_eq_default _ _ h, gateTerms_zero]

/-- A gate's chunk is one of its layer's, or the zero chunk. -/
theorem getD_mem_or {l : List ℕ} {g : ℕ} : l.getD g 0 ∈ l ∨ l.getD g 0 = 0 := by
  by_cases h : g < l.length
  · left
    rw [List.getD_eq_getElem _ _ h]
    exact List.getElem_mem h
  · right
    exact List.getD_eq_default _ _ (by omega)

omit [DecidableEq F] in
/-- Reading the wire `a` of a padded layer is reading the value `a`, below the padding. -/
theorem vecRead_wire {n a : ℕ} (u : Fin (2 ^ n) → F) (h : a < 2 ^ n) :
    u (wire n a) = vecRead u a := by
  simp [wire, vecRead, h, Nat.mod_eq_of_lt h]

omit [DecidableEq F] in
/-- A sum over the corners of a list is the sum of the mapped list. -/
theorem sum_get {α : Type} (cs : List α) (f : α → F) :
    ∑ i : Fin cs.length, f (cs.get i) = (cs.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_get <;> simp

/-- A sum over the corners of a layer: the sum, gate by gate, over each gate's corners. -/
theorem sum_layerOf {w : ℕ} {κ : ℕ → F} {l : List ℕ} {n : ℕ}
    (f : Layer.Corner F (2 ^ dim l) (2 ^ n) → F) :
    ∑ i, f (layerOf w κ l n i) = ∑ g, ((gateCorners w κ l (dim l) n g).map f).sum := by
  show ∑ i : Fin (layerCorners w κ l (dim l) n).length,
    f ((layerCorners w κ l (dim l) n).get i) = _
  rw [sum_get, layerCorners, List.flatMap_def, List.map_flatten, List.sum_flatten, List.map_map,
    List.map_map, Fin.sum_univ_def]
  rfl

/-- Only gate `g`'s corners are at gate `g`. -/
theorem sum_layerOf_gate {w : ℕ} {κ : ℕ → F} {l : List ℕ} {n : ℕ} (g : Fin (2 ^ dim l))
    (f : Layer.Corner F (2 ^ dim l) (2 ^ n) → F) :
    ∑ i, (if (layerOf w κ l n i).gate = g then f (layerOf w κ l n i) else 0) =
      ((gateCorners w κ l (dim l) n g).map f).sum := by
  rw [sum_layerOf (fun c => if c.gate = g then f c else 0)]
  rw [Finset.sum_eq_single g]
  · congr 1
    apply List.map_congr_left
    intro c hc
    simp only [gateCorners, List.mem_map] at hc
    obtain ⟨t, _, rfl⟩ := hc
    simp
  · intro g' _ hg'
    apply List.sum_eq_zero
    intro x hx
    simp only [gateCorners, List.map_map, List.mem_map, Function.comp] at hx
    obtain ⟨t, _, rfl⟩ := hx
    simp [hg']
  · simp

omit [DecidableEq F] in
/-- A sum over a filtered list: the terms the filter drops count zero. -/
theorem sum_map_filter {α : Type} (p : α → Bool) (f : α → F) :
    ∀ l : List α, ((l.filter p).map f).sum = (l.map fun x => if p x then f x else 0).sum
  | [] => rfl
  | x :: xs => by
    by_cases hp : p x <;> simp [hp, sum_map_filter p f xs]

/-- A kept term's coefficient is `0` exactly when it is an assertion term. -/
theorem coef_eq_zero_iff {κ : ℕ → F} {t : Term} (h : keep κ t = true) :
    coef κ t = 0 ↔ t.k = 0 := by
  by_cases hk : t.k = 0
  · simp [coef, hk]
  · simp only [keep, Bool.or_eq_true, Nat.beq_eq, hk, false_or, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    simp [coef, hk, h]

/-- A term list with an assertion term has one. -/
theorem hasAssert_of_mem : ∀ {ts : List Term} {t : Term}, t ∈ ts → t.k = 0 → hasAssert ts = true
  | s :: ss, t, ht, hk => by
    rcases List.mem_cons.mp ht with rfl | ht
    · rw [hasAssert, hk]
      rfl
    · rw [hasAssert, hasAssert_of_mem ht hk, Bool.or_true]

omit [DecidableEq F] in
/-- Without an assertion term, the assertion terms' sum vanishes. -/
theorem sum_asserts_of_not_hasAssert (f : Term → F) :
    ∀ ts : List Term, hasAssert ts = false → (ts.map fun t => if t.k = 0 then f t else 0).sum = 0
  | [], _ => rfl
  | t :: ts, h => by
    rw [hasAssert, Bool.or_eq_false_iff] at h
    have hk : t.k ≠ 0 := Nat.ne_of_beq_eq_false h.1
    simp [hk, sum_asserts_of_not_hasAssert f ts h.2]

omit [DecidableEq F] in
/-- With at most one assertion term, each assertion term's value is the assertion terms' sum. -/
theorem atMostOneAssert_sum (f : Term → F) :
    ∀ ts : List Term, atMostOneAssert ts = true → ∀ t ∈ ts, t.k = 0 →
      f t = (ts.map fun t => if t.k = 0 then f t else 0).sum
  | [], _, _, h, _ => by simp at h
  | u :: ts, h, t, ht, hk => by
    by_cases hu : u.k = 0
    · have hb : Nat.beq u.k 0 = true := by
        rw [hu]
        rfl
      rw [atMostOneAssert, hb, Bool.cond_true, Bool.not_eq_true'] at h
      have hz := sum_asserts_of_not_hasAssert f ts h
      rcases List.mem_cons.mp ht with rfl | ht
      · simp [hu, hz]
      · rw [hasAssert_of_mem ht hk] at h
        exact Bool.noConfusion h
    · have hb : Nat.beq u.k 0 = false := by
        cases h' : Nat.beq u.k 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true h') hu
      rw [atMostOneAssert, hb, Bool.cond_false] at h
      rcases List.mem_cons.mp ht with rfl | ht
      · exact absurd hk hu
      · simp [hu, atMostOneAssert_sum f ts h t ht hk]

/-- The source layer's output at gate `g`: the sum of its kept terms. -/
theorem output_layerOf {w : ℕ} {κ : ℕ → F} {l : List ℕ} {n : ℕ} (u : Fin (2 ^ n) → F)
    (g : Fin (2 ^ dim l)) :
    GKR.Circuit.output (layerOf w κ l n) u g =
      (((gateTerms w (l.getD g 0)).filter (keep κ)).map fun t =>
        coef κ t * (u (wire n t.a) * u (wire n t.b))).sum := by
  simp only [GKR.Circuit.output, Layer.product]
  rw [sum_layerOf_gate g (fun c => c.coefficient * (u c.left * u c.right))]
  simp only [gateCorners, List.map_map]
  rfl

/-- The source layer's assertions at gate `g`: the sum of its assertion terms' products. -/
theorem assertions_layerOf {w : ℕ} {κ : ℕ → F} {l : List ℕ} {n : ℕ} (u : Fin (2 ^ n) → F)
    (g : Fin (2 ^ dim l)) :
    Layer.assertions (layerOf w κ l n) u g =
      ((gateTerms w (l.getD g 0)).map fun t =>
        if t.k = 0 then u (wire n t.a) * u (wire n t.b) else 0).sum := by
  calc Layer.assertions (layerOf w κ l n) u g
      = ∑ i, (if (layerOf w κ l n i).gate = g then
          (fun c : Layer.Corner F (2 ^ dim l) (2 ^ n) =>
            if c.coefficient = 0 then u c.left * u c.right else 0) (layerOf w κ l n i)
          else 0) := by
        unfold Layer.assertions
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp_all [Layer.product]
    _ = _ := by
        refine (sum_layerOf_gate g
          (fun c => if c.coefficient = 0 then u c.left * u c.right else 0)).trans ?_
        simp only [gateCorners, List.map_map]
        rw [sum_map_filter]
        refine congrArg List.sum (List.map_congr_left fun t _ => ?_)
        by_cases hk : keep κ t = true
        · simp only [Function.comp, hk, ite_true, coef_eq_zero_iff hk]
        · have : t.k ≠ 0 := by
            intro h0
            simp [keep, h0] at hk
          simp only [Function.comp, hk, Bool.false_eq_true, ite_false, this]

/-- The step of the induction: one layer of the source on top of the layers below it. -/
theorem layer_sound {w : ℕ} {κ : ℕ → F} {l : List ℕ} {n wp : ℕ} (u : Fin (2 ^ n) → F)
    (hwp : wp ≤ 2 ^ n) (hr : LayerReads w l wp)
    (hU : ∀ c ∈ l, atMostOneAssert (gateTerms w c) = true)
    (hA : ∀ g, Layer.assertions (layerOf w κ l n) u g = 0) :
    (∀ g < l.length, ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 →
        vecRead u t.a * vecRead u t.b = 0) ∧
      vecRead (GKR.Circuit.output (layerOf w κ l n) u) = layerValue w κ l (vecRead u) := by
  have hasrt : ∀ g < l.length, ∀ t ∈ gateTerms w (l.getD g 0), t.k = 0 →
      vecRead u t.a * vecRead u t.b = 0 := by
    intro g hg t ht hk
    have hmem : l.getD g 0 ∈ l := by
      rw [List.getD_eq_getElem _ _ hg]
      exact List.getElem_mem hg
    have hlt : g < 2 ^ dim l := lt_of_lt_of_le hg (Nat.le_pow_clog (by norm_num) _)
    have hab := hr _ hmem t ht
    rw [← vecRead_wire u (by omega), ← vecRead_wire u (by omega),
      atMostOneAssert_sum (fun t => u (wire n t.a) * u (wire n t.b)) _ (hU _ hmem) t ht hk,
      ← assertions_layerOf u ⟨g, hlt⟩]
    exact hA _
  refine ⟨hasrt, ?_⟩
  funext g
  by_cases hg : g < l.length
  · have hlt : g < 2 ^ dim l := lt_of_lt_of_le hg (Nat.le_pow_clog (by norm_num) _)
    have hmem : l.getD g 0 ∈ l := by
      rw [List.getD_eq_getElem _ _ hg]
      exact List.getElem_mem hg
    simp only [vecRead, hlt, ↓reduceDIte]
    rw [output_layerOf, layerValue, sum_map_filter]
    refine congrArg List.sum (List.map_congr_left fun t ht => ?_)
    have hab := hr _ hmem t ht
    rw [vecRead_wire u (by omega), vecRead_wire u (by omega)]
    by_cases hk : t.k = 0
    · have hz := hasrt g hg t ht hk
      simp [keep, coef, hk, mul_assoc, hz]
    · by_cases hκ : κ t.k = 0
      · simp [keep, hk, hκ]
      · simp [keep, coef, hk, hκ, mul_assoc]
  · have hn : gateTerms w (l.getD g 0) = [] := gateTerms_getD_of_le (by omega)
    rw [layerValue, hn]
    by_cases hlt : g < 2 ^ dim l
    · have hn' : gateTerms w (l.getD ((⟨g, hlt⟩ : Fin (2 ^ dim l)) : ℕ) 0) = [] := hn
      simp only [vecRead, hlt, ↓reduceDIte]
      rw [output_layerOf, hn']
      rfl
    · simp [vecRead, hlt]

/-- The width of the wires below the layers `rs` (listed from the output down): the first
layer's length, or `n0` for the inputs. -/
def lowWidth (n0 : ℕ) : List (List ℕ) → ℕ
  | [] => n0
  | l :: _ => l.length

/-- The reads of the layers `rs`, listed from the output down: each layer reads wires of the
layer below it, the last one wires below `n0`. -/
def RevReads (w n0 : ℕ) : List (List ℕ) → Prop
  | [] => True
  | l :: rs => LayerReads w l (lowWidth n0 rs) ∧ RevReads w n0 rs

/-- The width below the layers `rs` with one more layer at the bottom. -/
theorem lowWidth_append (n0 : ℕ) (l : List ℕ) :
    ∀ rs : List (List ℕ), lowWidth n0 (rs ++ [l]) = lowWidth l.length rs
  | [] => rfl
  | _ :: _ => rfl

/-- The reads of the layers `rs` with one more layer at the bottom. -/
theorem revReads_append (w n0 : ℕ) (l : List ℕ) :
    ∀ rs : List (List ℕ), RevReads w n0 (rs ++ [l]) ↔ RevReads w l.length rs ∧ LayerReads w l n0
  | [] => by simp [RevReads, lowWidth]
  | r :: rs => by
    simp only [List.cons_append, RevReads, lowWidth_append, revReads_append w n0 l rs, and_assoc]

/-- The reads from the inputs up, listed from the output down. -/
theorem revReads_reverse (w : ℕ) :
    ∀ (ls : List (List ℕ)) (wp : ℕ), ReadsFrom w wp ls → RevReads w wp ls.reverse
  | [], _, _ => trivial
  | l :: ls, wp, h => by
    rw [List.reverse_cons, revReads_append]
    exact ⟨revReads_reverse w ls l.length h.2, h.1⟩

/-- The wires below any layer fit its padded input, when the inputs fit in `2 ^ d`. -/
theorem lowWidth_le {n0 d : ℕ} (h : n0 ≤ 2 ^ d) :
    ∀ rs : List (List ℕ), lowWidth n0 rs ≤ 2 ^ lowDim d rs
  | [] => h
  | _ :: _ => Nat.le_pow_clog (by norm_num) _

/-- **The induction over the source's layers**: if the source circuit of the layers `rs` (listed
from the output down) meets its assertions on the input `u`, its output is the layered circuit's
values after the layers, and every layered satisfaction above them extends down to the input. -/
theorem build_sound {w : ℕ} {κ : ℕ → F} {d n0 : ℕ} (hfit : n0 ≤ 2 ^ d) :
    ∀ (rs : List (List ℕ)) (u : Fin (2 ^ (build w κ d rs).inputDim) → F),
      RevReads w n0 rs → (∀ l ∈ rs, ∀ c ∈ l, atMostOneAssert (gateTerms w c) = true) →
      (build w κ d rs).AssertionsHold u →
        vecRead ((build w κ d rs).eval u) = run w κ rs.reverse (vecRead u) ∧
          ∀ ms, Sat w κ ms (run w κ rs.reverse (vecRead u)) →
            Sat w κ (rs.reverse ++ ms) (vecRead u)
  | [], u, _, _, _ => ⟨rfl, fun _ h => h⟩
  | l :: rs, u, hr, hU, hA => by
    obtain ⟨hAl, hAt⟩ := hA
    obtain ⟨ih1, ih2⟩ := build_sound hfit rs u hr.2
      (fun l' hl' => hU l' (List.mem_cons_of_mem _ hl')) hAt
    obtain ⟨has, hval⟩ := layer_sound ((build w κ d rs).eval u) (lowWidth_le hfit rs) hr.1
      (hU l (List.mem_cons_self ..)) hAl
    rw [ih1] at has hval
    refine ⟨?_, ?_⟩
    · rw [List.reverse_cons, run_append_singleton]
      exact hval
    · intro ms hs
      rw [List.reverse_cons, List.append_assoc, List.singleton_append]
      apply ih2
      rw [List.reverse_cons, run_append_singleton] at hs
      exact ⟨has, hs⟩

omit [DecidableEq F] in
/-- Reading a vector through a cast of its dimension. -/
theorem vecRead_comp_cast {n d : ℕ} (h : 2 ^ n = 2 ^ d) (v : Fin (2 ^ d) → F) :
    vecRead (v ∘ Fin.cast h) = vecRead v := by
  funext p
  by_cases hp : p < 2 ^ n
  · simp [vecRead, hp, ← h]
  · simp [vecRead, hp, ← h]

/-- **Soundness of the bridge**: if every gate of `C` has at most one assertion term, every term
reads wires of the layer below it and the inputs fit in `2 ^ d`, then wherever the source circuit
`toSource C w κ d` is satisfied by `v`, the layered circuit is satisfied by `vecRead v`. -/
theorem toSource_satisfied {C : Layered} {w : ℕ} {κ : ℕ → F} {d : ℕ}
    (hu : uniqueAssertsB w C = true) (hfit : C.inputs ≤ 2 ^ d) (hr : C.ReadsBelow w)
    {v : Fin (2 ^ d) → F} (h : (toSource C w κ d).Satisfied v) :
    C.Satisfied w κ (vecRead v) := by
  have hU : ∀ l ∈ C.layers.reverse, ∀ c ∈ l, atMostOneAssert (gateTerms w c) = true := by
    intro l hl c hc
    simp only [uniqueAssertsB, layerUniqueB, List.all_eq_true] at hu
    exact hu l (List.mem_reverse.mp hl) c hc
  have hR := revReads_reverse w C.layers C.inputs hr
  unfold Layered.Satisfied
  rw [← List.reverse_reverse C.layers]
  unfold toSource LayeredCircuit.Satisfied LayeredCircuit.circuit LayeredCircuit.inputIndex at h
  generalize C.layers.reverse = rs at hU hR h ⊢
  cases rs with
  | nil =>
    obtain ⟨hz, -⟩ := h
    intro g
    by_cases hg : g < 2 ^ d
    · have := hz ⟨g, hg⟩
      change (∑ i : Fin (2 ^ d), if i = ⟨g, hg⟩ then (1 : F) * (v i * v i) else 0) = 0 at this
      rw [Finset.sum_eq_single ⟨g, hg⟩ (fun j _ hj => by simp [hj])
        (fun h => absurd (Finset.mem_univ _) h)] at this
      simpa [vecRead, hg] using this
    · simp [vecRead, hg]
  | cons l rs =>
    obtain ⟨hz, hA⟩ := h
    have hb := build_sound hfit (l :: rs)
      (v ∘ Fin.cast (congrArg (fun m => 2 ^ m) (build_inputDim w κ d (l :: rs)))) hR hU hA
    rw [vecRead_comp_cast] at hb
    obtain ⟨h1, h2⟩ := hb
    have := h2 [] (by
      rw [← h1]
      intro g
      unfold vecRead
      split_ifs with hg
      · exact hz ⟨g, hg⟩
      · rfl)
    rwa [List.append_nil] at this

/-- An accepted gate's terms read wires below `wp`. -/
theorem termsOk_reads {w : ℕ} {T : Certificate.Table} {wp r : ℕ} :
    ∀ ts us, termsOk w T wp r ts us = true → ∀ t ∈ ts, t.a < wp ∧ t.b < wp
  | [], _, _ => by simp
  | t :: ts, u :: us, h => by
    simp only [termsOk, Bool.and_eq_true, Nat.blt_eq] at h
    intro t' ht'
    rcases List.mem_cons.mp ht' with rfl | ht'
    · exact ⟨h.1.1.1.1.1.2, h.1.1.1.1.2⟩
    · exact termsOk_reads ts us h.2 t' ht'
  | _ :: _, [], h => by simp [termsOk] at h

/-- An accepted copy gate's term reads wires below `wp`. -/
theorem copyOk_reads {w : ℕ} {T : Certificate.Table} {wp r : ℕ} :
    ∀ ts, copyOk w T wp r ts = true → ∀ t ∈ ts, t.a < wp ∧ t.b < wp
  | [t], h => by
    simp only [copyOk, Bool.and_eq_true, Nat.blt_eq] at h
    intro t' ht'
    rw [List.mem_singleton.mp ht']
    exact ⟨h.1.1.2, h.1.2⟩
  | [], h => by simp [copyOk] at h
  | _ :: _ :: _, h => by simp [copyOk] at h

/-- An accepted gate's terms, copy or not, read wires below `wp`. -/
theorem gateOk_reads {w : ℕ} {D : Dag} {Tp Tc : Certificate.Table} {wp c : ℕ}
    (h : gateOk w D Tp wp Tc c = true) : ∀ t ∈ gateTerms w c, t.a < wp ∧ t.b < wp := by
  unfold gateOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨_, h⟩ := h
  cases hf : flagged w c with
  | false =>
    rw [hf, Bool.cond_false, Bool.and_eq_true] at h
    exact termsOk_reads _ _ h.2
  | true =>
    rw [hf, Bool.cond_true] at h
    exact copyOk_reads _ h

/-- An accepted layer reads wires below `wp`. -/
theorem gatesOk_reads {w : ℕ} {D : Dag} {Tp Tc : Certificate.Table} {wp : ℕ} :
    ∀ (g : ℕ) (cs : List ℕ), gatesOk w D Tp wp Tc g cs = true → LayerReads w cs wp
  | _, [], _ => by simp [LayerReads]
  | g, c :: cs, h => by
    simp only [gatesOk, Bool.and_eq_true] at h
    intro c' hc' t ht
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact gateOk_reads h.1.2 t ht
    · exact gatesOk_reads _ cs h.2 c' hc' t ht

/-- Accepted layers read, each, wires of the layer below it. -/
theorem layersOk_reads {w : ℕ} {D : Dag} {outs : List (ℕ × ℕ)} {outw : List ℕ} :
    ∀ (Tp : Certificate.Table) (wp : ℕ) (Ts : List Certificate.Table) (ls : List (List ℕ)),
      layersOk w D outs outw Tp wp Ts ls = true → ReadsFrom w wp ls
  | _, _, _, [], _ => trivial
  | _, _, T :: Ts, l :: ls, h => by
    simp only [layersOk, Bool.and_eq_true] at h
    exact ⟨gatesOk_reads 0 l h.1, layersOk_reads T l.length Ts ls h.2⟩
  | _, _, [], _ :: _, h => by simp [layersOk] at h

/-- **The certificate checker's reads**: an accepted certificate's layered circuit reads, in each
layer, wires of the layer below it. -/
theorem readsBelow_of_check {D : Dag} {C : Layered} {K : Cert} (h : check D C K = true) :
    C.ReadsBelow K.width := by
  simp only [check, Bool.and_eq_true] at h
  exact layersOk_reads _ _ _ _ h.1.1.2

end Soundness

/-! ## Shape -/

section Shape

variable {F : Type} [Field F] [DecidableEq F]

/-- A layer of at most `2 ^ width` gates has dimension at most `width`. -/
theorem dim_le {l : List ℕ} {width : ℕ} (h : l.length ≤ 2 ^ width) : dim l ≤ width :=
  Nat.clog_le_of_le_pow h

/-- The source circuit of layers of at most `2 ^ width` gates over an input of dimension at
most `width` reads at most `2 ^ width` wires in every layer. -/
theorem widths_build {w : ℕ} {κ : ℕ → F} {d width : ℕ} (hd : d ≤ width) :
    ∀ rs : List (List ℕ), (∀ l ∈ rs, l.length ≤ 2 ^ width) →
      lowDim d rs ≤ width ∧ CircuitBudget.WidthsAtMost (build w κ d rs) width
  | [], _ => ⟨hd, trivial⟩
  | l :: rs, h => by
    have ih := widths_build (w := w) (κ := κ) hd rs
      (fun l' hl' => h l' (List.mem_cons_of_mem _ hl'))
    exact ⟨dim_le (h l (List.mem_cons_self ..)), ih.1, ih.2⟩

/-- The source circuit of the layers `rs` has one layer per layer of `rs`. -/
theorem depth_build {w : ℕ} {κ : ℕ → F} {d : ℕ} :
    ∀ rs : List (List ℕ), (build w κ d rs).depth = rs.length
  | [] => rfl
  | _ :: rs => congrArg (· + 1) (depth_build rs)

/-- **The shape of the source**: if `C` has at least one and at most `depth` layers of at most
`2 ^ width` gates (`shapeB`) and the input dimension `d` is at most `width`, the source circuit has
at most `2 ^ width` wires in every layer and at most `depth` layers. -/
theorem toSource_shapeAtMost {C : Layered} {w : ℕ} {κ : ℕ → F} {d width depth : ℕ}
    (hs : shapeB C width depth = true) (hd : d ≤ width) :
    (toSource C w κ d).ShapeAtMost width depth := by
  simp only [shapeB, Bool.and_eq_true, Nat.blt_eq, Nat.ble_eq, List.all_eq_true] at hs
  obtain ⟨⟨hpos, hdep⟩, hlen⟩ := hs
  have hlen' : ∀ l ∈ C.layers.reverse, l.length ≤ 2 ^ width :=
    fun l hl => hlen l (List.mem_reverse.mp hl)
  rw [← List.length_reverse] at hpos hdep
  unfold toSource
  generalize C.layers.reverse = rs at hpos hdep hlen' ⊢
  cases rs with
  | nil => simp at hpos
  | cons l rs =>
    have hw := widths_build (w := w) (κ := κ) hd (l :: rs) hlen'
    refine ⟨hw.1, hw.2, ?_⟩
    change (build w κ d (l :: rs)).depth ≤ depth
    rw [depth_build]
    exact hdep

/-- **The shape of the source of circuit `c`**: at the width (`circuitWidth`) and layers of
circuit `c` of the realized program, when `C` passes `shapeB` there and `d` is at most the
width. -/
theorem toSource_shape {ir : RealizedProgram} {c : ℕ} {C : Layered} {w : ℕ} {κ : ℕ → F} {d : ℕ}
    (hs : shapeB C (ir.circuitWidth c) (ir.circuit c).layers = true)
    (hd : d ≤ ir.circuitWidth c) :
    (toSource C w κ d).ShapeAtMost (ir.circuitWidth c) (ir.circuit c).layers :=
  toSource_shapeAtMost hs hd

end Shape

end GordieHowe.GKR.CertificateBridge
