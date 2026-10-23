-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeMod
public import GordieHowe.Language.Realizations.MACEquality
public import GordieHowe.Language.RealizedProgram.Affine

@[expose] public section

/-!
# GordieHowe: the MAC of a cross-field `equal`, realized

The lemmas of the MAC realization of a cross-field `equal`, hosted by the `x` domain
(`GordieHowe.RealizedProgram.MacShapeOk`) or by no domain (`GordieHowe.RealizedProgram.MacTwoTailOk`; compiler/mac.h, `mac` and
`mac_odd`):

* **The model** (`Interp.MacModel`, a property of the interpretation): the field of every MAC tail's
  powers is a binary field with a polynomial basis of the tail's width and taps whose coordinates are
  the bits of the integer reading and whose elements are the powers of the generator (the decoding of
  `2`), and whose constants `2^j` decode to the generator's powers; the opaque function computing the
  target's bits returns the bits of its argument.
* **The powers** (`GordieHowe.RealizedProgram.reader_powers`): the powers value reads `β^(c+1)` (`powersB`).
* **The MAC checks over the fields** (`GordieHowe.RealizedProgram.MacFieldCheckAt`: the tag's
  message `T` is the masked MAC at the key of the chunks of a field's operand with the field's pad;
  the checks over two fields bind, `GordieHowe.RealizedProgram.MacFieldCheckAt.binding`, by
  `MAC.binding`): the check over the hosting field by its H half
  (`GordieHowe.RealizedProgram.macFieldCheckAt_of_macH`: `MacHHoldsAt`, by the compiler's own
  circuit or the H predicate `<mac>.H`, `macHHolds_of_pred`), the check over a field of odd
  characteristic by its tail `mod_2` (`GordieHowe.RealizedProgram.macFieldCheckAt_of_odd`: the
  tail's congruence over the integers gives each bit of `T` as the parity of the integer
  accumulator, `NamedOp.applyInt_macConv`, so `T` is the masked MAC of the check's operand,
  `MACRows.maskedMAC_eq_of_unpack`), the check over a field of characteristic `2` by its field
  `equal` (`GordieHowe.RealizedProgram.macFieldCheckAt_of_two`: the field computes each accumulator
  entry modulo `2`).
* **Soundness** (`GordieHowe.RealizedProgram.crossHolds_or_macBad`, hosted; `GordieHowe.RealizedProgram.crossHolds_or_macBad_twoTail`, no
  domain hosting the MAC): the cross-field `equal` holds or the key is a root of the MAC's binding
  polynomial (`macEvent`). Where the hosted MAC's H operand reads below `2` (a bit, by the
  polynomial basis, `eq_zero_or_one_of_toNat_lt_two`), equal packed chunks give equal coordinates
  (`crossHolds_of_chunks`); where no domain hosts the MAC, each check's operand reads bits by the
  program (an interval in odd characteristic; `exprBitsB` in characteristic `2`: views of `Bit`
  values stored at their node or with their Boolean checks, `evalWith_bit_of_exprBitsB`), and equal
  chunks give equal coordinates (`crossHolds_of_chunksA`).
* **The event's probability** (`GordieHowe.RealizedProgram.probUniform_macBad_le`): at most `chunks / |K|` over the key,
  uniform in the MAC field.

The H operand's Booleanity is not established here: the cross-field `equal`'s meaning
(`GordieHowe.RealizedProgram.HoldsWith`, the compiler's contract) concludes the operands' equality only where every
coordinate of the H operand reads below `2`. ML-DSA's H operand `c_enc² + c_enc` is made with
`bit_from_unchecked`; its Booleanity is established by the source program (the shuffle) and proved
in the round-by-round soundness of `Π_P₀`.
-/

namespace GordieHowe.RealizedProgram

open Export IOP
open scoped NNReal ENNReal

/-- **A binary MAC field of width `w` and reduction taps `taps`** (a property of the field's
representation in Lean): characteristic `2`, a polynomial basis (`Conv.ConvBasis`) whose coordinates
are the bits of the integer reading (`toNat`, bit `j` the coefficient of `g^j`) and whose elements
are the powers of the generator `g`, the decoding of `2`, and constants `2^j` decoding to `g^j` (the
H predicate's coefficients, `RealizedProgram.macHPredB`). -/
structure FieldInterp.MacFieldOk (F : FieldInterp) (w : ℕ) (taps : Finset ℕ) : Prop where
  /-- Characteristic `2`. -/
  charTwo : CharP F.K 2
  /-- The polynomial basis. -/
  basis : ∃ B : Conv.ConvBasis w taps F.K,
    (∀ x j, B.unpack x j = (F.toNat x).testBit j) ∧ ∀ j, B.e j = F.decode 2 ^ (j : ℕ)
  /-- A constant `2^j`, `j < w`, decodes to the `j`-th power of the generator (the constants are
  the polynomial-basis bits). -/
  decodePow : ∀ j < w, F.decode (2 ^ j) = F.decode 2 ^ j

/-- **Field `f` of the interpretation is a binary MAC field** of width `w` and reduction taps `taps`
(`FieldInterp.MacFieldOk`). -/
abbrev Interp.MacFieldOk (I : Interp) (f w : ℕ) (taps : Finset ℕ) : Prop := (I f).MacFieldOk w taps

/-- **The interpretation of a program's MACs** (a property of the model): for every MAC tail
`mod_2(b + macConv(r, w, nch, taps)(y), tb)` (`mod`) and every MAC tail of characteristic `2`, the
field `equal` `b + macConv(r, w, nch, taps)(y) = tb` (`two`), the field of the powers `r` is a
binary MAC field of width `w` and taps `taps` (`MacFieldOk`), and the opaque function computing `tb`
returns bit `i` of its argument's first coordinate (`<mac>.target_bits`). -/
structure Interp.MacModel (I : Interp) (ir : RealizedProgram) : Prop where
  /-- The tails `mod_2`. -/
  mod : ∀ t < ir.predicates.length, ∀ d b r w nch taps y tb real,
    (ir.predicate t).body =
        .mod d 2 (.add (.leaf b) (.apply (.macConv r w nch taps) y)) (.leaf tb) real →
      I.MacFieldOk (ir.valueField r) w taps.toFinset ∧
        ∀ nm args, (ir.value tb).kind = .pub (.opaque nm args) → ∀ xs i,
          I.opaqueFn nm xs i = if ((xs.headD 0) 0).testBit i then 1 else 0
  /-- The tails of characteristic `2`. -/
  two : ∀ t < ir.predicates.length, ∀ d b r w nch taps y tb tgt,
    (ir.predicate t).body =
        .equal d (.add (.leaf b) (.apply (.macConv r w nch taps) y)) (.leaf tb) tgt →
      I.MacFieldOk (ir.valueField r) w taps.toFinset ∧
        ∀ nm args, (ir.value tb).kind = .pub (.opaque nm args) → ∀ xs i,
          I.opaqueFn nm xs i = if ((xs.headD 0) 0).testBit i then 1 else 0

section

/-- **Whether predicate `t` is a MAC tail** `mod_2(b + macConv(r, w, nch, taps)(y), tb)` or a MAC
tail of characteristic `2`, `equal(b + macConv(r, w, nch, taps)(y), tb)`, the predicates
`Interp.MacModel` reads. -/
def isMacTail (ir : RealizedProgram) (t : ℕ) : Bool :=
  match (ir.predicate t).body with
  | .mod _ 2 (.add (.leaf _) (.apply (.macConv _ _ _ _) _)) (.leaf _) _ => true
  | .equal _ (.add (.leaf _) (.apply (.macConv _ _ _ _) _)) (.leaf _) _ => true
  | _ => false

/-- **Every MAC tail of the program has its powers in field `f`, chunk width `w` and taps `taps`,
and its target's bits computed by the opaque function `nm`, and no tail has characteristic `2`**
(decided): the program's part of `Interp.MacModel` (`Interp.macModel_of_tails`). -/
def macTailsAt (ir : RealizedProgram) (f w : ℕ) (taps : Finset ℕ) (nm : String) : Bool :=
  (List.range ir.predicates.length).all fun t =>
    match (ir.predicate t).body with
    | .mod _ 2 (.add (.leaf _) (.apply (.macConv r w' _ taps') _)) (.leaf tb) _ =>
      ir.valueField r == f && w' == w && decide (taps'.toFinset = taps) &&
        match (ir.value tb).kind with
        | .pub (.opaque nm' _) => nm' == nm
        | _ => false
    | .equal _ (.add (.leaf _) (.apply (.macConv _ _ _ _) _)) (.leaf _) _ => false
    | _ => true

end

/-- **The MAC model from the program's MAC tails** (`RealizedProgram.macTailsAt`): where every MAC tail has
its powers in field `f` of width `w` and taps `taps` and its target's bits computed by `nm`, the
interpretation is a MAC model when `f` is a binary MAC field of that width and those taps
(`MacFieldOk`) and `nm` returns the bits of its argument. -/
theorem Interp.macModel_of_tails {I : Interp} {ir : RealizedProgram} {f w : ℕ} {taps : Finset ℕ}
    {nm : String} (h : ir.macTailsAt f w taps nm = true) (hF : I.MacFieldOk f w taps)
    (hop : ∀ xs i, I.opaqueFn nm xs i = if ((xs.headD 0) 0).testBit i then 1 else 0) :
    I.MacModel ir := by
  refine ⟨fun t ht d b r w' nch taps' y tb real hb => ?_, fun t ht d b r w' nch taps' y tb tgt hb => ?_⟩
  · have h1 := List.all_eq_true.1 h t (List.mem_range.2 ht)
    simp only [hb, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    obtain ⟨⟨⟨hr, rfl⟩, rfl⟩, hk⟩ := h1
    refine ⟨hr ▸ hF, fun nm' args hk' xs i => ?_⟩
    rw [hk'] at hk
    simp only [beq_iff_eq] at hk
    rw [hk]
    exact hop xs i
  · have h1 := List.all_eq_true.1 h t (List.mem_range.2 ht)
    simp [hb] at h1

/-- **A program without MAC tails constrains no interpretation's MACs** (`Interp.MacModel` holds
vacuously). -/
theorem Interp.macModel_of_noTail {I : Interp} {ir : RealizedProgram}
    (h : ∀ t < ir.predicates.length, ir.isMacTail t = false) : I.MacModel ir := by
  refine ⟨fun t ht d b r w nch taps y tb real hb => ?_, fun t ht d b r w nch taps y tb tgt hb => ?_⟩
  · have := h t ht
    simp [RealizedProgram.isMacTail, hb] at this
  · have := h t ht
    simp [RealizedProgram.isMacTail, hb] at this

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-! ## Reading values -/

/-- **A public expression reads its expression** one level down. -/
theorem reader_of_pubExpr (e : ir.Env I) {v : ℕ} {E : Expr} (hk : (ir.value v).kind = .pub (.expr E))
    (i : ℕ) : ir.reader e v i = ir.evalE (ir.read e ir.values.length) (ir.valueField v) E i := by
  simp only [reader, fuel, read, hk]

/-- **A challenge value reads its challenge** at any positive level. -/
theorem read_of_challenge (e : ir.Env I) {v c n : ℕ} (hk : (ir.value v).kind = .challenge c)
    (hn : 0 < n) (i : ℕ) : ir.read e n v i = castElt (e.chal c i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [read, hk]

/-- **A constant reads its entries** at any positive level. -/
theorem read_of_constant (e : ir.Env I) {v n : ℕ} {es : List ℕ}
    (hk : (ir.value v).kind = .constant es) (hn : 0 < n) (i : ℕ) :
    ir.read e n v i = (I (ir.valueField v)).decode (es.getD i 0) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [read, hk]

/-- **A message reads its late value plus its pad** at any positive level. -/
theorem read_of_message (e : ir.Env I) {v u n : ℕ} (hk : (ir.value v).kind = .message u)
    (hn : 0 < n) (i : ℕ) : ir.read e n v i = castElt (e.late u i + e.asg.pad u i) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp only [read, hk]

/-! ## The powers -/

/-- **The powers map's entries**: entry `c · nch + t` is `0` for `t ≤ c` and `1` otherwise. -/
theorem powersMap_getD {nch c t : ℕ} (hc : c < nch) (ht : t < nch) :
    (powersMap nch).getD (c * nch + t) 0 = if t ≤ c then 0 else 1 := by
  have hlt : c * nch + t < nch * nch := by nlinarith
  rw [List.getD_eq_getElem?_getD, powersMap, List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht,
    Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt ht, Nat.zero_add]

/-- **A product of `β` at the first `c + 1` of `n` positions and `1` elsewhere** is `β^(c+1)`. -/
theorem prod_range_ite {K : Type*} [CommMonoid K] (β : K) (c : ℕ) :
    ∀ n, c < n → ((List.range n).map fun t => if t ≤ c then β else 1).prod = β ^ (c + 1)
  | 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, h => by
    rw [List.range_succ, List.map_append, List.prod_append]
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · rw [prod_range_ite β c n h]
      simp [show ¬ n ≤ c by omega]
    · have hall : ((List.range c).map fun t => if t ≤ c then β else 1) =
          List.replicate c β := by
        rw [List.eq_replicate_iff]
        refine ⟨by simp, fun b hb => ?_⟩
        obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
        rw [if_pos (by simp at ht; omega)]
      simp [hall, List.prod_replicate, pow_succ]

/-- **The powers value reads the key's powers** (`powersB`) at every level from `2` on:
coordinate `c < nch` is `β^(c+1)`, `β` coordinate `0` of the key, read in the powers' field. -/
theorem read_powers (hL : I.Lawful ir primeNodes) (e : ir.Env I) {r key nch f : ℕ}
    (hf : f < ir.fields.length) (h2 : 1 < ir.charOf f) (h : ir.powersB r key nch f = true) {n : ℕ}
    (hn : 0 < n) {c : ℕ} (hc : c < nch) :
    (castElt (ir.read e (n + 1) r c) : (I f).K) = (castElt (e.chal key 0) : (I f).K) ^ (c + 1) := by
  unfold powersB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hr, hrf⟩, hkf⟩, h⟩ := h
  split at h
  · rename_i m idx kv one hk
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨rfl, hidx⟩, hkv⟩, hsz⟩, hkvf⟩, hkey⟩, hone⟩ := h
    replace hidx := (IndexMap.toList_of_sameB _ _ _ hidx).trans (toList_powersRuns _)
    -- the key's value
    have hkv' : ∀ i, (castElt (ir.read e n kv i) : (I f).K) = castElt (e.chal key i) := by
      intro i
      revert hkey
      cases hkk : (ir.value kv).kind <;> simp
      rename_i c'
      rintro rfl
      rw [read_of_challenge e hkk hn, castElt_castElt_eq, if_pos (hkf.trans hkvf.symm)]
    -- the constant one
    have hone' : (castElt (ir.read e n one 0) : (I f).K) = 1 := by
      unfold constAll at hone
      split at hone
      · rename_i es hk1
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, beq_iff_eq] at hone
        obtain ⟨⟨hn1, hall⟩, hof⟩ := hone
        have h0 : es.getD 0 0 = 1 := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
          exact hall _ (List.getElem_mem _)
        rw [read_of_constant e hk1 hn, h0, hL.decode_natCast _ (hof ▸ hf) 1 (hof ▸ h2)]
        exact_mod_cast castElt_natCast hof 1
      · cases hone
    have hlenkv : Expr.len ir (ir.refLen ir.exprs.length) (.leaf kv) = 1 := by
      simp [Expr.len, hsz]
    have hrd : ir.read e (n + 1) r c = ir.evalE (ir.read e n) (ir.valueField r)
        (.prod m (.reindex idx (.concat (.leaf kv) (.leaf one)))) c := by
      simp only [read, hk]
    rw [hrd, castElt_evalE hrf]
    simp only [evalE, Expr.eval]
    rw [← prod_range_ite _ c m hc]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [List.mem_range] at ht
    rw [IndexMap.entry_eq_getD_toList, hidx, powersMap_getD hc ht]
    split_ifs with htc h0 h1
    · exact hkv' 0
    · rw [hlenkv] at h0
      omega
    · rw [hlenkv] at h1
      omega
    · rw [hlenkv]
      exact hone'
  · cases h

/-- **The powers value reads the key's powers** (`powersB`): coordinate `c < nch` is `β^(c+1)`, `β`
coordinate `0` of the key, read in the powers' field. -/
theorem reader_powers (hL : I.Lawful ir primeNodes) (e : ir.Env I) {r key nch f : ℕ}
    (hf : f < ir.fields.length) (h2 : 1 < ir.charOf f) (h : ir.powersB r key nch f = true) {c : ℕ}
    (hc : c < nch) :
    (castElt (ir.reader e r c) : (I f).K) = (castElt (e.chal key 0) : (I f).K) ^ (c + 1) := by
  have hr : r < ir.values.length := by
    unfold powersB at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.1.1.1
  exact read_powers hL e hf h2 h (n := ir.values.length) (by omega) hc

/-! ## Casts between equal field identifiers -/

theorem toNat_castElt_of_eq {a b : ℕ} (h : a = b) (x : (I a).K) :
    (I b).toNat (castElt x) = (I a).toNat x := by
  subst h
  simp

theorem castElt_inj_of_eq {a b : ℕ} (h : a = b) {x y : (I a).K} :
    (castElt x : (I b).K) = castElt y ↔ x = y := by
  subst h
  simp

theorem castElt_one_of_eq {a b : ℕ} (h : a = b) : (castElt (1 : (I a).K) : (I b).K) = 1 := by
  subst h
  simp

/-! ## Bits from intervals -/

/-- **An expression read within `[0, 1]`** at the reader `rd` in domain `d`: every coordinate's
integer reading lies in `[0, 1]` and casts to its value (a derivation's `ivl d e 0 1` fact). -/
def Bits01 (ir : RealizedProgram) (rd : ir.Valuation I) (d : ℕ) (e : Expr) : Prop :=
  ∀ i < ir.exprLen e, 0 ≤ ir.evalIntWith rd d e i ∧ ir.evalIntWith rd d e i ≤ 1 ∧
    ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i

/-- **An expression read within `[0, 1]` reads bits.** -/
theorem Bits01.bit {rd : ir.Valuation I} {d : ℕ} {e : Expr} (h : Bits01 ir rd d e) {i : ℕ}
    (hi : i < ir.exprLen e) : ir.evalWith rd d e i = 0 ∨ ir.evalWith rd d e i = 1 := by
  obtain ⟨h0, h1, hc⟩ := h i hi
  rw [← hc]
  rcases (by omega : ir.evalIntWith rd d e i = 0 ∨ ir.evalIntWith rd d e i = 1) with h | h <;>
    simp [h]

/-- **An expression read within `[0, 1]` reads its indicator on the integers.** -/
theorem Bits01.ite {rd : ir.Valuation I} {d : ℕ} {e : Expr} (h : Bits01 ir rd d e) {i : ℕ}
    (hi : i < ir.exprLen e) :
    ir.evalIntWith rd d e i = if ir.evalWith rd d e i = 1 then 1 else 0 := by
  obtain ⟨h0, h1, hc⟩ := h i hi
  rcases (by omega : ir.evalIntWith rd d e i = 0 ∨ ir.evalIntWith rd d e i = 1) with h | h
  · rw [h, if_neg]
    rw [← hc, h]
    simp
  · rw [h, if_pos]
    rw [← hc, h]
    simp

/-- **A value read within `[0, 1]` reads its indicator on the integers.** -/
theorem Bits01.leaf_ite {rd : ir.Valuation I} {d b : ℕ} (h : Bits01 ir rd d (.leaf b)) {i : ℕ}
    (hi : i < (ir.value b).size) :
    ir.intOf rd b i = if (castElt (rd b i) : (I (ir.domainField d)).K) = 1 then 1 else 0 :=
  h.ite hi

/-- **An expression with an interval within `[0, 1]` reads bits** (`exprIvl`, at `p > 2`), under the
leaf facts. -/
theorem bits_of_ivl (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)} (hK : ir.ShiftFacts rd sr)
    (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ} (hd : d < ir.domains.length)
    (h2 : 2 < ir.charOf (ir.domainField d)) {e : Expr} (he : ir.ExprOk (ir.domainField d) e)
    (hw : IvlWithin (ir.exprIvl L (ir.domainField d) e) 0 1) {i : ℕ}
    (hi : i < ir.exprLen e) : ir.evalWith rd d e i = 0 ∨ ir.evalWith rd d e i = 1 := by
  obtain ⟨⟨h0, h1⟩, hc⟩ := exprIvl_within hwf hI hL hF hK hLok hd h2 he hw hi
  rw [← hc]
  rcases (by omega : ir.evalIntWith rd d e i = 0 ∨ ir.evalIntWith rd d e i = 1) with h | h <;>
    simp [h]

/-- **An expression with an interval within `[0, 1]` is read within `[0, 1]`** (`Bits01`), under
the leaf facts. -/
theorem bits01_of_ivl (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)} (hK : ir.ShiftFacts rd sr)
    (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ} (hd : d < ir.domains.length)
    (h2 : 2 < ir.charOf (ir.domainField d)) {e : Expr} (he : ir.ExprOk (ir.domainField d) e)
    (hw : IvlWithin (ir.exprIvl L (ir.domainField d) e) 0 1) : Bits01 ir rd d e := fun i hi => by
  obtain ⟨⟨h0, h1⟩, hc⟩ := exprIvl_within hwf hI hL hF hK hLok hd h2 he hw hi
  exact ⟨h0, h1, hc⟩

/-! ## Shared expressions on the integers -/

/-- **A shared expression's integer value does not depend on the levels** past its index, when the
shared expressions read only entries of smaller index. -/
theorem refInt_stable (ho : ir.RefsOrdered) (rd : ir.Valuation I) (f : ℕ) :
    ∀ k, k < ir.exprs.length → ∀ n m, k < n → k < m → ir.refInt rd f n k = ir.refInt rd f m k
  | k, hk, n + 1, m + 1, hn, hm => by
    funext i
    simp only [refInt]
    exact congrFun (Expr.evalInt_congr ir (ir.expr k) (fun _ _ => ⟨rfl, rfl⟩) fun k' hk' =>
      have := ho k hk k' hk'
      refInt_stable ho rd f k' (by omega) n m (by omega) (by omega)) i

/-- **A reference reads its shared expression on the integers.** -/
theorem evalInt_ref (ho : ir.RefsOrdered) (rd : ir.Valuation I) (f : ℕ) {k : ℕ}
    (hk : k < ir.exprs.length) :
    Expr.evalInt ir f rd (ir.intOf rd) (ir.refInt rd f ir.exprs.length) (ir.refLen ir.exprs.length)
        (.ref k) =
      Expr.evalInt ir f rd (ir.intOf rd) (ir.refInt rd f ir.exprs.length) (ir.refLen ir.exprs.length)
        (ir.expr k) := by
  funext i
  simp only [Expr.evalInt]
  rw [refInt_stable ho rd _ k hk _ (k + 1) hk (by omega)]
  simp only [refInt]
  exact congrFun (Expr.evalInt_congr ir (ir.expr k) (fun _ _ => ⟨rfl, rfl⟩) fun k' hk' =>
    have := ho k hk k' hk'
    refInt_stable ho rd _ k' (by omega) _ _ (by omega) (by omega)) i

/-- **A reference reads its shared expression on the integers.** -/
theorem evalIntWith_ref (ho : ir.RefsOrdered) (rd : ir.Valuation I) (d : ℕ) {k : ℕ}
    (hk : k < ir.exprs.length) : ir.evalIntWith rd d (.ref k) = ir.evalIntWith rd d (ir.expr k) :=
  evalInt_ref ho rd _ hk

/-! ## Operands padded by zeros -/

/-- **A coordinate below the length reads unpadded.** -/
theorem evalPad_of_lt {rd : ir.Valuation I} {d : ℕ} {e : Expr} {i : ℕ} (h : i < ir.exprLen e) :
    ir.evalPad rd d e i = ir.evalWith rd d e i := if_pos h

/-- **A coordinate past the length reads `0` padded.** -/
theorem evalPad_of_le {rd : ir.Valuation I} {d : ℕ} {e : Expr} {i : ℕ} (h : ir.exprLen e ≤ i) :
    ir.evalPad rd d e i = 0 := if_neg (by omega)

/-- **`z'` reads `z` followed by zeros to `N` coordinates** at the reader `rd` in domain `d` (a fact
about values: the realization of a MAC reads its operand of at most `chunks · width` coordinates
through `z'`): `z'` has `N` coordinates and `z` at most `N`; padded by zeros (`evalPad`), they read
alike; on the integers, coordinate `i < N` of `z'` is `z`'s below `z`'s length and `0` past it. -/
def PadsTo (rd : ir.Valuation I) (d : ℕ) (z' z : Expr) (N : ℕ) : Prop :=
  ir.exprLen z' = N ∧ ir.exprLen z ≤ N ∧ (∀ i, ir.evalPad rd d z' i = ir.evalPad rd d z i) ∧
    ∀ i < N, ir.evalIntWith rd d z' i = if i < ir.exprLen z then ir.evalIntWith rd d z i else 0

/-- **The value a view source reads**: `g b j` at coordinate `j` of `b`, `z` at a zero. -/
def srcVal {α : Type*} (g : Expr → ℕ → α) (z : α) : Option (Expr × ℕ) → α
  | some (b, j) => g b j
  | none => z

/-- **A view reads where `viewSrc` says**, in field `f`, at a reader reading constants as
constants: coordinate `j` of `b` (on the field and on the integers), or `0`. -/
theorem viewSrc_sound (ho : ir.RefsOrdered) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {f : ℕ} (hf : f < ir.fields.length) (hc0 : 0 < ir.charOf f) :
    ∀ n e i, ir.evalE rd f e i = srcVal (ir.evalE rd f) 0 (ir.viewSrc f n e i) ∧
      Expr.evalInt ir f rd (ir.intOf rd) (ir.refInt rd f ir.exprs.length)
          (ir.refLen ir.exprs.length) e i =
        srcVal (Expr.evalInt ir f rd (ir.intOf rd) (ir.refInt rd f ir.exprs.length)
          (ir.refLen ir.exprs.length)) 0 (ir.viewSrc f n e i)
  | 0, e, i => ⟨rfl, rfl⟩
  | n + 1, e, i => by
    cases e with
    | reindex idx e' =>
      simp only [viewSrc]
      exact viewSrc_sound ho hI hL hK hf hc0 n e' _
    | concat a b =>
      simp only [viewSrc]
      split_ifs with hia
      · have := viewSrc_sound ho hI hL hK hf hc0 n a i
        simp only [evalE, Expr.eval, Expr.evalInt] at this ⊢
        rw [if_pos (show i < Expr.len ir (ir.refLen ir.exprs.length) a from hia),
          if_pos (show i < Expr.len ir (ir.refLen ir.exprs.length) a from hia)]
        exact this
      · have := viewSrc_sound ho hI hL hK hf hc0 n b (i - ir.exprLen a)
        simp only [evalE, Expr.eval, Expr.evalInt] at this ⊢
        rw [if_neg (show ¬ i < Expr.len ir (ir.refLen ir.exprs.length) a from hia),
          if_neg (show ¬ i < Expr.len ir (ir.refLen ir.exprs.length) a from hia)]
        exact this
    | leaf c =>
      simp only [viewSrc]
      split
      · rename_i es hk
        split_ifs with hc
        · obtain ⟨hes, hvf, -⟩ := hc
          simp only [srcVal]
          refine ⟨?_, ?_⟩
          · simp only [evalE, Expr.eval]
            rw [hK c es hk i, hes, hL.decode_natCast _ (hvf ▸ hf) 0 (by
              simp only [charOf] at hc0; rw [hvf]; exact hc0)]
            simp
          · simp only [Expr.evalInt, intOf, hk, hes, FieldInterp.centered]
            have hch := hI.characteristic _ (hvf ▸ hf)
            simp only [charOf] at hc0
            rw [if_pos (by rw [hch, hvf]; omega)]
            rfl
        · exact ⟨rfl, rfl⟩
      · exact ⟨rfl, rfl⟩
    | ref k =>
      simp only [viewSrc]
      split_ifs with hk
      · have := viewSrc_sound ho hI hL hK hf hc0 n (ir.expr k) i
        rw [congrFun (evalE_ref ho rd f hk) i, congrFun (evalInt_ref ho rd f hk) i]
        exact this
      · exact ⟨rfl, rfl⟩
    | _ => exact ⟨rfl, rfl⟩

/-- **Agreeing view sources read alike** (`srcEqB`). -/
theorem srcEqB_eval {α : Type*} {o o' : Option (Expr × ℕ)} (h : srcEqB o o' = true)
    (g : Expr → ℕ → α) (z : α) : srcVal g z o = srcVal g z o' := by
  rcases o with _ | ⟨a, i⟩ <;> rcases o' with _ | ⟨b, j⟩ <;> simp only [srcEqB, Bool.and_eq_true,
    beq_iff_eq, Bool.false_eq_true] at h
  · rfl
  · obtain ⟨hab, rfl⟩ := h
    rw [Expr.eq_of_beq hab]

/-- **`zeroPadWalkB` is sound**: `z'` reads `z` followed by zeros (`PadsTo`), at a reader reading
constants as constants. -/
theorem padsTo_of_zeroPadWalkB (ho : ir.RefsOrdered) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {d N : ℕ} {z' z : Expr} (hdF : ir.domainField d < ir.fields.length)
    (hc0 : 0 < ir.charOf (ir.domainField d)) (h : ir.zeroPadWalkB (ir.domainField d) N z' z = true) :
    ir.PadsTo rd d z' z N := by
  unfold zeroPadWalkB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨hl', hl⟩, hall⟩ := h
  have hv := viewSrc_sound ho hI hL hK hdF hc0 padFuel
  refine ⟨hl', hl, fun i => ?_, fun i hi => ?_⟩
  · unfold evalPad
    by_cases hiN : i < N
    · rw [if_pos (hl' ▸ hiN)]
      have he := srcEqB_eval (hall i hiN) (ir.evalE rd (ir.domainField d)) 0
      simp only [evalWith]
      rw [(hv z' i).1, he]
      by_cases hin : i < ir.exprLen z
      · rw [if_pos hin, if_pos hin, (hv z i).1]
      · rw [if_neg hin, if_neg hin]
        rfl
    · rw [if_neg (by omega), if_neg (by omega)]
  · have he := srcEqB_eval (hall i hi) (Expr.evalInt ir (ir.domainField d) rd
      (ir.intOf rd) (ir.refInt rd (ir.domainField d) ir.exprs.length) (ir.refLen ir.exprs.length)) 0
    simp only [evalIntWith]
    rw [(hv z' i).2, he]
    by_cases hin : i < ir.exprLen z
    · rw [if_pos hin, if_pos hin, (hv z i).2]
    · rw [if_neg hin, if_neg hin]
      rfl

/-- **The lengths of a padding** (`zeroPadB`): `z'` has `N` coordinates, `z` at most `N`. -/
theorem zeroPadB_len {f N : ℕ} {z' z : Expr} (h : ir.zeroPadB f N z' z = true) :
    ir.exprLen z' = N ∧ ir.exprLen z ≤ N := by
  unfold zeroPadB zeroPadWalkB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hb, hl⟩ | h
  · obtain rfl := Expr.eq_of_beq hb
    exact ⟨hl, hl.le⟩
  · exact h.1

/-- **An operand of `N` coordinates is its own padding** (`zeroPadB`). -/
theorem zeroPadB_self {f N : ℕ} {z : Expr} (h : ir.exprLen z = N) : ir.zeroPadB f N z z = true := by
  unfold zeroPadB
  simp [Expr.beq_self, h]

/-- **`zeroPadB` is sound**: `z'` reads `z` followed by zeros (`PadsTo`), at a reader reading
constants as constants. -/
theorem padsTo_of_zeroPadB (ho : ir.RefsOrdered) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I}
    (hK : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      rd v i = (I (ir.valueField v)).decode (es.getD i 0))
    {d N : ℕ} {z' z : Expr} (hdF : ir.domainField d < ir.fields.length)
    (hc0 : 0 < ir.charOf (ir.domainField d)) (h : ir.zeroPadB (ir.domainField d) N z' z = true) :
    ir.PadsTo rd d z' z N := by
  unfold zeroPadB at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  rcases h with ⟨hb, hl⟩ | h
  · obtain rfl := Expr.eq_of_beq hb
    refine ⟨hl, hl.le, fun _ => rfl, fun i hi => ?_⟩
    rw [if_pos (hl ▸ hi)]
  · exact padsTo_of_zeroPadWalkB ho hI hL hK hdF hc0 h

/-- **An operand read padded by zeros is read within `[0, 1]`** where the operand is (`PadsTo`). -/
theorem bits01_of_padsTo {rd : ir.Valuation I} {d N : ℕ} {z' z : Expr}
    (h : ir.PadsTo rd d z' z N) (hz : Bits01 ir rd d z) : Bits01 ir rd d z' := by
  obtain ⟨hl', -, hv, hint⟩ := h
  intro i hi
  have hiN : i < N := hl' ▸ hi
  have hev := hv i
  rw [evalPad_of_lt hi] at hev
  rw [hev, hint i hiN]
  by_cases hin : i < ir.exprLen z
  · rw [if_pos hin, evalPad_of_lt hin]
    exact hz i hin
  · rw [if_neg hin, evalPad_of_le (Nat.le_of_not_lt hin)]
    simp

/-- **The chunks of an operand padded by zeros are the operand's** (`PadsTo`). -/
theorem macChunkA_of_padsTo {rd : ir.Valuation I} {d N : ℕ} {z' z : Expr}
    (h : ir.PadsTo rd d z' z N) (f w c : ℕ) : ir.macChunkA rd f d z' w c = ir.macChunkA rd f d z w c := by
  simp only [macChunkA, h.2.2.1]

/-- **The H chunks of an operand padded by zeros are the operand's** (`PadsTo`). -/
theorem macChunkH_of_padsTo {rd : ir.Valuation I} {d N : ℕ} {z' z : Expr}
    (h : ir.PadsTo rd d z' z N) (f w c : ℕ) : ir.macChunkH rd f d z' w c = ir.macChunkH rd f d z w c := by
  simp only [macChunkH, h.2.2.1]

/-- **The H half at an operand padded by zeros is the operand's** (`PadsTo`). -/
theorem macHHoldsAt_of_padsTo {rd : ir.Valuation I} {d N : ℕ} {z' z : Expr}
    (h : ir.PadsTo rd d z' z N) {real : MacRealization} {β : (I real.macField).K} :
    ir.MacHHoldsAt rd d z' real β ↔ ir.MacHHoldsAt rd d z real β := by
  simp only [MacHHoldsAt, macChunkH_of_padsTo h]

/-- **The target's bits read the bits of the tag's message** (`targetBitsB`), under the model's
opaque function: coordinate `m` is the cast of bit `m` of the message's integer reading. -/
theorem reader_targetBits (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes) (e : ir.Env I)
    {tb dy tag : ℕ} (h : ir.targetBitsB tb dy tag = true) (hd : dy < ir.domains.length)
    (h2 : 1 < ir.charOf (ir.domainField dy))
    (htf : ∀ nm args, (ir.value tb).kind = .pub (.opaque nm args) → ∀ xs i,
      I.opaqueFn nm xs i = if ((xs.headD 0) 0).testBit i then 1 else 0) (m : ℕ) :
    ∃ bt : ℕ, bt < 2 ∧ ir.reader e tb m = (bt : (I (ir.valueField tb)).K) ∧
      (bt = 1 ↔ ((I (ir.valueField tag)).toNat (e.late tag 0 + e.asg.pad tag 0)).testBit m) := by
  unfold targetBitsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨htbl, htf'⟩, -⟩, h⟩ := h
  split at h
  · rename_i nm msg hk
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hml, hmf⟩, h⟩ := h
    split at h
    · rename_i u hmk
      simp only [beq_iff_eq] at h
      subst h
      have hf := domainField_lt hwf hd
      have hlen : 0 < ir.values.length := by omega
      refine ⟨if ((I (ir.valueField u)).toNat (e.late u 0 + e.asg.pad u 0)).testBit m
        then 1 else 0, by split_ifs <;> omega, ?_, by split_ifs <;> simp_all⟩
      rw [show ir.reader e tb m = _ from by simp only [reader, fuel, read, hk]; rfl]
      simp only [List.cons_ne_nil, ↓reduceIte]
      rw [htf nm [msg] hk, List.map_cons, List.headD_cons, read_of_message e hmk hlen,
        toNat_castElt_of_eq hmf.symm]
      rw [htf']
      split_ifs
      · exact hL.decode_natCast _ hf 1 (by simp only [charOf] at h2; omega)
      · exact hL.decode_natCast _ hf 0 (by simp only [charOf] at h2; omega)
    · cases h
  · cases h

/-- **An element reading below `2` is `0` or `1`** in a field with a basis whose coordinates are
the bits of the integer reading (`MacFieldOk`) and whose first element is `1`: its bits above `0`
vanish, so it is `0` or the first basis element. -/
theorem eq_zero_or_one_of_toNat_lt_two {f w : ℕ} (hw : 0 < w) (B : MACBasis w (I f).K)
    (hunp : ∀ z j, B.unpack z j = ((I f).toNat z).testBit j) (he : B.e ⟨0, hw⟩ = 1)
    {z : (I f).K} (hz : (I f).toNat z < 2) : z = 0 ∨ z = 1 := by
  rw [← B.pack_unpack z, Finset.sum_eq_single (⟨0, hw⟩ : Fin w)]
  · by_cases h : B.unpack z ⟨0, hw⟩
    · right
      rw [if_pos h, he]
    · left
      rw [if_neg h]
  · intro j _ hj
    have hj0 : 0 < (j : ℕ) := Nat.pos_of_ne_zero fun h => hj (Fin.ext h)
    rw [if_neg]
    rw [hunp, Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz
      (by simpa using Nat.pow_le_pow_right (by norm_num : 0 < 2) hj0))]
    exact Bool.false_ne_true
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- **Equal chunks of bits give the cross-field `equal`**: where the chunks of the H operand (in the
MAC field `dx`'s, of characteristic `2`, with a basis whose coordinates are the bits of the integer
reading and whose first element is `1`) and of the A operand's bits read into it agree, and the A
operand reads bits, the cross-field `equal` holds in the compiler's contract: the A operand's
readings are bits, and where every coordinate of the H operand reads below `2` (so is a bit,
`eq_zero_or_one_of_toNat_lt_two`), the operands' readings agree. -/
theorem crossHolds_of_chunks (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {dx dy : ℕ}
    {x y : Expr} {k : CrossKind} {real : MacRealization}
    (hfx : ir.domainField dx = real.macField) (hmf : real.macField < ir.fields.length)
    (hdF : ir.domainField dy < ir.fields.length) (hch2 : ir.charOf real.macField = 2)
    (h2 : 2 < ir.charOf (ir.domainField dy)) (hw1 : k.width = 1) (hw0 : 0 < real.width)
    (hlenX : ir.exprLen x ≤ real.chunks * real.width)
    (hlenY : ir.exprLen y = ir.exprLen x)
    (hyb : ∀ i < ir.exprLen y, ir.evalWith rd dy y i = 0 ∨ ir.evalWith rd dy y i = 1)
    (B : MACBasis real.width (I real.macField).K)
    (hunp : ∀ z j, B.unpack z j = ((I real.macField).toNat z).testBit j)
    (he : B.e ⟨0, hw0⟩ = 1) (hch : ∀ c : Fin real.chunks,
      MAC.pack B (fun i => castElt (ir.evalPad rd dx x (c * real.width + i))) =
        MAC.pack B fun j => if ir.evalPad rd dy y (c * real.width + j) = 1 then 1 else 0) :
    ir.HoldsWith rd (.cross dx x dy y k real) := by
  have hdxf : ir.domainField dx < ir.fields.length := hfx ▸ hmf
  have hcx : 1 < (ir.field (ir.domainField dx)).characteristic := by
    rw [hfx]
    simp only [charOf] at hch2
    omega
  have hcy : 1 < (ir.field (ir.domainField dy)).characteristic := by
    simp only [charOf] at h2
    omega
  have hone1 : ∀ {a : ℕ}, a < ir.fields.length → 1 < (ir.field a).characteristic →
      (I a).toNat 1 = 1 := fun ha h1 => by simpa using hL.toNat_natCast _ ha 1 h1
  have hzero0 : ∀ {a : ℕ}, a < ir.fields.length → 0 < (ir.field a).characteristic →
      (I a).toNat 0 = 0 := fun ha h0 => by simpa using hL.toNat_natCast _ ha 0 h0
  refine ⟨fun i hi => ?_, fun hx i hi => ?_⟩
  · rw [hw1, pow_one]
    rcases hyb i (by rw [hlenY]; exact hi) with hy0 | hy1
    · rw [hy0, hzero0 hdF (by omega)]
      norm_num
    · rw [hy1, hone1 hdF hcy]
      norm_num
  -- the H operand reads bits
  have hxb : ∀ i < ir.exprLen x, ir.evalWith rd dx x i = 0 ∨ ir.evalWith rd dx x i = 1 := by
    intro i hi
    have h := hx i hi
    rw [hw1, pow_one, ← toNat_castElt_of_eq hfx] at h
    rcases eq_zero_or_one_of_toNat_lt_two hw0 B hunp he h with h0 | h1
    · exact .inl ((castElt_inj_of_eq hfx).1 (h0.trans castElt_zero.symm))
    · exact .inr ((castElt_inj_of_eq hfx).1 (h1.trans (castElt_one_of_eq hfx).symm))
  have hiN : i < real.chunks * real.width := lt_of_lt_of_le hi hlenX
  have hc : i / real.width < real.chunks := by
    rw [Nat.div_lt_iff_lt_mul hw0]
    exact hiN
  have hij : i / real.width * real.width + i % real.width = i := Nat.div_add_mod' i real.width
  have hxb' : ∀ j' : Fin real.width,
      (castElt (ir.evalPad rd dx x ((⟨_, hc⟩ : Fin real.chunks) * real.width + j')) :
          (I real.macField).K) = 0 ∨
        (castElt (ir.evalPad rd dx x ((⟨_, hc⟩ : Fin real.chunks) * real.width + j')) :
          (I real.macField).K) = 1 := by
    intro j'
    by_cases hlt : i / real.width * real.width + j' < ir.exprLen x
    · rw [evalPad_of_lt hlt]
      rcases hxb _ hlt with h0 | h1
      · left
        rw [h0, castElt_zero]
      · right
        rw [h1, castElt_one_of_eq hfx]
    · left
      rw [evalPad_of_le (Nat.le_of_not_lt hlt), castElt_zero]
  have hpk := MAC.pack_injective B hxb' (fun j' => by split_ifs <;> simp) (hch ⟨_, hc⟩)
  have hcj := congrFun hpk ⟨i % real.width, Nat.mod_lt _ hw0⟩
  simp only [hij] at hcj
  rw [evalPad_of_lt hi, evalPad_of_lt (show i < ir.exprLen y by rw [hlenY]; exact hi)] at hcj
  have hyb' := hyb i (by rw [hlenY]; exact hi)
  have hxbi := hxb i hi
  rcases hyb' with hy0 | hy1
  · have hx0 : ir.evalWith rd dx x i = 0 := by
      rw [hy0, if_neg zero_ne_one] at hcj
      rcases hxbi with h | h
      · exact h
      · rw [h, castElt_one_of_eq hfx] at hcj
        exact absurd hcj one_ne_zero
    rw [hx0, hy0, hzero0 hdxf (by omega), hzero0 hdF (by omega)]
  · have hx1 : ir.evalWith rd dx x i = 1 := by
      rw [hy1, if_pos rfl] at hcj
      rcases hxbi with h | h
      · rw [h, castElt_zero] at hcj
        exact absurd hcj.symm one_ne_zero
      · exact h
    rw [hx1, hy1, hone1 hdxf hcx, hone1 hdF hcy]

/-! ## The H predicate -/

/-- **A sum of groups along the last axis**: output coordinate `j` of `sum w` is the sum of the
operand's coordinates `j w, …, j w + w − 1`. -/
theorem NamedOp.apply_sum (ir : RealizedProgram) {f : ℕ} (leaf : ir.Valuation I) (w : ℕ)
    (x : ℕ → (I f).K) (j : ℕ) :
    NamedOp.apply ir f leaf (.sum w) x j = ∑ t : Fin w, x (j * w + t) := by
  simp [NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols, Ops.sum, Nat.mod_one]

/-- **The generator powers' index map**: entry `c · w + t` is `t`. -/
theorem genPowsMap_getD {nch w c t : ℕ} (hc : c < nch) (ht : t < w) :
    (genPowsMap nch w).getD (c * w + t) 0 = t := by
  have hlt : c * w + t < nch * w := by nlinarith
  rw [List.getD_eq_getElem?_getD, genPowsMap, List.getElem?_map, List.getElem?_range hlt]
  simp only [Option.map_some, Option.getD_some]
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ht]

/-- **A constant read in an equal field identifier** is its decoding there. -/
theorem castElt_decode_of_eq {a b : ℕ} (h : a = b) (n : ℕ) :
    (castElt ((I a).decode n) : (I b).K) = (I b).decode n := by
  subst h
  simp

/-- **The generator powers read their decodings** (`genPowsB`): coordinate `t < w` of `g`, read in
field `f`, is the decoding of `2^t`. -/
theorem reader_genPows (e : ir.Env I) {g w f : ℕ} (h : ir.genPowsB g w f = true) {t : ℕ}
    (ht : t < w) : (castElt (ir.reader e g t) : (I f).K) = (I f).decode (2 ^ t) := by
  unfold genPowsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨-, hgf⟩, h⟩ := h
  split at h
  · rename_i es hk
    simp only [beq_iff_eq] at h
    rw [reader_of_constant e hk, castElt_decode_of_eq hgf, h, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_range ht]
    rfl
  · cases h

/-- **The generator's powers' view reads the powers** (`genViewB`): coordinate `c w + t`, `c < nch`,
`t < w`, is `2^t` decoded. -/
theorem evalE_genView (e : ir.Env I) {nch w f : ℕ} {G : Expr} (h : ir.genViewB nch w f G = true)
    {c t : ℕ} (hc : c < nch) (ht : t < w) :
    ir.evalE (ir.reader e) f G (c * w + t) = (I f).decode (2 ^ t) := by
  unfold genViewB at h
  split at h
  · rename_i idx g
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    change castElt (ir.reader e g (idx.entry (c * w + t))) = _
    rw [IndexMap.entry_eq_getD_toList, h.1, genPowsMap_getD hc ht, reader_genPows e h.2 ht]
  · rename_i g
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨rfl, hg⟩ := h
    have hc0 : c = 0 := by omega
    subst hc0
    change castElt (ir.reader e g (0 * w + t)) = _
    rw [zero_mul, zero_add, reader_genPows e hg ht]
  · cases h

/-- **The H predicate states the H half** (`macHPredB`): under the leaf facts (every field `equal`
holds), the predicate `U + Σ_c r_c · Σ_i X_H[c w + i] · g_i = 0` gives, in characteristic `2`, with
`r_c = β^(c+1)` (`reader_powers`) and the constants `g_i` decoding to the generator's powers
(`hpow2`, the model's `MacFieldOk.decodePow`), the tag `U = Σ_c β^(c+1) · chunk_c(X_H)`
(`MacHHoldsAt`). -/
theorem macHHolds_of_pred (ho : ir.RefsOrdered) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes) (e : ir.Env I)
    {pid dx : ℕ} {x : Expr} {real : MacRealization} {p : ℕ}
    (hHp : ir.HoldsWith (ir.reader e) (ir.predicate p).body)
    (hp : ir.macHPredB pid dx x real p = true) (hfx : ir.domainField dx = real.macField)
    (hmf : real.macField < ir.fields.length) (htag : ir.macTagB real = true)
    (hpow2 : ∀ j < real.width, (I real.macField).decode (2 ^ j) = (I real.macField).decode 2 ^ j) :
    ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0)) := by
  unfold macHPredB at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨⟨⟨hpl, -⟩, hch2⟩, hp⟩ := hp
  split at hp
  · rename_i d u n r w x' G z tgt hb
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    obtain ⟨⟨⟨⟨⟨⟨⟨hd, rfl⟩, rfl⟩, rfl⟩, hx⟩, hpow⟩, hgv⟩, hz⟩ := hp
    rw [hd] at hb
    have hdxF : ir.domainField dx < ir.fields.length := hfx ▸ hmf
    have hcx0 : 0 < ir.charOf (ir.domainField dx) := by rw [hfx, hch2]; omega
    have hKe : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
        ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) :=
      fun _ _ hk i => reader_of_constant e hk i
    have hpx := padsTo_of_zeroPadB ho hI hL hKe hdxF hcx0 hx
    have hlx' := hpx.1
    refine (macHHoldsAt_of_padsTo hpx).1 ?_
    have hH := hHp
    rw [hb] at hH
    unfold macTagB at htag
    simp only [Bool.and_eq_true, decide_eq_true_eq] at htag
    obtain ⟨⟨⟨-, -⟩, htsz⟩, -⟩ := htag
    have h0 := hH 0 (by simpa [exprLen, Expr.len] using htsz)
    have h1 := congrArg (fun v => (castElt v : (I real.macField).K)) h0
    simp only [evalWith, castElt_evalE hfx] at h1
    have : CharP (I real.macField).K 2 := by
      have := charP_field hI hmf
      simp only [charOf] at hch2
      rwa [hch2] at this
    have hz0 : ir.evalE (ir.reader e) real.macField (.leaf z) 0 = 0 := by
      have := evalE_leaf_constAll_of hL (fun _ _ hk i => reader_of_constant e hk i) hz hmf
        (by rw [hch2]; omega) Nat.zero_lt_one
      simpa using this
    have hap : ∀ (op : NamedOp) (E : Expr) (i : ℕ), ir.evalE (ir.reader e) real.macField (.apply op E) i =
        NamedOp.apply ir real.macField (ir.reader e) op (ir.evalE (ir.reader e) real.macField E) i :=
      fun _ _ _ => rfl
    have hmul : ∀ (E E' : Expr) (i : ℕ), ir.evalE (ir.reader e) real.macField (.mul E E') i =
        ir.evalE (ir.reader e) real.macField E i * ir.evalE (ir.reader e) real.macField E' i :=
      fun _ _ _ => rfl
    have hre : ∀ (m : IndexMap) (E : Expr) (i : ℕ),
        ir.evalE (ir.reader e) real.macField (.reindex m E) i =
          ir.evalE (ir.reader e) real.macField E (m.entry i) := fun _ _ _ => rfl
    rw [hz0] at h1
    simp only [evalE_add, hap, hmul, hre, evalE_leaf, NamedOp.apply_sum, zero_mul, zero_add] at h1
    have hsum : (∑ c : Fin real.chunks, (castElt (ir.reader e r c) : (I real.macField).K) *
        ∑ t : Fin real.width, ir.evalE (ir.reader e) real.macField x' (c * real.width + t) *
          ir.evalE (ir.reader e) real.macField G (c * real.width + t)) =
        ∑ c : Fin real.chunks, (castElt (e.chal real.key 0) : (I real.macField).K) ^ ((c : ℕ) + 1) *
          ir.macChunkH (ir.reader e) real.macField dx x' real.width c := by
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [reader_powers hL e hmf (by omega) hpow c.2]
      congr 1
      simp only [macChunkH]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [evalPad_of_lt (by rw [hlx']; have := c.2; have := t.2; nlinarith)]
      rw [evalE_genView e hgv c.2 t.2, hpow2 t t.2, evalWith, castElt_evalE hfx, mul_comm]
    rw [hsum] at h1
    unfold MacHHoldsAt
    rw [eq_neg_of_add_eq_zero_left h1, CharTwo.neg_eq]
  · cases hp

/-! ## Soundness -/

/-- **An expression reading bits reads its indicator on the integers** (`exprIvl` within `[0, 1]`,
at `p > 2`): its integer reading is `1` where its value is `1`, and `0` elsewhere. -/
theorem evalIntWith_eq_ite_of_bits (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) {e : Expr}
    (he : ir.ExprOk (ir.domainField d) e)
    (hw : IvlWithin (ir.exprIvl L (ir.domainField d) e) 0 1) {i : ℕ}
    (hi : i < ir.exprLen e) :
    ir.evalIntWith rd d e i = if ir.evalWith rd d e i = 1 then 1 else 0 := by
  obtain ⟨⟨h0, h1⟩, hc⟩ := exprIvl_within hwf hI hL hF hK hLok hd h2 he hw hi
  rcases (by omega : ir.evalIntWith rd d e i = 0 ∨ ir.evalIntWith rd d e i = 1) with h | h
  · rw [h, if_neg]
    rw [← hc, h]
    simp
  · rw [h, if_pos]
    rw [← hc, h]
    simp

/-- **A value reading bits reads its indicator on the integers** (`exprIvl` of a leaf within
`[0, 1]`): its integer reading is `1` where it reads `1` in field `f`, and `0` elsewhere. -/
theorem intOf_eq_ite_of_leafIvl (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {f b : ℕ}
    (hw : IvlWithin (ir.exprIvl L f (.leaf b)) 0 1) {i : ℕ} (hi : i < (ir.value b).size) :
    ir.intOf rd b i = if (castElt (rd b i) : (I f).K) = 1 then 1 else 0 := by
  unfold exprIvl ivlOf at hw
  simp only [Expr.ivl] at hw
  revert hw
  cases hJ : L f b with
  | none => simp [IvlWithin]
  | some J =>
    intro hw
    have hm := Ivl.mem_of_within hw (hLok.sound hwf hI hL (hF.ivlFacts hK) trivial hJ i hi)
    have hc := hLok.cast hwf hI hL (hF.ivlFacts hK) trivial hJ i hi
    rcases (by omega : ir.intOf rd b i = 0 ∨ ir.intOf rd b i = 1) with h | h
    · rw [h, if_neg]
      rw [← hc, h]
      simp
    · rw [h, if_pos]
      rw [← hc, h]
      simp

variable (ir) in
/-- **A MAC check over a field gives the target** in the environment `e`: the tag's message `T` (the late value plus
its pad, read in the MAC field) is the masked MAC at the key of the chunks `ch` of the check's
operand with the field's pad `pd`, `Σ_c β^(c+1) ch_c + pd` (`MAC.sharedWitnessMAC`). -/
def MacFieldCheckAt (e : ir.Env I) (real : MacRealization) (ch : Fin real.chunks → (I real.macField).K)
    (pd : (I real.macField).K) : Prop :=
  MAC.sharedWitnessMAC ch (MAC.ladder real.chunks (castElt (e.chal real.key 0))) + pd =
    castElt (e.late real.tag 0 + e.asg.pad real.tag 0)

/-- **The checks over two fields of a MAC that give the same target bind their chunks** (`MAC.binding`): the chunks
and pads agree, or the key is a root of their binding polynomial. -/
theorem MacFieldCheckAt.binding {e : ir.Env I} {real : MacRealization}
    {ch₁ ch₂ : Fin real.chunks → (I real.macField).K} {pd₁ pd₂ : (I real.macField).K}
    (h₁ : ir.MacFieldCheckAt e real ch₁ pd₁) (h₂ : ir.MacFieldCheckAt e real ch₂ pd₂) :
    (ch₁ = ch₂ ∧ pd₁ = pd₂) ∨ (MAC.bindingEvent ch₁ ch₂ pd₁ pd₂).BadAt (castElt (e.chal real.key 0)) :=
  MAC.binding (h₁.trans h₂.symm)

/-- **The H half gives the MAC check over the hosting field** (`MacHHoldsAt`): the tag is
`Σ_c β^(c+1) chunk_c(X_H)`, so its message is the masked MAC of the H operand's chunks with the
tag's pad. -/
theorem macFieldCheckAt_of_macH {e : ir.Env I} {dx : ℕ} {x : Expr} {real : MacRealization}
    (htagk : (ir.value real.tag).kind = .late)
    (h : ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0))) :
    ir.MacFieldCheckAt e real (fun c => ir.macChunkH (ir.reader e) real.macField dx x real.width c)
      (castElt (e.asg.pad real.tag 0)) := by
  have hlate : ir.reader e real.tag 0 = e.late real.tag 0 := by rw [reader_of_late e htagk]
  simp only [MacHHoldsAt] at h
  unfold MacFieldCheckAt
  rw [castElt_add, ← hlate, h]
  simp only [MAC.sharedWitnessMAC, MAC.ladder]
  congr 1
  exact Finset.sum_congr rfl fun c _ => mul_comm _ _

/-- **A masked MAC of the readings of a check's blind and operand gives the check**
(`MACRows.maskedMAC`): in a basis whose elements are the powers of the generator, the masked MAC of
the witness of the check's blind `b` and operand `z` (domain `d`, `b` of `d`'s field) is
`Σ_c β^(c+1) chunk_c(z) + tag(b)`, the chunks and the blind's tag read at the coordinates equal to
`1` (`macChunkA`, `macBlindTag`). -/
theorem macFieldCheckAt_of_maskedMAC {e : ir.Env I} {d b : ℕ} {z : Expr} {real : MacRealization}
    {taps : Finset ℕ} (B : Conv.ConvBasis real.width taps (I real.macField).K)
    (heB : ∀ j, B.e j = (I real.macField).decode 2 ^ (j : ℕ))
    (hbf : ir.valueField b = ir.domainField d)
    (hlen : ir.exprLen z = real.chunks * real.width)
    (h : MACRows.maskedMAC B.toMACBasis (castElt (e.chal real.key 0))
        ((0, fun j => ir.evalWith (ir.reader e) d (.leaf b) j,
          fun c j => ir.evalWith (ir.reader e) d z (c * real.width + j)) :
          MACRows.Wit (I (ir.domainField d)).K real.width real.chunks) =
      castElt (e.late real.tag 0 + e.asg.pad real.tag 0)) :
    ir.MacFieldCheckAt e real (fun c => ir.macChunkA (ir.reader e) real.macField d z real.width c)
      (ir.macBlindTag (ir.reader e) real.macField b real.width) := by
  unfold MacFieldCheckAt
  rw [← h]
  simp only [MACRows.maskedMAC, MACRows.x, MACRows.pmac, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.fst_apply, LinearMap.snd_apply]
  congr 1
  · congr 1
    funext c
    simp only [macChunkA, MAC.pack]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [heB, evalPad_of_lt (by rw [hlen]; have := c.2; have := i.2; nlinarith)]
    exact mul_comm _ _
  · simp only [macBlindTag, MAC.pack]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [heB]
    refine (mul_comm _ _).trans ?_
    congr 1
    show (if ir.reader e b i = 1 then (1 : (I real.macField).K) else 0) =
      if ir.evalWith (ir.reader e) d (.leaf b) i = 1 then 1 else 0
    have hev : ir.evalWith (ir.reader e) d (.leaf b) i = castElt (ir.reader e b i) :=
      evalE_leaf _ _ _ _
    by_cases h1 : ir.reader e b i = 1
    · rw [if_pos h1, if_pos (show ir.evalWith (ir.reader e) d (.leaf b) i = 1 by
        rw [hev, h1, castElt_one_of_eq hbf])]
    · rw [if_neg h1, if_neg (show ¬ ir.evalWith (ir.reader e) d (.leaf b) i = 1 from fun h' =>
        h1 ((castElt_inj_of_eq hbf).1 ((hev.symm.trans h').trans (castElt_one_of_eq hbf).symm)))]

/-- **The model's MAC field at a MAC check over a field of odd characteristic**: the tail's powers
lie in the MAC field, which is a binary MAC field of the MAC's width (`MacFieldOk`, from
`Interp.MacModel`). -/
theorem exists_macFieldOk_of_tailAt (hM : I.MacModel ir) {pid d b t : ℕ} {z : Expr}
    {real : MacRealization} (ht : t < ir.predicates.length)
    (htB : ir.macTailAtB pid d z b real t = true) :
    ∃ taps : Finset ℕ, I.MacFieldOk real.macField real.width taps := by
  unfold macTailAtB at htB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htB
  obtain ⟨-, htB⟩ := htB
  split at htB
  · rename_i d' b' r w nch taps z' tb real' hbt
    simp only [Bool.and_eq_true, beq_iff_eq] at htB
    obtain ⟨⟨⟨⟨⟨⟨⟨-, -⟩, rfl⟩, -⟩, -⟩, hpow⟩, -⟩, -⟩ := htB
    obtain ⟨hMF, -⟩ := hM.mod t ht _ _ _ _ _ _ _ _ _ hbt
    have hrf : ir.valueField r = real.macField := by
      unfold powersB at hpow
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpow
      exact hpow.1.1.2
    exact ⟨_, hrf ▸ hMF⟩
  · cases htB

/-- **The target's bits are not a constant** (`targetBitsB`). -/
theorem targetBitsB_not_constant {tb d tag : ℕ} (h : ir.targetBitsB tb d tag = true) {es : List ℕ}
    (hes : (ir.value tb).kind = .constant es) : False := by
  unfold targetBitsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  rw [hes] at h
  cases h

/-- **The target's bits are not bound to digits** (`targetBitsB`). -/
theorem targetBitsB_not_bound {tb d tag : ℕ} (h : ir.targetBitsB tb d tag = true) {x : Expr}
    (hx : (ir.value tb).kind = .bound x) : False := by
  unfold targetBitsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  rw [hx] at h
  cases h

/-- **The target's bits lie in their domain's field** (`targetBitsB`). -/
theorem targetBitsB_field {tb d tag : ℕ} (h : ir.targetBitsB tb d tag = true) :
    ir.valueField tb = ir.domainField d := by
  unfold targetBitsB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1.2

/-- **A MAC check over a field of odd characteristic gives the target** (compiler/mac.h, the tail
`mod_2(b + macConv(r)(z), bits(T))`): where the check's tail holds over the integers, each bit of
`T` is the parity of the integer accumulator (`NamedOp.applyInt_macConv`), so `T` is the masked MAC
of the check's operand with its blind (`MACRows.maskedMAC_eq_of_unpack`). No bound on the
accumulator enters: the tail's realization (one group or grouped) proves its congruence over the
integers. `hM` is a property of the model (`Interp.MacModel`). -/
theorem macFieldCheckAt_of_odd (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I)
    {pid d b : ℕ}
    {z : Expr} {real : MacRealization} (hd : d < ir.domains.length)
    (hlen : ir.exprLen z = real.chunks * real.width)
    (hw0 : 0 < real.width) (hmf : real.macField < ir.fields.length)
    (htag : ir.macTagB real = true) (h2 : 2 < ir.charOf (ir.domainField d))
    (hbf : ir.valueField b = ir.domainField d) (hbsz : (ir.value b).size = real.width)
    (hbI : ∀ i < (ir.value b).size, ir.intOf (ir.reader e) b i =
      if (castElt (ir.reader e b i) : (I (ir.domainField d)).K) = 1 then 1 else 0)
    (hzI : ∀ i < ir.exprLen z, ir.evalIntWith (ir.reader e) d z i =
      if ir.evalWith (ir.reader e) d z i = 1 then 1 else 0)
    {t : ℕ} (ht : t < ir.predicates.length) (htB : ir.macTailAtB pid d z b real t = true)
    (hT : ir.HoldsWith (ir.reader e) (ir.predicate t).body) :
    ir.MacFieldCheckAt e real (fun c => ir.macChunkA (ir.reader e) real.macField d z real.width c)
      (ir.macBlindTag (ir.reader e) real.macField b real.width) := by
  obtain ⟨hpch, -, -, -⟩ := modData hwf hI hL hd h2
  have hdF := domainField_lt hwf hd
  have htag' := htag
  unfold macTagB at htag'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htag'
  obtain ⟨⟨⟨-, htagf⟩, -⟩, -⟩ := htag'
  unfold macTailAtB at htB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htB
  obtain ⟨-, htB⟩ := htB
  split at htB
  · rename_i d' b' r w nch taps z' tb real' hbt
    simp only [Bool.and_eq_true, beq_iff_eq] at htB
    obtain ⟨⟨⟨⟨⟨⟨⟨hd', hb'⟩, hw⟩, hnch⟩, hz'⟩, hpow⟩, htb⟩, hcm⟩ := htB
    have hz'' := Expr.eq_of_beq hz'
    subst d' b' w nch z'
    split at hcm
    · simp only [decide_eq_true_eq] at hcm
      obtain ⟨hMF, htf⟩ := hM.mod t ht _ _ _ _ _ _ _ _ _ hbt
      have hrf : ir.valueField r = real.macField := by
        unfold powersB at hpow
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpow
        exact hpow.1.1.2
      rw [hrf] at hMF
      have := hMF.charTwo
      obtain ⟨B, hunp, heB⟩ := hMF.basis
      have hch2 : ir.charOf real.macField = 2 := by
        have h1 := hI.ringChar _ hmf
        rw [ringChar.eq (I real.macField).K 2, hI.characteristic _ hmf] at h1
        exact h1.symm
      set L : Expr := .add (.leaf b) (.apply (.macConv r real.width real.chunks taps) z) with hLdef
      set rd := ir.reader e with hrd
      set β : (I real.macField).K := castElt (e.chal real.key 0) with hβ
      set Tval : (I real.macField).K := castElt (e.late real.tag 0 + e.asg.pad real.tag 0)
        with hTv
      set W : MACRows.Wit (I (ir.domainField d)).K real.width real.chunks :=
        (0, fun j => ir.evalWith rd d (.leaf b) j, fun c j => ir.evalWith rd d z (c * real.width + j))
        with hW
      have hrb : ∀ c : Fin real.chunks, NamedOp.macRb ir rd r real.width c =
          Conv.bitsNat B.toMACBasis (β ^ ((c : ℕ) + 1)) := by
        intro c
        funext j
        have hpw := reader_powers hL e hmf (by rw [hch2]; omega) hpow c.2
        rw [← hrd, ← hβ] at hpw
        simp only [NamedOp.macRb, Conv.bitsNat, hunp, ← hpw, toNat_castElt_of_eq hrf]
      -- the tail's left side on the integers is the integer accumulator
      have hacc : ∀ m : Fin real.width, ir.evalIntWith rd d L m =
          (MACRows.accumulatorNat taps.toFinset B.toMACBasis β W m : ℤ) := by
        intro m
        have hbm : ir.intOf rd b m = if ir.evalWith rd d (.leaf b) m = 1 then 1 else 0 := by
          rw [hbI m (by rw [hbsz]; exact m.2)]
          rfl
        have hyc : ∀ c : Fin real.chunks, ∀ j : Fin real.width,
            ir.evalIntWith rd d z (c * real.width + j) =
              if ir.evalWith rd d z (c * real.width + j) = 1 then 1 else 0 := fun c j =>
          hzI _ (by
            rw [hlen]
            have := c.2
            have := j.2
            nlinarith)
        have happ := NamedOp.applyInt_macConv ir hpch
          (fun k hk => hL.toNat_natCast _ hdF k hk) rd (r := r) (nch := real.chunks) (taps := taps)
          hw0 hcm (fun j => ir.evalIntWith rd d z j) m
        have hev : ir.evalIntWith rd d L m = ir.intOf rd b m +
            NamedOp.applyInt ir (ir.domainField d) rd (.macConv r real.width real.chunks taps)
              (fun j => ir.evalIntWith rd d z j) m := rfl
        rw [hev, happ, hbm]
        simp only [MACRows.accumulatorNat, Nat.cast_add, Nat.cast_sum, Nat.mod_eq_of_lt m.2,
          Nat.div_eq_of_lt m.2, zero_mul, zero_add, Conv.applyConv_eq_mulVec, Matrix.mulVec,
          dotProduct, Nat.cast_mul, hW, MACRows.pmac, MACRows.x, LinearMap.coe_comp,
          Function.comp_apply, LinearMap.fst_apply, LinearMap.snd_apply]
        refine congrArg₂ (· + ·) ?_ ?_
        · split_ifs <;> rfl
        · refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
          rw [hrb c, hyc c j]
          split_ifs <;> simp
      -- each bit of the target is the parity of the integer accumulator
      have hparity : ∀ m : Fin real.width, (B.unpack Tval m ↔
          MACRows.accumulatorNat taps.toFinset B.toMACBasis β W m % 2 = 1) := by
        intro m
        have hm : (m : ℕ) < ir.exprLen L := by
          show (m : ℕ) < (ir.value b).size
          rw [hbsz]
          exact m.2
        have hT' := hT
        rw [hbt] at hT'
        have h2d := hT' m hm
        obtain ⟨bt, hbt2, hrdtb, hbtiff⟩ := reader_targetBits hwf hL e htb hd (by omega) htf m
        have hint : ir.evalIntWith rd d (.leaf tb) m = bt := by
          simp only [evalIntWith, Expr.evalInt]
          rw [intOf_of_ne_constant rd (fun es hes => targetBitsB_not_constant htb hes) _
              (fun x hx => targetBitsB_not_bound htb hx), hrd, hrdtb,
            hL.toNat_natCast _ (targetBitsB_field htb ▸ hdF) bt
              (by rw [targetBitsB_field htb]; simp only [charOf] at h2; omega)]
        rw [hint, hacc m] at h2d
        rw [hunp, hTv, toNat_castElt_of_eq htagf, ← hbtiff]
        obtain ⟨q, hq⟩ := h2d
        omega
      exact macFieldCheckAt_of_maskedMAC B heB hbf hlen (MACRows.maskedMAC_eq_of_unpack B hparity)
    · simp at hcm
  · cases htB

/-- **The MAC convolution along the last axis is its block** at each output coordinate below the
width. -/
theorem NamedOp.apply_macConv_block (ir : RealizedProgram) {f : ℕ} (leaf : ir.Valuation I) {r w nch : ℕ}
    {taps : List ℕ} (x : ℕ → (I f).K) {m : ℕ} (hm : m < w) :
    NamedOp.apply ir f leaf (.macConv r w nch taps) x m =
      Ops.macConv w nch taps (NamedOp.macRb ir leaf r w) x m := by
  simp only [NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols, Nat.mod_eq_of_lt hm,
    Nat.div_eq_of_lt hm, zero_mul, zero_add]
  rfl

/-- **A natural reads its parity in characteristic `2`.** -/
theorem natCast_eq_mod_two {K : Type*} [Field K] [CharP K 2] (n : ℕ) :
    (n : K) = ((n % 2 : ℕ) : K) :=
  CharP.natCast_eq_natCast_mod K 2 n

/-! ### Operands read as bits -/

/-- **A bit read in another field identifier is a bit** (`castElt`: itself or `0`). -/
theorem castElt_bit {a b : ℕ} {x : (I a).K} (h : x = 0 ∨ x = 1) :
    (castElt x : (I b).K) = 0 ∨ (castElt x : (I b).K) = 1 := by
  rcases h with rfl | rfl
  · exact .inl castElt_zero
  · unfold castElt
    split
    · rename_i h
      subst h
      exact .inr rfl
    · exact .inl rfl

/-- **A view of bits reads bits** (`bitsB`): where every leaf in `bl` reads bits below its size and
every shared expression in `rb` reads bits below its length, every coordinate of the view below
its length is a bit. -/
theorem Expr.eval_bit_of_bitsB {f : ℕ} {leaf : ir.Valuation I} {R : ℕ → ℕ → (I f).K}
    {rl : ℕ → ℕ} {bl rb : ℕ → Bool}
    (hl : ∀ v, bl v = true → ∀ i < (ir.value v).size,
      (castElt (leaf v i) : (I f).K) = 0 ∨ (castElt (leaf v i) : (I f).K) = 1)
    (hr : ∀ k, rb k = true → ∀ i < rl k, R k i = 0 ∨ R k i = 1) :
    ∀ (e : Expr), ir.bitsB bl rb rl e = true → ∀ i < Expr.len ir rl e,
      Expr.eval ir f leaf R rl e i = 0 ∨ Expr.eval ir f leaf R rl e i = 1
  | .leaf v, h, i, hi => hl v h i hi
  | .reindex idx e, h, i, hi => by
    simp only [bitsB, Bool.and_eq_true] at h
    exact Expr.eval_bit_of_bitsB hl hr e h.1 _ (IndexMap.entry_lt_of_inRange h.2 hi)
  | .concat a b, h, i, hi => by
    simp only [bitsB, Bool.and_eq_true] at h
    simp only [Expr.len] at hi
    simp only [Expr.eval]
    split_ifs with hia
    · exact Expr.eval_bit_of_bitsB hl hr a h.1 i hia
    · exact Expr.eval_bit_of_bitsB hl hr b h.2 _ (by omega)
  | .ref k, h, i, hi => hr k h i hi
  | .add _ _, h, _, _ => by simp [bitsB] at h
  | .sub _ _, h, _, _ => by simp [bitsB] at h
  | .scale _ _, h, _, _ => by simp [bitsB] at h
  | .mul _ _, h, _, _ => by simp [bitsB] at h
  | .linear _ _, h, _, _ => by simp [bitsB] at h
  | .prod _ _, h, _, _ => by simp [bitsB] at h
  | .mux _ _ _, h, _, _ => by simp [bitsB] at h
  | .apply _ _, h, _, _ => by simp [bitsB] at h
  | .logic _ _ _, h, _, _ => by simp [bitsB] at h

/-- **The shared views of bits read bits** (`refBitsT`) at every level, for a program whose shared
expressions read earlier entries. -/
theorem refVal_bit_of_refBitsT {f : ℕ} {leaf : ir.Valuation I} (ho : ir.RefsOrdered)
    {bl : ℕ → Bool}
    (hl : ∀ v, bl v = true → ∀ i < (ir.value v).size,
      (castElt (leaf v i) : (I f).K) = 0 ∨ (castElt (leaf v i) : (I f).K) = 1) :
    ∀ n m k, ir.refBitsT bl m k = true → ∀ i < ir.refLen ir.exprs.length k,
      ir.refVal leaf n f k i = 0 ∨ ir.refVal leaf n f k i = 1
  | 0, _, _, _, _, _ => .inl rfl
  | _ + 1, 0, _, h, _, _ => by simp [refBitsT] at h
  | n + 1, m + 1, k, h, i, hi => by
    simp only [refBitsT, Bool.and_eq_true, decide_eq_true_eq] at h
    rw [refLen_eq_len ho h.1] at hi
    exact Expr.eval_bit_of_bitsB hl (fun k' hk' => refVal_bit_of_refBitsT ho hl n m k' hk') _ h.2
      i hi

/-- **An expression that reads bits by the program reads bits** (`exprBitsB`), in any
characteristic: under the leaf facts, each leaf is a `Bit` value stored at its node `bit` or with its
Boolean check (`bit_of_primeRead`), and a view of such leaves reads bits. -/
theorem evalWith_bit_of_exprBitsB (hwf : ir.WellFormed) {rd : ir.Valuation I}
    (hF : ir.LeafFacts rd) {d : ℕ} {e : Expr} (h : ir.exprBitsB primeNodes e = true) {i : ℕ}
    (hi : i < ir.exprLen e) : ir.evalWith rd d e i = 0 ∨ ir.evalWith rd d e i = 1 := by
  have hl : ∀ v, ir.bitLeafB primeNodes v = true → ∀ j < (ir.value v).size,
      (castElt (rd v j) : (I (ir.domainField d)).K) = 0 ∨
        (castElt (rd v j) : (I (ir.domainField d)).K) = 1 := by
    intro v hv j hj
    simp only [bitLeafB, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact castElt_bit (bit_of_primeRead hF hv.1.1 hv.2 hv.1.2 hj)
  exact Expr.eval_bit_of_bitsB hl
    (fun k hk => refVal_bit_of_refBitsT hwf.refsOrdered hl _ _ k hk) e h i hi

/-- **A MAC check over a field of characteristic `2` gives the target** (the check `acc = bits(T)`
entrywise in a field of characteristic `2`): where the check's tail holds and the operand reads
bits, each accumulator entry computed in the field is the cast of the integer accumulator, which in
characteristic `2` is its parity; so the blind reads bits, each bit of `T` is the parity of the
integer accumulator, and `T` is the masked MAC of the check's operand with its blind
(`MACRows.maskedMAC_eq_of_unpack`). `hM` is a property of the model (`Interp.MacModel`). -/
theorem macFieldCheckAt_of_two (hI : I.Registered ir) (hwf : ir.WellFormed)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I) {pid d b : ℕ}
    {z : Expr} {real : MacRealization} (hd : d < ir.domains.length)
    (hlen : ir.exprLen z = real.chunks * real.width) (hmf : real.macField < ir.fields.length)
    (htag : ir.macTagB real = true)
    (hbf : ir.valueField b = ir.domainField d) (hbsz : (ir.value b).size = real.width)
    (hzb : ∀ i < ir.exprLen z, ir.evalWith (ir.reader e) d z i = 0 ∨
      ir.evalWith (ir.reader e) d z i = 1)
    {t : ℕ} (ht : t < ir.predicates.length) (htB : ir.macTailTwoB pid d z b real t = true)
    (hT : ir.HoldsWith (ir.reader e) (ir.predicate t).body) :
    ir.MacFieldCheckAt e real (fun c => ir.macChunkA (ir.reader e) real.macField d z real.width c)
      (ir.macBlindTag (ir.reader e) real.macField b real.width) := by
  have hdF := domainField_lt hwf hd
  have htag' := htag
  unfold macTagB at htag'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htag'
  obtain ⟨⟨⟨-, htagf⟩, -⟩, -⟩ := htag'
  unfold macTailTwoB at htB
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htB
  obtain ⟨⟨-, hc2⟩, htB⟩ := htB
  split at htB
  · rename_i d' b' r w nch taps z' tb tgt hbt
    simp only [Bool.and_eq_true, beq_iff_eq] at htB
    obtain ⟨⟨⟨⟨⟨⟨hd', hb'⟩, hw⟩, hnch⟩, hz'⟩, hpow⟩, htb⟩ := htB
    have hz'' := Expr.eq_of_beq hz'
    subst d' b' w nch z'
    obtain ⟨hMF, htf⟩ := hM.two t ht _ _ _ _ _ _ _ _ _ hbt
    have hrf : ir.valueField r = real.macField := by
      unfold powersB at hpow
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hpow
      exact hpow.1.1.2
    rw [hrf] at hMF
    have := hMF.charTwo
    obtain ⟨B, hunp, heB⟩ := hMF.basis
    have hch2 : ir.charOf real.macField = 2 := by
      have h1 := hI.ringChar _ hmf
      rw [ringChar.eq (I real.macField).K 2, hI.characteristic _ hmf] at h1
      exact h1.symm
    have hdc : CharP (I (ir.domainField d)).K 2 := by
      have := charP_field hI hdF
      simp only [charOf] at hc2
      rwa [hc2] at this
    have h01 : (1 : (I (ir.domainField d)).K) ≠ 0 := one_ne_zero
    set rd := ir.reader e with hrd
    set β : (I real.macField).K := castElt (e.chal real.key 0) with hβ
    set Tval : (I real.macField).K := castElt (e.late real.tag 0 + e.asg.pad real.tag 0)
      with hTv
    set W : MACRows.Wit (I (ir.domainField d)).K real.width real.chunks :=
      (0, fun j => ir.evalWith rd d (.leaf b) j, fun c j => ir.evalWith rd d z (c * real.width + j))
      with hW
    have hrb : ∀ c : Fin real.chunks, NamedOp.macRb ir rd r real.width c =
        Conv.bitsNat B.toMACBasis (β ^ ((c : ℕ) + 1)) := by
      intro c
      funext j
      have hpw := reader_powers hL e hmf (by rw [hch2]; omega) hpow c.2
      rw [← hrd, ← hβ] at hpw
      simp only [NamedOp.macRb, Conv.bitsNat, hunp, ← hpw, toNat_castElt_of_eq hrf]
    -- the integer sum of the convolution
    set N : Fin real.width → ℕ := fun m => ∑ c : Fin real.chunks,
      Conv.applyConv taps.toFinset (Conv.bitsNat B.toMACBasis (β ^ ((c : ℕ) + 1)))
        (fun j => if ir.evalWith rd d z (c * real.width + j) = 1 then 1 else 0) m with hN
    -- the convolution computed in the field is the cast of the integer sum
    have hconv : ∀ m : Fin real.width,
        NamedOp.apply ir (ir.domainField d) rd (.macConv r real.width real.chunks taps)
          (ir.evalE rd (ir.domainField d) z) m = ((N m : ℕ) : (I (ir.domainField d)).K) := by
      intro m
      rw [NamedOp.apply_macConv_block ir rd _ m.2]
      have hx : Ops.macConv real.width real.chunks taps (NamedOp.macRb ir rd r real.width)
            (ir.evalE rd (ir.domainField d) z) m =
          Ops.macConv real.width real.chunks taps (NamedOp.macRb ir rd r real.width)
            (fun t => ((if ir.evalE rd (ir.domainField d) z t = 1 then 1 else 0 : ℕ) :
              (I (ir.domainField d)).K)) m := by
        unfold Ops.macConv
        rw [dif_pos m.2, dif_pos m.2]
        refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun j _ => ?_
        congr 1
        have hlt : (c : ℕ) * real.width + j < ir.exprLen z := by
          rw [hlen]
          have := c.2
          have := j.2
          nlinarith
        rcases hzb _ hlt with h0 | h1
        · simp only [evalWith] at h0
          simp [h0]
        · simp only [evalWith] at h1
          simp [h1]
      rw [hx, Ops.macConv_natCast _ _ _ _ _ m.2]
      simp only [hN]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [hrb c]
      rfl
    -- each bit of the target is the parity of the integer accumulator
    have hparity : ∀ m : Fin real.width, (B.unpack Tval m ↔
        MACRows.accumulatorNat taps.toFinset B.toMACBasis β W m % 2 = 1) := by
      intro m
      have hm : (m : ℕ) < ir.exprLen (.add (.leaf b) (.apply (.macConv r real.width real.chunks
          taps) z)) := by
        show (m : ℕ) < (ir.value b).size
        rw [hbsz]
        exact m.2
      have hT' := hT
      rw [hbt] at hT'
      have h2d := hT' m hm
      obtain ⟨bt, hbt2, hrdtb, hbtiff⟩ := reader_targetBits hwf hL e htb hd (by omega) htf m
      have htbv : ir.evalWith rd d (.leaf tb) m = (bt : (I (ir.domainField d)).K) := by
        have hev : ir.evalWith rd d (.leaf tb) m = castElt (rd tb m) := evalE_leaf _ _ _ _
        rw [hev, hrd, hrdtb, castElt_natCast (targetBitsB_field htb)]
      have hadd : ir.evalWith rd d (.add (.leaf b) (.apply (.macConv r real.width real.chunks taps)
          z)) m = ir.evalWith rd d (.leaf b) m + NamedOp.apply ir (ir.domainField d) rd
            (.macConv r real.width real.chunks taps) (ir.evalE rd (ir.domainField d) z) m := rfl
      rw [hadd, hconv m, htbv] at h2d
      -- the blind's coordinate is the parity of `bt + N m`
      have hbm : ir.evalWith rd d (.leaf b) m = (((bt + N m) % 2 : ℕ) : (I (ir.domainField d)).K) := by
        rw [← natCast_eq_mod_two, Nat.cast_add, ← h2d, add_assoc, CharTwo.add_self_eq_zero,
          add_zero]
      have hind : (if ir.evalWith rd d (.leaf b) m = 1 then 1 else 0) = (bt + N m) % 2 := by
        rw [hbm]
        rcases Nat.mod_two_eq_zero_or_one (bt + N m) with h | h <;> rw [h] <;> simp [h01.symm]
      have hacc : MACRows.accumulatorNat taps.toFinset B.toMACBasis β W m =
          (bt + N m) % 2 + N m := by
        rw [← hind]
        rfl
      rw [hunp, hTv, toNat_castElt_of_eq htagf, ← hbtiff, hacc]
      omega
    exact macFieldCheckAt_of_maskedMAC B heB hbf hlen (MACRows.maskedMAC_eq_of_unpack B hparity)
  · cases htB

/-- **Equal chunks of bits in the checks over two fields of characteristic other than `2`'s MAC field give the
cross-field `equal`**: where both operands read bits and their chunks of the coordinates equal to
`1` agree in the MAC field (`macChunkA`, in a basis whose elements are the generator's powers),
the operands' readings agree, so the cross-field `equal` holds in the compiler's contract. -/
theorem crossHolds_of_chunksA (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} {dx dy : ℕ}
    {x y : Expr} {k : CrossKind} {real : MacRealization}
    (hdxF : ir.domainField dx < ir.fields.length) (hdyF : ir.domainField dy < ir.fields.length)
    (hcx : 1 < ir.charOf (ir.domainField dx)) (hcy : 1 < ir.charOf (ir.domainField dy))
    (hw1 : k.width = 1) (hw0 : 0 < real.width)
    (hlenX : ir.exprLen x = real.chunks * real.width)
    (hlenY : ir.exprLen y = real.chunks * real.width)
    (hxb : ∀ i < ir.exprLen x, ir.evalWith rd dx x i = 0 ∨ ir.evalWith rd dx x i = 1)
    (hyb : ∀ i < ir.exprLen y, ir.evalWith rd dy y i = 0 ∨ ir.evalWith rd dy y i = 1)
    (B : MACBasis real.width (I real.macField).K)
    (heB : ∀ j, B.e j = (I real.macField).decode 2 ^ (j : ℕ))
    (hch : ∀ c : Fin real.chunks, ir.macChunkA rd real.macField dx x real.width c =
      ir.macChunkA rd real.macField dy y real.width c) :
    ir.HoldsWith rd (.cross dx x dy y k real) := by
  have hone1 : ∀ {a : ℕ}, a < ir.fields.length → 1 < ir.charOf a → (I a).toNat 1 = 1 :=
    fun ha h1 => by simpa using hL.toNat_natCast _ ha 1 h1
  have hzero0 : ∀ {a : ℕ}, a < ir.fields.length → 1 < ir.charOf a → (I a).toNat 0 = 0 :=
    fun ha h1 => by simpa using hL.toNat_natCast _ ha 0 (lt_trans Nat.zero_lt_one h1)
  have hpack : ∀ (d : ℕ) (z : Expr) (c : Fin real.chunks),
      ir.macChunkA rd real.macField d z real.width c =
        MAC.pack B fun j => if ir.evalPad rd d z (c * real.width + j) = 1 then 1 else 0 := by
    intro d z c
    simp only [macChunkA, MAC.pack]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [heB, mul_comm]
  refine ⟨fun i hi => ?_, fun _ i hi => ?_⟩
  · rw [hw1, pow_one]
    rcases hyb i (by rw [hlenY, ← hlenX]; exact hi) with hy0 | hy1
    · rw [hy0, hzero0 hdyF hcy]
      norm_num
    · rw [hy1, hone1 hdyF hcy]
      norm_num
  rw [hlenX] at hi
  have hc : i / real.width < real.chunks := by
    rw [Nat.div_lt_iff_lt_mul hw0]
    exact hi
  have hij : i / real.width * real.width + i % real.width = i := Nat.div_add_mod' i real.width
  have hpk := MAC.pack_injective B (fun j => by split_ifs <;> simp) (fun j => by split_ifs <;> simp)
    ((hpack dx x ⟨_, hc⟩).symm.trans ((hch ⟨_, hc⟩).trans (hpack dy y ⟨_, hc⟩)))
  have hcj := congrFun hpk ⟨i % real.width, Nat.mod_lt _ hw0⟩
  simp only [hij] at hcj
  rw [evalPad_of_lt (show i < ir.exprLen x by rw [hlenX]; exact hi),
    evalPad_of_lt (show i < ir.exprLen y by rw [hlenY]; exact hi)] at hcj
  rcases hxb i (by rw [hlenX]; exact hi) with hx0 | hx1 <;>
    rcases hyb i (by rw [hlenY]; exact hi) with hy0 | hy1
  · rw [hx0, hy0, hzero0 hdxF hcx, hzero0 hdyF hcy]
  · rw [hx0, hy1, if_neg zero_ne_one, if_pos rfl] at hcj
    exact absurd hcj zero_ne_one
  · rw [hx1, hy0, if_pos rfl, if_neg zero_ne_one] at hcj
    exact absurd hcj one_ne_zero
  · rw [hx1, hy1, hone1 hdxF hcx, hone1 hdyF hcy]

/-- **A MAC's tail of odd characteristic is no cross-field `equal`**: it is a `mod_2`. -/
theorem macTailAtB_not_cross {pid d t b : ℕ} {z : Expr} {real : MacRealization}
    (h : ir.macTailAtB pid d z b real t = true) {dx' dy' : ℕ} {x' y' : Expr}
    {k' : CrossKind} {real' : MacRealization} :
    (ir.predicate t).body ≠ .cross dx' x' dy' y' k' real' := fun hb => by
  unfold macTailAtB at h
  rw [hb] at h
  simp at h

/-- **A MAC's tail of characteristic `2` is no cross-field `equal`**: it is a field `equal`. -/
theorem macTailTwoB_not_cross {pid d t b : ℕ} {z : Expr} {real : MacRealization}
    (h : ir.macTailTwoB pid d z b real t = true) {dx' dy' : ℕ} {x' y' : Expr}
    {k' : CrossKind} {real' : MacRealization} :
    (ir.predicate t).body ≠ .cross dx' x' dy' y' k' real' := fun hb => by
  unfold macTailTwoB at h
  rw [hb] at h
  simp at h

/-- **The tail of a hosted MAC is the tail of the check over `y`'s field, of odd characteristic**, at
its operand: `y` padded by zeros (`PadsTo`), checked by `macTailAtB` at the blind,
`real.blind = some b`. -/
theorem macTailB_pad {pid dy t b : ℕ} {y : Expr} {real : MacRealization}
    (hb : real.blind = some b) (h : ir.macTailB pid dy y real t = true) :
    ∃ z', ir.zeroPadB (ir.domainField dy) (real.chunks * real.width) z' y = true ∧
      ir.macTailAtB pid dy z' b real t = true := by
  unfold macTailB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hlt, hrole⟩, h⟩ := h
  split at h
  · rename_i d b' r w nch taps y' tb real' hbt
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨hd, hb'⟩, hw⟩, hnch⟩, hpad⟩, hpow⟩, htb⟩, hcm⟩ := h
    rw [hb, Option.some.injEq] at hb'
    refine ⟨y', hpad, ?_⟩
    unfold macTailAtB
    simp only [hlt, decide_true, hrole, Bool.true_and, hbt, hd, hb', hw, hnch, Expr.beq_self,
      hpow, htb, beq_self_eq_true, Bool.and_true, Bool.true_and]
    rw [← hw]
    exact hcm
  · cases h

/-- **The blind of a hosted MAC is the blind of the check over `y`'s field** (`macBlindB` at
`real.blind = some b`). -/
theorem macBlindAtB_of_macBlindB {dy b : ℕ}
    {real : MacRealization} (hb : real.blind = some b)
    (h : ir.macBlindB L dy real = true) : ir.macBlindAtB L dy b real = true := by
  unfold macBlindB at h
  rw [hb] at h
  exact h

/-- **A hosted MAC's interval-free shape** (`MacShapeOk` but its intervals and its tail, which a
derivation states as facts). -/
structure MacHostedCore (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) (k : CrossKind)
    (real : MacRealization) : Prop where
  width : k.width = 1
  pos : 0 < real.width
  field : real.macField < ir.fields.length
  hField : ir.domainField dx = real.macField
  key : ir.macKeyB pid real = true
  tag : ir.macTagB real = true
  lenX : ir.exprLen x ≤ real.chunks * real.width
  lenY : ir.exprLen y = ir.exprLen x
  before : ir.macReadsBeforeB x y real = true
  char : 2 < ir.charOf (ir.domainField dy)
  half : ir.macHalfB pid dx x real = true
  noBlindX : real.blindX = none

variable (ir) in
/-- **`MacHostedCore` as a Boolean.** -/
def macHostedCoreB (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) (k : CrossKind)
    (real : MacRealization) : Bool :=
  decide (k.width = 1) && decide (0 < real.width) && decide (real.macField < ir.fields.length) &&
    decide (ir.domainField dx = real.macField) && ir.macKeyB pid real && ir.macTagB real &&
    decide (ir.exprLen x ≤ real.chunks * real.width) &&
    decide (ir.exprLen y = ir.exprLen x) && ir.macReadsBeforeB x y real &&
    decide (2 < ir.charOf (ir.domainField dy)) && ir.macHalfB pid dx x real &&
    decide (real.blindX = none)

theorem MacHostedCore.of_B {pid dx : ℕ} {x : Expr} {dy : ℕ} {y : Expr} {k : CrossKind}
    {real : MacRealization} (h : ir.macHostedCoreB pid dx x dy y k real = true) :
    ir.MacHostedCore pid dx x dy y k real := by
  simp only [macHostedCoreB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem MacShapeOk.core {pid dx : ℕ} {x : Expr} {dy : ℕ} {y : Expr} {k : CrossKind}
    {real : MacRealization} (h : ir.MacShapeOk primeNodes pid dx x dy y k real) :
    ir.MacHostedCore pid dx x dy y k real :=
  ⟨h.width, h.pos, h.field, h.hField, h.key, h.tag, h.lenX, h.lenY, h.before, h.char, h.half,
    h.noBlindX⟩

theorem macHostedCoreB_of_core {pid dx : ℕ} {x : Expr} {dy : ℕ} {y : Expr} {k : CrossKind}
    {real : MacRealization} (h : ir.MacHostedCore pid dx x dy y k real) :
    ir.macHostedCoreB pid dx x dy y k real = true := by
  simp only [macHostedCoreB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h.width, h.pos⟩, h.field⟩, h.hField⟩, h.key⟩, h.tag⟩, h.lenX⟩, h.lenY⟩,
    h.before⟩, h.char⟩, h.half⟩, h.noBlindX⟩

/-- **A two-tail MAC's interval-free shape** (`MacTwoTailOk` but its checks over the two fields). -/
structure MacTwoCore (pid : ℕ) (x y : Expr) (k : CrossKind) (real : MacRealization) : Prop where
  width : k.width = 1
  pos : 0 < real.width
  field : real.macField < ir.fields.length
  key : ir.macKeyB pid real = true
  tag : ir.macTagB real = true
  noH : real.hPredicate = none
  lenX : ir.exprLen x = real.chunks * real.width
  lenY : ir.exprLen y = real.chunks * real.width
  before : ir.macReadsBeforeB x y real = true

variable (ir) in
/-- **`MacTwoCore` as a Boolean.** -/
def macTwoCoreB (pid : ℕ) (x y : Expr) (k : CrossKind) (real : MacRealization) : Bool :=
  decide (k.width = 1) && decide (0 < real.width) && decide (real.macField < ir.fields.length) &&
    ir.macKeyB pid real && ir.macTagB real && decide (real.hPredicate = none) &&
    decide (ir.exprLen x = real.chunks * real.width) &&
    decide (ir.exprLen y = real.chunks * real.width) && ir.macReadsBeforeB x y real

theorem MacTwoCore.of_B {pid : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (h : ir.macTwoCoreB pid x y k real = true) : ir.MacTwoCore pid x y k real := by
  simp only [macTwoCoreB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩

theorem MacTwoTailOk.core {pid dx : ℕ} {x : Expr} {dy : ℕ} {y : Expr} {k : CrossKind}
    {real : MacRealization} {bx b : ℕ} (h : ir.MacTwoTailOk primeNodes pid dx x dy y k real bx b) :
    ir.MacTwoCore pid x y k real :=
  ⟨h.width, h.pos, h.field, h.key, h.tag, h.noH, h.lenX, h.lenY, h.before⟩

theorem macTwoCoreB_of_core {pid : ℕ} {x y : Expr} {k : CrossKind} {real : MacRealization}
    (h : ir.MacTwoCore pid x y k real) : ir.macTwoCoreB pid x y k real = true := by
  simp only [macTwoCoreB, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨h.width, h.pos⟩, h.field⟩, h.key⟩, h.tag⟩, h.noH⟩, h.lenX⟩, h.lenY⟩, h.before⟩

/-- **The H predicate of a MAC is a field `equal` of the program** (`macHPredB`). -/
theorem macHPredB_pred {pid dx : ℕ} {x : Expr} {real : MacRealization} {p : ℕ}
    (hp : ir.macHPredB pid dx x real p = true) :
    p < ir.predicates.length ∧ (ir.predicate p).body.isEqual = true := by
  unfold macHPredB at hp
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hp
  obtain ⟨⟨⟨hpl, -⟩, -⟩, hp⟩ := hp
  refine ⟨hpl, ?_⟩
  split at hp
  · rename_i hb
    rw [hb]
    rfl
  · cases hp

/-- **The MAC's soundness, hosted form, over the facts it reads**: the A operand `y` read within
`[0, 1]` (`Bits01`), the blind `b` read as its indicator, the tail `t` (`macTailB`) holding, and
the H half (`hH`, or the H predicate holding, `hHp`); see `crossHolds_or_macBad`. -/
theorem crossHolds_or_macBad_named (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I) {pid dx : ℕ} {x : Expr}
    {dy : ℕ} {y : Expr} {k : CrossKind} {real : MacRealization} (hpid : pid < ir.predicates.length)
    (hb : (ir.predicate pid).body = .cross dx x dy y k real)
    (hok : ir.MacHostedCore pid dx x dy y k real) {b : ℕ} (hbl : real.blind = some b)
    (hbf : ir.valueField b = ir.domainField dy) (hbsz : (ir.value b).size = real.width)
    (hy01 : Bits01 ir (ir.reader e) dy y)
    (hbI : ∀ i < (ir.value b).size, ir.intOf (ir.reader e) b i =
      if (castElt (ir.reader e b i) : (I (ir.domainField dy)).K) = 1 then 1 else 0)
    {t : ℕ} (ht : t < ir.predicates.length) (htB : ir.macTailB pid dy y real t = true)
    (hT : ir.HoldsWith (ir.reader e) (ir.predicate t).body)
    (hH : real.hPredicate = none →
      ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0)))
    (hHp : ∀ p, real.hPredicate = some p → ir.HoldsWith (ir.reader e) (ir.predicate p).body) :
    ir.HoldsWith (ir.reader e) (.cross dx x dy y k real) ∨
      (ir.macEvent e dx x dy y real).BadAt (castElt (e.chal real.key 0)) := by
  have hpoX := hwf.predicates _ (predicate_mem hpid)
  rw [hb] at hpoX
  have hyok := hpoX.1 (dy, y) (by simp [PredBody.exprs])
  have hdF := domainField_lt hwf hyok.1
  have htagk : (ir.value real.tag).kind = .late := by
    have h := hok.tag
    unfold macTagB at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    revert h
    cases (ir.value real.tag).kind <;> simp
  obtain ⟨z', hpad, htB'⟩ := macTailB_pad hbl htB
  have hKe : ∀ v es, (ir.value v).kind = .constant es → ∀ i,
      ir.reader e v i = (I (ir.valueField v)).decode (es.getD i 0) :=
    fun _ _ hk i => reader_of_constant e hk i
  have hc0 : 0 < ir.charOf (ir.domainField dy) := by have := hok.char; omega
  have hpz := padsTo_of_zeroPadB hwf.refsOrdered hI hL hKe hdF hc0 hpad
  have hlz := hpz.1
  have hz01 := bits01_of_padsTo hpz hy01
  have hY := macFieldCheckAt_of_odd hwf hI hL hM e hyok.1 hlz hok.pos hok.field hok.tag
    hok.char hbf hbsz hbI (fun i hi => hz01.ite hi) ht htB' hT
  simp only [macChunkA_of_padsTo hpz] at hY
  obtain ⟨taps, hMF⟩ := exists_macFieldOk_of_tailAt hM ht htB'
  obtain ⟨B, hunp, heB⟩ := hMF.basis
  -- the H half
  have hHh : ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0)) := by
    have hhalf := hok.half
    unfold macHalfB at hhalf
    revert hhalf
    cases hhp : real.hPredicate with
    | none => exact fun _ => hH hhp
    | some p =>
      exact fun hp => macHHolds_of_pred hwf.refsOrdered hI hL e (hHp p hhp) hp hok.hField hok.field hok.tag
        hMF.decodePow
  have hch2 : ir.charOf real.macField = 2 := by
    have := hMF.charTwo
    have h1 := hI.ringChar _ hok.field
    rw [ringChar.eq (I real.macField).K 2, hI.characteristic _ hok.field] at h1
    exact h1.symm
  rcases MacFieldCheckAt.binding (macFieldCheckAt_of_macH htagk hHh) hY with ⟨hch, -⟩ | hbad
  · left
    refine crossHolds_of_chunks hL hok.hField hok.field hdF hch2 hok.char hok.width hok.pos
      hok.lenX hok.lenY
        (fun i hi => hy01.bit hi)
      B.toMACBasis hunp ((heB _).trans (pow_zero _)) fun c => ?_
    have hc := congrFun hch c
    simp only [macChunkH, macChunkA] at hc
    simp only [MAC.pack]
    convert hc using 1
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [heB, mul_comm]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [heB, mul_comm]
  · right
    simp only [macEvent, hok.noBlindX, hbl, Option.getD_some]
    exact hbad

/-- **The MAC's soundness, hosted form** (compiler/mac.h): for a cross-field `equal` with the MAC
realization whose `x` domain hosts the MAC (`MacShapeOk`), where the H half holds (`MacHHoldsAt` at
the key: by the compiler's own circuit, `hH`, or by the H predicate `<mac>.H`, a field `equal` of
the leaf facts, `macHHolds_of_pred`) and the tail `mod_2` holds, either the cross-field `equal`
holds (in the compiler's contract, `RealizedProgram.HoldsWith`: the H operand's Booleanity is the caller's)
or the key is a root of the MAC's binding polynomial (`macEvent`). The tail gives `T` as the masked
MAC of the A operand with the blind's tag (`macFieldCheckAt_of_odd`); the H half gives it as the masked
MAC of the H operand with the tag's pad (`macFieldCheckAt_of_macH`); the two bind (`MacFieldCheckAt.binding`).
`hM` is a property of the model (`Interp.MacModel`). -/
theorem crossHolds_or_macBad (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I)
    (hF : ir.LeafFacts (ir.reader e)) (hK : ir.ShiftFacts (ir.reader e)) {pid dx : ℕ} {x : Expr}
    {dy : ℕ} {y : Expr} {k : CrossKind} {real : MacRealization} (hpid : pid < ir.predicates.length)
    (hb : (ir.predicate pid).body = .cross dx x dy y k real)
    (hok : ir.MacShapeOk primeNodes pid dx x dy y k real)
    (htail : ∀ t < ir.predicates.length, ir.macTailB pid dy y real t = true →
      ir.HoldsWith (ir.reader e) (ir.predicate t).body)
    (hH : real.hPredicate = none →
      ir.MacHHoldsAt (ir.reader e) dx x real (castElt (e.chal real.key 0))) :
    ir.HoldsWith (ir.reader e) (.cross dx x dy y k real) ∨
      (ir.macEvent e dx x dy y real).BadAt (castElt (e.chal real.key 0)) := by
  have hpoX := hwf.predicates _ (predicate_mem hpid)
  rw [hb] at hpoX
  have hyok := hpoX.1 (dy, y) (by simp [PredBody.exprs])
  obtain ⟨L, hLok, hblind, hbits⟩ := hok.ivls
  obtain ⟨b, hbl⟩ : ∃ b, real.blind = some b := by
    have h := hblind
    unfold macBlindB at h
    revert h
    cases real.blind with
    | none => simp
    | some b => exact fun _ => ⟨b, rfl⟩
  have hbl0 := macBlindAtB_of_macBlindB hbl hblind
  have hbIv : IvlWithin (ir.exprIvl L (ir.domainField dy) (.leaf b)) 0 1 := by
    unfold macBlindAtB at hbl0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbl0
    exact hbl0.2
  have hbl1 := hbl0
  unfold macBlindAtB at hbl1
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hbl1
  obtain ⟨⟨⟨-, hbf⟩, hbsz⟩, -⟩ := hbl1
  obtain ⟨t, ht, htB⟩ := hok.tail
  refine crossHolds_or_macBad_named hwf hI hL hM e hpid hb hok.core hbl hbf hbsz
    (bits01_of_ivl hwf hI hL hF hK hLok hyok.1 hok.char hyok.2 hbits)
    (fun i hi => intOf_eq_ite_of_leafIvl hwf hI hL hF hK hLok hbIv hi) ht htB (htail t ht htB) hH
    fun p hp => ?_
  have hh := hok.half
  simp only [macHalfB, hp] at hh
  obtain ⟨hpl, heq⟩ := macHPredB_pred hh
  exact hF.equals p hpl heq

/-- **What a MAC check over a field gives, for a MAC that no domain hosts**: its operand reads bits,
its field has characteristic above `1`, it gives the target as the masked MAC of its operand
with its blind (`MacFieldCheckAt`), and the MAC field is a binary MAC field of the MAC's width
(`MacFieldOk`). -/
structure MacFieldCheckFacts (e : ir.Env I) (d : ℕ) (z : Expr) (b : ℕ) (real : MacRealization) :
    Prop where
  /-- The operand reads bits. -/
  bits : ∀ i < ir.exprLen z, ir.evalWith (ir.reader e) d z i = 0 ∨
    ir.evalWith (ir.reader e) d z i = 1
  /-- The field's characteristic exceeds `1`. -/
  char : 1 < ir.charOf (ir.domainField d)
  /-- The check gives the target. -/
  side : ir.MacFieldCheckAt e real (fun c => ir.macChunkA (ir.reader e) real.macField d z real.width c)
    (ir.macBlindTag (ir.reader e) real.macField b real.width)
  /-- The MAC field is a binary MAC field of the MAC's width. -/
  field : ∃ taps : Finset ℕ, I.MacFieldOk real.macField real.width taps

/-- **A MAC check over a field, for a MAC that no domain hosts, gives its facts**, over the facts it
reads: its operand `z` reads bits (and, at odd characteristic, its indicator), its blind `b` reads
its indicator at odd characteristic, and its tail `t` holds (`macTailAtB` at odd characteristic,
`macTailTwoB` at characteristic `2`). -/
theorem macFieldCheckFacts_named (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I) {pid d b : ℕ}
    {z : Expr} {real : MacRealization} (hd : d < ir.domains.length)
    (hlen : ir.exprLen z = real.chunks * real.width)
    (hw0 : 0 < real.width) (hmf : real.macField < ir.fields.length)
    (htag : ir.macTagB real = true)
    (hbf : ir.valueField b = ir.domainField d) (hbsz : (ir.value b).size = real.width)
    (hzb : ∀ i < ir.exprLen z, ir.evalWith (ir.reader e) d z i = 0 ∨
      ir.evalWith (ir.reader e) d z i = 1)
    (hzI : 2 < ir.charOf (ir.domainField d) → ∀ i < ir.exprLen z,
      ir.evalIntWith (ir.reader e) d z i = if ir.evalWith (ir.reader e) d z i = 1 then 1 else 0)
    (hbI : 2 < ir.charOf (ir.domainField d) → ∀ i < (ir.value b).size, ir.intOf (ir.reader e) b i =
      if (castElt (ir.reader e b i) : (I (ir.domainField d)).K) = 1 then 1 else 0)
    {t : ℕ} (ht : t < ir.predicates.length)
    (htB : ((ir.macTailAtB pid d z b real t && decide (2 < ir.charOf (ir.domainField d))) ||
      ir.macTailTwoB pid d z b real t) = true)
    (hT : ir.HoldsWith (ir.reader e) (ir.predicate t).body) :
    ir.MacFieldCheckFacts e d z b real := by
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at htB
  rcases htB with ⟨htA, h2⟩ | htT
  · exact ⟨hzb, by omega, macFieldCheckAt_of_odd hwf hI hL hM e hd hlen hw0 hmf htag h2 hbf hbsz
      (hbI h2) (hzI h2) ht htA hT, exists_macFieldOk_of_tailAt hM ht htA⟩
  · have htB' := htT
    unfold macTailTwoB at htB'
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htB'
    obtain ⟨⟨-, hc2⟩, htB'⟩ := htB'
    refine ⟨hzb, by omega, macFieldCheckAt_of_two hI hwf hL hM e hd hlen hmf htag hbf hbsz hzb ht
      htT hT, ?_⟩
    split at htB'
    · rename_i d' b' r w nch taps z' tb tgt hbt
      simp only [Bool.and_eq_true, beq_iff_eq] at htB'
      obtain ⟨⟨⟨⟨⟨⟨-, -⟩, rfl⟩, -⟩, -⟩, hpow⟩, -⟩ := htB'
      obtain ⟨hMF, -⟩ := hM.two t ht _ _ _ _ _ _ _ _ _ hbt
      have hrf : ir.valueField r = real.macField := by
        unfold powersB at hpow
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hpow
        exact hpow.1.1.2
      exact ⟨_, hrf ▸ hMF⟩
    · cases htB'

/-- **A MAC check over a field, for a MAC that no domain hosts, gives its facts**
(`MacTailFieldOk`): a check over a field of odd characteristic by its interval and its tail `mod_2`
(`macFieldCheckAt_of_odd`), a check over a field of characteristic `2` by the program's bits
(`exprBitsB`, `evalWith_bit_of_exprBitsB`) and its field `equal` (`macFieldCheckAt_of_two`); where
every predicate other than a cross-field `equal` holds (`hnc`). `hM` is a property of the model
(`Interp.MacModel`). -/
theorem macFieldCheckFacts_of_tailField (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I)
    (hF : ir.LeafFacts (ir.reader e)) {sr : List (ℕ × ℕ)} (hK : ir.ShiftFacts (ir.reader e) sr)
    (hLok : ir.LeafIvlsOk primeNodes sr L) {pid d b : ℕ}
    {z : Expr} {real : MacRealization} (hd : d < ir.domains.length)
    (hz : ir.ExprOk (ir.domainField d) z) (hlen : ir.exprLen z = real.chunks * real.width)
    (hw0 : 0 < real.width) (hmf : real.macField < ir.fields.length)
    (htag : ir.macTagB real = true) (hs : ir.MacTailFieldOk primeNodes L pid d z b real)
    (hnc : ∀ t < ir.predicates.length,
      (∀ dx' x' dy' y' k' real', (ir.predicate t).body ≠ .cross dx' x' dy' y' k' real') →
        ir.HoldsWith (ir.reader e) (ir.predicate t).body) :
    ir.MacFieldCheckFacts e d z b real := by
  rcases hs with hs | hs
  · obtain ⟨t, ht, htB⟩ := hs.tail
    have hbl0 := hs.blind
    unfold macBlindAtB at hbl0
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hbl0
    obtain ⟨⟨⟨-, hbf⟩, hbsz⟩, hbIv⟩ := hbl0
    exact macFieldCheckFacts_named hwf hI hL hM e hd hlen hw0 hmf htag hbf hbsz
      (fun i hi => bits_of_ivl hwf hI hL hF hK hLok hd hs.char hz hs.bits hi)
      (fun h2 i hi => evalIntWith_eq_ite_of_bits hwf hI hL hF hK hLok hd h2 hz hs.bits hi)
      (fun _ i hi => intOf_eq_ite_of_leafIvl hwf hI hL hF hK hLok hbIv hi) ht
      (by rw [htB, decide_eq_true hs.char]; rfl)
      (hnc t ht fun _ _ _ _ _ _ => macTailAtB_not_cross htB)
  · obtain ⟨t, ht, htB⟩ := hs.tail
    have hc2 : ir.charOf (ir.domainField d) = 2 := by
      have h := htB
      unfold macTailTwoB at h
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
      exact h.1.2
    exact macFieldCheckFacts_named hwf hI hL hM e hd hlen hw0 hmf htag hs.blindField hs.blindSize
      (fun i hi => evalWith_bit_of_exprBitsB hwf hF hs.bits hi)
      (fun h2 => absurd hc2 (by omega)) (fun h2 => absurd hc2 (by omega)) ht
      (by rw [htB, Bool.or_true])
      (hnc t ht fun _ _ _ _ _ _ => macTailTwoB_not_cross htB)

/-- **The MAC's soundness, two-tail form, over the facts it reads**: the checks over the two
fields' facts (`MacFieldCheckFacts`); see `crossHolds_or_macBad_twoTail`. -/
theorem crossHolds_or_macBad_twoTail_named (hwf : ir.WellFormed) (hL : I.Lawful ir primeNodes)
    (e : ir.Env I) {pid dx : ℕ} {x : Expr} {dy : ℕ} {y : Expr} {k : CrossKind}
    {real : MacRealization} {bx b : ℕ} (hpid : pid < ir.predicates.length)
    (hb : (ir.predicate pid).body = .cross dx x dy y k real)
    (hbx : real.blindX = some bx) (hbl : real.blind = some b)
    (hok : ir.MacTwoCore pid x y k real)
    (hX : ir.MacFieldCheckFacts e dx x bx real) (hY : ir.MacFieldCheckFacts e dy y b real) :
    ir.HoldsWith (ir.reader e) (.cross dx x dy y k real) ∨
      (ir.macEvent e dx x dy y real).BadAt (castElt (e.chal real.key 0)) := by
  have hpoX := hwf.predicates _ (predicate_mem hpid)
  rw [hb] at hpoX
  have hxok := hpoX.1 (dx, x) (by simp [PredBody.exprs])
  have hyok := hpoX.1 (dy, y) (by simp [PredBody.exprs])
  obtain ⟨taps, hMF⟩ := hY.field
  obtain ⟨B, -, heB⟩ := hMF.basis
  rcases MacFieldCheckAt.binding hX.side hY.side with ⟨hch, -⟩ | hbad
  · exact .inl (crossHolds_of_chunksA hL (domainField_lt hwf hxok.1) (domainField_lt hwf hyok.1)
      hX.char hY.char hok.width hok.pos hok.lenX hok.lenY hX.bits hY.bits B.toMACBasis heB
      fun c => congrFun hch c)
  · right
    simp only [macEvent, hbx, hbl, Option.getD_some]
    exact hbad

/-- **The MAC's soundness, two-tail form** (compiler/mac.h, `mac_odd`): for a cross-field `equal`
whose MAC no domain hosts (`MacTwoTailOk`, blinds `bx` and `b`, the check over each field of odd
characteristic or of characteristic `2`, so every pair of characteristics), where the tails hold
(`hnc`: every predicate other than a cross-field `equal` holds), either the cross-field `equal`
holds (in the compiler's contract) or the key is a root of the MAC's binding polynomial
(`macEvent`). Each check's operand reads bits, and the check gives `T` as the masked MAC of its
operand with its blind (`macFieldCheckFacts_of_tailField`), and the two bind
(`MacFieldCheckAt.binding`). `hM` is a property of the model (`Interp.MacModel`). -/
theorem crossHolds_or_macBad_twoTail (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I)
    (hF : ir.LeafFacts (ir.reader e)) (hK : ir.ShiftFacts (ir.reader e)) {pid dx : ℕ} {x : Expr}
    {dy : ℕ} {y : Expr} {k : CrossKind} {real : MacRealization} {bx b : ℕ}
    (hpid : pid < ir.predicates.length) (hb : (ir.predicate pid).body = .cross dx x dy y k real)
    (hbx : real.blindX = some bx) (hbl : real.blind = some b)
    (hok : ir.MacTwoTailOk primeNodes pid dx x dy y k real bx b)
    (hnc : ∀ t < ir.predicates.length,
      (∀ dx' x' dy' y' k' real', (ir.predicate t).body ≠ .cross dx' x' dy' y' k' real') →
        ir.HoldsWith (ir.reader e) (ir.predicate t).body) :
    ir.HoldsWith (ir.reader e) (.cross dx x dy y k real) ∨
      (ir.macEvent e dx x dy y real).BadAt (castElt (e.chal real.key 0)) := by
  have hpoX := hwf.predicates _ (predicate_mem hpid)
  rw [hb] at hpoX
  have hxok := hpoX.1 (dx, x) (by simp [PredBody.exprs])
  have hyok := hpoX.1 (dy, y) (by simp [PredBody.exprs])
  obtain ⟨L, hLok, hsX, hsY⟩ := hok.ivls
  exact crossHolds_or_macBad_twoTail_named hwf hL e hpid hb hbx hbl hok.core
    (macFieldCheckFacts_of_tailField hwf hI hL hM e hF hK hLok hxok.1 hxok.2 hok.lenX hok.pos
      hok.field hok.tag hsX hnc)
    (macFieldCheckFacts_of_tailField hwf hI hL hM e hF hK hLok hyok.1 hyok.2 hok.lenY hok.pos
      hok.field hok.tag hsY hnc)

/-! ## The event's probability -/

/-- **One coordinate of a challenge of one coordinate drawn from the field** is uniform in the
field. -/
theorem probUniform_fullCoord {F : FieldInterp} {n : ℕ} (hn : n = 1) (h0 : 0 < n) {s : Sampler}
    (hs : s = .full) (P : F.K → Prop) :
    Pr[c ← (Fin n → F.SamplerTy s) : P (F.samplerVal s (c ⟨0, h0⟩))] = Pr[a ← F.K : P a] := by
  subst hn hs
  exact Uniform.probUniform_comp (f := fun c : Fin 1 → F.K => c ⟨0, h0⟩)
    (Uniform.of_equiv (Equiv.funUnique (Fin 1) F.K)) P

/-- **A uniform element read in an equal field identifier** is uniform there. -/
theorem probUniform_castElt {a b : ℕ} (h : a = b) (P : (I b).K → Prop) :
    Pr[x ← (I a).K : P (castElt x)] = Pr[y ← (I b).K : P y] := by
  subst h
  simp

/-- **The MAC event's probability over its key** (`macKeyB`: one coordinate, uniform in the MAC
field): an event of the MAC field fixed before the key (`macEvent` of an environment agreeing up to
the key) has its key coordinate as a root with probability at most its degree over `|K|`; for the
MAC's binding event the degree is `chunks`. -/
theorem probUniform_macBad_le {pid : ℕ} {real : MacRealization} (hk : ir.macKeyB pid real = true)
    (ev : ChallengeEvent (I real.macField).K) (e : ir.Env I) :
    Pr[c ← ir.ChalVal I real.key : ev.BadAt (castElt ((e.setChal real.key c).chal real.key 0))] ≤
      ((ev.deg / Fintype.card (I real.macField).K : ℝ≥0) : ℝ≥0∞) := by
  simp only [macKeyB, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hk
  obtain ⟨⟨⟨⟨-, hsz⟩, hsm⟩, hkf⟩, -⟩ := hk
  have h0 : 0 < (ir.challenge real.key).size := by rw [hsz]; omega
  simp only [setChal_chal_zero e _ h0]
  rw [probUniform_fullCoord hsz h0 hsm (fun a => ev.BadAt (castElt a)),
    probUniform_castElt hkf (fun a => ev.BadAt a)]
  exact ChallengeEvent.probUniform_badAt_le ev

/-- **The MAC's binding event has degree `chunks`.** -/
theorem macEvent_deg (e : ir.Env I) (dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr)
    (real : MacRealization) : (ir.macEvent e dx x dy y real).deg = real.chunks := by
  unfold macEvent
  split <;> rfl

end

end GordieHowe.RealizedProgram
