-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.RealizeMac

@[expose] public section

/-!
# GordieHowe: the grouped form of `mod_q`, realized

The lemma that turns a `mod_q` in the grouped form (`GordieHowe.RealizedProgram.GroupedFormOk`; compiler/mod.h,
`kGrouped`) into its integer congruence (`GordieHowe.RealizedProgram.holdsWith_mod_of_grouped`). The left side
`b + macConv(r, w, nch, taps)(y)` reaches the characteristic `p`, so its chunks are summed in groups
(the paper's Section 4.1.3, Integer congruences: each group's residue modulo `q` with its own
quotient, then the sum of the residues):

* **The groups** (`GordieHowe.RealizedProgram.groupSum`): group `g` of chunks `[s, s + n)` has the accumulator row
  `acc[g w + i] = macConv(r_s, …, r_{s+n−1})(y_s, …)_i`; its integer reading `S_g` is the sum of the
  chunks' integer convolutions (`NamedOp.applyInt_macConv`, the powers' bits read through
  `GordieHowe.RealizedProgram.macRb_subPowers`), lies in `[0, smax]` with `smax < p` (the interval evaluator), and casts
  to the accumulator. The residue `r_g = acc_g − q · Σ_j T^j gq_j` is a natural `ρ < Rb` (Boolean
  for `q = 2`, else a direct `in`), the digits naturals below `N_d`; the tail `(Rb − 1) + q Q_max < p`
  lifts `S_g = ρ + q Q_g` to the integers (`IntLift.natCast_inj_of_lt`).
* **The tiling** (`sum_tiles`): the groups' chunk runs tile `[0, nch)`, so the left side's integer
  reading is the blind's plus `Σ_g S_g`.
* **The final sum** `b + Σ_g r_g`: the derived quotient `Q = q⁻¹ (fin − e')` (`finalQuotB`), its
  direct `in` and the no-wrap conditions give `fin − e' = q k` over the integers
  (`IntIn.sub_eq_natCast`), as in the one-digit form.

So `e − e' = q (k + Σ_g Q_g)`. No model fact beyond the lawful integer readings enters; the honest
prover needs no lemma (the group rows, the residues' checks and the digits' and quotient's `in`s are
predicates of the program, which the honest strategy's `sat` gives).
-/

namespace GordieHowe.RealizedProgram

open Export

namespace IndexMap

/-- **An index map of one run `[s, s + n)` reads `s + t` at `t < n`.** -/
theorem entry_of_runList {m : IndexMap} {s n : ℕ} (h : m.toList = RealizedProgram.runList s n) {t : ℕ}
    (ht : t < n) : m.entry t = s + t := by
  rw [entry_eq_getD_toList, h, RealizedProgram.runList, List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range ht]
  rfl

/-- **An index map of one run `[s, s + n)` has `n` entries.** -/
theorem size_of_runList {m : IndexMap} {s n : ℕ} (h : m.toList = RealizedProgram.runList s n) :
    m.size = n := by
  rw [← length_toList, h, RealizedProgram.runList, List.length_map, List.length_range]

end IndexMap

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String} {L : ℕ → ℕ → Option Ivl}

/-- **One step of dereferencing keeps an expression's integer values.** -/
theorem evalIntWith_deref (ho : ir.RefsOrdered) (rd : ir.Valuation I) (d : ℕ) (e : Expr) :
    ir.evalIntWith rd d (ir.deref e) = ir.evalIntWith rd d e := by
  cases e with
  | ref k =>
    simp only [deref]
    split_ifs with hk
    · exact (evalIntWith_ref ho rd d hk).symm
    · rfl
  | _ => rfl

/-! ## The powers of a group -/

/-- **The powers of a group read the powers' bits** (`subPowersB`): where `r` holds the key's powers
(`powersB`), the value `rg` holding `r_s, …, r_{s+n−1}` reads, at chunk `c < n`, the bits of
`r_{s+c}`. -/
theorem macRb_subPowers (hL : I.Lawful ir primeNodes) (e : ir.Env I) {r key nch f rg s n w : ℕ}
    (hf : f < ir.fields.length) (h2 : 1 < ir.charOf f) (hp : ir.powersB r key nch f = true)
    (hs : ir.subPowersB rg r s n = true) {c : ℕ} (hc : c < n) (hsc : s + c < nch) :
    NamedOp.macRb ir (ir.reader e) rg w c = NamedOp.macRb ir (ir.reader e) r w (s + c) := by
  unfold subPowersB at hs
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hs
  obtain ⟨⟨⟨hrg, hr⟩, hgf⟩, hs⟩ := hs
  have hrf : ir.valueField r = f := by
    unfold powersB at hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    exact hp.1.1.2
  split at hs
  · rename_i idx r' hk
    simp only [Bool.and_eq_true, beq_iff_eq] at hs
    obtain ⟨hr', hidx⟩ := hs
    subst r'
    -- `rg` and `r` are distinct values, so the program has at least two
    have hne : rg ≠ r := by
      rintro rfl
      unfold powersB at hp
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
      rw [hk] at hp
      simp at hp
    have hlen : 2 ≤ ir.values.length := by omega
    have hrd : ir.reader e rg c = castElt (ir.read e ir.values.length r (s + c)) := by
      rw [reader_of_pubExpr e hk, ← IndexMap.entry_of_runList hidx hc]
      rfl
    have hlow := read_powers hL e hf h2 hp (n := ir.values.length - 1) (by omega) hsc
    have hhigh := read_powers hL e hf h2 hp (n := ir.values.length) (by omega) hsc
    rw [Nat.sub_add_cancel (by omega)] at hlow
    have heq : ir.read e ir.values.length r (s + c) = ir.reader e r (s + c) := by
      rw [← castElt_inj_of_eq hrf, hlow]
      exact hhigh.symm
    funext j
    simp only [NamedOp.macRb, hrd, toNat_castElt_of_eq hgf.symm, heq]
  · cases hs

/-- **An expression with an interval within `[lo, hi]` is read within it and casts to its value**
(`exprIvl_within` from the shape and the shared expressions alone, as a subexpression has them). -/
theorem exprIvl_within_of_shape (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts rd sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d : ℕ}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) {e : Expr}
    (hs : ir.exprShapeOk e = true) (hr : ∀ k ∈ e.refs, k < ir.exprs.length) {lo hi : ℤ}
    (hw : IvlWithin (ir.exprIvl L (ir.domainField d) e) lo hi) {i : ℕ}
    (hie : i < ir.exprLen e) : (lo ≤ ir.evalIntWith rd d e i ∧ ir.evalIntWith rd d e i ≤ hi) ∧
      ((ir.evalIntWith rd d e i : ℤ) : (I (ir.domainField d)).K) = ir.evalWith rd d e i := by
  obtain ⟨hp, hchar, h01, hdec⟩ := modData hwf hI hL hd h2
  have htn := hL.toNat_natCast _ (domainField_lt hwf hd)
  unfold exprIvl at hw
  cases hJ : ir.ivlOf (ir.charOf (ir.domainField d)) (L (ir.domainField d))
      e
  · rw [hJ] at hw
    exact hw.elim
  rename_i J
  rw [hJ] at hw
  exact ⟨Ivl.mem_of_within hw (evalIntWith_mem_ivlOf hwf.exprs hp h01 htn
      (fun v J hJ => hLok.sound hwf hI hL (hF.ivlFacts hK) trivial hJ) hchar
      (fun v J hJ => hLok.cast hwf hI hL (hF.ivlFacts hK) trivial hJ) hdec
      (fun v J hJ => hLok.field hJ) hs hr hJ i hie),
    evalIntWith_cast hwf.exprs hp hchar h01 htn hdec
      (fun v J hJ => hLok.cast hwf hI hL (hF.ivlFacts hK) trivial hJ)
      (fun v J hJ => hLok.sound hwf hI hL (hF.ivlFacts hK) trivial hJ)
      (fun v J hJ => hLok.field hJ) hs hr hJ i hie⟩

/-- **Value `r` holds a MAC key's powers** (`macPowersB`): `powersB` at the key the public expression
reads. -/
theorem exists_powersB_of_macPowersB {r nch : ℕ} (h : ir.macPowersB r nch = true) :
    ∃ key, ir.powersB r key nch (ir.valueField r) = true := by
  unfold macPowersB at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨-, h⟩ := h
  split at h
  · split at h
    · exact ⟨_, h⟩
    · cases h
  · cases h

/-- **The integer convolution of chunk `c`** at output coordinate `i < w` of the MAC unit form
`macConv(r, w, nch, taps)(y)`: `Σ_j Conv(r_c)[i][j] · y[c w + j]` on the integers, the powers' bits
read by `rd` (`NamedOp.macRb`). -/
def chunkTerm (rd : ir.Valuation I) (d r w : ℕ) (taps : List ℕ) (y : Expr) (i c : ℕ) (hw : 0 < w) :
    ℤ :=
  ∑ j : Fin w, (Conv.matrix taps.toFinset (NamedOp.macRb ir rd r w c) ⟨i % w, Nat.mod_lt _ hw⟩ j : ℤ) *
    ir.evalIntWith rd d y (c * w + j)

/-- **The MAC unit form on the integers**: coordinate `i < w` of `b + macConv(r, w, nch, taps)(y)`
is the blind's integer reading plus the chunks' integer convolutions (`chunkTerm`), when
`2 w` is below the characteristic. -/
theorem evalIntWith_macUnits (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (rd : ir.Valuation I) {d : ℕ} (hd : d < ir.domains.length)
    (h2 : 2 < ir.charOf (ir.domainField d)) (u : MacUnits) (hw : 0 < u.width)
    (hcm : 2 * u.width < ir.charOf (ir.domainField d)) {i : ℕ}
    (hi : i < u.width) :
    ir.evalIntWith rd d (.add (.leaf u.blind) (.apply (.macConv u.powers u.width u.chunks u.taps)
      u.operand)) i =
      ir.intOf rd u.blind i + ∑ c ∈ Finset.range u.chunks,
        ir.chunkTerm rd d u.powers u.width u.taps u.operand i c hw := by
  obtain ⟨hpch, -, -, -⟩ := modData hwf hI hL hd h2
  have hev : ir.evalIntWith rd d (.add (.leaf u.blind) (.apply (.macConv u.powers u.width u.chunks
      u.taps) u.operand)) i = ir.intOf rd u.blind i + NamedOp.applyInt ir (ir.domainField d) rd
        (.macConv u.powers u.width u.chunks u.taps) (ir.evalIntWith rd d u.operand) i := rfl
  rw [hev, NamedOp.applyInt_macConv ir hpch (hL.toNat_natCast _ (domainField_lt hwf hd)) rd hw hcm]
  simp only [Nat.div_eq_of_lt hi, zero_mul, zero_add]
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

variable (ir) in
/-- **A group's accumulator row, without its interval** (`groupRowB` but the interval of its
convolution, which a derivation states as a fact). -/
def groupRowCoreB (d : ℕ) (u : MacUnits) (G : GroupedMod) (acc g : ℕ) (fc : ℕ × ℕ) (b : PredBody) :
    Bool :=
  match b with
  | .equal d' (.add (.reindex ia (.leaf acc')) (.scale (.const c)
      (.apply (.macConv rg w cnt taps) Yv))) (.leaf z) _ =>
    d' == d && acc' == acc && c + 1 == ir.charOf (ir.domainField d) && w == u.width &&
      cnt == fc.2 && taps == u.taps && ia.toList == runList (g * u.width) u.width &&
      ir.subPowersB rg u.powers (fc.1 - 1) fc.2 &&
      (match ir.deref Yv with
        | .reindex iy y' => y'.beq u.operand &&
          iy.toList == runList ((fc.1 - 1) * u.width) (fc.2 * u.width)
        | _ => false) &&
      ir.constAll z 0 u.width (ir.domainField d) &&
      decide (ir.exprLen (.apply (.macConv rg w cnt taps) Yv) = u.width) &&
      ir.exprShapeOk (.apply (.macConv rg w cnt taps) Yv) &&
      Yv.refs.all (· < ir.exprs.length)
  | _ => false

/-- **The convolution term of a group's accumulator row** `acc_view + c · E = z`. -/
def groupRowExpr? : PredBody → Option Expr
  | .equal _ (.add (.reindex _ (.leaf _)) (.scale (.const _) E)) (.leaf _) _ => some E
  | _ => none

/-- **A group's accumulator row on the integers** (`groupRowB`): where the row holds (a field
`equal`), the integer reading `S` of the group's convolution is the sum of the integer convolutions
of its chunks `[first − 1, first − 1 + count)` (`chunkTerm`; the group's powers are the unit form's,
`macRb_subPowers`), lies in `[0, smax]` (the interval evaluator) and casts to the group's
accumulator `acc[g w + i]`. -/
theorem groupSum (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    (e : ir.Env I) (hF : ir.LeafFacts (ir.reader e)) {sr : List (ℕ × ℕ)}
    (hK : ir.ShiftFacts (ir.reader e) sr) (hLok : ir.LeafIvlsOk primeNodes sr L) {d acc g : ℕ}
    {u : MacUnits}
    {G : GroupedMod} {fc : ℕ × ℕ} {b : PredBody} (hd : d < ir.domains.length)
    (h2 : 2 < ir.charOf (ir.domainField d)) (hw : 0 < u.width)
    (hpow : ir.macPowersB u.powers u.chunks = true)
    (hcm : 2 * u.width < ir.charOf (ir.domainField d))
    (hfit : fc.1 - 1 + fc.2 ≤ u.chunks) (hrow : ir.groupRowB L d u G acc g fc b = true)
    (hH : ir.HoldsWith (ir.reader e) b) {i : ℕ} (hi : i < u.width) :
    ∃ S : ℤ, S = ∑ c ∈ Finset.range fc.2,
        ir.chunkTerm (ir.reader e) d u.powers u.width u.taps u.operand i (fc.1 - 1 + c) hw ∧
      0 ≤ S ∧ S ≤ G.groupBound ∧
      ((S : ℤ) : (I (ir.domainField d)).K) = castElt (ir.reader e acc (g * u.width + i)) := by
  obtain ⟨hpch, hcharF, h01, hdec⟩ := modData hwf hI hL hd h2
  have hdF := domainField_lt hwf hd
  obtain ⟨key, hkey⟩ := exists_powersB_of_macPowersB hpow
  have hpow' := hpow
  unfold macPowersB at hpow'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpow'
  obtain ⟨⟨hrfl, hr1⟩, -⟩ := hpow'
  unfold groupRowB at hrow
  split at hrow
  · rename_i d' ia acc' c rg w' cnt taps' ys z tgt
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrow
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd', hacc⟩, hc⟩, hw'⟩, hcnt⟩, htaps⟩, hia⟩, hsub⟩, hY⟩, hz⟩, hlenE⟩,
      hsE⟩, hrE⟩, hivl⟩ := hrow
    subst d' acc' w' cnt taps'
    split at hY
    · rename_i iy y' hderef
      simp only [Bool.and_eq_true, beq_iff_eq] at hY
      obtain ⟨hy', hiy⟩ := hY
      have hy'' := Expr.eq_of_beq hy'
      subst hy''
      set rd := ir.reader e with hrd
      set Eg : Expr := .apply (.macConv rg u.width fc.2 u.taps) ys with hEg
      have hrE' : ∀ k ∈ Eg.refs, k < ir.exprs.length := by
        simpa [Expr.refs, hEg, List.all_eq_true] using hrE
      obtain ⟨⟨hS0, hS1⟩, hScast⟩ := exprIvl_within_of_shape hwf hI hL hF hK hLok hd h2 hsE hrE'
        hivl
        (by rw [hlenE]; exact hi)
      refine ⟨ir.evalIntWith rd d Eg i, ?_, hS0, hS1, ?_⟩
      · -- the chunks of the group
        have hev : ir.evalIntWith rd d Eg i = NamedOp.applyInt ir (ir.domainField d) rd
            (.macConv rg u.width fc.2 u.taps) (ir.evalIntWith rd d ys) i := rfl
        rw [hev, NamedOp.applyInt_macConv ir hpch (hL.toNat_natCast _ hdF) rd hw hcm]
        simp only [Nat.div_eq_of_lt hi, zero_mul, zero_add]
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun c' _ => ?_
        simp only [chunkTerm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hlt : (c' : ℕ) * u.width + j < fc.2 * u.width := by
          have := c'.2
          have := j.2
          nlinarith
        rw [macRb_subPowers hL e (hrfl) (hr1) hkey hsub c'.2 (by omega),
          ← evalIntWith_deref hwf.refsOrdered rd d ys, hderef]
        change _ * ir.evalIntWith rd d _ (iy.entry _) = _
        rw [IndexMap.entry_of_runList hiy hlt]
        congr 2
        ring
      · -- the accumulator row
        have hlenL : i < ir.exprLen (.add (.reindex ia (.leaf acc)) (.scale (.const c) Eg)) := by
          change i < ia.size
          rw [IndexMap.size_of_runList hia]
          exact hi
        have hrow := hH i hlenL
        simp only [evalWith, evalE_add, evalE_scale_const] at hrow
        rw [evalE_leaf_constAll hL hF hz hdF (by omega) hi] at hrow
        have hre : ir.evalE rd (ir.domainField d) (.reindex ia (.leaf acc)) i =
            castElt (rd acc (g * u.width + i)) := by
          change castElt (rd acc (ia.entry i)) = _
          rw [IndexMap.entry_of_runList hia hi]
        rw [hre, hdec c (by omega)] at hrow
        have hc1 : ((c : ℕ) : (I (ir.domainField d)).K) = -1 := by
          have : ((c + 1 : ℕ) : (I (ir.domainField d)).K) = 0 := by
            rw [hc]
            exact CharP.cast_eq_zero _ _
          push_cast at this
          linear_combination this
        rw [hc1, Nat.cast_zero] at hrow
        rw [hScast]
        simp only [evalWith]
        linear_combination -hrow
    · cases hY
  · cases hrow

/-! ## The residues -/

/-- **`k` digits below `N` in base `T` make a number at most `Σ_j T^j (N − 1)`** (`groupQuotMax`). -/
theorem sum_digits_le {K : Type} [CommSemiring K] {T N : ℕ} :
    ∀ (k : ℕ) (x : ℕ → K), (∀ l < k, ∃ δ < N, x l = (δ : K)) →
      ∃ Q ≤ groupQuotMax T k N, ∑ l : Fin k, (T : K) ^ (l : ℕ) * x l = (Q : K)
  | 0, _, _ => ⟨0, Nat.zero_le _, by simp⟩
  | k + 1, x, h => by
    obtain ⟨δ, hδ, hx0⟩ := h 0 (Nat.succ_pos k)
    obtain ⟨Q, hQ, hQv⟩ := sum_digits_le (T := T) (N := N) k (fun l => x (l + 1)) fun l hl =>
      h (l + 1) (by omega)
    refine ⟨δ + T * Q, ?_, ?_⟩
    · simp only [groupQuotMax, List.replicate_succ, digitsMax] at hQ ⊢
      have := Nat.mul_le_mul_left T hQ
      omega
    · rw [Fin.sum_univ_succ]
      simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_succ, pow_succ]
      rw [hx0]
      have : ∑ l : Fin k, (T : K) ^ (l : ℕ) * T * x (l + 1) =
          T * ∑ l : Fin k, (T : K) ^ (l : ℕ) * x (l + 1) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
      rw [this, hQv]
      push_cast
      ring

/-- **A batch of numbers from their digits** along the last axis: output coordinate `j` below the
batch's length is `Σ_l T^l x[j k + l]`. -/
theorem NamedOp.apply_batched_fromDigits (ir : RealizedProgram) {f : ℕ} (leaf : ir.Valuation I)
    {bb k T : ℕ} (x : ℕ → (I f).K) {j : ℕ} (hj : j < bb) :
    NamedOp.apply ir f leaf (.batched bb (.fromDigits k T)) x j =
      ∑ l : Fin k, (I f).decode T ^ (l : ℕ) * x (j * k + l) := by
  simp [NamedOp.apply, NamedOp.block, NamedOp.rows, NamedOp.cols, Ops.fromDigits,
    Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj, hj, Nat.mod_one]

/-- **A residue is a small natural and the accumulator its residue plus `q` times the digits**
(`residuesB`, `residueBound`): under the leaf facts, at coordinate `j` of the residues, the
residue `r_j = acc_j − q · Σ_l T^l gq[j k + l]` is the cast of a natural `ρ < Rb` (a Boolean check
for `Rb = 2`, else a direct `in`), the digits naturals below `N_d` (a direct `in`), so
`acc_j = ρ + q Q` with `Q ≤ Σ_l T^l (N_d − 1)`. -/
theorem residue_eq (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d q acc : ℕ} {u : MacUnits} {G : GroupedMod}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) (hq : 0 < q)
    (hres : ir.residuesB d q u G acc = true) {Nd : ℕ}
    (hNd : ir.exprRange d G.groupDigits = some Nd) {Rb : ℕ}
    (hRb : ir.residueBound d G.residues = some Rb) {j : ℕ} (hj : j < G.groups.length * u.width) :
    ∃ ρ Q : ℕ, ρ < Rb ∧ Q ≤ groupQuotMax G.base G.digitCount Nd ∧
      ir.evalWith rd d G.residues j = (ρ : (I (ir.domainField d)).K) ∧
      (castElt (rd acc j) : (I (ir.domainField d)).K) = ρ + q * Q := by
  obtain ⟨-, hcharF, -, hdec⟩ := modData hwf hI hL hd h2
  unfold residuesB at hres
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hres
  obtain ⟨⟨⟨⟨⟨hacc, haccf⟩, haccs⟩, hRlen⟩, hRrefs⟩, hres⟩ := hres
  split at hres
  · rename_i acc' c bb k T gq' gq hR hgd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hacc', hgq'⟩, hc⟩, hbb⟩, hk⟩, hT⟩, hTp⟩, hgql⟩, hgqf⟩, hgqs⟩ := hres
    subst acc' gq' bb k T
    -- the residue's value
    have hRv : ir.evalWith rd d G.residues j = castElt (rd acc j) - (q : (I (ir.domainField d)).K) *
        ∑ l : Fin G.digitCount, (G.base : (I (ir.domainField d)).K) ^ (l : ℕ) *
          ir.evalWith rd d (.leaf gq) (j * G.digitCount + l) := by
      simp only [evalWith]
      rw [← evalE_deref hwf.refsOrdered, hR]
      change castElt (rd acc j) + (I (ir.domainField d)).decode c *
        NamedOp.apply ir (ir.domainField d) rd (.batched (G.groups.length * u.width)
          (.fromDigits G.digitCount G.base)) (ir.evalE rd (ir.domainField d) (.leaf gq)) j = _
      rw [NamedOp.apply_batched_fromDigits ir rd _ hj, hdec c (by omega), hdec G.base hTp]
      have hcq : ((c : ℕ) : (I (ir.domainField d)).K) = -(q : (I (ir.domainField d)).K) := by
        have : ((c + q : ℕ) : (I (ir.domainField d)).K) = 0 := by
          rw [hc]
          exact CharP.cast_eq_zero _ _
        push_cast at this
        linear_combination this
      rw [hcq]
      ring
    -- the digits
    obtain ⟨Q, hQ, hQv⟩ := sum_digits_le (T := G.base) (N := Nd) G.digitCount
      (fun l => ir.evalWith rd d (.leaf gq) (j * G.digitCount + l)) fun l hl => by
        refine exprRange_sound hF (hgd ▸ hNd) ?_
        change j * G.digitCount + l < (ir.value gq).size
        rw [hgqs]
        have : j * G.digitCount + l < (j + 1) * G.digitCount := by nlinarith
        calc j * G.digitCount + l < (j + 1) * G.digitCount := this
          _ ≤ G.groups.length * u.width * G.digitCount := Nat.mul_le_mul_right _ hj
    -- the residue's bound
    have hρ : ∃ ρ < Rb, ir.evalWith rd d G.residues j = (ρ : (I (ir.domainField d)).K) := by
      unfold residueBound at hRb
      split_ifs at hRb with hb
      · cases hRb
        obtain ⟨pr, hpr, hpb⟩ := List.any_eq_true.1 hb
        obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hpr
        split at hpb
        · rename_i d' R₁ R₂ R₃ tgt hbody
          simp only [Bool.and_eq_true, beq_iff_eq] at hpb
          obtain ⟨⟨⟨hd', h1⟩, h2'⟩, h3⟩ := hpb
          subst d'
          have hH := hF.equals pid hpid (by rw [hbody]; rfl)
          rw [hbody, Expr.eq_of_beq h1, Expr.eq_of_beq h2', Expr.eq_of_beq h3] at hH
          have hx := hH j (by
            change j < ir.exprLen G.residues
            rw [hRlen]
            exact hj)
          simp only [evalWith] at hx
          change ir.evalE rd _ G.residues j * ir.evalE rd _ G.residues j = _ at hx
          have hx' : ir.evalE rd (ir.domainField d) G.residues j *
              (ir.evalE rd (ir.domainField d) G.residues j - 1) = 0 := by
            linear_combination hx
          rcases mul_eq_zero.1 hx' with h0 | h1'
          · exact ⟨0, by norm_num, by simp only [evalWith, h0, Nat.cast_zero]⟩
          · exact ⟨1, by norm_num, by
              simp only [evalWith, Nat.cast_one]
              linear_combination h1'⟩
        · cases hpb
      · exact (exprRange_sound hF hRb (by rw [hRlen]; exact hj)).imp fun _ h => h
    obtain ⟨ρ, hρRb, hρv⟩ := hρ
    refine ⟨ρ, Q, hρRb, hQ, hρv, ?_⟩
    rw [hρv, hQv] at hRv
    linear_combination -hRv
  · cases hres

/-! ## The final sum -/

/-- **The final sum's value** (`finSumB`): at a coordinate `i < w`,
`a · (b_i + Σ_{j<g} R[j w + i])`. -/
theorem evalE_finSum {a b w : ℕ} {R : Expr} (rd : ir.Valuation I) (f : ℕ) {i : ℕ} (hi : i < w) :
    ∀ (g : ℕ) (F : Expr), finSumB a b R w g F = true →
      ir.evalE rd f F i = (I f).decode a * (castElt (rd b i) +
        ∑ j ∈ Finset.range g, ir.evalE rd f R (j * w + i))
  | 0, F, h => by
    simp only [finSumB, finHeadB] at h
    split at h
    · rename_i a' b'
      simp only [Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [evalE_scale_const, evalE_leaf]
    · cases h
  | g + 1, F, h => by
    simp only [finSumB] at h
    split at h
    · rename_i F' t
      simp only [Bool.and_eq_true] at h
      obtain ⟨ht, hF'⟩ := h
      unfold finTermB at ht
      split at ht
      · rename_i a' ia R'
        simp only [Bool.and_eq_true, beq_iff_eq] at ht
        obtain ⟨⟨rfl, hR⟩, hia⟩ := ht
        rw [evalE_add, evalE_scale_const, evalE_finSum rd f hi g F' hF', Finset.sum_range_succ,
          ← Expr.eq_of_beq hR]
        have : ir.evalE rd f (.reindex ia R') i = ir.evalE rd f R' (g * w + i) := by
          change ir.evalE rd f R' (ia.entry i) = _
          rw [IndexMap.entry_of_runList hia hi]
        rw [this]
        ring
      · cases ht
    · cases h

/-- **A direct `in` on an expression bounds it** (`digitRangeOf`): under the leaf facts, at a
coordinate below the left side's length, the expression is the cast of a natural below the bound. -/
theorem exists_lt_of_digitRangeOf {rd : ir.Valuation I} (hF : ir.LeafFacts rd) {d : ℕ} {e D : Expr}
    {rid N : ℕ} (h : ir.digitRangeOf d e D rid = some N) {i : ℕ} (hi : i < ir.exprLen e) :
    ∃ k < N, ir.evalWith rd d D i = k := by
  unfold digitRangeOf at h
  split_ifs at h with hr
  split at h
  · rename_i d' D' N' r' hbody
    split_ifs at h with hc
    cases h
    obtain ⟨rfl, hk, hb, hlen, -⟩ := hc
    have hH := hF.directs rid hr _ _ _ _ hbody hk
    rw [hbody] at hH
    obtain ⟨k, hkN, hkv⟩ := hH i (by simpa [hlen] using hi) _ (List.mem_singleton_self _)
    rw [Expr.eq_of_beq hb] at hkv
    exact ⟨k, hkN, hkv⟩
  · cases h

/-! ## The grouped form -/

/-- **A sum over a list's map is the sum over its indices.** -/
theorem list_sum_map_eq_sum_range {α M : Type*} [AddCommMonoid M] [Inhabited α] (φ : α → M) :
    ∀ l : List α, (l.map φ).sum = ∑ g ∈ Finset.range l.length, φ (l.getD g default)
  | [] => by simp
  | a :: l => by
    rw [List.map_cons, List.sum_cons, list_sum_map_eq_sum_range φ l, List.length_cons,
      Finset.sum_range_succ']
    simp [add_comm]

/-- **The MAC unit form is its units' expression** (`macUnits?`). -/
theorem eq_of_macUnits? {E : Expr} {u : MacUnits} (h : macUnits? E = some u) :
    E = .add (.leaf u.blind) (.apply (.macConv u.powers u.width u.chunks u.taps) u.operand) := by
  unfold macUnits? at h
  split at h
  · cases h
    rfl
  · cases h

/-- **An accumulator row is a field `equal`** (`groupRowB`). -/
theorem isEqual_of_groupRowB {d acc g : ℕ} {u : MacUnits} {G : GroupedMod} {fc : ℕ × ℕ}
    {b : PredBody} (h : ir.groupRowB L d u G acc g fc b = true) : b.isEqual = true := by
  unfold groupRowB at h
  split at h
  · rfl
  · cases h

/-- **A `mod_q` in the grouped form holds** (`GroupedFormOk`; see the module docstring): under the
leaf facts, every group's integer sum is its residue plus `q` times its quotient (`groupSum`,
`residue_eq`, the group bound and the tail below `p`), the groups tile the chunks (`sum_tiles`), and
the final sum `b + Σ_g r_g` is congruent to the right side by the one-digit form's argument, so
`q` divides `e − e'` over the integers. -/
theorem holdsWith_mod_of_grouped (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (e : ir.Env I) (hF : ir.LeafFacts (ir.reader e))
    {sr : List (ℕ × ℕ)} (hK : ir.ShiftFacts (ir.reader e) sr) (hLok : ir.LeafIvlsOk primeNodes sr L)
    {d q : ℕ}
    {E E' : Expr} {real : ModRealization} (hpo : ir.PredOk (.mod d q E E' real))
    (hok : ir.GroupedFormOk L d q E E' real) :
    ir.HoldsWith (ir.reader e) (.mod d q E E' real) := by
  obtain ⟨hex, hlen⟩ := hpo
  have hE := hex (d, E) (by simp [PredBody.exprs])
  have hE' := hex (d, E') (by simp [PredBody.exprs])
  have hd := hE.1
  have hdF := domainField_lt hwf hd
  have h2 := hok.char
  obtain ⟨hpch, hcharF, h01, hdec⟩ := modData hwf hI hL hd h2
  have hshape := hok.shape
  have hbounds := hok.bounds
  unfold groupedShapeB at hshape
  unfold groupedBoundsB at hbounds
  cases hG : real.grouped with
  | none =>
    rw [hG] at hshape
    cases hshape
  | some G =>
  cases hu : macUnits? E with
  | none =>
    rw [hG, hu] at hshape
    cases hshape
  | some u =>
  rw [hG, hu] at hshape hbounds
  dsimp only at hshape hbounds
  split at hshape
  · rename_i acc hA
    simp only [Bool.and_eq_true, List.all_eq_true, List.any_eq_true, List.mem_range] at hshape
    obtain ⟨⟨⟨hunits, hrows⟩, hres⟩, hfin⟩ := hshape
    split at hbounds
    · rename_i Rb Nd Jb hRb hNd hJb
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at hbounds
      obtain ⟨⟨⟨hgb, htail⟩, hnw⟩, rid, hrid, hQr⟩ := hbounds
      obtain rfl := eq_of_macUnits? hu
      -- the units
      unfold macUnitsOkB at hunits
      simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hunits
      obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpw, hbl⟩, hbf⟩, hbs⟩, hw0⟩, hyl⟩, hcmB⟩, hfirst⟩, htile⟩ := hunits
      split at hcmB
      · simp only [decide_eq_true_eq] at hcmB
        have hcm : 2 * u.width < ir.charOf (ir.domainField d) := hcmB
        set rd := ir.reader e with hrd
        set ng := G.groups.length with hng
        intro i hi
        have hiw : i < u.width := by
          change i < (ir.value u.blind).size at hi
          rw [hbs] at hi
          exact hi
        -- the left side on the integers, by groups
        have hEint := evalIntWith_macUnits hwf hI hL rd hd h2 u hw0 hcm hiw
        rw [Finset.range_eq_Ico, sum_tiles _ htile, GroupedMod.chunkRuns, List.map_map,
          list_sum_map_eq_sum_range] at hEint
        -- every group: its sum is its residue plus `q` times its quotient
        have hgrp : ∀ g, ∃ ρ Q : ℕ, g < ng → ρ < Rb ∧
            ir.evalWith rd d G.residues (g * u.width + i) = (ρ : (I (ir.domainField d)).K) ∧
            ∑ c ∈ Finset.range (G.groups.getD g default).2,
                ir.chunkTerm rd d u.powers u.width u.taps u.operand i
                  ((G.groups.getD g default).1 - 1 + c) hw0 = ρ + q * Q := by
          intro g
          by_cases hg : g < ng
          · obtain ⟨pr, hpr, hrow⟩ := hrows g hg
            obtain ⟨pid, hpid, rfl⟩ := exists_index_of_mem hpr
            have hH := hF.equals pid hpid (isEqual_of_groupRowB hrow)
            have hmem : G.groups.getD g default ∈ G.groups := by
              rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg, Option.getD_some]
              exact List.getElem_mem _
            have hfit := (tiles_bound htile _ (List.mem_map_of_mem hmem)).2
            obtain ⟨S, hS, hS0, hS1, hSc⟩ := groupSum hwf hI hL e hF hK hLok hd h2 hw0 hpw hcm hfit
              hrow hH hiw
            have hj : g * u.width + i < ng * u.width := by nlinarith
            obtain ⟨ρ, Q, hρ, hQ, hρv, hacc⟩ := residue_eq hwf hI hL hF hd h2 hok.qpos hres hNd hRb hj
            refine ⟨ρ, Q, fun _ => ⟨hρ, hρv, ?_⟩⟩
            rw [← hS]
            have hlt : ρ + q * Q < ir.charOf (ir.domainField d) := by
              have := Nat.mul_le_mul_left q hQ
              omega
            have hSn : S = (S.toNat : ℤ) := (Int.toNat_of_nonneg hS0).symm
            have hcast : ((S.toNat : ℕ) : (I (ir.domainField d)).K) = ((ρ + q * Q : ℕ) : _) := by
              rw [← Int.cast_natCast, ← hSn, hSc, hacc]
              push_cast
              ring
            have := IntLift.natCast_inj_of_lt (K := (I (ir.domainField d)).K)
              (p := ir.charOf (ir.domainField d)) (by omega) hlt hcast
            rw [hSn, this]
            push_cast
            ring
          · exact ⟨0, 0, fun h => absurd h hg⟩
        choose ρ Q hρ using hgrp
        have hsumS : ∑ g ∈ Finset.range ng, ∑ c ∈ Finset.range (G.groups.getD g default).2,
            ir.chunkTerm rd d u.powers u.width u.taps u.operand i
              ((G.groups.getD g default).1 - 1 + c) hw0 =
            ∑ g ∈ Finset.range ng, ((ρ g : ℤ) + q * Q g) := by
          refine Finset.sum_congr rfl fun g hg => ?_
          exact (hρ g (Finset.mem_range.1 hg)).2.2
        simp only [Function.comp_apply] at hEint
        rw [hsumS] at hEint
        -- the final sum
        unfold finalQuotB at hfin
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
        obtain ⟨-, hfin⟩ := hfin
        split at hfin
        · rename_i F cq e₂ hQe
          split at hfin
          · rename_i a hca
            simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
            obtain ⟨⟨⟨⟨⟨hFs, he₂⟩, ha⟩, hcq⟩, hqa⟩, hqc⟩ := hfin
            have hQf : ir.evalWith rd d real.quotExpr i =
                (a : (I (ir.domainField d)).K) * (castElt (rd u.blind i) +
                  ∑ g ∈ Finset.range ng, (ρ g : (I (ir.domainField d)).K)) +
                  (cq : (I (ir.domainField d)).K) * ir.evalWith rd d E' i := by
              simp only [evalWith]
              rw [← evalE_deref hwf.refsOrdered, hQe, evalE_add, evalE_scale_const,
                evalE_finSum rd _ hiw ng F hFs, Expr.eq_of_beq he₂, hdec a ha, hdec cq hcq]
              congr 3
              refine Finset.sum_congr rfl fun g hg => ?_
              exact (hρ g (Finset.mem_range.1 hg)).2.1
            have hqa' : (q : (I (ir.domainField d)).K) * a = 1 := by
              rw [← Nat.cast_mul, CharP.cast_eq_mod (I (ir.domainField d)).K
                (ir.charOf (ir.domainField d)), hqa, Nat.cast_one]
            have hqc' : (q : (I (ir.domainField d)).K) * cq + 1 = 0 := by
              rw [← Nat.cast_mul, ← Nat.cast_one, ← Nat.cast_add,
                CharP.cast_eq_mod (I (ir.domainField d)).K (ir.charOf (ir.domainField d)), hqc,
                Nat.cast_zero]
            -- the final quotient's direct `in`
            obtain ⟨rid, hrid, hQr⟩ : ∃ rid ∈ real.ranges, ∃ N,
                ir.digitRangeOf d (.add (.leaf u.blind)
                  (.apply (.macConv u.powers u.width u.chunks u.taps) u.operand))
                  real.quotExpr rid = some N ∧
                ((q * (N - 1) : ℕ) : ℤ) + real.rhsHi - Jb.lo < ir.charOf (ir.domainField d) := by
              refine ⟨rid, hrid, ?_⟩
              split at hQr
              · rename_i N hN
                exact ⟨N, hN, of_decide_eq_true hQr⟩
              · cases hQr
            obtain ⟨N, hN, hNw⟩ := hQr
            obtain ⟨kQ, hkQ, hkQv⟩ := exists_lt_of_digitRangeOf hF hN hi
            -- the blind and the right side on the integers
            have hJb' : L (ir.domainField d) u.blind = some Jb := by
              simpa [exprIvl, ivlOf, Expr.ivl] using hJb
            have hbJ := hLok.sound hwf hI hL (hF.ivlFacts hK) trivial hJb' i hi
            have hbc := hLok.cast hwf hI hL (hF.ivlFacts hK) trivial hJb' i hi
            obtain ⟨⟨hr0, hr1⟩, hrc⟩ := exprIvl_within hwf hI hL hF hK hLok hd h2 hE'.2 hok.rhs
              (hlen ▸ hi)
            have hρle : ∑ g ∈ Finset.range ng, (ρ g : ℤ) ≤ ((ng * (Rb - 1) : ℕ) : ℤ) := by
              have : ∑ g ∈ Finset.range ng, (ρ g : ℤ) ≤ ∑ _g ∈ Finset.range ng, ((Rb - 1 : ℕ) : ℤ) :=
                Finset.sum_le_sum fun g hg => by
                  have := (hρ g (Finset.mem_range.1 hg)).1
                  omega
              simpa using this
            have hρ0 : 0 ≤ ∑ g ∈ Finset.range ng, (ρ g : ℤ) :=
              Finset.sum_nonneg fun g _ => Int.natCast_nonneg _
            have hz : IntIn (Jb.lo - real.rhsHi) (Jb.hi + ((ng * (Rb - 1) : ℕ) : ℤ) - real.rhsLo)
                (ir.intOf rd u.blind i + ∑ g ∈ Finset.range ng, (ρ g : ℤ) - ir.evalIntWith rd d E' i)
                ((castElt (rd u.blind i) + ∑ g ∈ Finset.range ng, (ρ g : (I (ir.domainField d)).K)) -
                  ir.evalWith rd d E' i) :=
              ⟨by linarith [hbJ.1], by linarith [hbJ.2], by push_cast; rw [hbc, hrc]⟩
            have hlift := IntIn.sub_eq_natCast (p := ir.charOf (ir.domainField d)) (c := 0)
              (n := q * kQ) (M := q * (N - 1) + 1) hz (by simpa using hnw)
              (by push_cast [Nat.cast_add] at hNw ⊢; linarith)
              (Nat.lt_succ_of_le (Nat.mul_le_mul_left q (by omega))) (by
                rw [Int.cast_zero, sub_zero, Nat.cast_mul, ← hkQv]
                linear_combination (-(q : (I (ir.domainField d)).K)) * hQf -
                  (castElt (rd u.blind i) + ∑ g ∈ Finset.range ng, (ρ g : (I (ir.domainField d)).K)) *
                    hqa' - ir.evalWith rd d E' i * hqc')
            refine ⟨kQ + ∑ g ∈ Finset.range ng, (Q g : ℤ), ?_⟩
            rw [hEint, Finset.sum_add_distrib, ← Finset.mul_sum]
            push_cast at hlift
            linarith
          · cases hfin
        · cases hfin
      · simp at hcmB
    · cases hbounds
  · cases hshape

/-! ## The grouped form over named facts -/

/-- **`groupSum_named`**: `groupSum` with the group's interval a stated fact. -/
theorem groupSum_named (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    (e : ir.Env I) {d acc g : ℕ}
    {u : MacUnits}
    {G : GroupedMod} {fc : ℕ × ℕ} {b : PredBody} (hd : d < ir.domains.length)
    (h2 : 2 < ir.charOf (ir.domainField d)) (hw : 0 < u.width)
    (hpow : ir.macPowersB u.powers u.chunks = true)
    (hcm : 2 * u.width < ir.charOf (ir.domainField d))
    (hfit : fc.1 - 1 + fc.2 ≤ u.chunks) (hrow : ir.groupRowCoreB d u G acc g fc b = true)
    (hH : ir.HoldsWith (ir.reader e) b)
    (hEg : ∀ Eg, groupRowExpr? b = some Eg → ∀ i < ir.exprLen Eg,
      0 ≤ ir.evalIntWith (ir.reader e) d Eg i ∧ ir.evalIntWith (ir.reader e) d Eg i ≤ G.groupBound ∧
        ((ir.evalIntWith (ir.reader e) d Eg i : ℤ) : (I (ir.domainField d)).K) =
          ir.evalWith (ir.reader e) d Eg i)
    {i : ℕ} (hi : i < u.width) :
    ∃ S : ℤ, S = ∑ c ∈ Finset.range fc.2,
        ir.chunkTerm (ir.reader e) d u.powers u.width u.taps u.operand i (fc.1 - 1 + c) hw ∧
      0 ≤ S ∧ S ≤ G.groupBound ∧
      ((S : ℤ) : (I (ir.domainField d)).K) = castElt (ir.reader e acc (g * u.width + i)) := by
  obtain ⟨hpch, hcharF, h01, hdec⟩ := modData hwf hI hL hd h2
  have hdF := domainField_lt hwf hd
  obtain ⟨key, hkey⟩ := exists_powersB_of_macPowersB hpow
  have hpow' := hpow
  unfold macPowersB at hpow'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hpow'
  obtain ⟨⟨hrfl, hr1⟩, -⟩ := hpow'
  unfold groupRowCoreB at hrow
  split at hrow
  · rename_i d' ia acc' c rg w' cnt taps' ys z tgt
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hrow
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hd', hacc⟩, hc⟩, hw'⟩, hcnt⟩, htaps⟩, hia⟩, hsub⟩, hY⟩, hz⟩, hlenE⟩,
      hsE⟩, hrE⟩ := hrow
    subst d' acc' w' cnt taps'
    split at hY
    · rename_i iy y' hderef
      simp only [Bool.and_eq_true, beq_iff_eq] at hY
      obtain ⟨hy', hiy⟩ := hY
      have hy'' := Expr.eq_of_beq hy'
      subst hy''
      set rd := ir.reader e with hrd
      set Eg : Expr := .apply (.macConv rg u.width fc.2 u.taps) ys with hEgdef
      have hrE' : ∀ k ∈ Eg.refs, k < ir.exprs.length := by
        simpa [Expr.refs, hEgdef, List.all_eq_true] using hrE
      obtain ⟨hS0, hS1, hScast⟩ := hEg Eg rfl i (by rw [hlenE]; exact hi)
      refine ⟨ir.evalIntWith rd d Eg i, ?_, hS0, hS1, ?_⟩
      · -- the chunks of the group
        have hev : ir.evalIntWith rd d Eg i = NamedOp.applyInt ir (ir.domainField d) rd
            (.macConv rg u.width fc.2 u.taps) (ir.evalIntWith rd d ys) i := rfl
        rw [hev, NamedOp.applyInt_macConv ir hpch (hL.toNat_natCast _ hdF) rd hw hcm]
        simp only [Nat.div_eq_of_lt hi, zero_mul, zero_add]
        rw [← Fin.sum_univ_eq_sum_range]
        refine Finset.sum_congr rfl fun c' _ => ?_
        simp only [chunkTerm]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hlt : (c' : ℕ) * u.width + j < fc.2 * u.width := by
          have := c'.2
          have := j.2
          nlinarith
        rw [macRb_subPowers hL e (hrfl) (hr1) hkey hsub c'.2 (by omega),
          ← evalIntWith_deref hwf.refsOrdered rd d ys, hderef]
        change _ * ir.evalIntWith rd d _ (iy.entry _) = _
        rw [IndexMap.entry_of_runList hiy hlt]
        congr 2
        ring
      · -- the accumulator row
        have hlenL : i < ir.exprLen (.add (.reindex ia (.leaf acc)) (.scale (.const c) Eg)) := by
          change i < ia.size
          rw [IndexMap.size_of_runList hia]
          exact hi
        have hrow := hH i hlenL
        simp only [evalWith, evalE_add, evalE_scale_const] at hrow
        rw [evalE_leaf_constAll_of hL (fun _ _ hk j => reader_of_constant e hk j) hz hdF (by omega)
          hi] at hrow
        have hre : ir.evalE rd (ir.domainField d) (.reindex ia (.leaf acc)) i =
            castElt (rd acc (g * u.width + i)) := by
          change castElt (rd acc (ia.entry i)) = _
          rw [IndexMap.entry_of_runList hia hi]
        rw [hre, hdec c (by omega)] at hrow
        have hc1 : ((c : ℕ) : (I (ir.domainField d)).K) = -1 := by
          have : ((c + 1 : ℕ) : (I (ir.domainField d)).K) = 0 := by
            rw [hc]
            exact CharP.cast_eq_zero _ _
          push_cast at this
          linear_combination this
        rw [hc1, Nat.cast_zero] at hrow
        rw [hScast]
        simp only [evalWith]
        linear_combination -hrow
    · cases hY
  · cases hrow

/-! ## The residues -/

theorem residue_eq_named (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    {rd : ir.Valuation I} {d q acc : ℕ} {u : MacUnits} {G : GroupedMod}
    (hd : d < ir.domains.length) (h2 : 2 < ir.charOf (ir.domainField d)) (hq : 0 < q)
    (hres : ir.residuesB d q u G acc = true) {Nd : ℕ}
    (hdig : ∀ j < ir.exprLen G.groupDigits, Range.IsNatBelow Nd (ir.evalWith rd d G.groupDigits j))
    {Rb : ℕ} (hρall : ∀ j < ir.exprLen G.residues, Range.IsNatBelow Rb (ir.evalWith rd d G.residues j))
    {j : ℕ} (hj : j < G.groups.length * u.width) :
    ∃ ρ Q : ℕ, ρ < Rb ∧ Q ≤ groupQuotMax G.base G.digitCount Nd ∧
      ir.evalWith rd d G.residues j = (ρ : (I (ir.domainField d)).K) ∧
      (castElt (rd acc j) : (I (ir.domainField d)).K) = ρ + q * Q := by
  obtain ⟨-, hcharF, -, hdec⟩ := modData hwf hI hL hd h2
  unfold residuesB at hres
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hres
  obtain ⟨⟨⟨⟨⟨hacc, haccf⟩, haccs⟩, hRlen⟩, hRrefs⟩, hres⟩ := hres
  split at hres
  · rename_i acc' c bb k T gq' gq hR hgd
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hres
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hacc', hgq'⟩, hc⟩, hbb⟩, hk⟩, hT⟩, hTp⟩, hgql⟩, hgqf⟩, hgqs⟩ := hres
    subst acc' gq' bb k T
    -- the residue's value
    have hRv : ir.evalWith rd d G.residues j = castElt (rd acc j) - (q : (I (ir.domainField d)).K) *
        ∑ l : Fin G.digitCount, (G.base : (I (ir.domainField d)).K) ^ (l : ℕ) *
          ir.evalWith rd d (.leaf gq) (j * G.digitCount + l) := by
      simp only [evalWith]
      rw [← evalE_deref hwf.refsOrdered, hR]
      change castElt (rd acc j) + (I (ir.domainField d)).decode c *
        NamedOp.apply ir (ir.domainField d) rd (.batched (G.groups.length * u.width)
          (.fromDigits G.digitCount G.base)) (ir.evalE rd (ir.domainField d) (.leaf gq)) j = _
      rw [NamedOp.apply_batched_fromDigits ir rd _ hj, hdec c (by omega), hdec G.base hTp]
      have hcq : ((c : ℕ) : (I (ir.domainField d)).K) = -(q : (I (ir.domainField d)).K) := by
        have : ((c + q : ℕ) : (I (ir.domainField d)).K) = 0 := by
          rw [hc]
          exact CharP.cast_eq_zero _ _
        push_cast at this
        linear_combination this
      rw [hcq]
      ring
    -- the digits
    obtain ⟨Q, hQ, hQv⟩ := sum_digits_le (T := G.base) (N := Nd) G.digitCount
      (fun l => ir.evalWith rd d (.leaf gq) (j * G.digitCount + l)) fun l hl => by
        have hlt : j * G.digitCount + l < ir.exprLen G.groupDigits := by
          rw [hgd]
          change j * G.digitCount + l < (ir.value gq).size
          rw [hgqs]
          have : j * G.digitCount + l < (j + 1) * G.digitCount := by nlinarith
          calc j * G.digitCount + l < (j + 1) * G.digitCount := this
            _ ≤ G.groups.length * u.width * G.digitCount := Nat.mul_le_mul_right _ hj
        obtain ⟨k, hk, hv⟩ := hdig _ hlt
        rw [hgd] at hv
        exact ⟨k, hk, hv.symm⟩
    obtain ⟨ρ, hρRb, hρv⟩ : ∃ ρ < Rb, ir.evalWith rd d G.residues j = (ρ : (I (ir.domainField d)).K) := by
      obtain ⟨ρ, hρ, hv⟩ := hρall j (by rw [hRlen]; exact hj)
      exact ⟨ρ, hρ, hv.symm⟩
    refine ⟨ρ, Q, hρRb, hQ, hρv, ?_⟩
    rw [hρv, hQv] at hRv
    linear_combination -hRv
  · cases hres

/-! ## The final sum -/

/-- **The grouped form over the facts it reads** (`holdsWith_mod_of_grouped` with every fact
named): the rows holding, each group's convolution within `[0, groupBound]`, the residues, digits and
final quotient below their bounds, the blind's and the right side's intervals, and the no-wrap
conditions at those numbers. -/
theorem holdsWith_mod_of_grouped_named (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (e : ir.Env I) {d q : ℕ} {E E' : Expr} {real : ModRealization}
    (hpo : ir.PredOk (.mod d q E E' real)) (hq : 0 < q) (h2 : 2 < ir.charOf (ir.domainField d))
    {G : GroupedMod} {u : MacUnits} {acc : ℕ} (hu : macUnits? E = some u)
    (hunits : ir.macUnitsOkB d u G = true) (hres : ir.residuesB d q u G acc = true)
    (hfin : ir.finalQuotB d q E' u G real = true) (rows : List ℕ)
    (hrowsB : ∀ g < G.groups.length, ir.groupRowCoreB d u G acc g (G.groups.getD g default)
      (ir.predicate (rows.getD g 0)).body = true)
    (hrowsH : ∀ g < G.groups.length,
      ir.HoldsWith (ir.reader e) (ir.predicate (rows.getD g 0)).body)
    (hEg : ∀ g < G.groups.length, ∀ Eg, groupRowExpr? (ir.predicate (rows.getD g 0)).body = some Eg →
      ∀ i < ir.exprLen Eg, 0 ≤ ir.evalIntWith (ir.reader e) d Eg i ∧
        ir.evalIntWith (ir.reader e) d Eg i ≤ G.groupBound ∧
        ((ir.evalIntWith (ir.reader e) d Eg i : ℤ) : (I (ir.domainField d)).K) =
          ir.evalWith (ir.reader e) d Eg i)
    {Rb Nd N : ℕ}
    (hρall : ∀ j < ir.exprLen G.residues,
      Range.IsNatBelow Rb (ir.evalWith (ir.reader e) d G.residues j))
    (hdig : ∀ j < ir.exprLen G.groupDigits,
      Range.IsNatBelow Nd (ir.evalWith (ir.reader e) d G.groupDigits j))
    (hQ : ∀ i < ir.exprLen E, Range.IsNatBelow N (ir.evalWith (ir.reader e) d real.quotExpr i))
    {lob hib lo' hi' : ℤ}
    (hbI : ∀ i < (ir.value u.blind).size, lob ≤ ir.intOf (ir.reader e) u.blind i ∧
      ir.intOf (ir.reader e) u.blind i ≤ hib ∧
      ((ir.intOf (ir.reader e) u.blind i : ℤ) : (I (ir.domainField d)).K) =
        castElt (ir.reader e u.blind i))
    (hrI : ∀ i < ir.exprLen E', lo' ≤ ir.evalIntWith (ir.reader e) d E' i ∧
      ir.evalIntWith (ir.reader e) d E' i ≤ hi' ∧
      ((ir.evalIntWith (ir.reader e) d E' i : ℤ) : (I (ir.domainField d)).K) =
        ir.evalWith (ir.reader e) d E' i)
    (hgb : G.groupBound < ir.charOf (ir.domainField d))
    (htail : Rb - 1 + q * groupQuotMax G.base G.digitCount Nd < ir.charOf (ir.domainField d))
    (hnw : hib + ((G.groups.length * (Rb - 1) : ℕ) : ℤ) - lo' < ir.charOf (ir.domainField d))
    (hNw : ((q * (N - 1) : ℕ) : ℤ) + hi' - lob < ir.charOf (ir.domainField d)) :
    ir.HoldsWith (ir.reader e) (.mod d q E E' real) := by
  obtain ⟨hex, hlen⟩ := hpo
  have hE := hex (d, E) (by simp [PredBody.exprs])
  have hE' := hex (d, E') (by simp [PredBody.exprs])
  have hd := hE.1
  have hdF := domainField_lt hwf hd
  obtain ⟨hpch, hcharF, h01, hdec⟩ := modData hwf hI hL hd h2
  obtain rfl := eq_of_macUnits? hu
  -- the units
  unfold macUnitsOkB at hunits
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hunits
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hpw, hbl⟩, hbf⟩, hbs⟩, hw0⟩, hyl⟩, hcmB⟩, hfirst⟩, htile⟩ := hunits
  split at hcmB
  · simp only [decide_eq_true_eq] at hcmB
    have hcm : 2 * u.width < ir.charOf (ir.domainField d) := hcmB
    set rd := ir.reader e with hrd
    set ng := G.groups.length with hng
    intro i hi
    have hiw : i < u.width := by
      change i < (ir.value u.blind).size at hi
      rw [hbs] at hi
      exact hi
    -- the left side on the integers, by groups
    have hEint := evalIntWith_macUnits hwf hI hL rd hd h2 u hw0 hcm hiw
    rw [Finset.range_eq_Ico, sum_tiles _ htile, GroupedMod.chunkRuns, List.map_map,
      list_sum_map_eq_sum_range] at hEint
    -- every group: its sum is its residue plus `q` times its quotient
    have hgrp : ∀ g, ∃ ρ Q : ℕ, g < ng → ρ < Rb ∧
        ir.evalWith rd d G.residues (g * u.width + i) = (ρ : (I (ir.domainField d)).K) ∧
        ∑ c ∈ Finset.range (G.groups.getD g default).2,
            ir.chunkTerm rd d u.powers u.width u.taps u.operand i
              ((G.groups.getD g default).1 - 1 + c) hw0 = ρ + q * Q := by
      intro g
      by_cases hg : g < ng
      · have hrow := hrowsB g hg
        have hH := hrowsH g hg
        have hmem : G.groups.getD g default ∈ G.groups := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hg, Option.getD_some]
          exact List.getElem_mem _
        have hfit := (tiles_bound htile _ (List.mem_map_of_mem hmem)).2
        obtain ⟨S, hS, hS0, hS1, hSc⟩ := groupSum_named hwf hI hL e hd h2 hw0 hpw hcm hfit
          hrow hH (hEg g hg) hiw
        have hj : g * u.width + i < ng * u.width := by nlinarith
        obtain ⟨ρ, Q, hρ, hQ, hρv, hacc⟩ := residue_eq_named hwf hI hL hd h2 hq hres hdig hρall hj
        refine ⟨ρ, Q, fun _ => ⟨hρ, hρv, ?_⟩⟩
        rw [← hS]
        have hlt : ρ + q * Q < ir.charOf (ir.domainField d) := by
          have := Nat.mul_le_mul_left q hQ
          omega
        have hSn : S = (S.toNat : ℤ) := (Int.toNat_of_nonneg hS0).symm
        have hcast : ((S.toNat : ℕ) : (I (ir.domainField d)).K) = ((ρ + q * Q : ℕ) : _) := by
          rw [← Int.cast_natCast, ← hSn, hSc, hacc]
          push_cast
          ring
        have := IntLift.natCast_inj_of_lt (K := (I (ir.domainField d)).K)
          (p := ir.charOf (ir.domainField d)) (by omega) hlt hcast
        rw [hSn, this]
        push_cast
        ring
      · exact ⟨0, 0, fun h => absurd h hg⟩
    choose ρ Q hρ using hgrp
    have hsumS : ∑ g ∈ Finset.range ng, ∑ c ∈ Finset.range (G.groups.getD g default).2,
        ir.chunkTerm rd d u.powers u.width u.taps u.operand i
          ((G.groups.getD g default).1 - 1 + c) hw0 =
        ∑ g ∈ Finset.range ng, ((ρ g : ℤ) + q * Q g) := by
      refine Finset.sum_congr rfl fun g hg => ?_
      exact (hρ g (Finset.mem_range.1 hg)).2.2
    simp only [Function.comp_apply] at hEint
    rw [hsumS] at hEint
    -- the final sum
    unfold finalQuotB at hfin
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
    obtain ⟨-, hfin⟩ := hfin
    split at hfin
    · rename_i F cq e₂ hQe
      split at hfin
      · rename_i a hca
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hfin
        obtain ⟨⟨⟨⟨⟨hFs, he₂⟩, ha⟩, hcq⟩, hqa⟩, hqc⟩ := hfin
        have hQf : ir.evalWith rd d real.quotExpr i =
            (a : (I (ir.domainField d)).K) * (castElt (rd u.blind i) +
              ∑ g ∈ Finset.range ng, (ρ g : (I (ir.domainField d)).K)) +
              (cq : (I (ir.domainField d)).K) * ir.evalWith rd d E' i := by
          simp only [evalWith]
          rw [← evalE_deref hwf.refsOrdered, hQe, evalE_add, evalE_scale_const,
            evalE_finSum rd _ hiw ng F hFs, Expr.eq_of_beq he₂, hdec a ha, hdec cq hcq]
          congr 3
          refine Finset.sum_congr rfl fun g hg => ?_
          exact (hρ g (Finset.mem_range.1 hg)).2.1
        have hqa' : (q : (I (ir.domainField d)).K) * a = 1 := by
          rw [← Nat.cast_mul, CharP.cast_eq_mod (I (ir.domainField d)).K
            (ir.charOf (ir.domainField d)), hqa, Nat.cast_one]
        have hqc' : (q : (I (ir.domainField d)).K) * cq + 1 = 0 := by
          rw [← Nat.cast_mul, ← Nat.cast_one, ← Nat.cast_add,
            CharP.cast_eq_mod (I (ir.domainField d)).K (ir.charOf (ir.domainField d)), hqc,
            Nat.cast_zero]
        obtain ⟨kQ, hkQ, hkQv⟩ : ∃ k < N, ir.evalWith rd d real.quotExpr i = k := by
          obtain ⟨k, hk, hv⟩ := hQ i hi
          exact ⟨k, hk, hv.symm⟩
        -- the blind and the right side on the integers
        obtain ⟨hb0, hb1, hbc⟩ := hbI i hi
        obtain ⟨hr0, hr1, hrc⟩ := hrI i (hlen ▸ hi)
        have hρle : ∑ g ∈ Finset.range ng, (ρ g : ℤ) ≤ ((ng * (Rb - 1) : ℕ) : ℤ) := by
          have : ∑ g ∈ Finset.range ng, (ρ g : ℤ) ≤ ∑ _g ∈ Finset.range ng, ((Rb - 1 : ℕ) : ℤ) :=
            Finset.sum_le_sum fun g hg => by
              have := (hρ g (Finset.mem_range.1 hg)).1
              omega
          simpa using this
        have hρ0 : 0 ≤ ∑ g ∈ Finset.range ng, (ρ g : ℤ) :=
          Finset.sum_nonneg fun g _ => Int.natCast_nonneg _
        have hz : IntIn (lob - hi') (hib + ((ng * (Rb - 1) : ℕ) : ℤ) - lo')
            (ir.intOf rd u.blind i + ∑ g ∈ Finset.range ng, (ρ g : ℤ) - ir.evalIntWith rd d E' i)
            ((castElt (rd u.blind i) + ∑ g ∈ Finset.range ng, (ρ g : (I (ir.domainField d)).K)) -
              ir.evalWith rd d E' i) :=
          ⟨by linarith, by linarith, by push_cast; rw [hbc, hrc]⟩
        have hlift := IntIn.sub_eq_natCast (p := ir.charOf (ir.domainField d)) (c := 0)
          (n := q * kQ) (M := q * (N - 1) + 1) hz (by simpa using hnw)
          (by push_cast [Nat.cast_add] at hNw ⊢; linarith)
          (Nat.lt_succ_of_le (Nat.mul_le_mul_left q (by omega))) (by
            rw [Int.cast_zero, sub_zero, Nat.cast_mul, ← hkQv]
            linear_combination (-(q : (I (ir.domainField d)).K)) * hQf -
              (castElt (rd u.blind i) + ∑ g ∈ Finset.range ng, (ρ g : (I (ir.domainField d)).K)) *
                hqa' - ir.evalWith rd d E' i * hqc')
        refine ⟨kQ + ∑ g ∈ Finset.range ng, (Q g : ℤ), ?_⟩
        rw [hEint, Finset.sum_add_distrib, ← Finset.mul_sum]
        push_cast at hlift
        linarith
      · cases hfin
    · cases hfin
  · simp at hcmB

end

end GordieHowe.RealizedProgram
