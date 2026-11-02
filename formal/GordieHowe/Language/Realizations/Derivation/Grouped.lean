-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Basic
public import GordieHoweNative.Language.Realizations.Derivation.Grouped

@[expose] public section

/-!
# GordieHowe: derivations, the grouped form of `mod_q`

`groupedMod rows ivs` concludes a `mod_q` in the grouped form (`holdsWith_mod_of_grouped_named`):
the left side `b + macConv(r)(y)` summed in groups of chunks, each group's residue with its quotient
digits, the final one-digit sum. Every fact it reads is named:
- `rows[g]`: group `g`'s accumulator row, of smaller rank, checked against the record
  (`groupRowCoreB`);
- `ivs[g]` (`g < #groups`): `ivl d E_g 0 groupBound`, `E_g` the row's convolution
  (`groupRowExpr?`);
- `ivs[#groups ..]`: `nat d residues Rb`, `nat d groupDigits Nd`, `nat d quotient N`,
  `ivl d (leaf blind) lo_b hi_b`, `ivl d e' lo' hi'`;
- the no-wrap conditions at those numbers.

The definitions are in `GordieHoweNative/Language/Realizations/Derivation/Grouped.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section Sound

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

theorem groupedNums_sound {rd : ir.Valuation I} {fs : List Fact}
    (hfs : ∀ f ∈ fs, f.HoldsWith ir rd) {d : ℕ} {E' : Expr} {G : GroupedMod} {u : MacUnits}
    {real : ModRealization} {rest : List ℕ} {Rb Nd N : ℕ} {lob hib lo' hi' : ℤ}
    (h : groupedNums fs d E' G u real rest = some (Rb, Nd, N, lob, hib, lo', hi')) :
    Fact.HoldsWith ir rd (.nat d G.residues Rb) ∧ Fact.HoldsWith ir rd (.nat d G.groupDigits Nd) ∧
      Fact.HoldsWith ir rd (.nat d real.quotExpr N) ∧
      Fact.HoldsWith ir rd (.ivl d (.leaf u.blind) lob hib) ∧
      Fact.HoldsWith ir rd (.ivl d E' lo' hi') := by
  unfold groupedNums at h
  split at h
  · rename_i ires idig iq ib irhs
    split at h
    · rename_i d1 R Rb' d2 D Nd' d3 Qx N' d4 B lob' hib' d5 Xr lo'' hi'' h1 h2 h3 h4 h5
      split_ifs at h with hc
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h
      obtain ⟨rfl, rfl, rfl, rfl, rfl, hR, hD, hQ, hB, hX⟩ := hc
      obtain rfl := Expr.eq_of_beq hR
      obtain rfl := Expr.eq_of_beq hD
      obtain rfl := Expr.eq_of_beq hQ
      obtain rfl := Expr.eq_of_beq hB
      obtain rfl := Expr.eq_of_beq hX
      exact ⟨hfs _ (List.mem_of_getElem? h1), hfs _ (List.mem_of_getElem? h2),
        hfs _ (List.mem_of_getElem? h3), hfs _ (List.mem_of_getElem? h4),
        hfs _ (List.mem_of_getElem? h5)⟩
    · cases h
  · cases h

/-- **`groupedFact_sound`**: the grouped form's rule is sound. -/
theorem groupedFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) {e : ir.Env I} {ctx : DerivCtx}
    {self pid : ℕ} {body : PredBody} (hown : ir.OwnBody pid body) (hc : CitesHold e ctx self)
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.Holds e) {rows ivs : List ℕ} {f : Fact}
    (hf : ir.groupedFact ctx self pid body fs rows ivs = some f) : f.Holds e := by
  unfold groupedFact at hf
  split at hf
  · rename_i d q E E' real
    rcases hown with ⟨hpid, hb⟩ | ⟨d', hd⟩
    swap
    · cases hd
    split at hf
    · rename_i G u hG hu
      split at hf
      · rename_i acc hA
        split at hf
        · rename_i Rb Nd N lob hib lo' hi' hnums
          split_ifs at hf with hcond
          cases hf
          obtain ⟨hform, hq, h2, hunits, hres, hfin, hrows, hlenQ, hgb, htail, hnw, hNw⟩ := hcond
          obtain ⟨hRf, hDf, hQf, hBf, hXf⟩ := groupedNums_sound hfs hnums
          have hpo := hwf.predicates _ (predicate_mem hpid)
          rw [hb] at hpo
          have hrw := fun g (hg : g < G.groups.length) =>
            List.all_eq_true.1 hrows g (List.mem_range.2 hg)
          show ir.HoldsWith (ir.reader e) (ir.predicate pid).body
          rw [hb]
          refine holdsWith_mod_of_grouped_named hwf hI hL e hpo hform hq h2 hu hunits hres hfin rows
            (fun g hg => ?_) (fun g hg => ?_) (fun g hg Eg hEg => ?_) hRf hDf
            (fun i hi => hQf i (lt_of_lt_of_le hi hlenQ)) hBf hXf hgb htail hnw hNw
          · have := hrw g hg
            simp only [Bool.and_eq_true, decide_eq_true_eq] at this
            exact this.1.2
          · have := hrw g hg
            simp only [Bool.and_eq_true, decide_eq_true_eq] at this
            exact hc.1 _ this.1.1.1 this.1.1.2
          · have := hrw g hg
            simp only [Bool.and_eq_true, decide_eq_true_eq] at this
            have h3 := this.2
            rw [hEg] at h3
            simp only [Option.any_eq_true] at h3
            obtain ⟨f', hf', hbeq⟩ := h3
            have hh := hfs _ (List.mem_of_getElem? hf')
            rw [Fact.eq_of_beq hbeq] at hh
            exact hh
        · cases hf
      · cases hf
    · cases hf
  · cases hf

end Sound

end GordieHowe.RealizedProgram
