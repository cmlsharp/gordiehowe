-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Derivation.Basic
public import GordieHoweNative.Language.Realizations.Derivation.Mac

@[expose] public section

/-!
# GordieHowe: derivations, the MAC rule

`mac ts h ivs` concludes a cross-field `equal` (`crossHolds_or_macBad_named`,
`crossHolds_or_macBad_twoTail_named`) from the facts the MAC's soundness reads, all named:
- the MAC's interval-free shape (`macHostedCoreB`, `macTwoCoreB`: key, tag, lengths, reads before
  the key, field) and its blinds' fields and sizes;
- its tail predicates `ts`, cited by rank (`[t]` hosted, `[tx, ty]` two-tail), each checked
  against the MAC record (`macTailB`; per field `macTailAtB` at odd characteristic or
  `macTailTwoB` at characteristic `2`);
- its H predicate `h`, cited by rank, equal to the record's;
- the facts `ivs` (`[iy, ib]` hosted, `[ix, ibx, iy, ib]` two-tail): each operand and blind read
  within `[0, 1]` (`ivl d e 0 1`).

The definitions are in `GordieHoweNative/Language/Realizations/Derivation/Mac.lean`
(the compiled library `GordieHoweNative`); this module has their lemmas.
-/

namespace GordieHowe.RealizedProgram

open Export Range IOP

section Sound

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

theorem bitsAtB_sound {rd : ir.Valuation I} {fs : List Fact} (hfs : ∀ f ∈ fs, f.HoldsWith ir rd)
    {k d : ℕ} {e : Expr} (h : bitsAtB fs k d e = true) : Bits01 ir rd d e := by
  unfold bitsAtB at h
  split at h
  · rename_i f hk
    have := hfs _ (List.mem_of_getElem? hk)
    rw [Fact.eq_of_beq h] at this
    intro i hi
    obtain ⟨h0, h1, hc⟩ := this i hi
    exact ⟨h0, h1, hc⟩
  · cases h

/-- **The blind of a check over a field** is a value of its field of the MAC's width. -/
theorem MacTailFieldOk.blind {L : ℕ → ℕ → Option Ivl} {pid d b : ℕ} {z : Expr}
    {real : MacRealization} (h : ir.MacTailFieldOk primeNodes L pid d z b real) :
    ir.valueField b = ir.domainField d ∧ (ir.value b).size = real.width := by
  rcases h with h | h
  · have hb := h.blind
    unfold macBlindAtB at hb
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
    exact ⟨hb.1.1.2, hb.1.2⟩
  · exact ⟨h.blindField, h.blindSize⟩

/-- **`macFact_sound`**: the MAC rule is sound, its cross-field `equal` holds or its key is bad. -/
theorem macFact_sound (hwf : ir.WellFormed) (hI : I.Registered ir) (hL : I.Lawful ir primeNodes)
    (hM : I.MacModel ir) {e : ir.Env I} (h : ir.RealizedAt e) {ctx : DerivCtx} {self pid : ℕ}
    {body : PredBody} (hown : ir.OwnBody pid body) (hc : CitesHold e ctx self)
    {fs : List Fact} (hfs : ∀ f ∈ fs, f.Holds e) {ts : List ℕ} {hp : Option ℕ} {ivs : List ℕ}
    {f : Fact} (hf : ir.macFact primeNodes ctx self pid body fs ts hp ivs = some f) :
    f.Holds e ∨ ∃ j, ir.RealEvent j e := by
  unfold macFact at hf
  split at hf
  · rename_i dx x dy y k real
    rcases hown with ⟨hpid, hb⟩ | ⟨d, hd⟩
    swap
    · cases hd
    split_ifs at hf with hhc
    have hpoX := hwf.predicates _ (predicate_mem hpid)
    rw [hb] at hpoX
    have hxok := hpoX.1 (dx, x) (by simp [PredBody.exprs])
    have hyok := hpoX.1 (dy, y) (by simp [PredBody.exprs])
    have hHp : ∀ p, real.hPredicate = some p → ir.HoldsWith (ir.reader e) (ir.predicate p).body := by
      intro p hpp
      unfold macHCiteB at hhc
      rw [hpp] at hhc
      cases hh : hp with
      | none =>
        rw [hh] at hhc
        cases hhc
      | some q =>
        rw [hh] at hhc
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hhc
        obtain ⟨⟨hpq, hq⟩, hr⟩ := hhc
        subst hpq
        exact hc.1 p hq hr
    have hevent : ir.HoldsWith (ir.reader e) (.cross dx x dy y k real) ∨
        (ir.macEvent e dx x dy y real).BadAt (castElt (e.chal real.key 0)) →
          (Fact.holds pid).Holds e ∨ ∃ j, ir.RealEvent j e := by
      intro hres
      rcases hres with hres | hbad
      · refine .inl ?_
        show ir.HoldsWith (ir.reader e) (ir.predicate pid).body
        rw [hb]
        exact hres
      · exact .inr ⟨real.key, .inr ⟨pid, hpid, dx, x, dy, y, k, real, hb, rfl, hbad⟩⟩
    split at hf
    · rename_i b t iy ib hbx hbl
      split_ifs at hf with hcond
      obtain ⟨hcore, hbf, hbsz, ht, hrt, htB, hiy, hib⟩ := hcond
      cases hf
      have hb01 := bitsAtB_sound hfs hib
      apply hevent
      refine crossHolds_or_macBad_named hwf hI hL hM e hpid hb (MacHostedCore.of_B hcore) hbl hbf
        hbsz (bitsAtB_sound hfs hiy)
        (fun i hi => hb01.leaf_ite hi) ht htB (hc.1 t ht hrt)
        (fun hn => h.macH _ (predicate_mem hpid) _ _ _ _ _ _ hb hn hbx) hHp
    · rename_i bx b tx ty ix ibx iy ib hbx hbl
      split_ifs at hf with hcond
      obtain ⟨hcore, hbxf, hbxs, hbf, hbs, htx, hrx, hty, hry, htxB, htyB, hix, hibx, hiy, hib⟩ :=
        hcond
      cases hf
      have hmac := MacTwoCore.of_B hcore
      have hx01 := bitsAtB_sound hfs hix
      have hbx01 := bitsAtB_sound hfs hibx
      have hy01 := bitsAtB_sound hfs hiy
      have hb01 := bitsAtB_sound hfs hib
      apply hevent
      exact crossHolds_or_macBad_twoTail_named hwf hL e hpid hb hbx hbl hmac
        (macFieldCheckFacts_named hwf hI hL hM e hxok.1 hmac.lenX hmac.pos hmac.field hmac.tag
          hbxf hbxs (fun i hi => hx01.bit hi) (fun _ i hi => hx01.ite hi)
          (fun _ i hi => hbx01.leaf_ite hi) htx htxB (hc.1 tx htx hrx))
        (macFieldCheckFacts_named hwf hI hL hM e hyok.1 hmac.lenY hmac.pos hmac.field hmac.tag
          hbf hbs (fun i hi => hy01.bit hi) (fun _ i hi => hy01.ite hi)
          (fun _ i hi => hb01.leaf_ite hi) hty htyB (hc.1 ty hty hry))
    · cases hf
  · cases hf

end Sound

end GordieHowe.RealizedProgram
