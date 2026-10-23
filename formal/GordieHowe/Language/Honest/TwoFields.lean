-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Honest.Source

@[expose] public section

/-!
# GordieHowe: the honest strategy's MAC checks over the fields of characteristic `2`

When no domain hosts a MAC, the MAC check over one of its fields may lie in a domain of
characteristic `2` (`GordieHowe.RealizedProgram.MacTwoFieldOk`): its tail is the field `equal`
`b + macConv(r)(z) = bits(T)` (`macTailTwoB`), not a `mod_2`. Such a check has no generated value of
its own; its tail reads the tag through the target's bits.

* **The tail at the honest values** (`tailTwo_holds_of_honest`, the converse of
  `GordieHowe.RealizedProgram.macFieldCheckAt_of_two`): where the tag is the MAC of the chunks of
  the check's operand, the blind reads the bits of the tag's pad and the operand reads bits, the
  field computes each accumulator entry as the cast of the integer accumulator, whose parity is the
  target's bit (`MACRows.unpack_maskedMAC`), so the tail holds.
* **A MAC check over a field of characteristic `2` with its tail**: the cross-field
  `equal`, the check (`GordieHowe.RealizedProgram.MacFieldCheckTwo`), the tail and the facts its
  honest values need; its source facts and the tail at the honest environment.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

section

variable {ir : RealizedProgram} {I : Interp} {primeNodes : ℕ → List String}

/-! ## The tail of a MAC check over a field of characteristic `2` at the honest values -/

/-- **The tail of a MAC check over a field of characteristic `2` holds at the honest values** (the
converse of `macFieldCheckAt_of_two`): where the tag is the MAC of the chunks of the check's operand
(`hT`), the check's blind is the polynomial-basis bits of the tag's pad (`hbl`) and the check's
operand reads bits (`hzb`), each accumulator entry computed in the field of characteristic `2` is
the cast of the integer accumulator's parity, which is the target's bit
(`MACRows.unpack_maskedMAC`), so the tail's field `equal` holds. `hM` is a property of the model
(`Interp.MacModel`). -/
theorem tailTwo_holds_of_honest (hwf : ir.WellFormed) (hI : I.Registered ir)
    (hL : I.Lawful ir primeNodes) (hM : I.MacModel ir) (e : ir.Env I) {pid d b : ℕ} {z : Expr}
    {real : MacRealization} (hd : d < ir.domains.length)
    (hlen : ir.exprLen z = real.chunks * real.width) (hmf : real.macField < ir.fields.length)
    (htag : ir.macTagB real = true) (hbf : ir.valueField b = ir.domainField d)
    (hbsz : (ir.value b).size = real.width) {t : ℕ} (ht : t < ir.predicates.length)
    (htB : ir.macTailTwoB pid d z b real t = true)
    (hT : (castElt (ir.reader e real.tag 0) : (I real.macField).K) =
      ∑ c : Fin real.chunks, (castElt (e.chal real.key 0) : (I real.macField).K) ^ ((c : ℕ) + 1) *
        ir.macChunkA (ir.reader e) real.macField d z real.width c)
    (hbl : ∀ i < real.width, ir.reader e b i =
      if ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit i then 1 else 0)
    (hzb : ∀ i < ir.exprLen z, ir.evalWith (ir.reader e) d z i = 0 ∨
      ir.evalWith (ir.reader e) d z i = 1) :
    ir.HoldsWith (ir.reader e) (ir.predicate t).body := by
  have hdF := domainField_lt hwf hd
  have htag' := htag
  unfold macTagB at htag'
  simp only [Bool.and_eq_true, decide_eq_true_eq] at htag'
  obtain ⟨⟨⟨-, htagf⟩, -⟩, htk⟩ := htag'
  have htagk : (ir.value real.tag).kind = .late := by
    revert htk
    cases (ir.value real.tag).kind <;> simp
  have htB' := htB
  unfold macTailTwoB at htB'
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at htB'
  obtain ⟨⟨-, hc2⟩, htB'⟩ := htB'
  split at htB'
  · rename_i d' b' r w nch taps z' tb tgt hbt
    simp only [Bool.and_eq_true, beq_iff_eq] at htB'
    obtain ⟨⟨⟨⟨⟨⟨hd', hb'⟩, hw⟩, hnch⟩, hz'⟩, hpow⟩, htb⟩ := htB'
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
    set PH : (I real.macField).K := castElt (e.asg.pad real.tag 0) with hPH
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
    -- the blind reads the pad's bits
    have hbval : ∀ j : Fin real.width, ir.evalWith rd d (.leaf b) j =
        if ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit j then 1 else 0 := by
      intro j
      simp only [evalWith, evalE_leaf]
      rw [hbl j j.2]
      split_ifs
      · exact castElt_one_of_eq hbf
      · exact castElt_zero
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
    -- the masked MAC of the check's operand is the target
    have hmac : MACRows.maskedMAC B.toMACBasis β W = Tval := by
      have hpad : MAC.pack B.toMACBasis (fun j => if MACRows.pmac W j = 1 then 1 else 0) = PH := by
        conv_rhs => rw [← B.toMACBasis.pack_unpack PH]
        unfold MAC.pack
        refine Finset.sum_congr rfl fun j _ => ?_
        have hu : B.toMACBasis.unpack PH j =
            ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit j := by
          rw [hunp, hPH, toNat_castElt_of_eq htagf]
        dsimp only
        rw [show MACRows.pmac W j = ir.evalWith rd d (.leaf b) j from rfl, hbval j, hu]
        by_cases h : ((I (ir.valueField real.tag)).toNat (e.asg.pad real.tag 0)).testBit j = true
        · rw [if_pos h, if_pos rfl, if_pos h, one_mul]
        · rw [if_neg h, if_neg zero_ne_one, if_neg h, zero_mul]
      have hlate : rd real.tag 0 = e.late real.tag 0 := by rw [hrd, reader_of_late e htagk]
      unfold MACRows.maskedMAC MAC.sharedWitnessMAC MAC.ladder
      rw [hpad, hTv, castElt_add, ← hlate, hT, hPH]
      congr 1
      refine Finset.sum_congr rfl fun c _ => ?_
      dsimp only
      rw [mul_comm]
      congr 1
      simp only [macChunkA, MAC.pack]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [heB, mul_comm, evalPad_of_lt (by rw [hlen]; have := c.2; have := i.2; nlinarith)]
      rfl
    have hpar := MACRows.unpack_maskedMAC B β W
    rw [hmac] at hpar
    rw [hbt]
    intro m hm
    have hm' : m < real.width := by
      change m < (ir.value b).size at hm
      rwa [hbsz] at hm
    obtain ⟨bt, hbt2, hrdtb, hbtiff⟩ := reader_targetBits hwf hL e htb hd (by omega) htf m
    have htbv : ir.evalWith rd d (.leaf tb) m = (bt : (I (ir.domainField d)).K) := by
      have hev : ir.evalWith rd d (.leaf tb) m = castElt (rd tb m) := evalE_leaf _ _ _ _
      rw [hev, hrd, hrdtb, castElt_natCast (targetBitsB_field htb)]
    have hadd : ir.evalWith rd d (.add (.leaf b) (.apply (.macConv r real.width real.chunks taps)
        z)) m = ir.evalWith rd d (.leaf b) m + NamedOp.apply ir (ir.domainField d) rd
          (.macConv r real.width real.chunks taps) (ir.evalE rd (ir.domainField d) z) m := rfl
    rw [hadd, hconv ⟨m, hm'⟩, htbv]
    set A := MACRows.accumulatorNat taps.toFinset B.toMACBasis β W ⟨m, hm'⟩ with hA
    -- the blind's coordinate is the cast of its indicator
    have hbind : ir.evalWith rd d (.leaf b) m =
        (((if ir.evalWith rd d (.leaf b) m = 1 then 1 else 0 : ℕ)) : (I (ir.domainField d)).K) := by
      rw [hbval ⟨m, hm'⟩]
      split_ifs <;> simp_all
    have hAeq : A = (if ir.evalWith rd d (.leaf b) m = 1 then 1 else 0) + N ⟨m, hm'⟩ := by
      rw [hA]
      rfl
    have hp := congrFun hpar ⟨m, hm'⟩
    rw [hunp, hTv, toNat_castElt_of_eq htagf] at hp
    have hb' : bt = 1 ↔ A % 2 = 1 := by
      rw [hbtiff, hp, decide_eq_true_iff]
    have hbtA : bt = A % 2 := by
      rcases Nat.mod_two_eq_zero_or_one A with h0 | h1
      · rw [h0]
        rcases (by omega : bt = 0 ∨ bt = 1) with h | h
        · exact h
        · rw [hb'.1 h] at h0
          exact absurd h0 (by norm_num)
      · rw [h1]
        exact hb'.2 h1
    rw [hbind, ← Nat.cast_add, ← hAeq, hbtA, ← natCast_eq_mod_two]
  · cases htB'

/-! ## A cross-field `equal`'s bits agree where it holds -/

/-- **A coordinate of the `x` operand is `1` exactly where the `y` operand's is**, where the
cross-field `equal` `pid` holds on bits (`hcyb`: the `y` operand's coordinates are bits) and both
domains have characteristic above `1`. -/
theorem evalWith_eq_one_iff_of_cross {rd : ir.Valuation I} (hwf : ir.WellFormed)
    (hL : I.Lawful ir primeNodes) {pid dx cdy : ℕ} {x cy : Expr} {k : CrossKind}
    {real : MacRealization} (hpid : pid < ir.predicates.length)
    (hb : (ir.predicate pid).body = .cross dx x cdy cy k real) (hk : k.width = 1)
    (hcr : ir.HoldsWith rd (.cross dx x cdy cy k real))
    (hxb : ∀ i < ir.exprLen x, ir.evalWith rd dx x i = 0 ∨ ir.evalWith rd dx x i = 1)
    (hcx : 1 < ir.charOf (ir.domainField dx)) (hcy : 1 < ir.charOf (ir.domainField cdy))
    (hcyb : ∀ i < ir.exprLen x, ir.evalWith rd cdy cy i = 0 ∨ ir.evalWith rd cdy cy i = 1)
    {i : ℕ} (hi : i < ir.exprLen x) :
    ir.evalWith rd dx x i = 1 ↔ ir.evalWith rd cdy cy i = 1 := by
  have hpo := hwf.predicates _ (predicate_mem hpid)
  rw [hb] at hpo
  have hdxF := domainField_lt hwf (hpo.1 (dx, x) (by simp [PredBody.exprs])).1
  have hdyF := domainField_lt hwf (hpo.1 (cdy, cy) (by simp [PredBody.exprs])).1
  simp only [charOf] at hcx hcy
  have hone : ∀ {a : ℕ}, a < ir.fields.length → 1 < (ir.field a).characteristic →
      (I a).toNat 1 = 1 := fun ha h1 => by simpa using hL.toNat_natCast _ ha 1 h1
  have hzero : ∀ {a : ℕ}, a < ir.fields.length → 1 < (ir.field a).characteristic →
      (I a).toNat 0 = 0 := fun ha h1 => by simpa using hL.toNat_natCast _ ha 0 (by omega)
  have hxlt : ∀ i < ir.exprLen x, (I (ir.domainField dx)).toNat (ir.evalWith rd dx x i) <
      2 ^ k.width := by
    intro i hi
    rw [hk, pow_one]
    rcases hxb i hi with h | h <;> rw [h]
    · rw [hzero hdxF hcx]; norm_num
    · rw [hone hdxF hcx]; norm_num
  have heq := hcr.2 hxlt _ hi
  rcases hxb _ hi with hx | hx <;> rcases hcyb _ hi with hy | hy <;> rw [hx, hy] at heq ⊢
  · simp
  · rw [hzero hdxF hcx, hone hdyF hcy] at heq
    exact absurd heq (by norm_num)
  · rw [hone hdxF hcx, hzero hdyF hcy] at heq
    exact absurd heq (by norm_num)
  · simp

/-! ## A MAC check over a field of characteristic `2` with its tail -/

/-- **The domains `dx` and `dy` of a MAC's operands have characteristic above `1`.** -/
def MacChars (ir : RealizedProgram) (dx dy : ℕ) : Prop :=
  1 < ir.charOf (ir.domainField dx) ∧ 1 < ir.charOf (ir.domainField dy)

instance (ir : RealizedProgram) (dx dy : ℕ) : Decidable (MacChars ir dx dy) := by
  unfold MacChars; infer_instance

variable (ir primeNodes) in
/-- **A MAC check over a field of characteristic `2`, for a MAC no domain hosts** (`MacTwoCore`,
both operands' domains of characteristic above `1` (`MacChars`), the check `MacTwoFieldOk`), at
domain `sd`, operand `sz` and blind `sb`: the check over `x`'s field with the blind `blindX` or the check over `y`'s field with the blind `blind`. -/
def MacFieldCheckTwo (pid dx : ℕ) (x : Expr) (dy : ℕ) (y : Expr) (k : CrossKind) (real : MacRealization)
    (sd : ℕ) (sz : Expr) (sb : ℕ) : Prop :=
  (∃ b, real.blindX = some sb ∧ real.blind = some b ∧
      ir.MacTwoCore pid x y k real ∧ MacChars ir dx dy ∧
        ir.MacTwoFieldOk primeNodes pid dx x sb real ∧ sd = dx ∧ sz = x) ∨
    ∃ bx, real.blindX = some bx ∧ real.blind = some sb ∧
      ir.MacTwoCore pid x y k real ∧ MacChars ir dx dy ∧
        ir.MacTwoFieldOk primeNodes pid dy y sb real ∧ sd = dy ∧ sz = y

end

end GordieHowe.RealizedProgram
