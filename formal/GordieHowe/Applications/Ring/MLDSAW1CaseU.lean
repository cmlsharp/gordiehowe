-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseSplitSide
public import GordieHowe.Applications.Ring.KeyFreeCanon

@[expose] public section

/-!
# Case U of a key-free forgery of the ML-DSA ring publishing `w₁`: the goals and the readout

The goals of the case split of the key-free chain (`RingSignature.KeyFree.kfChain_le`) at
the ML-DSA ring publishing `w₁`, made on the canonical extracted witness
(`RingSignature.KeyFree.kfCanon`), and the forgery read from it. The readout of the key-free forger
sees neither the key coins nor the base component, so the case of the member's listed hash is
decided on a witness the readout can name: the first extracted witness of `w1ExpRel` with an
honest member.

- `w1Honest`, `w1Ok`: the honest member of a witness, and the test of the canonical witness.
- `w1Goal`: the goal at the chain (`Goal` of `kfChain_le` at `side := w1Side`), and
  `w1Goal_of`: it holds at every checked fresh witness of `w1ExpRel` (`hgoal`).
- `w1CaseU`, `w1CaseS`: the member's listed hash is the hash at `ω`, or a logged signing request
  programmed it; `w1Goal_split`: the goal at one witness gives one of them at every witness passing
  `w1Ok` (`hsplit` of `forgerWinsKF_canon`).
- `w1Readout`: the forgery read from a canonical witness; `bverify_w1Readout`: in case U it
  verifies at every oracle with base component `ω`; `honest_w1Readout`: its key is an uncorrupted
  user's.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section CaseU

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p prims Msg N reps} {Mo : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] {Frg : Type}

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "X₀f" => W1ExpStmt prims RMsg N
local notation "Rq" => W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q
local notation "MUR" => MURequest (SignOracle.none Bf) n

attribute [local instance] admDecF

/-- **The honest member of a witness**: the key at the witness's position in the ring of `x₀` is
the key `pks i` of a user `i` whose corruption is not among the requests `rs`. -/
def w1Honest (pks : Fin n → PubKey p prims) (x₀ : X₀f) (rs : List (MUR ⊕ Rq))
    (w : RingSignature.RingWitOf (FIPSSignature p prims)) : Prop :=
  ∃ i, x₀.1.ring.1[w.idx]? = some (pks i) ∧ (.inl (.corrupt i) : MUR ⊕ Rq) ∉ rs

variable (prims O Mo βmin tol enc k D bmsg adm) in
/-- **The test of the canonical witness** at the output `f` and the requests `rs`: the witness is
one of `w1ExpRel` for the program statement of `f`, with an honest member. -/
def w1Ok (pks : Fin n → PubKey p prims) (f : Frg × X₀f) (rs : List (MUR ⊕ Rq))
    (w : RingSignature.RingWitOf (FIPSSignature p prims)) : Prop :=
  (f.2, w) ∈ w1ExpRel prims enc bmsg adm ∧ w1Honest pks f.2 rs w

variable (prims O Mo βmin tol enc k D bmsg adm) in
/-- **The goal of the key-free chain** at the base component `ω`: the witness passes `w1Ok`, and
the forgery satisfies the side condition `w1Side` at `ω`. -/
def w1Goal (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (ω : X → Y₁) (f : Frg × X₀f)
    (rs : List (MUR ⊕ Rq)) (w : RingSignature.RingWitOf (FIPSSignature p prims)) : Prop :=
  w1Ok prims O Mo βmin tol enc k D bmsg adm pks f rs w ∧ w1Side (adm := adm) O sp pks ω f rs

/-- **The goal holds at every fresh witness of `w1ExpRel`** (`hgoal` of `kfChain_le` at
`side := w1Side`, `relK := w1ExpRel` and `wit := fun _ w => w`): the honest ring of `kfFresh`
gives the honest member. -/
theorem w1Goal_of (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (ω : X → Y₁)
    (f : Frg × X₀f) (rs : List (MUR ⊕ Rq)) (w : RingSignature.RingWitOf (FIPSSignature p prims))
    (hon : ∀ pk ∈ f.2.1.ring.1, ∃ i, pks i = pk ∧ (.inl (.corrupt i) : MUR ⊕ Rq) ∉ rs)
    (hside : w1Side (adm := adm) O sp pks ω f rs)
    (hw : (f.2, w) ∈ w1ExpRel prims enc bmsg adm) :
    w1Goal prims O Mo βmin tol enc k D bmsg adm sp pks ω f rs w := by
  obtain ⟨-, hi, -⟩ := id hw
  obtain ⟨i, hpk, hc⟩ := hon _ (List.getElem_mem hi)
  exact ⟨⟨hw, i, (List.getElem?_eq_getElem hi).trans (congrArg some hpk.symm), hc⟩, hside⟩

variable (O) in
/-- **Case U at a witness**: the hash the program statement of `f` lists at the witness's
position is the hash `w1HashAt` at `ω` of the member, the base message and `w₁`. -/
def w1CaseU (sp : Y ≃+ Y₁ × Y₂) (ω : X → Y₁) (f : Frg × X₀f) (w : RingSignature.RingWitOf (FIPSSignature p prims)) :
    Prop :=
  ∀ (hi : w.idx < f.2.1.ring.1.length) c, f.2.2[w.idx]? = some c →
    c = w1HashAt O sp ω (f.2.1.ring.1[w.idx]'hi) (bmsg f.2.1.ring f.2.1.msg) f.2.1.pub

/-- **Case S at a witness**: a main signing request `(s, R', m', xb)` of `rs` has the
message-representative point of the member, the ring statement `(R', m', x.pub)` and lists, for
its signer, the hash listed at the witness's position. -/
def w1CaseS (pks : Fin n → PubKey p prims) (f : Frg × X₀f) (rs : List (MUR ⊕ Rq))
    (w : RingSignature.RingWitOf (FIPSSignature p prims)) : Prop :=
  ∃ hi : w.idx < f.2.1.ring.1.length, ∃ c, f.2.2[w.idx]? = some c ∧
    ∃ e ∈ rs, ∃ s R' m' xb, w1SignEntry e = some (s, R', m', xb) ∧
      O.muPt (pubTr prims (f.2.1.ring.1[w.idx]'hi), bmsg f.2.1.ring f.2.1.msg) =
        O.muPt (pubTr prims (pks s), bmsg R' m') ∧
      xb.1.ring = R' ∧ xb.1.msg = m' ∧ xb.1.pub = f.2.1.pub ∧
      xb.2.val[R'.1.idxOf (pks s)]? = some c

/-- **The goal at one witness splits every witness passing the test** into case U and case S
(`hsplit` of `forgerWinsKF_canon`): `w1Side` decides every listed hash. -/
theorem w1Goal_split (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (ω : X → Y₁)
    (f : Frg × X₀f) (rs : List (MUR ⊕ Rq)) (w w' : RingSignature.RingWitOf (FIPSSignature p prims))
    (hg : w1Goal prims O Mo βmin tol enc k D bmsg adm sp pks ω f rs w)
    (hok : w1Ok prims O Mo βmin tol enc k D bmsg adm pks f rs w') :
    w1CaseU (bmsg := bmsg) O sp ω f w' ∨ w1CaseS (adm := adm) pks f rs w' := by
  obtain ⟨-, hi, c, hc, -⟩ := hok.1
  rcases hg.2.2 w'.idx hi c hc with hU | hS
  · refine Or.inl fun hi' c' hc' => ?_
    rw [hc] at hc'
    cases hc'
    exact hU
  · exact Or.inr ⟨hi, c, hc, hS⟩

variable (bmsg) in
/-- **The forgery read from a canonical witness** `w?` at the output `f`: the member at the
witness's position in the ring of `f`, the base message and the witness's signature; `f₀` if there
is no witness or its position is outside the ring. -/
def w1Readout (f₀ : PubKey p prims × Msg × FIPSSignature p prims) (f : Frg × X₀f)
    (w? : Option (RingSignature.RingWitOf (FIPSSignature p prims))) : PubKey p prims × Msg × FIPSSignature p prims :=
  match w? with
  | some w =>
    if hi : w.idx < f.2.1.ring.1.length then
      (f.2.1.ring.1[w.idx]'hi, bmsg f.2.1.ring f.2.1.msg, w.sig)
    else f₀
  | none => f₀

omit [AddGroup Y] in
/-- **The readout of a witness of `w1ExpRel`** is its member, the base message and its
signature. -/
theorem w1Readout_some (f₀ : PubKey p prims × Msg × FIPSSignature p prims) (f : Frg × X₀f)
    (w : RingSignature.RingWitOf (FIPSSignature p prims)) (hi : w.idx < f.2.1.ring.1.length) :
    w1Readout bmsg f₀ f (some w) = (f.2.1.ring.1[w.idx]'hi, bmsg f.2.1.ring f.2.1.msg, w.sig) := by
  simp only [w1Readout, hi, ↓reduceDIte]

/-- **Case U at the canonical witness gives base verification** (`bverify_join_of_w1Side`): the
readout of a witness passing `w1Ok` and in case U at `ω` verifies at `join sp ω h`, for every
second component `h` and decodings reading only the first component. -/
theorem bverify_w1Readout (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp) (ω : X → Y₁) (h : X → Y₂)
    (f₀ : PubKey p prims × Msg × FIPSSignature p prims) (pks : Fin n → PubKey p prims)
    (f : Frg × X₀f) (rs : List (MUR ⊕ Rq)) (w : RingSignature.RingWitOf (FIPSSignature p prims))
    (hok : w1Ok prims O Mo βmin tol enc k D bmsg adm pks f rs w)
    (hU : w1CaseU (bmsg := bmsg) O sp ω f w) :
    (freshBase prims O Mo βmin tol enc k D bmsg).bverify (join sp ω h)
      (w1Readout bmsg f₀ f (some w)).1 (w1Readout bmsg f₀ f (some w)).2.1
      (w1Readout bmsg f₀ f (some w)).2.2 = true := by
  obtain ⟨hi, hv⟩ := bverify_join_of_w1Side (Mo := Mo) (βmin := βmin) (tol := tol) (k := k) (D := D)
    sp hO ω h (f.2, w) hok.1 hU
  rw [w1Readout_some f₀ f w hi]
  exact hv

omit [AddGroup Y] in
/-- **The readout of a witness passing `w1Ok` has an honest key**: it is the key of a user whose
corruption is not among the requests. -/
theorem honest_w1Readout (f₀ : PubKey p prims × Msg × FIPSSignature p prims)
    (pks : Fin n → PubKey p prims) (f : Frg × X₀f) (rs : List (MUR ⊕ Rq))
    (w : RingSignature.RingWitOf (FIPSSignature p prims)) (hok : w1Ok prims O Mo βmin tol enc k D bmsg adm pks f rs w) :
    ∃ i, pks i = (w1Readout bmsg f₀ f (some w)).1 ∧ (.inl (.corrupt i) : MUR ⊕ Rq) ∉ rs := by
  obtain ⟨⟨-, hi, -⟩, i, hpk, hc⟩ := hok
  refine ⟨i, ?_, hc⟩
  rw [w1Readout_some f₀ f w hi]
  rw [List.getElem?_eq_getElem hi] at hpk
  exact (Option.some.inj hpk).symm

end CaseU

end GordieHowe.Ring.MLDSAW1
