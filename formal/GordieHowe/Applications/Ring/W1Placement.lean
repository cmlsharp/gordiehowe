-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.QueryBits
public import GordieHowe.Applications.Ring.MLDSAW1Ring

@[expose] public section

/-!
# The ML-DSA ring's oracle points in the oracle domain

The ML-DSA w₁ ring reads four application oracles from the one random oracle (`W1Oracles`,
`MaskOracle`): the message representative `H_µ` at `(tr, m)` (`muPt`), the commitment hash at
`(µ, w₁)` (`chPt`), the members' commitment hashes at `(R, j, r)` (`gPt`), and the hedged mask
derivation (`MaskOracle.pt`). This file places their points in the oracle domain
`Bits (queryBits k kN kS L)` of `Query.toBits`:

    tag byte ‖ payload ‖ zero padding

with tags `4` (`w1MuPt`), `5` (`w1ChPt`), `6` (`w1GPt`), `7` (`w1MaskPt`), which the encoded
queries do not use (they use `0`–`3`), and as payload an injection of the point's finite domain
into the `payloadBits k kN kS L`-bit strings (`Bits.embOfCard`). The injections exist when each
domain has at most `2 ^ payloadBits k kN kS L` elements (`W1Fit`), which holds when `L` is at least
the four domains' cardinalities (`w1Fit_of_le`).

The placements are injective, have pairwise different values across the four roles, and miss the
range of `Query.toBits`.
-/

namespace GordieHowe.QROM

namespace Bits

/-- An injection of a finite type with at most `2 ^ n` elements into the `n`-bit strings: its
enumeration (`Fintype.equivFin`), then the binary digits (`Bits.equivFin`). -/
noncomputable def embOfCard {T : Type*} [Fintype T] {n : ℕ} (h : Fintype.card T ≤ 2 ^ n) :
    T ↪ Bits n :=
  (Fintype.equivFin T).toEmbedding.trans ((Fin.castLEEmb h).trans (equivFin n).symm.toEmbedding)

end Bits

variable {k kN kS L : ℕ} {T : Type*}

/-- An application oracle point: the tag byte `tag` and the payload `ι t`, zero-padded to
`payloadBits k kN kS L` bits (`Bits.frame`, as `Query.bits`). -/
def appPt (tag : Byte) {n : ℕ} (hn : n ≤ payloadBits k kN kS L) (ι : T ↪ Bits n) :
    T ↪ Bits (queryBits k kN kS L) :=
  ⟨fun t => Bits.frame tag hn (ι t), fun _ _ e => ι.injective (Bits.frame_injective tag hn e)⟩

theorem appPt_apply (tag : Byte) {n : ℕ} (hn : n ≤ payloadBits k kN kS L) (ι : T ↪ Bits n)
    (t : T) : appPt tag hn ι t = Bits.frame tag hn (ι t) := rfl

/-- An application point with a tag of at least `4` is not an encoded query. -/
theorem appPt_notMem_range_toBits (tag : Byte) (htag : 4 ≤ (tag : ℕ)) {n : ℕ}
    (hn : n ≤ payloadBits k kN kS L) (ι : T ↪ Bits n) (t : T) :
    appPt tag hn ι t ∉ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L)) := by
  rintro ⟨q, hq⟩
  cases q <;>
  · have := congrArg Fin.val (Bits.tag_eq_of_frame_eq hq)
    simp at this
    omega

/-- Application points with different tags are different. -/
theorem appPt_ne_of_tag_ne {T' : Type*} {tag tag' : Byte} (h : tag ≠ tag') {n n' : ℕ}
    (hn : n ≤ payloadBits k kN kS L) (hn' : n' ≤ payloadBits k kN kS L) (ι : T ↪ Bits n)
    (ι' : T' ↪ Bits n') (t : T) (t' : T') : appPt tag hn ι t ≠ appPt tag' hn' ι' t' :=
  fun e => h (Bits.tag_eq_of_frame_eq e)

end GordieHowe.QROM

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature
open GordieHowe.QROM (Bits appPt appPt_ne_of_tag_ne appPt_notMem_range_toBits Query payloadBits
  queryBits transcript_le_payloadBits)

variable {p : Params} {prims : Primitives p} {Msg : Type} {N reps T : ℕ}
  [Fintype Msg] [Fintype prims.Power2High] [DecidableEq prims.Power2High]

/-- **The ML-DSA ring's oracle domains fit the payload**: each of the four application points'
domains has at most `2 ^ payloadBits k kN kS L` elements. -/
structure W1Fit (k kN kS L : ℕ) (p : Params) (prims : Primitives p) (Msg : Type) (N reps T : ℕ)
    [Fintype Msg] [Fintype prims.Power2High] [DecidableEq prims.Power2High] : Prop where
  mu : Fintype.card (Bytes 64 × Msg) ≤ 2 ^ payloadBits k kN kS L
  ch : Fintype.card (Bytes 64 × BucketVec p) ≤ 2 ^ payloadBits k kN kS L
  g : Fintype.card (KeyRing (PubKey p prims) N × Fin N × Fin reps) ≤ 2 ^ payloadBits k kN kS L
  mask : Fintype.card (Bytes 32 × MaskPt T Msg) ≤ 2 ^ payloadBits k kN kS L

variable {k kN kS L : ℕ} (F : W1Fit k kN kS L p prims Msg N reps T)

/-- The message-representative points `(tr, m)`, tag `4`. -/
noncomputable def w1MuPt : Bytes 64 × Msg ↪ Bits (queryBits k kN kS L) :=
  appPt 4 le_rfl (Bits.embOfCard F.mu)

/-- The commitment-hash points `(µ, w₁)`, tag `5`. -/
noncomputable def w1ChPt : Bytes 64 × BucketVec p ↪ Bits (queryBits k kN kS L) :=
  appPt 5 le_rfl (Bits.embOfCard F.ch)

/-- The members' commitment-hash points `(R, j, r)`, tag `6`. -/
noncomputable def w1GPt :
    KeyRing (PubKey p prims) N × Fin N × Fin reps ↪ Bits (queryBits k kN kS L) :=
  appPt 6 le_rfl (Bits.embOfCard F.g)

/-- The hedged mask points `(rnd, u)`, tag `7`. -/
noncomputable def w1MaskPt : Bytes 32 × MaskPt T Msg ↪ Bits (queryBits k kN kS L) :=
  appPt 7 le_rfl (Bits.embOfCard F.mask)

theorem w1MuPt_injective : Function.Injective (w1MuPt F) := (w1MuPt F).injective
theorem w1ChPt_injective : Function.Injective (w1ChPt F) := (w1ChPt F).injective
theorem w1GPt_injective : Function.Injective (w1GPt F) := (w1GPt F).injective
theorem w1MaskPt_injective : Function.Injective (w1MaskPt F) := (w1MaskPt F).injective

theorem w1MuPt_ne_w1ChPt (a : Bytes 64 × Msg) (b : Bytes 64 × BucketVec p) :
    w1MuPt F a ≠ w1ChPt F b :=
  appPt_ne_of_tag_ne (by decide) _ _ _ _ a b
theorem w1MuPt_ne_w1GPt (a : Bytes 64 × Msg) (b : KeyRing (PubKey p prims) N × Fin N × Fin reps) :
    w1MuPt F a ≠ w1GPt F b :=
  appPt_ne_of_tag_ne (by decide) _ _ _ _ a b
theorem w1ChPt_ne_w1GPt (a : Bytes 64 × BucketVec p) (b : KeyRing (PubKey p prims) N × Fin N × Fin reps) :
    w1ChPt F a ≠ w1GPt F b :=
  appPt_ne_of_tag_ne (by decide) _ _ _ _ a b
theorem w1MuPt_ne_w1MaskPt (a : Bytes 64 × Msg) (b : Bytes 32 × MaskPt T Msg) :
    w1MuPt F a ≠ w1MaskPt F b :=
  appPt_ne_of_tag_ne (by decide) _ _ _ _ a b
theorem w1ChPt_ne_w1MaskPt (a : Bytes 64 × BucketVec p) (b : Bytes 32 × MaskPt T Msg) :
    w1ChPt F a ≠ w1MaskPt F b :=
  appPt_ne_of_tag_ne (by decide) _ _ _ _ a b
theorem w1GPt_ne_w1MaskPt (a : KeyRing (PubKey p prims) N × Fin N × Fin reps) (b : Bytes 32 × MaskPt T Msg) :
    w1GPt F a ≠ w1MaskPt F b :=
  appPt_ne_of_tag_ne (by decide) _ _ _ _ a b

theorem w1MuPt_notMem_range_toBits (a : Bytes 64 × Msg) :
    w1MuPt F a ∉ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L)) :=
  appPt_notMem_range_toBits _ (by decide) _ _ a
theorem w1ChPt_notMem_range_toBits (a : Bytes 64 × BucketVec p) :
    w1ChPt F a ∉ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L)) :=
  appPt_notMem_range_toBits _ (by decide) _ _ a
theorem w1GPt_notMem_range_toBits (a : KeyRing (PubKey p prims) N × Fin N × Fin reps) :
    w1GPt F a ∉ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L)) :=
  appPt_notMem_range_toBits _ (by decide) _ _ a
theorem w1MaskPt_notMem_range_toBits (a : Bytes 32 × MaskPt T Msg) :
    w1MaskPt F a ∉ Set.range (Query.toBits (k := k) (kN := kN) (kS := kS) (L := L)) :=
  appPt_notMem_range_toBits _ (by decide) _ _ a

omit [Fintype Msg] [Fintype prims.Power2High] [DecidableEq prims.Power2High] in
/-- A cardinality of at most `L` is below `2 ^ payloadBits k kN kS L`. -/
theorem card_le_two_pow_payloadBits {c : ℕ} (h : c ≤ L) : c ≤ 2 ^ payloadBits k kN kS L := by
  have h8 : L ≤ payloadBits k kN kS L := by
    have := transcript_le_payloadBits (k := k) (kN := kN) (kS := kS) (L := L)
    omega
  exact (h.trans (Nat.lt_two_pow_self).le).trans (Nat.pow_le_pow_right (by norm_num) h8)

/-- **The domains fit when `L` is at least their cardinalities.** -/
theorem w1Fit_of_le
    (hL : max (max (Fintype.card (Bytes 64 × Msg)) (Fintype.card (Bytes 64 × BucketVec p)))
      (max (Fintype.card (KeyRing (PubKey p prims) N × Fin N × Fin reps))
        (Fintype.card (Bytes 32 × MaskPt T Msg))) ≤ L) :
    W1Fit k kN kS L p prims Msg N reps T where
  mu := card_le_two_pow_payloadBits (by omega)
  ch := card_le_two_pow_payloadBits (by omega)
  g := card_le_two_pow_payloadBits (by omega)
  mask := card_le_two_pow_payloadBits (by omega)

end GordieHowe.Ring.MLDSAW1
