-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeRoute2
public import GordieHowe.Applications.Ring.RingForgerSplit

@[expose] public section

/-!
# The case split of a key-free forgery of the ML-DSA ring publishing `w₁`

In the extraction run of the key-free chain (`RingSignature.KeyFree.kfChain_le`) a forgery's
explicit statement `x₀ = (R, m, w₁, hashes)` and its extracted witness `(i, σ*)` are compared with
the base component `ω` and with the logged signing requests. The commitment hash `x₀` lists for the
member `pk_i` is either the oracle's at `ω` (the forgery is a fresh base forgery, case U), or the
hash a signing request of the same key and base message programmed for the same `w₁` (case S).

- `w1MuAt`, `w1HashAt`: the message representative and the commitment hash of `(pk, bm, w₁)` read
  from the base component `ω`.
- `w1SignEntry`: the signing request, its program statement and its signature in a main request.
- `w1Coll`: two distinct message-representative points, of a forgery member and of a logged
  signing request, with equal message representatives at `ω`.
- `bverify_join_of_hashAt`: case U gives base verification at every oracle with base component
  `ω`.
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section CaseSplit

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p prims Msg N reps} {Mo : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "PSf" => PS
local notation "X₀f" => W1ExpStmt prims RMsg N

attribute [local instance] admDecF

variable (O) in
/-- **The message representative of `(pk, bm)` at the base component `ω`.** -/
def w1MuAt (sp : Y ≃+ Y₁ × Y₂) (ω : X → Y₁) (pk : PubKey p prims) (bm : Msg) : Bytes 64 :=
  O.muAt sp (ω (O.muPt (pubTr prims pk, bm)))

variable (O) in
/-- **The commitment hash of `(pk, bm, w₁)` at the base component `ω`.** -/
def w1HashAt (sp : Y ≃+ Y₁ × Y₂) (ω : X → Y₁) (pk : PubKey p prims) (bm : Msg)
    (w₁ : BucketVec p) : CommitHashBytes p :=
  O.chAt sp (ω (O.chPt (w1MuAt O sp ω pk bm, w₁)))

/-- **The signing request of a main request**: the user, the ring, the message and the bounded
program statement of a relayed signing request; none for other main requests. -/
def w1SignEntry :
    MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q →
    Option (Fin n × KeyRing (PubKey p prims) N × RMsg × W1BStmt prims RMsg N)
  | .inr (.inl (xb, (.sign s R m, _), _)) => some (s, R, m, xb)
  | _ => none

variable (O) in
/-- **A collision of message representatives at the forgery**: a member `pk` of the forgery's ring
`R` and a logged signing request `(s, R', m')` with distinct message-representative points and
equal message representatives at `ω`. -/
def w1Coll (sp : Y ≃+ Y₁ × Y₂) (pks : Fin n → PubKey p prims) (ω : X → Y₁)
    (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (rs : List (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q)) :
    Prop :=
  ∃ pk ∈ R.1, ∃ e ∈ rs, ∃ s R' m' xb, w1SignEntry e = some (s, R', m', xb) ∧
    O.muPt (pubTr prims pk, bmsg R m) ≠ O.muPt (pubTr prims (pks s), bmsg R' m') ∧
    w1MuAt O sp ω pk (bmsg R m) = w1MuAt O sp ω (pks s) (bmsg R' m')

omit hadm in
/-- **Case U gives base verification at every oracle with base component `ω`**: a witness of
`w1ExpRel` whose member's listed hash is `w1HashAt` at `ω` verifies at `join sp ω h`, for every
second component `h` and decodings reading only the first component. -/
theorem bverify_join_of_hashAt (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp) (ω : X → Y₁)
    (h : X → Y₂) (q : X₀f × RingSignature.RingWitOf (FIPSSignature p prims))
    (hq : q ∈ w1ExpRel prims enc bmsg adm)
    (hc : ∀ hi : q.2.idx < q.1.1.ring.1.length, q.1.2[q.2.idx]? =
      some (w1HashAt O sp ω (q.1.1.ring.1[q.2.idx]'hi) (bmsg q.1.1.ring q.1.1.msg) q.1.1.pub)) :
    ∃ hi : q.2.idx < q.1.1.ring.1.length,
      (w1BaseSigner prims O βmin tol enc Lf bmsg).bverify (join sp ω h)
        (q.1.1.ring.1[q.2.idx]'hi) (bmsg q.1.1.ring q.1.1.msg) q.2.sig = true :=
  bverify_of_mem_w1ExpRel prims hO (join sp ω h) q hq fun hi => by
    rw [hc hi, base_join]
    rfl

end CaseSplit

end GordieHowe.Ring.MLDSAW1
