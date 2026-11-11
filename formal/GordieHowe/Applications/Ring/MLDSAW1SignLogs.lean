-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseSplitSide
public import GordieHowe.Applications.Ring.KeyFreeSignLogs

@[expose] public section

/-!
# The logged signing entries of the key-free extraction run for the ML-DSA ring publishing `w₁`

The key-free statement of `GordieHowe/Applications/Ring/KeyFreeSignLogs.lean`
(`simProb_seAlgKF_kfSigned`) at the ML-DSA ring publishing `w₁`, with the test
`(w1SignEntry ·).isSome`: the dummies and the corruptions are not signing entries
(`w1SignEntry_dummyR`, `w1SignEntry_corrupt`), and a signed request of the relay at the base
component that is a signing entry `(s, R, m, xb)` is the relay's honest output
(`w1SignEntry_of_kfSignedAsk`).
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section Side

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
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] {Frg : Type}

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "PSf" => PS
local notation "X₀f" => W1ExpStmt prims RMsg N

attribute [local instance] admDecF


omit [AddGroup Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] in
/-- **The dummy proof request is not a signing entry.** -/
theorem w1SignEntry_dummyR (r : RingSignature.Insider.Req Bf PSf adm n × ℕ) :
    w1SignEntry (.inr (w1DummyR (prims := prims) (O := O) (Mo := Mo) (βmin := βmin) (tol := tol)
      (enc := enc) (k := k) (D := D) (bmsg := bmsg) (PS := PS) (Q := Q) r)) = none :=
  rfl

omit [AddGroup Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] in
/-- **A corruption is not a signing entry.** -/
theorem w1SignEntry_corrupt (i : Fin n) :
    w1SignEntry (.inl (.corrupt i) :
      MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q) = none :=
  rfl

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **A signed request of the relay at the base component that is a signing entry `(s, R, m, xb)`**
(`KFSignedAsk` at `w1KFFactors`, `w1StmtPω` and `w1ToR`): for request number `c < Q`, a table `T`
and an answer `y` at the kept point, `s` is a member of the supported ring `R`, the public part
and signature `q` are `w1KFOut` at the base component read through `T`, and the tagged statement
`xb` is `w1Bnd` of `w1StmtPω` at the base component read through `T` overridden at the kept point
by the published value `q.1.2` with the second component of `y`; the entry is the proof request
of `xb` tagged with the request and its capped number, with the signature `q.2`. -/
theorem w1SignEntry_of_kfSignedAsk [DecidableEq X] (sp : Y ≃+ Y₁ × Y₂) (hO : O.ReadsFst sp)
    (pks : Fin n → PubKey p prims) (sc : Fin Q → KFCoins k D Y₁) (ω : X → Y₁)
    {e : MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q}
    (he : KFSignedAsk (PS := PSf) (adm := adm) sp Bf pks
      (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO)
      (w1StmtPω prims O Mo βmin tol enc k D bmsg sp) (w1ToR (Q := Q)) sc ω e)
    {s : Fin n} {R : KeyRing (PubKey p prims) N} {m : RMsg}
    {xb : W1BStmt prims RMsg N}
    (hs : w1SignEntry e = some (s, R, m, xb)) :
    ∃ (c : ℕ) (hc : c < Q) (Tb : X → Option Y) (q : (BucketVec p × Y₁) × FIPSSignature p prims)
      (y : Y), pks s ∈ R.1 ∧ adm R ∧
      w1KFOut (T := T) prims O sp βmin tol enc k D bmsg (ωT sp ω Tb) (pks s) R c m
        (sc ⟨c, hc⟩) = some q ∧
      xb = w1Bnd (w1StmtPω prims O Mo βmin tol enc k D bmsg sp (ωT sp ω (overT Tb (lastAssign
        [⟨w1KFKept prims O sp bmsg (ωT sp ω Tb) (pks s) R m q.1,
          sp.symm (q.1.2, (sp y).2)⟩]))) ⟨R, m, q.1.1⟩) ∧
      e = .inr (.inl (xb, (.sign s R m, w1Num Q c), q.2)) := by
  obtain ⟨Tb, c, r, s', R', m', hc, q, y, -, h1, h2, h3, rfl⟩ := he
  simp only [w1SignEntry, w1ToR, Option.some.injEq, Prod.mk.injEq] at hs
  obtain ⟨rfl, rfl, rfl, rfl⟩ := hs
  exact ⟨c, hc, Tb, q, y, h1, h2, h3, rfl, rfl⟩

end Side

end GordieHowe.Ring.MLDSAW1
