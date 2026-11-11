-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeBase
public import GordieHowe.Applications.Ring.KeyFreeRelaySwap

@[expose] public section

/-!
# The key-free signer of the ML-DSA ring publishing `w₁` under a swap of its side coins

The hypotheses of `progSwap_kfRelaySide` and `sameShape_kfRelaySide`
(`GordieHowe/Applications/Ring/KeyFreeRelaySwap.lean`) at the ML-DSA ring publishing `w₁`, and the
move of the main requests.

- `lockstep_hashesProg`, `countsLE_hashesProg`: the members' commitment hashes are read in lockstep
  at any messages and commitments, two queries per key on every path.
- `lockstep_w1KFPre`, `lockstep_w1KFOutB`, `countsLE_w1KFPre`, `countsLE_w1KFOutB`: the key-free
  signer's base-component program is in lockstep at any two side coins (its reads before the
  commitment hashes are at points free of the coins; it reads the commitment hash of every attempt
  whatever the coins), with at most `w1KFPreq` reads on every path.
- `w1ProofSw`, `w1MainSw`, `w1MainSw_inl`, `w1MainSw_of_isLeft`, `w1MainSw_inr_inr`,
  `w1MainSw_default`, `w1MainSw_reqOf`: the signature of the proof requests tagged `t₀` moved by
  `swσ`; it fixes the requests to the main challenger, the dummy requests and the default, and moves a request's main request as its signature.
- `w1IdleOf`, `w1KFRelay`, **`sameShape_w1KFRelaySide`** (ii-b),
  **`progSwap_w1KFRelaySide`** (ii-c): the
  side-mode key-free relay at side coins swapped at one request.
- `w1MainSw_reqOf_of_ne`, **`offTagFixed_w1KFRelaySide`** (ii-d): off `J` the relay asks main
  requests fixed by `w1MainSw`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree GordieHowe.OracleProg

section Stmt

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  {p : Params} (prims : Primitives p) {Msg : Type} {N reps : ℕ}
  (O : W1Oracles X Y p prims Msg N reps)

/-- **The members' commitment hashes are read in lockstep** at any messages and commitments. -/
theorem lockstep_hashesProg (m m' : Msg) (w1 w1' : BucketVec p) :
    ∀ l : List (PubKey p prims), Lockstep (fun _ _ => True) (fun _ _ _ _ => True)
      (fun _ _ => True) (hashesProg sp prims O m w1 l) (hashesProg sp prims O m' w1' l)
  | [] => trivial
  | _ :: l => ⟨trivial, fun _ _ _ => ⟨trivial, fun _ _ _ =>
      (lockstep_hashesProg m m' w1 w1' l).mapOutput fun _ _ _ => trivial⟩⟩

/-- **The members' commitment hashes make two queries per key** on every path. -/
theorem countsLE_hashesProg (m : Msg) (w1 : BucketVec p) :
    ∀ l : List (PubKey p prims),
      CountsLE (fun _ => true) (2 * l.length) (hashesProg sp prims O m w1 l)
  | [] => trivial
  | pk :: l => by
    show CountsLE _ _ (.query (O.muPt (pubTr prims pk, m)) fun a =>
      .query (O.chPt (O.muAt sp a, w1)) fun c =>
        (hashesProg sp prims O m w1 l).mapOutput (O.chAt sp c :: ·))
    refine (countsLE_query fun _ => countsLE_query fun _ =>
      (countsLE_hashesProg m w1 l).mapOutput).mono ?_
    simp only [List.length_cons]
    omega

end Stmt

section Sign

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁]
  [AddGroup Y₂] (O : W1Oracles X Y p prims Msg N reps) (sp : Y ≃+ Y₁ × Y₂) (βmin : ℚ≥0)
  (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) {RMsg : Type}
  (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) [Fintype Msg] [DecidableEq Msg]
  [Fintype RMsg] [DecidableEq RMsg]

/-- **The key-free signer before its kept read is in lockstep at any two side coins**: its reads
before the commitment hashes are at points free of the coins, so equal answers there give the same
branch; it reads the commitment hashes of every attempt, `k · T · |R|` reads, whatever the coins,
and then returns. -/
theorem lockstep_w1KFPre (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ) (m : RMsg)
    (s s' : KFCoins (p := p) (T := T) k D Y₁) :
    Lockstep (fun _ _ => True) EqAt (fun _ _ => True)
      (w1KFPre prims O sp βmin tol enc k D bmsg pk R c m s)
      (w1KFPre prims O sp βmin tol enc k D bmsg pk R c m s') := by
  unfold w1KFPre
  refine (lockstep_refl (QA := fun _ _ => True) (fun _ => trivial) _).bind fun ok ok' hok => ?_
  subst hok
  refine (lockstep_refl (QA := fun _ _ => True) (fun _ => trivial) _).bind fun ok₂ ok₂' hok => ?_
  subst hok
  split_ifs with h hi
  · refine (lockstep_refl (QA := fun _ _ => True) (fun _ => trivial) _).bind fun ans ans' he => ?_
    subst he
    refine ⟨trivial, fun yMu yMu' hy => ?_⟩
    rw [← hy rfl]
    refine Lockstep.bind (fun _ _ _ => by exact trivial) (Lockstep.tabulate _ _ _ fun _ _ => ?_)
    exact ⟨trivial, fun _ _ _ => trivial⟩
  · exact trivial
  · exact trivial

/-- **The base-component program of the key-free signer is in lockstep at any two side coins.** -/
theorem lockstep_w1KFOutB (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ)
    (m : RMsg) (s s' : KFCoins (p := p) (T := T) k D Y₁) :
    Lockstep (fun _ _ => True) EqAt (fun _ _ => True)
      (w1KFOutB prims O sp βmin tol enc k D bmsg pk R c m s)
      (w1KFOutB prims O sp βmin tol enc k D bmsg pk R c m s') := by
  rw [w1KFOutB_def, w1KFOutB_def]
  exact (lockstep_w1KFPre prims O sp βmin tol enc k D bmsg pk R c m s s').translate
    (fun _ _ _ => trivial) fun _ _ _ _ _ hb he => by rw [hb he]

/-- **The key-free signer before its kept read makes at most `w1KFPreq` reads on every path.** -/
theorem countsLE_w1KFPre (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ)
    (m : RMsg) (s : KFCoins (p := p) (T := T) k D Y₁) :
    CountsLE (fun _ => true) (w1KFPreq N reps k T)
      (w1KFPre prims O sp βmin tol enc k D bmsg pk R c m s) := by
  unfold w1KFPre
  have hring : CountsLE (fun _ => true) (N * reps) (ringCheckProg prims O βmin tol R) := by
    unfold ringCheckProg
    refine (CountsLE.tabulate (q := 1) _ _ fun _ _ =>
      countsLE_query fun _ => countsLE_pure 0 _).mapOutput.mono ?_
    simp [List.length_product]
  have hmu : CountsLE (fun _ => true) N (muDistinctProg prims O R (bmsg R m)) := by
    unfold muDistinctProg
    refine (countsLE_queryAll _).mapOutput.mono ?_
    simpa using R.2
  refine (hring.bind (q₂ := N + (N + (1 + k * T * N))) fun ok => ?_).mono le_rfl
  refine (hmu.bind (q₂ := N + (1 + k * T * N)) fun ok' => ?_).mono le_rfl
  split_ifs with h hi
  · refine CountsLE.mono (CountsLE.bind (q₂ := 1 + k * T * N) (fun ans => ?_)
      ((countsLE_queryAll _).mono (q' := N) ?hl)) le_rfl
    case hl => simpa using R.2
    rw [Nat.add_comm]
    refine countsLE_query fun yMu => ?_
    have h₂ := CountsLE.tabulate (P := fun _ => true) (q := 1)
      (fun _ => (default : CommitHashBytes p))
      (Finset.univ.toList : List ((Fin k × Fin T) × Fin R.1.length))
      (Pi := fun ctj => .query (O.chPt ((ans.map O.muAns).getD ctj.2 default,
        kfW1s prims O sp k pk s.1 ctj.1)) fun y => .pure (O.chAns y))
      fun _ _ => countsLE_query fun _ => countsLE_pure 0 _
    refine ((h₂.bind (q₂ := 0) fun cs => countsLE_pure 0 _).mono ?_)
    simp only [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      mul_one, Nat.add_zero]
    exact Nat.mul_le_mul_left _ R.2
  · exact countsLE_pure _ _
  · exact countsLE_pure _ _

/-- **The base-component program of the key-free signer makes at most `w1KFPreq` reads on every
path.** -/
theorem countsLE_w1KFOutB (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ)
    (m : RMsg) (s : KFCoins (p := p) (T := T) k D Y₁) :
    CountsLE (fun _ => true) (w1KFPreq N reps k T)
      (w1KFOutB prims O sp βmin tol enc k D bmsg pk R c m s) := by
  rw [w1KFOutB_def]
  exact (countsLE_w1KFPre prims O sp βmin tol enc k D bmsg pk R c m s).translate fun _ => rfl

end Sign

section Relay

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
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

attribute [local instance] admDecF

open Classical in
/-- **The signature of the proof requests tagged `t₀` moved by `swσ`**; other proof requests
kept. -/
noncomputable def w1ProofSw (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (swσ : Equiv.Perm (FIPSSignature p prims)) :
    Equiv.Perm (W1BStmt prims RMsg N ×
      (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) × FIPSSignature p prims) where
  toFun q := (q.1, q.2.1, if q.2.1 = t₀ then swσ q.2.2 else q.2.2)
  invFun q := (q.1, q.2.1, if q.2.1 = t₀ then swσ.symm q.2.2 else q.2.2)
  left_inv q := by
    rcases q with ⟨a, t, σ⟩
    by_cases h : t = t₀ <;> simp [h]
  right_inv q := by
    rcases q with ⟨a, t, σ⟩
    by_cases h : t = t₀ <;> simp [h]

/-- **The main requests with the signature of the proof requests tagged `t₀` moved by `swσ`**:
the corruptions, key requests and dummy requests kept. -/
noncomputable def w1MainSw (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (swσ : Equiv.Perm (FIPSSignature p prims)) :
    Equiv.Perm (MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.sumCongr (w1ProofSw t₀ swσ) (Equiv.refl _))

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The moved main requests fix the requests to the main challenger**, the idle one among
them. -/
theorem w1MainSw_inl (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (swσ : Equiv.Perm (FIPSSignature p prims)) (i : MURequest (SignOracle.none (Bf).core) n) :
    w1MainSw t₀ swσ (.inl i) = .inl i :=
  rfl

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The moved main requests fix every request to the main challenger.** -/
theorem w1MainSw_of_isLeft (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (swσ : Equiv.Perm (FIPSSignature p prims))
    (a : MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q)
    (ha : a.isLeft) : w1MainSw t₀ swσ a = a := by
  rcases a with _ | _
  · rfl
  · exact absurd ha (by simp)

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The moved main requests fix the dummy requests.** -/
theorem w1MainSw_inr_inr (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (swσ : Equiv.Perm (FIPSSignature p prims))
    (d : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) :
    w1MainSw t₀ swσ (.inr (.inr d) : MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q) = .inr (.inr d) :=
  rfl

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The moved main requests fix the default request** (by instance inference a dummy
request). -/
theorem w1MainSw_default [NeZero n]
    (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (swσ : Equiv.Perm (FIPSSignature p prims)) :
    w1MainSw t₀ swσ (default : MURequest (SignOracle.none (Bf).core) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q) = default :=
  rfl

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The moved main request of a request** is the main request of the request with its signature
moved. -/
theorem w1MainSw_reqOf (swσ : Equiv.Perm (FIPSSignature p prims))
    (r : RingSignature.Insider.Req Bf PSf adm n) (c : Fin (Q + 1))
    (o : Option (BucketVec p × FIPSSignature p prims × List (Assignment X Y)))
    (x₀ : Option (W1ExpStmt prims RMsg N)) :
    w1MainSw (r, w1Num Q c) swσ
        (reqOf Bf (w1ToR (PS := PS) (Q := Q)) w1DummyR c r o x₀) =
      reqOf Bf (w1ToR (PS := PS) (Q := Q)) w1DummyR c r (mapSig Bf swσ o) x₀ := by
  rcases r with _ | _ | _ <;> rcases o with _ | ⟨y, σ, a⟩ <;> rcases x₀ with _ | x <;>
    first
    | rfl
    | (simp [reqOf, mapSig, w1MainSw, w1ProofSw, w1ToR, w1DummyR] <;> rfl)

variable (sp : Y ≃+ Y₁ × Y₂) [DecidableEq X] [Inhabited X] (hO : O.ReadsFst sp)
  (pks : Fin n → PubKey p prims)

local notation "Fw" => w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg hO
/-- **A request to the main challenger as the idle request** of the relay. -/
abbrev w1IdleOf (i : MURequest (SignOracle.none (Bf).core) n) :
    MURequest (SignOracle.none (Bf).core) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q :=
  .inl i

local notation "Sw" => w1KFStmt prims O Mo βmin tol enc k D bmsg sp

/-- **The side-mode key-free relay at the ML-DSA ring publishing `w₁`**, at the side coins `sc`,
the side function `ω` and the idle request `inl i`. -/
noncomputable abbrev w1KFRelay (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (ω : X → Y₁)
    (i : MURequest (SignOracle.none (Bf).core) n) :=
  AssignRelay.relayOf (kfRelaySide (PS := PSf) (adm := adm) sp Bf pks Fw Sw
    (w1ToR (PS := PS) (Q := Q)) (w1DummyR (PS := PS) (Q := Q)) sc ω (w1IdleOf i)) Q

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **(ii-b) at the ML-DSA ring publishing `w₁`**: the side-mode key-free relay at other side
coins has its shape. -/
theorem sameShape_w1KFRelaySide (sc sc' : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (ω : X → Y₁) (i : MURequest (SignOracle.none (Bf).core) n) :
    (w1KFRelay (Mo := Mo) (PS := PS) (adm := adm) sp hO pks sc ω i).SameShape
      (w1KFRelay (Mo := Mo) (PS := PS) (adm := adm) sp hO pks sc' ω i).prog :=
  sameShape_kfRelaySide sp Bf pks Fw Sw (w1ToR (PS := PS) (Q := Q)) (w1DummyR (PS := PS) (Q := Q))
    (fun pk Rg c m s s' => lockstep_w1KFOutB prims O sp βmin tol enc k D bmsg pk Rg c m s s')
    (fun Rg m y y' => (lockstep_hashesProg sp prims O _ _ _ _ Rg.1).mapOutput
      fun _ _ _ => trivial) sc sc' ω (w1IdleOf i)

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **(ii-c) at the ML-DSA ring publishing `w₁`**: the side-mode key-free relay at side coins
swapped at one request, with the signature of its proof request moved by `swσ` (`w1MainSw`). -/
theorem progSwap_w1KFRelaySide (sc sc' : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (ω : X → Y₁) (i : MURequest (SignOracle.none (Bf).core) n)
    (J : (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) × (X → Option Y) → Bool)
    (r₀ : (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) × (X → Option Y))
    (swσ : Equiv.Perm (FIPSSignature p prims))
    (hoff : ∀ r, J r = false → ∀ s Rg m (hc : (r.1.2 : ℕ) < Q), r.1.1 = .sign s Rg m →
      sc' ⟨r.1.2, hc⟩ = sc ⟨r.1.2, hc⟩)
    (hφ : CoinSwapAt sp Bf pks Fw sc sc' ω r₀.2 r₀.1.2 r₀.1.1 swσ) :
    (w1KFRelay (Mo := Mo) (PS := PS) (adm := adm) sp hO pks sc ω i).ProgSwap
      (w1KFRelay (Mo := Mo) (PS := PS) (adm := adm) sp hO pks sc' ω i).prog J
      (· = r₀) (w1MainSw (r₀.1.1, w1Num Q r₀.1.2) swσ)
      (AssignRelay.recordSw (w1MainSw (r₀.1.1, w1Num Q r₀.1.2) swσ)) :=
  progSwap_kfRelaySide sp Bf pks Fw Sw (w1ToR (PS := PS) (Q := Q)) (w1DummyR (PS := PS) (Q := Q))
    (fun pk Rg c m s s' => lockstep_w1KFOutB prims O sp βmin tol enc k D bmsg pk Rg c m s s')
    (fun Rg m y y' => (lockstep_hashesProg sp prims O _ _ _ _ Rg.1).mapOutput
      fun _ _ _ => trivial)
    (fun pk Rg c m s => countsLE_w1KFOutB prims O sp βmin tol enc k D bmsg pk Rg c m s)
    (fun x => ((countsLE_hashesProg sp prims O _ _ x.ring.1).mapOutput).mono
      (Nat.mul_le_mul_left 2 x.ring.2))
    sc sc' ω (w1IdleOf i) J r₀ swσ _ hoff hφ
    (fun o x₀ => by simpa using w1MainSw_reqOf swσ r₀.1.1 r₀.1.2 o x₀) rfl

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The moved main requests fix the main request of a request with another tag.** -/
theorem w1MainSw_reqOf_of_ne (t₀ : RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))
    (swσ : Equiv.Perm (FIPSSignature p prims)) (r : RingSignature.Insider.Req Bf PSf adm n)
    (c : Fin (Q + 1)) (ht : (r, w1Num Q c) ≠ t₀)
    (o : Option (BucketVec p × FIPSSignature p prims × List (Assignment X Y)))
    (x₀ : Option (W1ExpStmt prims RMsg N)) :
    w1MainSw t₀ swσ (reqOf Bf (w1ToR (PS := PS) (Q := Q)) w1DummyR c r o x₀) =
      reqOf Bf (w1ToR (PS := PS) (Q := Q)) w1DummyR c r o x₀ := by
  rcases r with _ | _ | _ <;> rcases o with _ | ⟨y, σ, a⟩ <;> rcases x₀ with _ | x <;>
    first
    | rfl
    | (simp [reqOf, w1MainSw, w1ProofSw, w1ToR, ht])

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins]
  [Nonempty TPS.Coins] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **(ii-d) at the ML-DSA ring publishing `w₁`**: off `J` the side-mode key-free relay asks main
requests fixed by `w1MainSw`, when every request failing `J` has another request and number than
`r₀`, or is a corruption (`hJ`). -/
theorem offTagFixed_w1KFRelaySide (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁)
    (ω : X → Y₁) (i : MURequest (SignOracle.none (Bf).core) n)
    (J : (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) × (X → Option Y) → Bool)
    (r₀ : (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) × (X → Option Y))
    (swσ : Equiv.Perm (FIPSSignature p prims))
    (hJ : ∀ r, J r = false → r.1 ≠ r₀.1 ∨ ∃ i', r.1.1 = .corrupt i') :
    (w1KFRelay (Mo := Mo) (PS := PS) (adm := adm) sp hO pks sc ω i).OffTagFixed J
      (w1MainSw (r₀.1.1, w1Num Q r₀.1.2) swσ) := by
  refine offTagFixed_kfRelaySide sp Bf pks Fw Sw (w1ToR (PS := PS) (Q := Q))
    (w1DummyR (PS := PS) (Q := Q)) sc ω (w1IdleOf i) J _ (fun r hr o x₀ => ?_) rfl
  rcases hJ r hr with hne | ⟨i', hi'⟩
  · refine w1MainSw_reqOf_of_ne _ swσ _ _ (fun he => hne ?_) o x₀
    obtain ⟨h1, h2⟩ := Prod.mk.inj he
    refine Prod.ext h1 (Fin.ext ?_)
    exact w1Num_injOn (Nat.le_of_lt_succ r.1.2.2) (Nat.le_of_lt_succ r₀.1.2.2) h2
  · rw [hi']
    rfl

end Relay

end GordieHowe.Ring.MLDSAW1
