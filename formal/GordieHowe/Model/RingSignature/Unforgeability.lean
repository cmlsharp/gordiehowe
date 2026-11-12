-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Completeness
public import GordieHowe.Model.RingSignature.Adversary

@[expose] public section

/-!
# Unforgeability with respect to insider corruption

The unforgeability game of a `RingScheme`, BKM06 Definition 7 (ePrint 2005/304, p. 7,
unforgeability w.r.t. insider corruption), against the adversaries of
`GordieHowe/Model/RingSignature/Adversary.lean`, with an optional second signing oracle for the
joint-security game (`GordieHowe/Model/RingSignature/Joint.lean`).

- `SideOracle S`: a signing oracle beside the ring signer, on messages `BMsg` with signatures
  `BSig`, answered from a user's key pair and the request's signing coins; `Covers bm R m`: a
  member's signature on `bm` makes a forgery on `(R, m)` not fresh. `SideOracle.none`: no side
  oracle (BKM06 Definition 7).
- `UnforgeRequest`, `UnforgeResponse`: corruption of user `i` (answered with its key coins),
  `OSign(s, R, m)` (answered by `S.sign` of user `s` when its key is in `R`, else `⊥`), and a side
  signing request.
- `UnforgeRequest.instInhabitedOfNeZero`: with a user, the requests are inhabited.
- `unforgeChallenger S n O keys Q`: the challenger at the users' key coins answering `Q` requests,
  each with fresh uniform signing coins.
- `UnforgeAdversary S n O V t`: a `t`-query adversary whose start input is the honest users' public
  keys and the table `V`, outputting `(R*, m*, σ*)`.
- `Fresh`, `Forges`: the winning condition: `σ*` verifies on `(R*, m*)` at the oracle; every key of
  `R*` is the key of an uncorrupted honest user; no answered `OSign(?, R*, m*)`; no answered side
  request covering `(R*, m*)` by a member of `R*`.
- `unforgeLaw`, `forgeProb`: the run (keys and oracle uniform) and the probability of a forgery;
  `insiderForgeProb := forgeProb (SideOracle.none S)` is BKM06 Definition 7.
- Sanity: `fresh_nil_iff` and `forges_nil` (with no requests, a verifying signature on a ring of
  honest keys is a forgery: the win condition is not vacuous), `Fresh.anti` (freshness is lost, never
  gained, along the history), `not_fresh_of_corrupted`, `forgeProb_le_one`, `trivial_forges`.

## Comparison with BKM06 Definition 7

BKM06's game: `n` key pairs from `Gen`, `S = {PK_i}` given to `A`; `OSign(s, M, R)` returns
`Sign_{SK_s}(M, R)` and requires `PK_s ∈ R`; `Corrupt(i)` returns `SK_i`; `A` outputs
`(R*, M*, σ*)` and succeeds if `Vrfy_{R*}(M*, σ*) = 1`, `A` never queried `(?, M*, R*)`, and
`R* ⊆ S \ C`. The deliberate differences:

1. **Corruption returns the key coins** `ω_i` (as BKP20, ePrint 2020/646, p. 7, and CCLM22,
   ePrint 2021/1616, Experiment 3, p. 21), which determine `SK_i`: at least as much as BKM06's
   `SK_i`.
2. **Rings are ordered lists with repetitions**, and "queried `(?, M*, R*)`" compares lists: a
   signature on a reordering of `R*` does not make `R*` used, so the adversary wins in more cases.
3. **Only answered requests count.** The challenger answers the first `Q` requests; a request after
   the `Q`-th gets `none` and does not count against freshness. Such a request returns nothing, so
   the adversary wins in more cases, never fewer, than under BKM06's "never queried".
4. **`OSign` for a ring without the signer's key is answered by `⊥`** (BKM06 requires
   `PK_s ∈ R`), and `S.sign`'s refusals are passed on as `⊥`.
5. **`R* ⊆ S \ C` by keys**: every key of `R*` is the key of some uncorrupted user. With two users
   of one key, the key is honest if either is uncorrupted.
6. **Quantum adversaries in the QROM** with at most `t` superposition queries to the oracle and `Q`
   requests; verification of the forgery at the same oracle.
7. **A side oracle** (`SideOracle`): absent in Definition 7 (`SideOracle.none`); the joint-security game
   adds the base scheme's ordinary signer and widens freshness by `Covers`.
-/

namespace GordieHowe.RingSignature

open GordieHowe.Quantum
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TS : RingTypes} (S : RingScheme X Y N TS) (n : ℕ)

/-- **A signing oracle beside the ring signer** (the joint-security game's ordinary base signer): on a
user's key pair, a message `BMsg` and the request's signing coins, a classical oracle program with
at most `q` queries returning a signature `BSig` or `none`; and `Covers bm R m`, which a member's
answered signature on `bm` makes a forgery on `(R, m)` not fresh. -/
structure SideOracle where
  /-- The messages of the side oracle. -/
  BMsg : Type
  /-- Its signatures. -/
  BSig : Type
  /-- The bound on its queries. -/
  q : ℕ
  /-- The side signer. -/
  sign : Signature.KeyPair S.PK S.SK → BMsg → S.SignCoins → OracleProg X Y (Option BSig)
  /-- It makes at most `q` queries. -/
  sign_queries : ∀ kp bm c, (sign kp bm c).QueriesLE q
  /-- A member's signature on `bm` makes a forgery on `(R, m)` not fresh. -/
  Covers : BMsg → KeyRing S.PK N → S.Msg → Prop

/-- **No side oracle** (BKM06 Definition 7): no messages, so no side requests. -/
@[reducible] def SideOracle.none : SideOracle S where
  BMsg := PEmpty
  BSig := PEmpty
  q := 0
  sign _ bm _ := bm.elim
  sign_queries _ bm _ := bm.elim
  Covers _ _ _ := False

variable {S} (O : SideOracle S)

/-- **A request of the unforgeability game**: the corruption of user `i`, a ring signature by user
`s` on `m` for the ring `R` (BKM06's `OSign(s, M, R)`), or a side signature by user `i` on `bm`. -/
inductive UnforgeRequest where
  /-- The corruption of user `i`. -/
  | corrupt (i : Fin n)
  /-- A ring signature by user `s` on `m` for the ring `R`. -/
  | sign (s : Fin n) (R : KeyRing S.PK N) (m : S.Msg)
  /-- A side signature by user `i` on `bm`. -/
  | sideSign (i : Fin n) (bm : O.BMsg)

/-- **A reply of the unforgeability game**: key coins, a ring signature or a side signature. -/
inductive UnforgeResponse where
  /-- The key coins of a corrupted user. -/
  | keyCoins (kc : S.KeyCoins)
  /-- A ring signature. -/
  | signature (σ : S.Sig)
  /-- A side signature. -/
  | sideSignature (τ : O.BSig)

/-! The decidable equalities of requests and replies are the definitions `deriving DecidableEq`
generates, written out: they read the instances of the field types `TS.PK`, `TS.Msg`, `TS.KeyCoins`
and `TS.Sig` from section binders, which a deriving handler does not see, and no others (no field
has type `X` or `Y`). -/

section DecEq

variable {n O} [DecidableEq TS.PK] [DecidableEq TS.Msg]

variable [DecidableEq O.BMsg]

/-- Decidable equality of requests, constructor by constructor and field by field. -/
def instDecidableEqUnforgeRequest.decEq (x y : UnforgeRequest n O) :
    Decidable (x = y) :=
  match x, y with
  | @UnforgeRequest.corrupt _ _ _ _ _ _ _ a0, @UnforgeRequest.corrupt _ _ _ _ _ _ _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)
  | UnforgeRequest.corrupt .., UnforgeRequest.sign .. => isFalse (by intro h; injection h)
  | UnforgeRequest.corrupt .., UnforgeRequest.sideSign .. => isFalse (by intro h; injection h)
  | UnforgeRequest.sign .., UnforgeRequest.corrupt .. => isFalse (by intro h; injection h)
  | @UnforgeRequest.sign _ _ _ _ _ _ _ a0 a1 a2, @UnforgeRequest.sign _ _ _ _ _ _ _ b0 b1 b2 =>
    if h : @a0 = @b0 then
      by subst h; exact (if h : @a1 = @b1 then
        by subst h; exact (if h : @a2 = @b2 then by subst h; exact isTrue rfl
        else isFalse (by intro n; injection n; apply h _; assumption))
      else isFalse (by intro n; injection n; apply h _; assumption))
    else isFalse (by intro n; injection n; apply h _; assumption)
  | UnforgeRequest.sign .., UnforgeRequest.sideSign .. => isFalse (by intro h; injection h)
  | UnforgeRequest.sideSign .., UnforgeRequest.corrupt .. => isFalse (by intro h; injection h)
  | UnforgeRequest.sideSign .., UnforgeRequest.sign .. => isFalse (by intro h; injection h)
  | @UnforgeRequest.sideSign _ _ _ _ _ _ _ a0 a1, @UnforgeRequest.sideSign _ _ _ _ _ _ _ b0 b1 =>
    if h : @a0 = @b0 then
      by subst h; exact (if h : @a1 = @b1 then by subst h; exact isTrue rfl
      else isFalse (by intro n; injection n; apply h _; assumption))
    else isFalse (by intro n; injection n; apply h _; assumption)

instance instDecidableEqUnforgeRequest :
    DecidableEq (UnforgeRequest n O) :=
  instDecidableEqUnforgeRequest.decEq

end DecEq

section DecEq

variable {O} [DecidableEq TS.KeyCoins] [DecidableEq TS.Sig]

variable [DecidableEq O.BSig]

/-- Decidable equality of replies, constructor by constructor and field by field. -/
def instDecidableEqUnforgeResponse.decEq (x y : UnforgeResponse O) :
    Decidable (x = y) :=
  match x, y with
  | @UnforgeResponse.keyCoins _ _ _ _ _ _ a0, @UnforgeResponse.keyCoins _ _ _ _ _ _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)
  | UnforgeResponse.keyCoins .., UnforgeResponse.signature .. => isFalse (by intro h; injection h)
  | UnforgeResponse.keyCoins .., UnforgeResponse.sideSignature .. =>
    isFalse (by intro h; injection h)
  | UnforgeResponse.signature .., UnforgeResponse.keyCoins .. => isFalse (by intro h; injection h)
  | @UnforgeResponse.signature _ _ _ _ _ _ a0, @UnforgeResponse.signature _ _ _ _ _ _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)
  | UnforgeResponse.signature .., UnforgeResponse.sideSignature .. =>
    isFalse (by intro h; injection h)
  | UnforgeResponse.sideSignature .., UnforgeResponse.keyCoins .. =>
    isFalse (by intro h; injection h)
  | UnforgeResponse.sideSignature .., UnforgeResponse.signature .. =>
    isFalse (by intro h; injection h)
  | @UnforgeResponse.sideSignature _ _ _ _ _ _ a0, @UnforgeResponse.sideSignature _ _ _ _ _ _ b0 =>
    if h : @a0 = @b0 then by subst h; exact isTrue rfl
    else isFalse (by intro n; injection n; apply h _; assumption)

instance instDecidableEqUnforgeResponse :
    DecidableEq (UnforgeResponse O) :=
  instDecidableEqUnforgeResponse.decEq

end DecEq

/-- Requests as a sum type. -/
def UnforgeRequest.equivSum :
    UnforgeRequest n O ≃ Fin n ⊕ (Fin n × KeyRing S.PK N × S.Msg) ⊕ (Fin n × O.BMsg) where
  toFun
    | .corrupt i => .inl i
    | .sign s R m => .inr (.inl (s, R, m))
    | .sideSign i bm => .inr (.inr (i, bm))
  invFun
    | .inl i => .corrupt i
    | .inr (.inl p) => .sign p.1 p.2.1 p.2.2
    | .inr (.inr p) => .sideSign p.1 p.2
  left_inv r := by cases r <;> rfl
  right_inv p := by rcases p with _ | ⟨_, _, _⟩ | ⟨_, _⟩ <;> rfl

instance instFintypeUnforgeRequest [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.Msg]
    [Fintype O.BMsg] :
    Fintype (UnforgeRequest n O) :=
  Fintype.ofEquiv _ (UnforgeRequest.equivSum n O).symm

/-- **With a user, the requests of the unforgeability game are inhabited** (by a corruption); the
one instance of `Inhabited (UnforgeRequest n O)`. -/
instance UnforgeRequest.instInhabitedOfNeZero [NeZero n] : Inhabited (UnforgeRequest n O) :=
  ⟨.corrupt 0⟩

/-- Replies as a sum type. -/
def UnforgeResponse.equivSum : UnforgeResponse O ≃ S.KeyCoins ⊕ S.Sig ⊕ O.BSig where
  toFun
    | .keyCoins kc => .inl kc
    | .signature σ => .inr (.inl σ)
    | .sideSignature τ => .inr (.inr τ)
  invFun
    | .inl kc => .keyCoins kc
    | .inr (.inl σ) => .signature σ
    | .inr (.inr τ) => .sideSignature τ
  left_inv r := by cases r <;> rfl
  right_inv p := by rcases p with _ | _ | _ <;> rfl

instance instFintypeUnforgeResponse [Fintype TS.KeyCoins] [Fintype TS.Sig] [Fintype O.BSig] :
    Fintype (UnforgeResponse O) :=
  Fintype.ofEquiv _ (UnforgeResponse.equivSum O).symm

variable (S) in
/-- **The challenger of the unforgeability game** at the honest users' key coins `keys`, answering
`Q` requests: request number `j < Q` with the signing coins `ω j` (uniform). Corruption returns the
user's key coins; `OSign(s, R, m)` is answered by the scheme's signer of user `s` when its public key
is in `R` (its refusal `none` passed on), and by `none` otherwise; a side request by the side signer.
Requests after the `Q`-th get `none`. It reprograms nothing. -/
noncomputable def unforgeChallenger [DecidableEq TS.PK] [Fintype TS.SignCoins]
    [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins] (keys : Fin n → S.KeyCoins) (Q : ℕ) :
    Challenger X Y (UnforgeRequest n O) (UnforgeResponse O) where
  Coins := Fin Q → S.SignCoins
  coins := PMF.uniformOfFintype _
  Q := Q
  q := max S.q O.q
  respond ω hist r :=
    if h : hist.length < Q then
      match r with
      | .corrupt i => .pure ⟨some (.keyCoins (keys i)), []⟩
      | .sign s R m =>
        if S.pk (keys s) ∈ R.1 then
          (S.sign (S.keyGen (keys s)) R m (ω ⟨hist.length, h⟩)).bind fun o =>
            .pure ⟨o.map .signature, []⟩
        else .pure ⟨none, []⟩
      | .sideSign i bm =>
        (O.sign (S.keyGen (keys i)) bm (ω ⟨hist.length, h⟩)).bind fun o =>
          .pure ⟨o.map .sideSignature, []⟩
    else .pure ⟨none, []⟩
  respond_queries ω hist r H := by
    split_ifs with h
    · rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
      · simp
      · dsimp only
        split_ifs
        · rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
          exact (S.sign_queries _ _ _ _ H).trans (le_max_left _ _)
        · simp
      · dsimp only
        rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
        exact (O.sign_queries _ _ _ H).trans (le_max_right _ _)
    · simp

/-! ### The winning condition -/

/-- The history of the unforgeability game. -/
abbrev UnforgeHist : Type := List (HistoryEntry (UnforgeRequest n O) (UnforgeResponse O))

variable {n O}

/-- **User `i` was corrupted** by an answered request of `hist`. -/
def Corrupted (hist : UnforgeHist n O) (i : Fin n) : Prop :=
  ∃ e ∈ hist, e.request = .corrupt i

/-- **A ring signature on `(R, m)` was requested** by an answered request of `hist` (BKM06's
`(?, M*, R*)`). -/
def SignQueried (hist : UnforgeHist n O) (R : KeyRing S.PK N) (m : S.Msg) : Prop :=
  ∃ e ∈ hist, ∃ s, e.request = .sign s R m

/-- **A member of `R` was asked for a side signature covering `(R, m)`** by an answered request of
`hist`, at the users' key coins `keys`. -/
def SideCovered (keys : Fin n → S.KeyCoins) (hist : UnforgeHist n O) (R : KeyRing S.PK N)
    (m : S.Msg) : Prop :=
  ∃ e ∈ hist, ∃ i bm, e.request = .sideSign i bm ∧ S.pk (keys i) ∈ R ∧ O.Covers bm R m

/-- **A fresh ring and message** for the key coins `keys` and the history `hist` (BKM06
Definition 7, step 4: "`A` never queried `(?, M*, R*)`, and `R* ⊆ S \ C`"): every key of the ring is
the key of an uncorrupted user, no ring signature on `(R, m)` was requested, and no member was asked
for a side signature covering `(R, m)`. -/
structure Fresh (keys : Fin n → S.KeyCoins) (hist : UnforgeHist n O) (R : KeyRing S.PK N)
    (m : S.Msg) : Prop where
  /-- Every key of the ring is the key of an uncorrupted user. -/
  honest_ring : ∀ pk ∈ R, ∃ i, S.pk (keys i) = pk ∧ ¬ Corrupted hist i
  /-- No ring signature on the ring and message was requested. -/
  not_signQueried : ¬ SignQueried hist R m
  /-- No member was asked for a side signature covering the ring and message. -/
  not_sideCovered : ¬ SideCovered keys hist R m

/-- **The output `(R*, m*, σ*)` is a forgery** at the key coins `keys`, the oracle `H` and the
history `hist`: `σ*` verifies on `(R*, m*)` at `H`, and `(R*, m*)` is fresh. -/
structure Forges (keys : Fin n → S.KeyCoins) (H : X → Y) (out : S.RingForgery)
    (hist : UnforgeHist n O) : Prop where
  /-- The signature verifies. -/
  verify_eq : S.verify H out.ring out.msg out.sig = true
  /-- The ring and message are fresh. -/
  fresh : Fresh keys hist out.ring out.msg

/-- **With no requests, a ring is fresh exactly when its keys are honest.** -/
theorem fresh_nil_iff {keys : Fin n → S.KeyCoins} {R : KeyRing S.PK N} {m : S.Msg} :
    Fresh (O := O) keys [] R m ↔ ∀ pk ∈ R.1, ∃ i, S.pk (keys i) = pk := by
  constructor
  · intro h pk hpk
    obtain ⟨i, hi, -⟩ := h.honest_ring pk hpk
    exact ⟨i, hi⟩
  · intro h
    refine ⟨fun pk hpk => ?_, ?_, ?_⟩
    · obtain ⟨i, hi⟩ := h pk hpk
      exact ⟨i, hi, by simp [Corrupted]⟩
    · simp [SignQueried]
    · simp [SideCovered]

/-- **The win condition is not vacuous**: with no requests, a verifying signature on a ring of
honest keys is a forgery. -/
theorem forges_nil {keys : Fin n → S.KeyCoins} {H : X → Y} {R : KeyRing S.PK N} {m : S.Msg}
    {σ : S.Sig} (hv : S.verify H R m σ = true) (hR : ∀ pk ∈ R.1, ∃ i, S.pk (keys i) = pk) :
    Forges (O := O) keys H (R, m, σ) [] :=
  ⟨hv, fresh_nil_iff.2 hR⟩

/-- **Freshness is lost, never gained**: a ring and message fresh after a history are fresh after
every sub-history. -/
theorem Fresh.anti {keys : Fin n → S.KeyCoins} {hist hist' : UnforgeHist n O}
    {R : KeyRing S.PK N} {m : S.Msg} (h : Fresh keys hist R m) (hsub : hist' ⊆ hist) :
    Fresh keys hist' R m where
  honest_ring pk hpk := by
    obtain ⟨i, hi, hc⟩ := h.honest_ring pk hpk
    exact ⟨i, hi, fun ⟨e, he, hr⟩ => hc ⟨e, hsub he, hr⟩⟩
  not_signQueried := fun ⟨e, he, hr⟩ => h.not_signQueried ⟨e, hsub he, hr⟩
  not_sideCovered := fun ⟨e, he, hr⟩ => h.not_sideCovered ⟨e, hsub he, hr⟩

/-- **A ring holding only corrupted users' keys is never fresh**: if every user whose key is `pk`
was corrupted, no ring containing `pk` is fresh. -/
theorem not_fresh_of_corrupted {keys : Fin n → S.KeyCoins} {hist : UnforgeHist n O}
    {R : KeyRing S.PK N} {m : S.Msg} {pk : S.PK} (hpk : pk ∈ R.1)
    (hc : ∀ i, S.pk (keys i) = pk → Corrupted hist i) : ¬ Fresh keys hist R m := fun h => by
  obtain ⟨i, hi, hn⟩ := h.honest_ring pk hpk
  exact hn (hc i hi)

/-- **Without a side oracle no forgery is covered.** -/
theorem not_sideCovered_none {keys : Fin n → S.KeyCoins}
    {hist : UnforgeHist n (SideOracle.none S)} {R : KeyRing S.PK N} {m : S.Msg} :
    ¬ SideCovered keys hist R m := fun ⟨_, _, _, bm, _⟩ => bm.elim

/-- **The trivial scheme's forgeries**: its verification accepts everything, so with no requests
every ring of honest keys is forged; `Forges` is satisfiable. -/
theorem trivial_forges {O : SideOracle (RingScheme.trivial X Y N)} {keys : Fin n → Unit}
    {H : X → Y} {R : KeyRing Unit N} (hR : ∀ pk ∈ R.1, ∃ i, (RingScheme.trivial X Y N).pk (keys i) = pk) :
    Forges (O := O) keys H (R, (), ()) [] :=
  forges_nil rfl hR

/-! ### The game -/

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.Msg] [DecidableEq TS.Msg]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] [Fintype TS.Sig] [DecidableEq TS.Sig]

variable [Fintype O.BMsg] [DecidableEq O.BMsg] [Fintype O.BSig] [DecidableEq O.BSig]

variable (S n O) in
/-- **An adversary of the unforgeability game** with `n` honest users and at most `t` queries: on
the users' public keys and the table `V` of the oracle, a `t`-query adversary making requests and
outputting a ring, a message and a ring signature (`GameAdversary`). -/
abbrev UnforgeAdversary (V : OracleView X Y) (t : ℕ) : Type 1 :=
  GameAdversary X Y (UnforgeRequest n O) (UnforgeResponse O) ((Fin n → S.PK) × V.Tab)
    S.RingForgery t

variable (S n) in
/-- **An adversary of BKM06 Definition 7**: no side oracle. -/
abbrev InsiderAdversary (V : OracleView X Y) (t : ℕ) : Type 1 :=
  UnforgeAdversary S n (SideOracle.none S) V t

variable {V : OracleView X Y} {t : ℕ} [Nonempty TS.KeyCoins] [Fintype TS.SignCoins]
  [DecidableEq TS.SignCoins] [Nonempty TS.SignCoins]

/-- **The run of the unforgeability game** with `Q` requests: the users' key coins and the oracle
uniform, the adversary on the public keys and the oracle's table against the challenger. -/
noncomputable def unforgeLaw (A : UnforgeAdversary S n O V t) (Q : ℕ) :
    PMF (GameRun (Fin n → S.KeyCoins) X Y S.RingForgery
      (UnforgeRequest n O) (UnforgeResponse O)) :=
  runLaw (fun keys H => A (fun i => S.pk (keys i), V.view H)) fun keys =>
    unforgeChallenger S n O keys Q

/-- **The probability of a forgery** in the unforgeability game with `Q` requests: the adversary
terminates with a forgery (`Forges`) for the users' key coins, the oracle and the answered
requests. -/
noncomputable def forgeProb (A : UnforgeAdversary S n O V t) (Q : ℕ) : ℝ≥0∞ :=
  (unforgeLaw A Q).toOuterMeasure {r | r.Wins Forges}

/-- **The forgery probability is at most `1`.** -/
theorem forgeProb_le_one (A : UnforgeAdversary S n O V t) (Q : ℕ) : forgeProb A Q ≤ 1 :=
  prob_runLaw_le_one _ _ _

/-- **The probability of a forgery in BKM06 Definition 7** (unforgeability w.r.t. insider
corruption) with `Q` requests: the game without a side oracle. -/
noncomputable def insiderForgeProb (A : InsiderAdversary S n V t) (Q : ℕ) : ℝ≥0∞ :=
  forgeProb A Q

/-- **No forgery output, no forgery**: if the scheme has no ring forgeries (for instance no
message, or no signature), the adversary never terminates with an output and the forgery
probability is `0`. -/
theorem forgeProb_eq_zero_of_isEmpty [IsEmpty S.RingForgery] (A : UnforgeAdversary S n O V t)
    (Q : ℕ) : forgeProb A Q = 0 :=
  (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2
    (Set.disjoint_left.2 fun _ _ ⟨p, _, _⟩ => isEmptyElim (p.1 : S.RingForgery))

/-- **No forgery output, no forgery in BKM06 Definition 7** (`forgeProb_eq_zero_of_isEmpty`). -/
theorem insiderForgeProb_eq_zero_of_isEmpty [IsEmpty S.RingForgery]
    (A : InsiderAdversary S n V t) (Q : ℕ) : insiderForgeProb A Q = 0 :=
  forgeProb_eq_zero_of_isEmpty A Q

end GordieHowe.RingSignature
