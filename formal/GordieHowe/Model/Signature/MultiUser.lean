-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.Properties
public import GordieHowe.Model.RingSignature.Adversary

@[expose] public section

/-!
# Multi-user unforgeability with adaptive corruption

The multi-user signature games with adaptive corruption, MU-EUF-CMA^corr (Bader, Hofheinz, Jager,
Kiltz, Li, "Tightly-Secure Authenticated Key Exchange", TCC 2015, ePrint 2014/797, Definition 2,
p. 6) and its strong form MU-SUF-CMA^corr (Diemert, Gellert, Jager, Lyu, "More Efficient Digital
Signatures with Tight Multi-user Security", PKC 2021, ePrint 2021/235, Definition 2, pp. 7–8),
for a `RingSignature.BaseSigner`, against the adversaries of
`GordieHowe/Model/RingSignature/Adversary.lean`. The games are defined once, over a signing
interface (`SignOracle`), and instantiated at the ring-aware signer (`SignOracle.ring`) and at the
ordinary signer (`SignOracle.std`, the base scheme's own game).

- `SignOracle B`: the signing oracle of a game: its messages `SMsg`, coins, a classical oracle
  program signing a message with a user's key pair and coins (it may refuse), and the base message
  `base sm` a signature on `sm` is for. `SignOracle.ring B`: messages `(R, m)`, answered by
  `bsign` at the signer's first position in `R` (refused when its key is not in `R`), for the base
  message `bmsg R m`. `SignOracle.std B`: base messages, answered by `ssign`. `SignOracle.ringStd B`:
  both, a request being a ring and a message or a base message (the key-reuse setting).
- `MURequest O n`, `MUResponse B`: the public key of user `i`, a signature of user `i` on a message
  (`sign i sm`), the corruption of user `i` (answered with its key coins); finite types through
  `MURequest.equivSum`, `MUResponse.equivSum`.
- `muChallenger O n keys Q`: the challenger at the users' key coins answering `Q` requests, each
  signing request with fresh uniform coins.
- `MUAdversary O n V t`: a `t`-query adversary on the users' public keys and the table `V` of the
  oracle, outputting a candidate `(pk, bm, σ)`. The replies of the challenger are public keys,
  signatures and key coins (`MUResponse`), so a secret key reaches it only through the key coins a
  corruption request returns.
- `MUHist O n`, `Corrupted`, `Signed`, `Returned`, `ReturnedSig`: the history and its records (user
  `i` corrupted; asked to sign a message for the base message `bm`; returned `σ` on such a message;
  returned `σ`). `Returned.signed`: a returned signature was asked for.
- `Forges` (MU-EUF-CMA^corr): `σ` verifies on `bm` under `pk` at the oracle, and `pk` is the key of a
  user neither corrupted nor asked to sign for `bm`. `StrongForges` (MU-SUF-CMA^corr): `pk` is the key
  of a user neither corrupted nor returned `σ` on a message for `bm`. `SigStrongForges`: neither
  corrupted nor returned `σ` on any message (the freshness of
  `GordieHowe/Applications/Ring/StrongForger.lean`, `Ring.StrongForgery`).
- `muLaw A Q`: the run of the game with `Q` requests. `muEufProb`, `muSufProb`, `muSufSigProb`: the
  probabilities of the three events in it.
- Relations: `Forges.strongForges` and `SigStrongForges.strongForges` (both events are contained in
  the strong one), so `muEufProb_le_muSufProb` and `muSufSigProb_le_muSufProb`; `forges_nil` (with
  no requests, a verifying signature under an honest key is a forgery: the events are not
  vacuous); `Forges.anti`, `StrongForges.anti` (freshness is lost, never gained, along the
  history); `muSufProb_eq_zero_of_reject`, `muEufProb_eq_zero_of_reject` (a base verification that
  rejects everything makes the MU-SUF-CMA^corr and MU-EUF-CMA^corr probabilities `0`);
  `muSufProb_le_one`, `muEufProb_le_one`.
- Transfer along a relay: `HistRelay hist hist'` says every signing request of `hist'` is for the
  base message of a signing request of `hist` by the same user, and every corruption in `hist'` is
  one in `hist`; then `Forges.of_histRelay` (a forgery for `hist` is one for `hist'`) and
  `StrongForges.of_histRelay` (a strong forgery for `hist` is one for `hist'` when every signature
  returned in `hist'` is returned in `hist` or lies in a set `Extra` of extra signatures, and the
  forgery's signature lies in no `Extra i bm` of its base message).

## Comparison with Bader et al. Definition 2 and Diemert et al. Definition 2

Their game: `n` key pairs; oracles `Sign(i, m)`, `Corrupt(i)` returning `sk_i`; the forger outputs
`(i*, m*, σ*)` and wins if `σ*` verifies on `m*` under `pk_{i*}`, `i*` was not corrupted, and
`(i*, m*)` was not signed (EUF) or `(m*, σ*)` was not returned to `i*` (SUF). The deliberate
differences:

1. **The forgery names a public key** in place of an index: it wins if some user with that key
   qualifies. The forgeries of `Ring.BaseForgery` (`GordieHowe/Applications/Ring/Games.lean`) do
   the same.
2. **Corruption returns the key coins** (as BKP20, ePrint 2020/646, p. 7, and CCLM22, ePrint
   2021/1616, Experiment 3, p. 21), which determine `sk_i`.
3. **The signing oracle is an interface.** At `SignOracle.std` it is the base scheme's signer on
   base messages: the game above for the base scheme (FIPS 204 / FIPS 206). At `SignOracle.ring` a
   request is `(R, m)` and is answered by the ring-aware signer, which may read the ring and
   refuse; freshness compares the base messages `bmsg R m`. The signer may refuse (`⊥`); a refused
   request is in the history and counts against freshness (it was "queried").
4. **Only answered requests count.** The challenger answers the first `Q` requests; a request after
   the `Q`-th gets `none` and is not recorded.
5. **Quantum adversaries in the QROM** with at most `t` superposition queries and `Q` requests, with
   the part `V` of the oracle given whole; verification of the forgery at the same oracle.
6. **Concrete probabilities in place of asymptotic advantages.** The adversaries need not be
   efficient, so the theorems of the library bound their games by these probabilities for explicit
   adversaries built from the adversaries of their games. For ML-DSA, FIPS 204 §3.1 (p. 9: "ML-DSA
   is designed to be strongly existentially unforgeable under chosen message attack (SUF-CMA)")
   is the cited reason to expect them small for efficient adversaries.
   For ML-DSA's design, Kiltz, Lyubashevsky, Schaffner (EUROCRYPT 2018, ePrint 2017/916, Theorem 3.1
   and eq. (21)) bound the SUF-CMA advantage of Dilithium in the QROM; ePrint 2023/245 (Devevey,
   Fallahpour, Passelègue, Stehlé) and ePrint 2023/246 (Barbosa et al.) report a gap in that
   paper's reduction from chosen-message to no-message attacks and give corrected proofs. The
   library does not prove these statements. Its bounds are stated in terms of `muEufProb` and
   `muSufProb` of explicit adversaries, and a theorem that assumes such a statement takes a named
   predicate over a class of adversaries: `MUEufCmaHard`, `MUSufCmaHard` and their single-user and
   no-message forms (`GordieHowe/Model/Signature/Assumptions.lean`), and at the library's base
   signers `MLDSASufCma`, `MLDSAMUSufCma`, `Falcon512EufCma`, `Falcon512MUEufCma`
   (`GordieHowe/Applications/Ring/BaseSignerAssumptions.lean`).
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes} (B : BaseSigner X Y N TB)

/-- **The signing oracle of a multi-user game** for the base signer `B`: messages `SMsg`, uniform
coins, a classical oracle program with at most `q` queries signing a message with a user's key pair
and coins (`none` is a refusal), and the base message `base sm` that a signature on `sm` is for. -/
structure SignOracle where
  /-- The messages of the oracle. -/
  SMsg : Type
  /-- The coins of one signature. -/
  Coins : Type
  [instFintypeSMsg : Fintype SMsg]
  [instDecEqSMsg : DecidableEq SMsg]
  [instFintypeCoins : Fintype Coins]
  [instDecEqCoins : DecidableEq Coins]
  [instNonemptyCoins : Nonempty Coins]
  /-- The bound on the signer's queries. -/
  q : ℕ
  /-- The signer. -/
  sign : B.PK × B.SK → SMsg → Coins → OracleProg X Y (Option B.BSig)
  /-- It makes at most `q` queries. -/
  sign_queries : ∀ kp sm c, (sign kp sm c).QueriesLE q
  /-- The base message a signature on the message is for. -/
  base : SMsg → B.BMsg

attribute [instance] SignOracle.instFintypeSMsg SignOracle.instDecEqSMsg
  SignOracle.instFintypeCoins SignOracle.instDecEqCoins SignOracle.instNonemptyCoins

namespace SignOracle

/-- **The ring-aware signing oracle**: a request `(R, m)` by the key pair `kp` is answered by `bsign`
at the first position of `kp.1` in `R` (as `ofBase` signs), and refused when `kp.1` is not in `R`;
the signature is for the base message `bmsg R m`. -/
noncomputable def ring : SignOracle B where
  SMsg := KeyRing B.PK N × B.Msg
  Coins := B.Coins
  q := B.q
  sign kp p c :=
    if kp.1 ∈ p.1.1 then B.bsign kp.2 p.1 (p.1.1.idxOf kp.1) p.2 c else .pure none
  sign_queries kp p c := by
    split_ifs
    · exact B.bsign_queries _ _ _ _ _
    · exact OracleProg.QueriesLE.pure _ _
  base p := B.bmsg p.1 p.2

/-- **The ordinary signing oracle**: base messages, answered by `ssign`. With it the game is the
base scheme's own multi-user game. -/
def std : SignOracle B where
  SMsg := B.BMsg
  Coins := B.Coins
  q := B.q
  sign kp bm c := B.ssign kp.2 bm c
  sign_queries kp bm c := B.ssign_queries kp.2 bm c
  base bm := bm

/-- **The ring-aware and the ordinary signing oracle together**: a request is a ring and a message
(`inl`, answered as `ring` answers it, for the base message `bmsg R m`) or a base message (`inr`,
answered by `ssign`, for itself). With it the game is the multi-user game of a user who signs with
one key both in rings and in the base scheme (the setting of the key-reuse game of
`GordieHowe/Model/RingSignature/KeyReuse.lean`). -/
noncomputable def ringStd : SignOracle B where
  SMsg := (KeyRing B.PK N × B.Msg) ⊕ B.BMsg
  Coins := B.Coins
  q := B.q
  sign kp
    | .inl p, c => (ring B).sign kp p c
    | .inr bm, c => (std B).sign kp bm c
  sign_queries kp sm c := by
    rcases sm with p | bm
    · exact (ring B).sign_queries kp p c
    · exact (std B).sign_queries kp bm c
  base
    | .inl p => (ring B).base p
    | .inr bm => (std B).base bm

end SignOracle

variable {B} (O : SignOracle B) (n : ℕ)

/-- **A request of the multi-user game**: the public key of user `i`, a signature of user `i` on
`sm`, or the corruption of user `i`. -/
inductive MURequest where
  /-- The public key of user `i`. -/
  | publicKey (i : Fin n)
  /-- A signature of user `i` on `sm`. -/
  | sign (i : Fin n) (sm : O.SMsg)
  /-- The corruption of user `i`. -/
  | corrupt (i : Fin n)
deriving DecidableEq

variable (B) in
/-- **A reply of the multi-user game**: a public key, a signature, or key coins. -/
inductive MUResponse where
  /-- A public key. -/
  | publicKey (pk : B.PK)
  /-- A signature. -/
  | signature (σ : B.BSig)
  /-- The key coins of a corrupted user. -/
  | keyCoins (kc : B.KeyCoins)
deriving DecidableEq

/-- Requests as a sum type. -/
def MURequest.equivSum : MURequest O n ≃ Fin n ⊕ (Fin n × O.SMsg) ⊕ Fin n where
  toFun
    | .publicKey i => .inl i
    | .sign i sm => .inr (.inl (i, sm))
    | .corrupt i => .inr (.inr i)
  invFun
    | .inl i => .publicKey i
    | .inr (.inl p) => .sign p.1 p.2
    | .inr (.inr i) => .corrupt i
  left_inv r := by cases r <;> rfl
  right_inv p := by rcases p with _ | ⟨_, _⟩ | _ <;> rfl

instance : Fintype (MURequest O n) :=
  Fintype.ofEquiv _ (MURequest.equivSum O n).symm

variable (B) in
/-- Replies as a sum type. -/
def MUResponse.equivSum : MUResponse B ≃ B.PK ⊕ B.BSig ⊕ B.KeyCoins where
  toFun
    | .publicKey pk => .inl pk
    | .signature σ => .inr (.inl σ)
    | .keyCoins kc => .inr (.inr kc)
  invFun
    | .inl pk => .publicKey pk
    | .inr (.inl σ) => .signature σ
    | .inr (.inr kc) => .keyCoins kc
  left_inv r := by cases r <;> rfl
  right_inv p := by rcases p with _ | _ | _ <;> rfl

instance : Fintype (MUResponse B) :=
  Fintype.ofEquiv _ (MUResponse.equivSum B).symm

/-- **The challenger of the multi-user game** at the users' key coins `keys`, answering `Q`
requests: request number `j < Q` with the signing coins `ω j` (uniform). A public-key request is
answered with the user's public key, a signing request by the oracle's signer with the user's key
pair (its refusal `none` passed on), a corruption with the user's key coins. Requests after the
`Q`-th get `none`. It reprograms nothing. -/
noncomputable def muChallenger (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    Challenger X Y (MURequest O n) (MUResponse B) where
  Coins := Fin Q → O.Coins
  coins := PMF.uniformOfFintype _
  Q := Q
  q := O.q
  respond ω hist r :=
    if h : hist.length < Q then
      match r with
      | .publicKey i => .pure ⟨some (.publicKey (B.pk (keys i))), []⟩
      | .sign i sm =>
        (O.sign (B.keyGen (keys i)) sm (ω ⟨hist.length, h⟩)).bind fun o =>
          .pure ⟨o.map .signature, []⟩
      | .corrupt i => .pure ⟨some (.keyCoins (keys i)), []⟩
    else .pure ⟨none, []⟩
  respond_queries ω hist r H := by
    split_ifs with h
    · rcases r with i | ⟨i, sm⟩ | i
      · simp
      · dsimp only
        rw [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil]
        exact O.sign_queries _ _ _ H
      · simp
    · simp

/-! ### The winning conditions -/

/-- The history of the multi-user game. -/
abbrev MUHist : Type := List (HistoryEntry (MURequest O n) (MUResponse B))

variable {O n}

/-- **User `i` was corrupted** by an answered request of `hist`. -/
def Corrupted (hist : MUHist O n) (i : Fin n) : Prop :=
  ∃ e ∈ hist, e.request = .corrupt i

/-- **User `i` was asked to sign for the base message `bm`** by an answered request of `hist` (refused
or not). -/
def Signed (hist : MUHist O n) (i : Fin n) (bm : B.BMsg) : Prop :=
  ∃ e ∈ hist, ∃ sm, e.request = .sign i sm ∧ O.base sm = bm

/-- **User `i` was returned `σ` on a message for the base message `bm`** by an answered request of
`hist`. -/
def Returned (hist : MUHist O n) (i : Fin n) (bm : B.BMsg) (σ : B.BSig) : Prop :=
  ∃ e ∈ hist, ∃ sm, e.request = .sign i sm ∧ O.base sm = bm ∧ e.response = some (.signature σ)

/-- **User `i` was returned `σ`** on some message by an answered request of `hist`. -/
def ReturnedSig (hist : MUHist O n) (i : Fin n) (σ : B.BSig) : Prop :=
  ∃ bm, Returned hist i bm σ

/-- **A forgery of MU-EUF-CMA^corr** at the key coins `keys`, the oracle `H` and the history `hist`:
`σ` verifies on `bm` under `pk` at `H`, and `pk` is the key of a user neither corrupted nor asked
to sign for `bm`. -/
structure Forges (keys : Fin n → B.KeyCoins) (H : X → Y) (f : B.PK × B.BMsg × B.BSig)
    (hist : MUHist O n) : Prop where
  /-- The signature verifies. -/
  verify_eq : B.bverify H f.1 f.2.1 f.2.2 = true
  /-- The key is that of a user neither corrupted nor asked to sign for the base message. -/
  exists_user : ∃ i, B.pk (keys i) = f.1 ∧ ¬ Corrupted hist i ∧ ¬ Signed hist i f.2.1

/-- **A forgery of MU-SUF-CMA^corr** (Diemert et al. Definition 2): `σ` verifies on `bm` under `pk`,
and `pk` is the key of a user neither corrupted nor returned `σ` on a message for `bm`. -/
structure StrongForges (keys : Fin n → B.KeyCoins) (H : X → Y) (f : B.PK × B.BMsg × B.BSig)
    (hist : MUHist O n) : Prop where
  /-- The signature verifies. -/
  verify_eq : B.bverify H f.1 f.2.1 f.2.2 = true
  /-- The key is that of a user neither corrupted nor returned the pair. -/
  exists_user : ∃ i, B.pk (keys i) = f.1 ∧ ¬ Corrupted hist i ∧ ¬ Returned hist i f.2.1 f.2.2

/-- **A strong forgery whose signature was never returned to the user** (the freshness of
`Ring.StrongForgery`, `GordieHowe/Applications/Ring/StrongForger.lean`): `σ` verifies on `bm` under
`pk`, and `pk` is the key of a user neither corrupted nor returned `σ` on any message. -/
structure SigStrongForges (keys : Fin n → B.KeyCoins) (H : X → Y) (f : B.PK × B.BMsg × B.BSig)
    (hist : MUHist O n) : Prop where
  /-- The signature verifies. -/
  verify_eq : B.bverify H f.1 f.2.1 f.2.2 = true
  /-- The key is that of a user neither corrupted nor returned the signature. -/
  exists_user : ∃ i, B.pk (keys i) = f.1 ∧ ¬ Corrupted hist i ∧ ¬ ReturnedSig hist i f.2.2

/-- A returned signature was asked for. -/
theorem Returned.signed {hist : MUHist O n} {i : Fin n} {bm : B.BMsg} {σ : B.BSig}
    (h : Returned hist i bm σ) : Signed hist i bm := by
  obtain ⟨e, he, sm, hr, hb, -⟩ := h
  exact ⟨e, he, sm, hr, hb⟩

/-- **An existential forgery is a strong forgery.** -/
theorem Forges.strongForges {keys : Fin n → B.KeyCoins} {H : X → Y} {f : B.PK × B.BMsg × B.BSig}
    {hist : MUHist O n} (h : Forges keys H f hist) : StrongForges keys H f hist := by
  obtain ⟨i, hi, hc, hs⟩ := h.exists_user
  exact ⟨h.verify_eq, i, hi, hc, fun hr => hs hr.signed⟩

/-- **A strong forgery with a never-returned signature is a strong forgery.** -/
theorem SigStrongForges.strongForges {keys : Fin n → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O n} (h : SigStrongForges keys H f hist) :
    StrongForges keys H f hist := by
  obtain ⟨i, hi, hc, hs⟩ := h.exists_user
  exact ⟨h.verify_eq, i, hi, hc, fun hr => hs ⟨_, hr⟩⟩

/-- **The win condition is not vacuous**: with no requests, a verifying signature under the key of
a user is a forgery. -/
theorem forges_nil {keys : Fin n → B.KeyCoins} {H : X → Y} {f : B.PK × B.BMsg × B.BSig}
    (hv : B.bverify H f.1 f.2.1 f.2.2 = true) (hk : ∃ i, B.pk (keys i) = f.1) :
    Forges (O := O) keys H f [] := by
  obtain ⟨i, hi⟩ := hk
  exact ⟨hv, i, hi, by simp [Corrupted], by simp [Signed]⟩

/-- **Freshness is lost, never gained**: a forgery after a history is one after every
sub-history. -/
theorem Forges.anti {keys : Fin n → B.KeyCoins} {H : X → Y} {f : B.PK × B.BMsg × B.BSig}
    {hist hist' : MUHist O n} (h : Forges keys H f hist) (hsub : hist' ⊆ hist) :
    Forges keys H f hist' := by
  obtain ⟨i, hi, hc, hs⟩ := h.exists_user
  exact ⟨h.verify_eq, i, hi, fun ⟨e, he, hr⟩ => hc ⟨e, hsub he, hr⟩,
    fun ⟨e, he, sm, hr⟩ => hs ⟨e, hsub he, sm, hr⟩⟩

/-- **Strong freshness is lost, never gained.** -/
theorem StrongForges.anti {keys : Fin n → B.KeyCoins} {H : X → Y} {f : B.PK × B.BMsg × B.BSig}
    {hist hist' : MUHist O n} (h : StrongForges keys H f hist) (hsub : hist' ⊆ hist) :
    StrongForges keys H f hist' := by
  obtain ⟨i, hi, hc, hs⟩ := h.exists_user
  exact ⟨h.verify_eq, i, hi, fun ⟨e, he, hr⟩ => hc ⟨e, hsub he, hr⟩,
    fun ⟨e, he, sm, hr⟩ => hs ⟨e, hsub he, sm, hr⟩⟩

/-! ### Transfer along a relay of requests -/

variable {O' : SignOracle B}

/-- **The history `hist'` of a game with the oracle `O'` relays the history `hist` of a game with
the oracle `O`**: every signing request of user `i` in `hist'` is for the base message of a signing
request of user `i` in `hist`, and every corruption in `hist'` is one in `hist`. -/
structure HistRelay (hist : MUHist O n) (hist' : MUHist O' n) : Prop where
  /-- Every signing request of the relay is for the base message of one of the history. -/
  sign_mem : ∀ e' ∈ hist', ∀ i sm', e'.request = .sign i sm' → Signed hist i (O'.base sm')
  /-- Every corruption of the relay is one of the history. -/
  corrupt_mem : ∀ i, Corrupted hist' i → Corrupted hist i

/-- **A forgery for a history is a forgery for every relay of it**: the relay asked no user to sign
for a base message the history did not, and corrupted no user the history did not. -/
theorem Forges.of_histRelay {keys : Fin n → B.KeyCoins} {H : X → Y} {f : B.PK × B.BMsg × B.BSig}
    {hist : MUHist O n} {hist' : MUHist O' n} (h : Forges keys H f hist)
    (hr : HistRelay hist hist') : Forges keys H f hist' := by
  obtain ⟨i, hi, hc, hs⟩ := h.exists_user
  refine ⟨h.verify_eq, i, hi, fun h' => hc (hr.corrupt_mem i h'), ?_⟩
  rintro ⟨e', he', sm', hreq, hb⟩
  exact hs (hb ▸ hr.sign_mem e' he' i sm' hreq)

/-- **A strong forgery for a history is one for a relay of it** when its signature is not among
the relay's extra signatures: if every signature returned in `hist'` is returned in `hist` or lies in
`Extra i bm` (the signatures the reduction obtained and did not pass on, such as the rejected
attempts of a rejection signer), a strong forgery for `hist` whose signature is in no `Extra i bm`
of its base message is a strong forgery for `hist'`. -/
theorem StrongForges.of_histRelay {keys : Fin n → B.KeyCoins} {H : X → Y}
    {f : B.PK × B.BMsg × B.BSig} {hist : MUHist O n} {hist' : MUHist O' n}
    {Extra : Fin n → B.BMsg → B.BSig → Prop} (h : StrongForges keys H f hist)
    (hr : HistRelay hist hist')
    (hret : ∀ i bm σ, Returned hist' i bm σ → Returned hist i bm σ ∨ Extra i bm σ)
    (hf : ∀ i, ¬ Extra i f.2.1 f.2.2) : StrongForges keys H f hist' := by
  obtain ⟨i, hi, hc, hs⟩ := h.exists_user
  refine ⟨h.verify_eq, i, hi, fun h' => hc (hr.corrupt_mem i h'), fun h' => ?_⟩
  rcases hret i _ _ h' with h'' | h''
  · exact hs h''
  · exact hf i h''

/-! ### The games -/

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y]

variable (O n) in
/-- **An adversary of the multi-user game** with `n` users and at most `t` queries: on the users'
public keys and the table `V` of the oracle, a `t`-query adversary making requests and outputting a
public key, a base message and a base signature (`GameAdversary`). -/
abbrev MUAdversary (V : OracleView X Y) (t : ℕ) : Type 1 :=
  GameAdversary X Y (MURequest O n) (MUResponse B) ((Fin n → B.PK) × V.Tab)
    (B.PK × B.BMsg × B.BSig) t

variable {V : OracleView X Y} {t : ℕ}

/-- **The run of the multi-user game** with `Q` requests: the users' key coins and the oracle
uniform, the adversary on the public keys and the oracle's table against the challenger. -/
noncomputable def muLaw (A : MUAdversary O n V t) (Q : ℕ) :
    PMF ((Fin n → B.KeyCoins) × (X → Y) ×
      Option ((B.PK × B.BMsg × B.BSig) × MUHist O n)) :=
  runLaw (fun keys H => A (fun i => B.pk (keys i), V.view H)) fun keys => muChallenger O n keys Q

/-- **The success probability of the adversary in MU-EUF-CMA^corr** with `Q` requests: it
terminates with a forgery (`Forges`) for the users' key coins, the oracle and the answered
requests. -/
noncomputable def muEufProb (A : MUAdversary O n V t) (Q : ℕ) : ℝ≥0∞ :=
  (muLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2}

/-- **The success probability of the adversary in MU-SUF-CMA^corr** with `Q` requests
(`StrongForges`). -/
noncomputable def muSufProb (A : MUAdversary O n V t) (Q : ℕ) : ℝ≥0∞ :=
  (muLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2, StrongForges x.1 x.2.1 p.1 p.2}

/-- **The success probability of the adversary in the strong game with never-returned
signatures** with `Q` requests (`SigStrongForges`, the freshness of `Ring.StrongForgery`). -/
noncomputable def muSufSigProb (A : MUAdversary O n V t) (Q : ℕ) : ℝ≥0∞ :=
  (muLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2, SigStrongForges x.1 x.2.1 p.1 p.2}

/-- **MU-EUF-CMA^corr is at most MU-SUF-CMA^corr**, adversary by adversary. -/
theorem muEufProb_le_muSufProb (A : MUAdversary O n V t) (Q : ℕ) :
    muEufProb A Q ≤ muSufProb A Q :=
  PMF.toOuterMeasure_mono _ fun _ ⟨⟨p, hp, hf⟩, _⟩ => ⟨p, hp, hf.strongForges⟩

/-- **The strong game with never-returned signatures is at most MU-SUF-CMA^corr**, adversary by
adversary. -/
theorem muSufSigProb_le_muSufProb (A : MUAdversary O n V t) (Q : ℕ) :
    muSufSigProb A Q ≤ muSufProb A Q :=
  PMF.toOuterMeasure_mono _ fun _ ⟨⟨p, hp, hf⟩, _⟩ => ⟨p, hp, hf.strongForges⟩

/-- The success probability in MU-SUF-CMA^corr is at most `1`. -/
theorem muSufProb_le_one (A : MUAdversary O n V t) (Q : ℕ) : muSufProb A Q ≤ 1 :=
  prob_runLaw_le_one _ _ _

/-- The success probability in MU-EUF-CMA^corr is at most `1`. -/
theorem muEufProb_le_one (A : MUAdversary O n V t) (Q : ℕ) : muEufProb A Q ≤ 1 :=
  prob_runLaw_le_one _ _ _

/-- **A base verification that rejects everything gives success probability `0`** in
MU-SUF-CMA^corr: a bound `0` can hold. -/
theorem muSufProb_eq_zero_of_reject (hrej : ∀ H pk bm σ, B.bverify H pk bm σ = false)
    (A : MUAdversary O n V t) (Q : ℕ) : muSufProb A Q = 0 := by
  refine (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 fun x _ hx => ?_)
  obtain ⟨p, -, hf⟩ := hx
  have h := hf.verify_eq
  rw [hrej] at h
  exact Bool.noConfusion h

/-- A base verification that rejects everything gives success probability `0` in
MU-EUF-CMA^corr. -/
theorem muEufProb_eq_zero_of_reject (hrej : ∀ H pk bm σ, B.bverify H pk bm σ = false)
    (A : MUAdversary O n V t) (Q : ℕ) : muEufProb A Q = 0 :=
  le_antisymm ((muEufProb_le_muSufProb A Q).trans (muSufProb_eq_zero_of_reject hrej A Q).le)
    zero_le

end GordieHowe.Signature
