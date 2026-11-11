-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.NMA
public import GordieHowe.Model.Signature.RejectionRelay
public import GordieHowe.Model.Signature.GuessUser

@[expose] public section

/-!
# Relations between the unforgeability games

- **No-message attacks embed into chosen-message attacks.** `nmaReq`: a request of the game
  without messages as the same public-key request or corruption at a signing oracle `O`.
  `nmaRelay O i₀`: the relay (`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`) asking each
  request as `nmaReq` of it, one main request and no query per request, the idle request the
  public key of user `i₀`. `relaysChallenger_nmaRelay`: the challenger without messages with `Q`
  requests is that relay of the challenger at `O` with `Q` requests. `nmaEmbed O i₀ A Q`: the
  relayed adversary, with the query bound `t` of `A`. `muEufNmaProb_le_muEufProb_nmaEmbed`:
  `muEufNmaProb A Q ≤ muEufProb (nmaEmbed O i₀ A Q) Q`; `muEufNmaProb_le_muSufProb_nmaEmbed`: the
  same in MU-SUF-CMA^corr. The single-user forms are `suEufNmaProb_le_suEufProb_nmaEmbed` and
  `suEufNmaProb_le_suSufProb_nmaEmbed` (user `0` idle).
- **Many users from one user.** `muEufProb_le_card_mul_suEufProb`: for every signing oracle,
  `muEufProb A Q ≤ n * suEufProb (suGuess O A Q) Q`, with the single-user adversary `suGuess` of
  `GordieHowe/Model/Signature/GuessUser.lean` guessing the target user (BHJKL15's loss `n`), at most
  `t + Q · O.q` queries. `muEufProbWithin_le_card_mul_suEufProbWithin`: the same with at most `Qs`
  signing and
  corruption requests (`GordieHowe/Model/Signature/MultiUserCount.lean`);
  `muSufProb_le_card_mul_suSufProb`: MU-SUF-CMA^corr at most `n` times SUF-CMA.
  `SignOracle.queryStd`, `SignOracle.not_noQuery_queryStd`,
  `muEufProb_le_card_mul_suEufProb_queryStd`:
  the bound at a signer that queries the oracle. `sum4_reorder`,
  `sum5_reorder`: finite sums reordered.
- **Existential forgeries are strong forgeries**: `muEufProb_le_muSufProb`
  (`GordieHowe/Model/Signature/MultiUser.lean`) and `suEufProb_le_suSufProb`
  (`GordieHowe/Model/Signature/SingleUser.lean`).
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {TB : SchemeTypes}
  {B : BaseScheme X Y TB} (O : SignOracle B) {n : ℕ}

/-! ### The embedding of the game without messages -/

/-- **A request of the game without messages at the signing oracle `O`**: the same public-key
request or corruption. -/
def nmaReq : MURequest (SignOracle.none B) n → MURequest O n
  | .publicKey i => .publicKey i
  | .sign _ sm => sm.elim
  | .corrupt i => .corrupt i

/-- **The relay of the game without messages to the game at `O`**: each request asked as `nmaReq`
of it and its reply passed on, one main request and no query per request, the idle request the
public key of user `i₀`. -/
def nmaRelay (i₀ : Fin n) :
    MultiRelay X Y (MURequest (SignOracle.none B) n) (MUResponse B) (MURequest O n)
      (MUResponse B) where
  prog := MultiRelay.plainProg fun r => askResp (nmaReq O r)
  K := 1
  K_pos := Nat.one_pos
  qR := 0
  idle := .publicKey i₀

variable [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins]

variable {O}

omit [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
/-- **The relay's histories relay the game without messages** (`HistRelay`): if every request of
`hist'` is the idle request or one that a request of `hist` relays to, `hist'` has no signing
request and corrupts only users that `hist` corrupts. -/
theorem histRelay_nmaRelay (i₀ : Fin n) {hist : MUHist (SignOracle.none B) n} {hist' : MUHist O n}
    (h : ∀ e' ∈ hist', e'.request = (nmaRelay (X := X) (Y := Y) O i₀).idle ∨
      ∃ e ∈ hist, (nmaRelay (X := X) (Y := Y) O i₀).CanAsk e.request e'.request) :
    HistRelay hist hist' where
  sign_mem e' he' i sm' hr := by
    rcases h e' he' with h1 | ⟨e, -, hc⟩
    · rw [hr] at h1
      cases h1
    · have := (nmaRelay O i₀).canAsk_of_asksIn (asksIn_askResp (X := X) (Y := Y)
        (Resp' := MUResponse B) (nmaReq O e.request)).plainProg hc
      rw [hr] at this
      rcases hreq : e.request with j | ⟨j, sm⟩ | j
      · rw [hreq] at this
        simp only [nmaReq] at this
        cases this
      · exact sm.elim
      · rw [hreq] at this
        simp only [nmaReq] at this
        cases this
  corrupt_mem i := by
    rintro ⟨e', he', hr⟩
    rcases h e' he' with h1 | ⟨e, he, hc⟩
    · rw [hr] at h1
      cases h1
    · have := (nmaRelay O i₀).canAsk_of_asksIn (asksIn_askResp (X := X) (Y := Y)
        (Resp' := MUResponse B) (nmaReq O e.request)).plainProg hc
      rw [hr] at this
      rcases hreq : e.request with j | ⟨j, sm⟩ | j
      · rw [hreq] at this
        simp only [nmaReq] at this
        cases this
      · exact sm.elim
      · rw [hreq] at this
        simp only [nmaReq] at this
        cases this
        exact ⟨e, he, hreq⟩

/-- **A probability distribution on a subsingleton is unique.** -/
theorem _root_.PMF.eq_of_subsingleton {α : Type} [Subsingleton α] (p p' : PMF α) : p = p' := by
  have h : ∀ (μ : PMF α) (a : α), μ a = 1 := fun μ a => by
    rw [← μ.tsum_coe, tsum_eq_single a fun b hb => absurd (Subsingleton.elim b a) hb]
  ext a
  rw [h p a, h p' a]

omit [Fintype O.SMsg] [DecidableEq O.SMsg] [Fintype O.Coins] [DecidableEq O.Coins]
  [Nonempty O.Coins] in
/-- **The reply of the challenger without messages is the reply at `O` to the embedded
request.** -/
theorem muReply_none (keys : Fin n → B.KeyCoins) (H : X → Y) (u : Unit) (c : O.Coins)
    (r : MURequest (SignOracle.none B) n) :
    muReply (SignOracle.none B) keys H u r = muReply O keys H c (nmaReq O r) := by
  rcases r with i | ⟨i, sm⟩ | i
  · rfl
  · exact sm.elim
  · rfl

variable (B) in
/-- **A signing oracle that queries the oracle**: the base scheme's ordinary signer
(`SignOracle.std`) after one query of `x₀`. -/
@[reducible] def SignOracle.queryStd (x₀ : X) : SignOracle B where
  SMsg := B.BMsg
  Coins := B.Coins
  q := B.q + 1
  sign kp bm c := .query x₀ fun _ => B.ssign kp.2 bm c
  sign_queries kp bm c H := by
    simp only [OracleProg.trace, List.length_cons]
    have := B.ssign_queries kp.2 bm c H
    omega
  base bm := bm

variable [Fintype X] [DecidableEq X] [Nonempty X] [Inhabited X] [Fintype Y] [DecidableEq Y]
  [AddGroup Y] [Nonempty Y]

variable [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]

/-- **The challenger without messages is the relay `nmaRelay` of the challenger at `O`**
(`MultiRelay.RelaysChallenger`), both answering `Q` requests: each request is answered as the
challenger at `O` answers its embedding. -/
theorem relaysChallenger_nmaRelay (keys : Fin n → B.KeyCoins) (i₀ : Fin n) (Q : ℕ) :
    letI : Inhabited (MURequest O n) := ⟨.publicKey i₀⟩
    (nmaRelay O i₀).RelaysChallenger (muChallenger (SignOracle.none B) n keys Q)
      (muChallenger O n keys Q) fun _ _ => () := by
  let _ : Inhabited (MURequest O n) := ⟨.publicKey i₀⟩
  exact {
    coins_eq := PMF.eq_of_subsingleton (α := Fin Q → Unit) _ _
    oracle_eq := fun H c _ lg => (muChallenger_noAssign _ keys Q).oracle_eq H c lg
    oracle_eq' := fun H c' _ lg => (muChallenger_noAssign _ keys Q).oracle_eq H c' lg
    answer_eq := fun H c' rs r hi => by
      have hi' : rs.length < Q := hi
      have hlen := (nmaRelay O i₀).length_mainReqs Q
        ((muChallenger O n keys Q).toPureEnv.answerAfter (H, c')) H rs hi'.le
      have hlt : ((nmaRelay (X := X) (Y := Y) O i₀).mainReqs Q
          ((muChallenger O n keys Q).toPureEnv.answerAfter (H, c')) H rs).length < Q := by
        rw [hlen]
        change 1 * rs.length < Q
        omega
      refine (answerAfter_muChallenger (SignOracle.none B) keys Q H _ rs r hi).trans ?_
      have h := MultiRelay.RunsWith.query_inr
        (ansM := (muChallenger O n keys Q).toPureEnv.answerAfter (H, c')) (H := H)
        (rs := (nmaRelay (X := X) (Y := Y) O i₀).mainReqs Q
          ((muChallenger O n keys Q).toPureEnv.answerAfter (H, c')) H rs)
        (k := fun b => OracleProg.pure (b.elim (fun _ => none) id)) (nmaReq O r)
        (MultiRelay.RunsWith.pure _ _)
      refine Eq.trans ?_ ((nmaRelay O i₀).runReply_eq_of_runsWith (r := r) rfl h
        (by simp [nmaRelay]) (Nat.zero_le _)).symm
      simp only [Sum.elim_inr, id]
      rw [answerAfter_muChallenger O keys Q H c' _ _ hlt]
      exact muReply_none keys H _ _ r }

variable {V : OracleView X Y} {t : ℕ}

variable (O) in
/-- **The adversary of the game at `O` embedding an adversary of the game without messages**: on
the public keys, the relay (`QueryBoundedAdversary.relay`) of `A`'s adversary by `nmaRelay O i₀`,
answering `Q` requests. It makes the queries of `A`: the relay adds `Q · 0`. -/
noncomputable def nmaEmbed (i₀ : Fin n) (A : MUAdversary (SignOracle.none B) n V t) (Q : ℕ) :
    MUAdversary O n V t := fun inp =>
  letI : Inhabited (MURequest O n) := ⟨.publicKey i₀⟩
  ((A inp).relay (nmaRelay O i₀) Q).mono (by simp [nmaRelay])

/-- **The embedding at one oracle's run**: at the users' key coins `keys` and the oracle `H`, an
event of `A`'s transcript in the game without messages has at most the probability of an event of
the embedded adversary's transcript in the game at `O`, when every relayed history keeps it. -/
theorem transcriptLaw_le_nmaEmbed (i₀ : Fin n) (A : MUAdversary (SignOracle.none B) n V t)
    (Q : ℕ) (keys : Fin n → B.KeyCoins) (H : X → Y)
    (E : (B.PK × B.BMsg × B.BSig) × MUHist (SignOracle.none B) n → Prop)
    (E' : (B.PK × B.BMsg × B.BSig) × MUHist O n → Prop)
    (himp : ∀ f hist hist', E (f, hist) → HistRelay hist hist' → E' (f, hist')) :
    ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw (muChallenger _ n keys Q)
        H).toOuterMeasure {x | ∃ p ∈ x, E p} ≤
      ((nmaEmbed O i₀ A Q (fun i => B.pk (keys i), V.view H)).transcriptLaw
        (muChallenger O n keys Q) H).toOuterMeasure {x | ∃ p ∈ x, E' p} := by
  let _ : Inhabited (MURequest O n) := ⟨.publicKey i₀⟩
  exact (A (fun i => B.pk (keys i), V.view H)).transcriptLaw_le_relay (nmaRelay O i₀)
    (muChallenger (SignOracle.none B) n keys Q) (muChallenger O n keys Q) (fun _ _ => ())
    (relaysChallenger_nmaRelay keys i₀ Q) H E E'
    fun f hist hist' hE hrel => himp f hist hist' hE (histRelay_nmaRelay i₀ hrel)

variable [Nonempty TB.KeyCoins]

/-- **The embedding for an event of the run**: an event of the run of the game without messages
has at most the probability of an event of the embedded adversary's run at `O`, when every relayed
history keeps it at the same key coins and oracle. -/
theorem muLaw_le_nmaEmbed (i₀ : Fin n) (A : MUAdversary (SignOracle.none B) n V t) (Q : ℕ)
    (E : (Fin n → B.KeyCoins) → (X → Y) →
      (B.PK × B.BMsg × B.BSig) × MUHist (SignOracle.none B) n → Prop)
    (E' : (Fin n → B.KeyCoins) → (X → Y) → (B.PK × B.BMsg × B.BSig) × MUHist O n → Prop)
    (himp : ∀ keys H f hist hist', E keys H (f, hist) → HistRelay hist hist' →
      E' keys H (f, hist')) :
    (muLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2, E x.1 x.2.1 p} ≤
      (muLaw (nmaEmbed O i₀ A Q) Q).toOuterMeasure {x | ∃ p ∈ x.2.2, E' x.1 x.2.1 p} := by
  unfold muLaw runLaw
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left ?_ zero_le
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  exact transcriptLaw_le_nmaEmbed i₀ A Q keys H (E keys H) (E' keys H)
    (fun f hist hist' => himp keys H f hist hist')

/-- **MU-EUF-NMA^corr embeds into MU-EUF-CMA^corr**: for every signing oracle `O`, the embedded
adversary `nmaEmbed O i₀ A Q`, with the query bound of `A` and the same number `Q` of requests, has
at least the success probability of `A`. -/
theorem muEufNmaProb_le_muEufProb_nmaEmbed (i₀ : Fin n) (A : MUAdversary (SignOracle.none B) n V t)
    (Q : ℕ) : muEufNmaProb A Q ≤ muEufProb (nmaEmbed O i₀ A Q) Q :=
  muLaw_le_nmaEmbed i₀ A Q (fun keys H p => Forges keys H p.1 p.2)
    (fun keys H p => Forges keys H p.1 p.2) fun _ _ _ _ _ hE hrel => hE.of_histRelay hrel

/-- **MU-EUF-NMA^corr embeds into MU-SUF-CMA^corr**: the embedded adversary's strong forgeries
include `A`'s forgeries, since the embedded adversary asks for no signature. -/
theorem muEufNmaProb_le_muSufProb_nmaEmbed (i₀ : Fin n) (A : MUAdversary (SignOracle.none B) n V t)
    (Q : ℕ) : muEufNmaProb A Q ≤ muSufProb (nmaEmbed O i₀ A Q) Q :=
  (muEufNmaProb_le_muEufProb_nmaEmbed i₀ A Q).trans (muEufProb_le_muSufProb _ Q)

/-- **EUF-NMA embeds into EUF-CMA** (single user, user `0` idle). -/
theorem suEufNmaProb_le_suEufProb_nmaEmbed (A : SUAdversary (SignOracle.none B) V t) (Q : ℕ) :
    suEufNmaProb A Q ≤ suEufProb (nmaEmbed O 0 A Q) Q :=
  muEufNmaProb_le_muEufProb_nmaEmbed 0 A Q

/-- **EUF-NMA embeds into SUF-CMA** (single user, user `0` idle). -/
theorem suEufNmaProb_le_suSufProb_nmaEmbed (A : SUAdversary (SignOracle.none B) V t) (Q : ℕ) :
    suEufNmaProb A Q ≤ suSufProb (nmaEmbed O 0 A Q) Q :=
  muEufNmaProb_le_muSufProb_nmaEmbed 0 A Q

/-! ### Many users from one user -/

variable [Fintype TB.Pub]
  [DecidableEq TB.Pub]

variable [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Coins] [DecidableEq TB.Coins]
  [Nonempty TB.Coins]

section Guess

variable [NeZero n]

omit [NeZero n] in
/-- Four finite sums reordered. -/
theorem sum4_reorder {α β γ δ : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (f : α → β → γ → δ → ℝ≥0∞) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ b, ∑ a, f a b c d := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  exact Finset.sum_comm

omit [NeZero n] in
/-- Five finite sums reordered. -/
theorem sum5_reorder {α β γ δ ε : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    [Fintype ε] (f : α → β → γ → δ → ε → ℝ≥0∞) :
    ∑ a, ∑ b, ∑ c, ∑ d, ∑ e, f a b c d e = ∑ c, ∑ e, ∑ b, ∑ d, ∑ a, f a b c d e := by
  rw [Finset.sum_comm]
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm).trans ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ => ?_
  refine (Finset.sum_congr rfl fun b _ => Finset.sum_comm).trans ?_
  rfl

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **MU-EUF-CMA^corr is at most `n` times EUF-CMA**: for every signing oracle, the single-user
adversary `suGuess O A Q` (`GordieHowe/Model/Signature/GuessUser.lean`: it guesses the target user
and answers the other users' requests itself, making the signer's oracle queries) with at most
`t + Q · O.q` queries and the same number `Q` of requests has at least `1 / n` of `A`'s success
probability. The signer may query the oracle, as the signers whose hashes are random oracles do. -/
theorem muEufProb_le_card_mul_suEufProb (A : MUAdversary O n V t) (Q : ℕ) :
    muEufProb A Q ≤ n * suEufProb (suGuess O A Q) Q := by
  classical
  refine (muEufProb_le_sum_guessWin O A Q).trans (le_of_eq ?_)
  rw [suEufProb_suGuess]
  have hn : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp [NeZero.ne n]) (by simp)
  calc ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑ H, PMF.uniformOfFintype (X → Y) H * ∑ i, ∑ ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          guessWin O A Q i keys ρ (keys i) H
      = ∑ i, ∑ ρ, ∑ H, ∑ keys, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
            guessWin O A Q i keys ρ (keys i) H) := by
        simp only [Finset.mul_sum]
        rw [sum4_reorder (fun keys H i ρ => PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
          (PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
            guessWin O A Q i keys ρ (keys i) H)))]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun keys _ => by ring
    _ = ∑ i, ∑ ρ, ∑ H, ∑ keys, ∑ k, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
            (PMF.uniformOfFintype B.KeyCoins k * guessWin O A Q i keys ρ k H)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => ?_
        rw [← Finset.mul_sum, sum_guessWin_resplit]
        simp only [Finset.mul_sum]
    _ = (n : ℝ≥0∞) * ∑ k, PMF.uniformOfFintype B.KeyCoins k *
        ∑ H, PMF.uniformOfFintype (X → Y) H *
          ∑ z, PMF.uniformOfFintype (Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins)) z *
            guessWin O A Q z.1 z.2.1 z.2.2 k H := by
        simp only [uniform_draw_apply, Fintype.sum_prod_type, Finset.mul_sum]
        rw [sum5_reorder (fun k H i keys ρ => (n : ℝ≥0∞) * (PMF.uniformOfFintype B.KeyCoins k *
          (PMF.uniformOfFintype (X → Y) H * ((n : ℝ≥0∞)⁻¹ *
            (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
              PMF.uniformOfFintype (Fin Q → O.Coins) ρ) * guessWin O A Q i keys ρ k H))))]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun keys _ =>
            Finset.sum_congr rfl fun k _ => ?_
        calc _ = (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * (PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
              PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
                (PMF.uniformOfFintype B.KeyCoins k * guessWin O A Q i keys ρ k H))) := by
              rw [hn, one_mul]
          _ = _ := by ring


omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **MU-EUF-CMA^corr with at most `Qs` signing and corruption requests is at most `n` times
EUF-CMA with at most `Qs` of them** (`muEufProbWithin` at `n` and at one user): for every signing
oracle, the single-user adversary `suGuess O A Q` with at most `t + Q · O.q` queries and the same
number `Q` of requests has at least `1 / n` of `A`'s success probability with at most `Qs` signing
and corruption requests: it forwards at most `A`'s signing and corruption requests about the target
user. -/
theorem muEufProbWithin_le_card_mul_suEufProbWithin (A : MUAdversary O n V t) (Q Qs : ℕ) :
    muEufProbWithin A Q Qs ≤ n * muEufProbWithin (suGuess O A Q) Q Qs := by
  classical
  refine (muEufProbWithin_le_sum_guessWinW O A Q Qs).trans (le_of_eq ?_)
  rw [muEufProbWithin_suGuess]
  have hn : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp [NeZero.ne n]) (by simp)
  calc ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑ H, PMF.uniformOfFintype (X → Y) H * ∑ i, ∑ ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          guessWinW O A Q Qs i keys ρ (keys i) H
      = ∑ i, ∑ ρ, ∑ H, ∑ keys, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
            guessWinW O A Q Qs i keys ρ (keys i) H) := by
        simp only [Finset.mul_sum]
        rw [sum4_reorder (fun keys H i ρ => PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
          (PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
            guessWinW O A Q Qs i keys ρ (keys i) H)))]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun keys _ => by ring
    _ = ∑ i, ∑ ρ, ∑ H, ∑ keys, ∑ k, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
            (PMF.uniformOfFintype B.KeyCoins k * guessWinW O A Q Qs i keys ρ k H)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => ?_
        rw [← Finset.mul_sum, sum_guessWinW_resplit]
        simp only [Finset.mul_sum]
    _ = (n : ℝ≥0∞) * ∑ k, PMF.uniformOfFintype B.KeyCoins k *
        ∑ H, PMF.uniformOfFintype (X → Y) H *
          ∑ z, PMF.uniformOfFintype (Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins)) z *
            guessWinW O A Q Qs z.1 z.2.1 z.2.2 k H := by
        simp only [uniform_draw_apply, Fintype.sum_prod_type, Finset.mul_sum]
        rw [sum5_reorder (fun k H i keys ρ => (n : ℝ≥0∞) * (PMF.uniformOfFintype B.KeyCoins k *
          (PMF.uniformOfFintype (X → Y) H * ((n : ℝ≥0∞)⁻¹ *
            (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
              PMF.uniformOfFintype (Fin Q → O.Coins) ρ) * guessWinW O A Q Qs i keys ρ k H))))]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun keys _ =>
            Finset.sum_congr rfl fun k _ => ?_
        calc _ = (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * (PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
              PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
                (PMF.uniformOfFintype B.KeyCoins k * guessWinW O A Q Qs i keys ρ k H))) := by
              rw [hn, one_mul]
          _ = _ := by ring

omit [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Pub]
  [DecidableEq TB.Pub] [Fintype TB.Coins] [DecidableEq TB.Coins] [Nonempty TB.Coins] in
/-- **MU-SUF-CMA^corr is at most `n` times SUF-CMA**: for every signing oracle, the single-user
adversary `suGuess O A Q` with at most `t + Q · O.q` queries and the same number `Q` of requests has
at least `1 / n` of `A`'s success probability in the strong game. -/
theorem muSufProb_le_card_mul_suSufProb (A : MUAdversary O n V t) (Q : ℕ) :
    muSufProb A Q ≤ n * suSufProb (suGuess O A Q) Q := by
  classical
  refine (muSufProb_le_sum_guessWinS O A Q).trans (le_of_eq ?_)
  rw [suSufProb_suGuess]
  have hn : (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ = 1 :=
    ENNReal.mul_inv_cancel (by simp [NeZero.ne n]) (by simp)
  calc ∑ keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑ H, PMF.uniformOfFintype (X → Y) H * ∑ i, ∑ ρ, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          guessWinS O A Q i keys ρ (keys i) H
      = ∑ i, ∑ ρ, ∑ H, ∑ keys, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
            guessWinS O A Q i keys ρ (keys i) H) := by
        simp only [Finset.mul_sum]
        rw [sum4_reorder (fun keys H i ρ => PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
          (PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
            guessWinS O A Q i keys ρ (keys i) H)))]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun keys _ => by ring
    _ = ∑ i, ∑ ρ, ∑ H, ∑ keys, ∑ k, PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
          PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
            (PMF.uniformOfFintype B.KeyCoins k * guessWinS O A Q i keys ρ k H)) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => ?_
        rw [← Finset.mul_sum, sum_guessWinS_resplit]
        simp only [Finset.mul_sum]
    _ = (n : ℝ≥0∞) * ∑ k, PMF.uniformOfFintype B.KeyCoins k *
        ∑ H, PMF.uniformOfFintype (X → Y) H *
          ∑ z, PMF.uniformOfFintype (Fin n × (Fin n → B.KeyCoins) × (Fin Q → O.Coins)) z *
            guessWinS O A Q z.1 z.2.1 z.2.2 k H := by
        simp only [uniform_draw_apply, Fintype.sum_prod_type, Finset.mul_sum]
        rw [sum5_reorder (fun k H i keys ρ => (n : ℝ≥0∞) * (PMF.uniformOfFintype B.KeyCoins k *
          (PMF.uniformOfFintype (X → Y) H * ((n : ℝ≥0∞)⁻¹ *
            (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
              PMF.uniformOfFintype (Fin Q → O.Coins) ρ) * guessWinS O A Q i keys ρ k H))))]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun ρ _ =>
          Finset.sum_congr rfl fun H _ => Finset.sum_congr rfl fun keys _ =>
            Finset.sum_congr rfl fun k _ => ?_
        calc _ = (n : ℝ≥0∞) * (n : ℝ≥0∞)⁻¹ * (PMF.uniformOfFintype (Fin Q → O.Coins) ρ *
              PMF.uniformOfFintype (X → Y) H * (PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
                (PMF.uniformOfFintype B.KeyCoins k * guessWinS O A Q i keys ρ k H))) := by
              rw [hn, one_mul]
          _ = _ := by ring

omit [NeZero n] [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.Pub] [DecidableEq TB.Pub] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins] [Fintype TB.BMsg] [DecidableEq TB.BMsg] [Fintype TB.Coins]
  [DecidableEq TB.Coins] in
/-- **The oracle-querying signer queries the oracle**: it is not without queries. -/
theorem SignOracle.not_noQuery_queryStd [Nonempty B.BMsg] (x₀ : X) :
    ¬ (SignOracle.queryStd B x₀).NoQuery := fun h => by
  have := h (B.keyGen (Classical.arbitrary _)) (Classical.arbitrary B.BMsg)
    (Classical.arbitrary B.Coins) fun _ => Classical.arbitrary Y
  simp [SignOracle.queryStd, OracleProg.trace] at this

omit [Fintype TB.Pub] [DecidableEq TB.Pub] in
/-- **The guessing bound at a signer that queries the oracle** (`muEufProb_le_card_mul_suEufProb`
at `SignOracle.queryStd`, `SignOracle.not_noQuery_queryStd`). -/
theorem muEufProb_le_card_mul_suEufProb_queryStd (x₀ : X)
    (A : MUAdversary (SignOracle.queryStd B x₀) n V t) (Q : ℕ) :
    muEufProb A Q ≤ n * suEufProb (suGuess (SignOracle.queryStd B x₀) A Q) Q :=
  muEufProb_le_card_mul_suEufProb A Q

end Guess

end GordieHowe.Signature
