-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.SPBCS.WitnessIndist
public import GordieHowe.Foundations.ToMathlib.PMFCoupling
public import GordieHowe.Headline

@[expose] public section

/-!
# Anonymity of ring signatures: one game, BKM06 Definition 4

The anonymity game of the ring signatures of this library, and its bound. The ring signature on
`(R, m)` is a public value `v` with a proof of the ring relation for the statement `(R, m, v)`,
compiled by spBCS (`GordieHowe/SPBCS/Basic.lean`; the proof is the compiled honest proof
`GordieHowe.SPBCS.proofLaw`, `GordieHowe/SPBCS/WitnessIndist.lean`). The public value is part of
the signer's output, read off the signature it produces: Falcon's salt, `Unit` for ML-DSA, the
commitment `w₁` of the ML-DSA ring signature of `PublicW1/`.

- `pubRun`, `tvDist_pubRun_le` (identical until bad), `map_wiRun_replay`,
  `gameAdvantage_pubRun_le`: rounds with public outputs or refusals, and spBCS witness
  indistinguishability for them (`SPBCS.witnessIndistinguishable` through a recomputed history
  that discards the proofs of refused rounds).
- `PubSigner`: a ring signer, with key generation from uniform coins, a signing law given an
  oracle `Orc` of the base scheme (`Unit` for a scheme without one), the ring relation at the
  oracle, and a public refusal rule `Admit` (the rings and messages the signer signs on).
- `PubAnonAdversary`, `PubAnonAdversary.game`, `PubAnonAdversary.advantage`: **the game**,
  anonymity against full key exposure (BKM06 Definition 4) with adversarial ring members and `Q`
  adaptive challenges.
- `PubAnonAdversary.advantage_le`: the bound, by coupling the two users' signing laws per oracle
  and keys (`PMF.exists_coupling_map_le_tvDist`): when both signatures are valid and their public
  values agree the witnesses share a statement and witness indistinguishability applies;
  otherwise the round is bad. It is
  `Q · (𝔼 ε + 2η) + Q · wiError δ (Q · C) + Pr[¬ Good]`, with `ε` the distance of the two users'
  public-value laws, `η` the probability that an honest signature is invalid, and `C` the number
  of challenges of the adversary's set valid for the users' keys.
- `schemeSigner`, `KeyedAnonAdversary`, `keyedAnonAdvantage`, `keyedAnon_le_of_correctWithin`,
  `keyedAnon_le`: the game for the generic ring signature of a `SigScheme`
  (`GordieHowe/Applications/Ring/Scheme.lean`), whose public value is a function of the signing
  coins (`SigScheme.PubOfCoins`: Falcon's salt, or `Pub = Unit`), so `ε = 0`; with correctness
  error `ε_c` the bound is `Q · wiError δ (Q · C) + 2 Q ε_c`, and `Q · wiError δ (Q · C)` for a
  perfectly correct scheme.

## The game

`n` honest key pairs are generated from uniform coins, and the adversary receives all the coins
at the start (full key exposure; corruption in this library returns the key-generation coins,
which reveal at least the secret key). The adversary sees the whole oracle of the base scheme and
the whole oracle of the compiled argument. In each of `Q` rounds it chooses a ring of arbitrary
keys, a ring message and two honest users whose keys are in the ring, as a function of the
coins, the oracles and the history; the challenger answers with the public value and the ring
signature of user `b`, or `⊥` when the signer refuses the ring (`Admit` fails; the rule reads only
the oracle, the ring and the message, so `⊥` is the same in both experiments). A round with the same user twice
is a signing query. The distinguisher sees the coins, both oracles and the history. Rings are
ordered lists of keys with the signer's position, stronger than BKM06's sets: the adversary also
fixes the order.

## Sources

BKM06 (Bender, Katz, Morselli, "Ring Signatures: Stronger Definitions, and Constructions without
Random Oracles", TCC 2006, LNCS 3876, pp. 60–79; ePrint 2005/304) Definition 4 (p. 6), anonymity
against full key exposure: the adversary receives the randomness used to generate all honest
keys, may query a signing oracle on rings containing adversarial keys, outputs `(M, i₀, i₁, R)`
and guesses the bit of `Sign_{i_b}(M, R)`. The keys are given at the start, as in CCLM22
(Chatterjee, Chung, Liang, Malavolta, PKC 2022, ePrint 2021/1616) Experiment 2 (p. 21) and BKP20
(ePrint 2020/646, p. 7), stronger than BKM06's timing. The adversaries are deterministic, those of
the witness-indistinguishability theorem of spBCS (`SPBCS.wiAdvantage_le`; CY24 Definition
33.1.1, p. 426, at unbounded queries): each choice is a function of the coins, the oracles and the
earlier outputs, and the distinguisher a predicate of all of them. A randomized or quantum
adversary with classical challenges is a mixture of such adversaries, a decomposition not
formalized here.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal BigOperators

/-! ### Rounds with public outputs -/

section PubRun

variable {Ω X W Pub Pf : Type} [Fintype Ω] [Nonempty Ω] (law : Ω → X → W → PMF Pf)
  (pubOf : X → Pub) {Q : ℕ}

/-- The history after `j` rounds: the public value and the proof of each round, or `none` (the
refusal `⊥`) for a refused round. -/
abbrev PubHist (Pub Pf : Type) (j : ℕ) : Type := Fin j → Option (Pub × Pf)

/-- **A selector**: in round `j`, from the oracle and the history, the statement and the witness
proved, or `none` when the round is refused. -/
abbrev Selector (Ω X W Pub Pf : Type) (Q : ℕ) : Type :=
  (j : Fin Q) → Ω → PubHist Pub Pf j → Option (X × W)

/-- **The output of a round** at the oracle `h`: for a selected statement and witness, the
statement's public value and a proof from `law`; for a refused round, `none`. -/
noncomputable def roundLaw (h : Ω) : Option (X × W) → PMF (Option (Pub × Pf))
  | none => PMF.pure none
  | some xw => (law h xw.1 xw.2).map fun π => some (pubOf xw.1, π)

variable (sel : Selector Ω X W Pub Pf Q)

/-- Round `j` with the selector `sel`: the output of the round (`roundLaw`) appended to the
history. -/
noncomputable def pubStep (j : Fin Q) (s : Ω × PubHist Pub Pf j) : PMF (Ω × PubHist Pub Pf (j + 1)) :=
  (roundLaw law pubOf s.1 (sel j s.1 s.2)).map fun r =>
    (s.1, Fin.snoc (α := fun _ => Option (Pub × Pf)) s.2 r)

/-- The experiment after `j` rounds: the oracle uniform, then the rounds. -/
noncomputable def pubRun : (j : ℕ) → j ≤ Q → PMF (Ω × PubHist Pub Pf j)
  | 0, _ => (PMF.uniformOfFintype Ω).map fun h => (h, Fin.elim0)
  | j + 1, hj => (pubRun j (by omega)).bind (pubStep law pubOf sel ⟨j, by omega⟩)

variable {law pubOf}

/-- Two selectors that agree before round `j` give the same experiment after `j` rounds. -/
theorem pubRun_congr {sel sel' : Selector Ω X W Pub Pf Q} :
    ∀ j (hj : j ≤ Q), (∀ i : Fin Q, i.1 < j → sel i = sel' i) →
      pubRun law pubOf sel j hj = pubRun law pubOf sel' j hj
  | 0, _, _ => rfl
  | j + 1, hj, h => by
    rw [pubRun, pubRun, pubRun_congr j (by omega) fun i hi => h i (by omega)]
    congr 1
    funext s
    rw [pubStep, pubStep, h ⟨j, by omega⟩ (by simp)]

/-- The probability that two selectors select differently in round `i`, in the experiment of the
first. -/
noncomputable def selectDiffProb (sel sel' : Selector Ω X W Pub Pf Q) (i : Fin Q) : ℝ :=
  ((pubRun law pubOf sel i.1 i.2.le).toOuterMeasure {s | sel i s.1 s.2 ≠ sel' i s.1 s.2}).toReal

/-- **Identical until bad**: two selectors give experiments at most the sum, over the rounds, of
the probability that they select differently in that round apart. -/
theorem tvDist_pubRun_le (sel sel' : Selector Ω X W Pub Pf Q) :
    ∀ j (hj : j ≤ Q), PMF.tvDist (pubRun law pubOf sel j hj) (pubRun law pubOf sel' j hj) ≤
      ∑ i : Fin j, selectDiffProb (law := law) (pubOf := pubOf) sel sel' (Fin.castLE hj i)
  | 0, _ => by simp [pubRun]
  | j + 1, hj => by
    rw [Fin.sum_univ_castSucc]
    have hstep : PMF.tvDist ((pubRun law pubOf sel j (by omega)).bind
        (pubStep law pubOf sel ⟨j, by omega⟩)) ((pubRun law pubOf sel j (by omega)).bind
        (pubStep law pubOf sel' ⟨j, by omega⟩)) ≤
        selectDiffProb (law := law) (pubOf := pubOf) sel sel' ⟨j, by omega⟩ := by
      refine (PMF.tvDist_bind_le_toOuterMeasure_ne _ _ _).trans ?_
      refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
        (PMF.toOuterMeasure_apply_le_one _ _)) (PMF.toOuterMeasure_mono _ ?_)
      intro s hs he
      exact hs.1 (by simp only [pubStep]; rw [he])
    have hih := tvDist_pubRun_le sel sel' j (by omega)
    have hlast : Fin.castLE hj (Fin.last j) = ⟨j, by omega⟩ := rfl
    have hcast : ∀ i : Fin j, Fin.castLE hj i.castSucc = Fin.castLE (by omega) i := fun _ => rfl
    rw [hlast]
    simp only [hcast]
    rw [pubRun, pubRun]
    refine (PMF.tvDist_triangle _ ((pubRun law pubOf sel j (by omega)).bind
      (pubStep law pubOf sel' ⟨j, by omega⟩)) _).trans ?_
    exact (add_le_add hstep ((PMF.tvDist_bind_right_le _ _ _).trans hih)).trans_eq (add_comm _ _)

end PubRun

/-! ### Selectors from two-witness choices, and witness indistinguishability -/

section ReplayWI

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {X W Pub : Type} {M : SPBCS Mg P X k kN kS L e}
  (pubOf : X → Pub) {Q : ℕ}

/-- **Two-witness choices from the history**: in round `j`, from the oracle and the history of
public values and proofs, a statement and two witnesses, or `none` for a refused round. -/
abbrev HistChoices (M : SPBCS Mg P X k kN kS L e) (W Pub : Type) (Q : ℕ) : Type :=
  (j : Fin Q) → (Query k kN kS L → Out k e) → PubHist Pub M.NIProof j →
    Option (SPBCS.WIChoice X W)

variable (F : HistChoices M W Pub Q)

/-- **The history recomputed from the proofs**: round `i` is refused when the choice of round `i`
from the earlier recomputed history is `none`, and otherwise holds the public value of the chosen
statement with the proof of round `i`. -/
def replay : (j : ℕ) → j ≤ Q → (Query k kN kS L → Out k e) → (Fin j → M.NIProof) →
    PubHist Pub M.NIProof j
  | 0, _, _, _ => Fin.elim0
  | j + 1, hj, h, πs =>
    Fin.snoc (α := fun _ => Option (Pub × M.NIProof)) (replay j (by omega) h (Fin.init πs))
      ((F ⟨j, by omega⟩ h (replay j (by omega) h (Fin.init πs))).map fun c =>
        (pubOf c.stmt, πs (Fin.last j)))

theorem replay_succ_snoc (j : ℕ) (hj : j + 1 ≤ Q) (h : Query k kN kS L → Out k e)
    (πs : Fin j → M.NIProof) (π : M.NIProof) :
    replay pubOf F (j + 1) hj h (Fin.snoc (α := fun _ => M.NIProof) πs π) =
      Fin.snoc (α := fun _ => Option (Pub × M.NIProof)) (replay pubOf F j (by omega) h πs)
        ((F ⟨j, by omega⟩ h (replay pubOf F j (by omega) h πs)).map fun c => (pubOf c.stmt, π)) := by
  rw [replay, Fin.init_snoc, Fin.snoc_last]

/-- **The witness-indistinguishability adversary of two-witness choices from the history**, with
a finite set `S` of admissible choices containing every choice and a choice `c₀ ∈ S` for the
refused rounds, whose proofs the recomputed history discards. -/
def HistChoices.toWIAdversary {rel : Set (X × W)} (S : Finset (SPBCS.WIChoice X W))
    (hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel) {c₀ : SPBCS.WIChoice X W}
    (hc₀ : c₀ ∈ S) (hF : ∀ j h hist c, F j h hist = some c → c ∈ S) : M.WIAdversary rel Q where
  choices := S
  admissible := hS
  choose j h πs := (F j h (replay pubOf F j j.2.le h πs)).getD c₀
  choose_mem j h πs := by
    cases hc : F j h (replay pubOf F j j.2.le h πs) with
    | none => exact hc₀
    | some c => exact hF _ _ _ _ hc

/-- The selector answering round `j` with the second witness when `bs j`, refusing the rounds whose
choice is `none`. -/
def HistChoices.selector (bs : ℕ → Bool) : Selector (Query k kN kS L → Out k e) X W Pub M.NIProof Q :=
  fun j h hist => (F j h hist).map fun c => (c.stmt, if bs j then c.wit₁ else c.wit₀)

variable {F}

/-- **The witness-indistinguishability experiment with its history recomputed** is the experiment
with public outputs of the selector. -/
theorem map_wiRun_replay (law : (Query k kN kS L → Out k e) → X → W → PMF M.NIProof)
    {rel : Set (X × W)} {S : Finset (SPBCS.WIChoice X W)}
    {hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel} {c₀ : SPBCS.WIChoice X W}
    {hc₀ : c₀ ∈ S} {hF : ∀ j h hist c, F j h hist = some c → c ∈ S} (bs : ℕ → Bool) :
    ∀ j (hj : j ≤ Q), (SPBCS.wiRun law (F.toWIAdversary pubOf S hS hc₀ hF) bs j hj).map
        (fun s => (s.1, replay pubOf F j hj s.1 s.2)) =
      pubRun law pubOf (F.selector bs) j hj
  | 0, _ => by
    rw [SPBCS.wiRun, pubRun, PMF.map_comp]
    congr 1
  | j + 1, hj => by
    rw [SPBCS.wiRun, pubRun, ← map_wiRun_replay law (hS := hS) (hc₀ := hc₀) (hF := hF) bs j
      (by omega), PMF.map_bind, PMF.bind_map]
    congr 1
    funext s
    simp only [Function.comp_apply, SPBCS.wiStep, pubStep, PMF.map_comp, HistChoices.selector,
      HistChoices.toWIAdversary]
    simp only [Function.comp_def, replay_succ_snoc]
    cases hc : F ⟨j, by omega⟩ s.1 (replay pubOf F j (by omega) s.1 s.2) with
    | none =>
      simp only [Option.map_none, Option.getD_none, roundLaw, PMF.pure_map]
      exact PMF.map_const _ _
    | some c =>
      simp only [Option.map_some, roundLaw, PMF.map_comp, Function.comp_def]
      rfl

/-- **Witness indistinguishability with public outputs**: for the spBCS compilation `M` whose
honest prover has honest-verifier zero knowledge at error `δ` for `rel` (`h`), and two-witness
choices from the history in a finite admissible set `S` (every choice not `none` is in `S`), the
experiments with public outputs answering every round with the first and with the second witness
are distinguished by any event of the oracle and the history with advantage at most
`Q · wiError δ |S|`. Refused rounds are the same in the two experiments; if `S` is empty every
round is refused and the experiments agree. -/
theorem gameAdvantage_pubRun_le {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P τ → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {R : Type} [Fintype R] [Nonempty R]
    {honest : W → R → CausalProver P τ X} {rel : Set (X × W)} {PubZ : Type} {pubZ : X → PubZ}
    (Rv : M.Reveal E Qs) {sim : CausalJointSimulator Rv.MV PubZ} {δ : ℝ≥0}
    (h : CausalHVZK Rv.MV rel honest pubZ sim δ) (S : Finset (SPBCS.WIChoice X W))
    (hS : ∀ c ∈ S, (c.stmt, c.wit₀) ∈ rel ∧ (c.stmt, c.wit₁) ∈ rel)
    (hF : ∀ j h hist c, F j h hist = some c → c ∈ S)
    (D : (Query k kN kS L → Out k e) → PubHist Pub M.NIProof Q → Prop) :
    GordieHowe.gameAdvantage
      (pubRun (fun h x w => proofLaw E Qs h x (honest w)) pubOf (F.selector fun _ => false) Q le_rfl)
      (pubRun (fun h x w => proofLaw E Qs h x (honest w)) pubOf (F.selector fun _ => true) Q le_rfl)
      {s | D s.1 s.2} ≤ Q * M.wiError δ S.card := by
  rcases S.eq_empty_or_nonempty with hS0 | ⟨c₀, hc₀⟩
  · have hnone : ∀ j h hist, F j h hist = none := fun j h hist => by
      cases hc : F j h hist with
      | none => rfl
      | some c => exact absurd (hF j h hist c hc) (by simp [hS0])
    have hsel : F.selector (fun _ => false) = F.selector fun _ => true := by
      funext j h hist
      simp [HistChoices.selector, hnone]
    rw [hsel]
    unfold GordieHowe.gameAdvantage GordieHowe.advantage
    rw [sub_self, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) (SPBCS.wiError_nonneg δ _)
  rw [← map_wiRun_replay pubOf _ (hS := hS) (hc₀ := hc₀) (hF := hF),
    ← map_wiRun_replay pubOf _ (hS := hS) (hc₀ := hc₀) (hF := hF)]
  have hadv := SPBCS.witnessIndistinguishable Rv (SPBCS.obsClose_of_causalHVZK Rv h) Q S.card
    (F.toWIAdversary pubOf S hS hc₀ hF) le_rfl (fun h πs => D h (replay pubOf F Q le_rfl h πs))
  unfold SPBCS.wiAdvantage SPBCS.wiAdvantageWith SPBCS.wiGameWith at hadv
  unfold GordieHowe.gameAdvantage at hadv ⊢
  simp only [PMF.toOuterMeasure_map_apply] at ⊢
  exact hadv

end ReplayWI

/-! ### Ring signers -/

/-- **A ring signer producing the public value of its signature**, with rings of at most `N` keys
and ring messages `RMsg`: key generation from uniform coins; a signing law given the oracle `Orc`
of the base scheme (for ML-DSA publishing `w₁`: the commitment hash `H` and the check oracle;
`Unit` for a scheme without one), the secret key, the ring, the signer's position and the ring
message, with values a public value and a base signature; the statements and witnesses of the
compiled argument (`stmt R m v` for the ring `R`, the message `m` and the public value `v`,
`wit i σ` for the position `i` and the base signature `σ`), with the public value read back by
`stmtPub`; the ring relation `rel` at an oracle; and the signer's public refusal rule `Admit`: at
the oracle `H` the signer signs on the rings `R` and ring messages `m` with `Admit H R m` and
outputs `⊥` on the others. The rule reads only the oracle, the ring and the message, not the
signer's key or position, so every signer refuses the same rings; `signLaw` is the signer's law on
the rings it admits. -/
structure PubSigner (N : ℕ) (RMsg : Type) where
  /-- Public keys. -/
  PK : Type
  /-- Secret keys. -/
  SK : Type
  /-- The coins of key generation. -/
  KeyCoins : Type
  /-- Public values. -/
  Pub : Type
  /-- Base signatures. -/
  Sig : Type
  /-- The oracle of the base scheme. -/
  Orc : Type
  /-- The statements of the compiled argument. -/
  Stmt : Type
  /-- The witnesses of the compiled argument. -/
  Wit : Type
  [instFintypePK : Fintype PK]
  [instDecEqPK : DecidableEq PK]
  [instFintypeKeyCoins : Fintype KeyCoins]
  [instNonemptyKeyCoins : Nonempty KeyCoins]
  [instFintypePub : Fintype Pub]
  [instDecEqPub : DecidableEq Pub]
  [instFintypeSig : Fintype Sig]
  [instDecEqSig : DecidableEq Sig]
  [instFintypeOrc : Fintype Orc]
  [instNonemptyOrc : Nonempty Orc]
  /-- Key generation from its coins. -/
  keyGen : KeyCoins → PK × SK
  /-- The signing law: the public value and the base signature. -/
  signLaw : Orc → SK → RingOf PK N → ℕ → RMsg → PMF (Pub × Sig)
  /-- The statement of a ring, a message and a public value. -/
  stmt : RingOf PK N → RMsg → Pub → Stmt
  /-- The witness of a position and a base signature. -/
  wit : ℕ → Sig → Wit
  /-- The public value of a statement. -/
  stmtPub : Stmt → Pub
  /-- The public value of a statement is the one it was built from. -/
  stmtPub_stmt : ∀ R m v, stmtPub (stmt R m v) = v
  /-- The ring relation at an oracle. -/
  rel : Orc → Set (Stmt × Wit)
  /-- The refusal rule: the rings and ring messages the signer signs on at an oracle. -/
  Admit : Orc → RingOf PK N → RMsg → Prop
  [instDecAdmit : ∀ H R m, Decidable (Admit H R m)]

attribute [instance] PubSigner.instFintypePK PubSigner.instDecEqPK PubSigner.instFintypeKeyCoins
  PubSigner.instNonemptyKeyCoins PubSigner.instFintypePub PubSigner.instDecEqPub
  PubSigner.instFintypeSig PubSigner.instDecEqSig PubSigner.instFintypeOrc
  PubSigner.instNonemptyOrc PubSigner.instDecAdmit

/-- **A challenge** of the anonymity game with `n` honest users and public keys `PK`: a ring, a
ring message, two honest users and the positions of their keys. With `user₀ = user₁` and
`idx₀ = idx₁` it is a signing query. It depends on the signer only through its public keys, so
two signers with the same keys (the ideal-mask and the hedged ML-DSA signer) share their
challenges. -/
structure RingChoice (PK RMsg : Type) (N n : ℕ) where
  /-- The ring. -/
  ring : RingOf PK N
  /-- The ring message. -/
  msg : RMsg
  /-- The user signing when `b = 0`. -/
  user₀ : Fin n
  /-- The user signing when `b = 1`. -/
  user₁ : Fin n
  /-- The position of `user₀`'s key. -/
  idx₀ : ℕ
  /-- The position of `user₁`'s key. -/
  idx₁ : ℕ
deriving DecidableEq

/-- The user of a challenge in the experiment `b`. -/
def RingChoice.user {PK RMsg : Type} {N n : ℕ} (c : RingChoice PK RMsg N n) (b : Bool) : Fin n :=
  if b then c.user₁ else c.user₀

/-- The position of a challenge in the experiment `b`. -/
def RingChoice.idx {PK RMsg : Type} {N n : ℕ} (c : RingChoice PK RMsg N n) (b : Bool) : ℕ :=
  if b then c.idx₁ else c.idx₀

/-- **A valid challenge** for the users' coins `keys` and the public-key map `pk`: the positions
hold the two users' public keys. -/
structure RingChoice.Valid {PK RMsg KC : Type} {N n : ℕ} (pk : KC → PK) (keys : Fin n → KC)
    (c : RingChoice PK RMsg N n) : Prop where
  /-- The first position is in the ring. -/
  idx₀_lt : c.idx₀ < c.ring.1.length
  /-- The first position holds `user₀`'s key. -/
  key₀ : c.ring.1[c.idx₀] = pk (keys c.user₀)
  /-- The second position is in the ring. -/
  idx₁_lt : c.idx₁ < c.ring.1.length
  /-- The second position holds `user₁`'s key. -/
  key₁ : c.ring.1[c.idx₁] = pk (keys c.user₁)

namespace PubSigner

variable {N : ℕ} {RMsg : Type} (S : PubSigner N RMsg)

/-- The public key generated from the coins `kc`. -/
def pk (kc : S.KeyCoins) : S.PK := (S.keyGen kc).1

/-- The secret key generated from the coins `kc`. -/
def sk (kc : S.KeyCoins) : S.SK := (S.keyGen kc).2

/-- **A valid signature** at the oracle `H`: the statement of the ring `R`, the message `m` and the
public value `v`, with the witness of the position `i` and the base signature `σ`, is in the ring
relation. -/
def Valid (H : S.Orc) (R : RingOf S.PK N) (m : RMsg) (v : S.Pub) (i : ℕ) (σ : S.Sig) : Prop :=
  (S.stmt R m v, S.wit i σ) ∈ S.rel H

/-- **Correctness of the signer**: on every ring it admits, every signature it can output with an
honestly generated key at position `i` of the ring is valid, at every oracle. -/
def Correct : Prop :=
  ∀ (H : S.Orc) (kc : S.KeyCoins) (R : RingOf S.PK N) (i : ℕ) (m : RMsg) (hi : i < R.1.length),
    S.Admit H R m → R.1[i] = S.pk kc →
      ∀ x ∈ (S.signLaw H (S.sk kc) R i m).support, S.Valid H R m x.1 i x.2

variable [DecidableEq RMsg]

/-- **A challenge** of the anonymity game with `n` honest users (`RingChoice`, with the signer's
public keys). -/
abbrev Choice (n : ℕ) : Type := RingChoice S.PK RMsg N n

/-- **A valid challenge** for the users' coins `keys` (BKM06 Definition 4, ePrint 2005/304, p. 6:
both users' public keys are in the ring): the positions hold the two users' public keys
(`RingChoice.Valid` at the signer's key generation). -/
abbrev Choice.Valid {n : ℕ} (keys : Fin n → S.KeyCoins) (c : S.Choice n) : Prop :=
  RingChoice.Valid S.pk keys c

variable {S}



/-- **The signing law of a challenge** in the experiment `b`, at the oracle `H` and the users'
coins `keys`: user `b` signs at its position. -/
noncomputable def Choice.signLaw {n : ℕ} (H : S.Orc) (keys : Fin n → S.KeyCoins) (c : S.Choice n)
    (b : Bool) : PMF (S.Pub × S.Sig) :=
  S.signLaw H (S.sk (keys (c.user b))) c.ring (c.idx b) c.msg

/-- **A valid output of user `b`** of a challenge at the oracle `H`: the public value and the base
signature `y` are valid at user `b`'s position. -/
def Choice.ValidAt {n : ℕ} (H : S.Orc) (c : S.Choice n) (b : Bool) (y : S.Pub × S.Sig) : Prop :=
  S.Valid H c.ring c.msg y.1 (c.idx b) y.2

end PubSigner

/-! ### The anonymity game -/

section Game

variable {N : ℕ} {RMsg : Type} [DecidableEq RMsg] {S : PubSigner N RMsg}
  {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] (M : SPBCS Mg P S.Stmt k kN kS L e)

variable (S) in
/-- **An anonymity adversary against full key exposure** (BKM06 Definition 4, ePrint 2005/304,
p. 6, with the keys given at the start as in CCLM22 Experiment 2, p. 21) with `n` honest users and
`Q` challenges: a finite set of challenges and, in round `j`, a challenge from it chosen as a
function of the honest users' key-generation coins, the whole oracle `H` of the base scheme, the
whole oracle of the compiled argument, and the public values and ring signatures of the earlier
rounds, with `⊥` for the refused rounds. A chosen challenge may hold any ring containing the two
users' public keys at its positions (`Choice.Valid`); a ring the signer refuses at `H`
(`PubSigner.Admit`) is answered by `⊥`, which the adversary sees. The adversary is deterministic
(a randomized one is a mixture). The set is fixed before the keys, so it holds candidate rings for
every key vector; the bounds count only the challenges valid for the actual keys
(`ValidCountLe`). -/
structure PubAnonAdversary (n Q : ℕ) where
  /-- The finite set of challenges the adversary may choose. -/
  choices : Finset (S.Choice n)
  /-- The challenge of round `j`. -/
  choose : (j : Fin Q) → (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
    PubHist S.Pub M.NIProof j → S.Choice n
  /-- Every chosen challenge is in the set. -/
  choose_mem : ∀ j keys H h hist, choose j keys H h hist ∈ choices
  /-- The positions of every chosen challenge hold the two users' public keys. -/
  choose_valid : ∀ j keys H h hist, (choose j keys H h hist).Valid S keys

namespace PubAnonAdversary

variable {M} {n Q : ℕ} (A : PubAnonAdversary S M n Q)

open Classical in
/-- **The challenges of the set valid for the users' coins `keys`**: those whose positions hold
the two users' public keys. -/
noncomputable def validChoices (keys : Fin n → S.KeyCoins) : Finset (S.Choice n) :=
  A.choices.filter fun c => c.Valid S keys

theorem mem_validChoices {keys : Fin n → S.KeyCoins} {c : S.Choice n} :
    c ∈ A.validChoices keys ↔ c ∈ A.choices ∧ c.Valid S keys := by
  classical
  unfold validChoices
  exact Finset.mem_filter

/-- **At most `C` challenges of the set are valid for any key vector.** This is the count the
bounds use: the set itself may hold candidate rings for every possible key vector. -/
def ValidCountLe (C : ℕ) : Prop :=
  ∀ keys : Fin n → S.KeyCoins, (A.validChoices keys).card ≤ C

/-- **A table of signatures**: for each round and each challenge of the set, a public value and a
base signature. -/
abbrev Table : Type := Fin Q → A.choices → S.Pub × S.Sig

/-- **The law of the signature table** in the experiment `b` at the oracle `H` and the users'
coins `keys`: every entry independent, the entry of a challenge signed by its user `b`. Round `j`
uses the entry of its chosen challenge only, so its signature has the signing law of that
challenge. -/
noncomputable def tableLaw (H : S.Orc) (keys : Fin n → S.KeyCoins) (b : Bool) : PMF A.Table :=
  PMF.pi fun _ => PMF.pi fun c : A.choices => c.1.signLaw H keys b

/-- **The selector of the experiment `b`** at the table `T`: round `j` is refused when the signer
refuses the chosen challenge's ring at `H`, and otherwise proves the chosen challenge's statement,
with the table's public value, with the witness of user `b`. -/
def selector (keys : Fin n → S.KeyCoins) (H : S.Orc) (b : Bool) (T : A.Table) :
    Selector (Query k kN kS L → Out k e) S.Stmt S.Wit S.Pub M.NIProof Q :=
  fun j h hist =>
    if S.Admit H (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg then
      some (S.stmt (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg
          (T j ⟨_, A.choose_mem j keys H h hist⟩).1,
        S.wit ((A.choose j keys H h hist).idx b) (T j ⟨_, A.choose_mem j keys H h hist⟩).2)
    else none

variable (E : (j : ι) → (M.comp j).Encoder) {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type} [Fintype R] [Nonempty R]
  (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt)

/-- The law of a ring signature at the oracle `H` of the base scheme: the compiled honest proof at
the oracle `h` of the compiled argument. -/
noncomputable def proofLawAt (H : S.Orc) (h : Query k kN kS L → Out k e) (x : S.Stmt) (w : S.Wit) :
    PMF M.NIProof :=
  proofLaw E (Qs H) h x (honest H w)

/-- **The experiment `b` of anonymity against full key exposure** (BKM06 Definition 4, p. 6): the
honest users' coins uniform, the oracle `H` of the base scheme uniform, the signature table of the
experiment `b`; then the oracle of the compiled argument uniform and the `Q` rounds, round `j`
answered by `⊥` when the signer refuses the chosen challenge's ring at `H`, and otherwise by the
public value and the ring signature of user `b` of the chosen challenge. The public value is the
signer's output. The outcome is the users' coins, both oracles and the history. -/
noncomputable def game (b : Bool) :
    PMF ((Fin n → S.KeyCoins) × S.Orc × (Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q) :=
  (PMF.uniformOfFintype (Fin n → S.KeyCoins)).bind fun keys =>
    (PMF.uniformOfFintype S.Orc).bind fun H =>
      (A.tableLaw H keys b).bind fun T =>
        (pubRun (proofLawAt E Qs honest H) S.stmtPub (A.selector keys H b T) Q le_rfl).map
          fun s => (keys, H, s.1, s.2)

/-- **The anonymity advantage** of the distinguisher `D`, given the users' coins, both oracles and
the history. -/
noncomputable def advantage
    (D : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) : ℝ :=
  GordieHowe.gameAdvantage (A.game E Qs honest false) (A.game E Qs honest true)
    {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}

/-! ### The coupled table -/

section Coupled

variable (H : S.Orc) (keys : Fin n → S.KeyCoins)

/-- **The coupling of the two signers of a challenge**: a joint law of the entries of user `0` and
user `1`, with those marginals, whose public values differ with probability at most the distance
of the two public-value laws (`PMF.exists_coupling_map_le_tvDist`). -/
noncomputable def coupling (c : A.choices) : PMF ((S.Pub × S.Sig) × (S.Pub × S.Sig)) :=
  Classical.choose (PMF.exists_coupling_map_le_tvDist (c.1.signLaw H keys false)
    (c.1.signLaw H keys true) Prod.fst)

theorem map_fst_coupling (c : A.choices) :
    (A.coupling H keys c).map Prod.fst = c.1.signLaw H keys false :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (c.1.signLaw H keys false)
    (c.1.signLaw H keys true) Prod.fst)).1

theorem map_snd_coupling (c : A.choices) :
    (A.coupling H keys c).map Prod.snd = c.1.signLaw H keys true :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (c.1.signLaw H keys false)
    (c.1.signLaw H keys true) Prod.fst)).2.1

theorem toReal_coupling_ne_le (c : A.choices) :
    ((A.coupling H keys c).toOuterMeasure {x | x.1.1 ≠ x.2.1}).toReal ≤
      PMF.tvDist ((c.1.signLaw H keys false).map Prod.fst) ((c.1.signLaw H keys true).map Prod.fst) :=
  (Classical.choose_spec (PMF.exists_coupling_map_le_tvDist (c.1.signLaw H keys false)
    (c.1.signLaw H keys true) Prod.fst)).2.2

/-- An event of the first entry of the coupling has its probability under user `0`'s law. -/
theorem coupling_fst_eq (c : A.choices) (U : Set (S.Pub × S.Sig)) :
    (A.coupling H keys c).toOuterMeasure {x | x.1 ∈ U} =
      (c.1.signLaw H keys false).toOuterMeasure U := by
  rw [← A.map_fst_coupling H keys c, PMF.toOuterMeasure_map_apply]
  rfl

/-- An event of the second entry of the coupling has its probability under user `1`'s law. -/
theorem coupling_snd_eq (c : A.choices) (U : Set (S.Pub × S.Sig)) :
    (A.coupling H keys c).toOuterMeasure {x | x.2 ∈ U} =
      (c.1.signLaw H keys true).toOuterMeasure U := by
  rw [← A.map_snd_coupling H keys c, PMF.toOuterMeasure_map_apply]
  rfl

/-- A table of coupled entries. -/
abbrev CTable : Type := Fin Q → A.choices → (S.Pub × S.Sig) × (S.Pub × S.Sig)

/-- The law of the coupled table: every entry independent, from the coupling of its challenge. -/
noncomputable def coupledLaw : PMF A.CTable :=
  PMF.pi fun _ => PMF.pi fun c => A.coupling H keys c

/-- The entries of user `b` of a coupled table. -/
def side (b : Bool) (T : A.CTable) : A.Table := fun j c => if b then (T j c).2 else (T j c).1

/-- **The signature table is a side of the coupled table.** -/
theorem tableLaw_eq_map_side (b : Bool) :
    A.tableLaw H keys b = (A.coupledLaw H keys).map (A.side b) := by
  have h1 : (A.coupledLaw H keys).map (A.side b) =
      PMF.pi fun _ => ((PMF.pi fun c => A.coupling H keys c).map fun row c =>
        if b then (row c).2 else (row c).1) :=
    PMF.pi_map (fun _ => PMF.pi fun c => A.coupling H keys c)
      (fun _ row c => if b then (row c).2 else (row c).1)
  rw [h1, tableLaw]
  congr 1
  funext j
  rw [PMF.pi_map (fun c => A.coupling H keys c) (fun _ x => if b then x.2 else x.1)]
  congr 1
  funext c
  cases b
  · exact (A.map_fst_coupling H keys c).symm
  · exact (A.map_snd_coupling H keys c).symm

end Coupled

/-! ### The hybrid -/

section Hybrid

variable (H : S.Orc) (keys : Fin n → S.KeyCoins)

variable (S) in
open Classical in
/-- **The hybrid choice of a challenge at a coupled entry** `x` at the oracle `H`: when user `0`'s
output is valid, the statement with its public value, user `0`'s witness, and user `1`'s witness
when that is valid with the same public value (user `0`'s otherwise); when only user `1`'s output
is valid, its statement and witness twice; when neither is valid, `none`. Every choice it makes is
admissible (`hybChoice_admissible`). -/
noncomputable def hybChoice (c : S.Choice n) (x : (S.Pub × S.Sig) × (S.Pub × S.Sig)) :
    Option (SPBCS.WIChoice S.Stmt S.Wit) :=
  if c.ValidAt H false x.1 then
    some ⟨S.stmt c.ring c.msg x.1.1, S.wit c.idx₀ x.1.2,
      if c.ValidAt H true x.2 ∧ x.1.1 = x.2.1 then S.wit c.idx₁ x.2.2 else S.wit c.idx₀ x.1.2⟩
  else if c.ValidAt H true x.2 then
    some ⟨S.stmt c.ring c.msg x.2.1, S.wit c.idx₁ x.2.2, S.wit c.idx₁ x.2.2⟩
  else none

/-- **Every hybrid choice is admissible**: both witnesses are in the ring relation at `H` for the
statement. -/
theorem hybChoice_admissible {c : S.Choice n} {x : (S.Pub × S.Sig) × (S.Pub × S.Sig)}
    {w : SPBCS.WIChoice S.Stmt S.Wit} (hw : hybChoice S H c x = some w) :
    (w.stmt, w.wit₀) ∈ S.rel H ∧ (w.stmt, w.wit₁) ∈ S.rel H := by
  unfold hybChoice at hw
  split_ifs at hw with h0 h1 h1'
  · cases hw
    obtain ⟨h1, he⟩ := h1
    refine ⟨h0, ?_⟩
    change S.Valid H c.ring c.msg x.1.1 c.idx₁ x.2.2
    rw [he]
    exact h1
  · cases hw
    exact ⟨h0, h0⟩
  · cases hw
    exact ⟨h1', h1'⟩

/-- **The hybrid two-witness choices** at the coupled table `T`, refusing the rounds whose ring the
signer refuses at `H`. -/
noncomputable def hybrid (T : A.CTable) : HistChoices M S.Wit S.Pub Q :=
  fun j h hist =>
    if S.Admit H (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg then
      hybChoice S H (A.choose j keys H h hist) (T j ⟨_, A.choose_mem j keys H h hist⟩)
    else none

open Classical in
/-- **The hybrid choice set** at the coupled table `T`: the hybrid choices of the challenges of the
set valid for `keys`, at every round. -/
noncomputable def hybridSet (T : A.CTable) : Finset (SPBCS.WIChoice S.Stmt S.Wit) :=
  ((Finset.univ : Finset (Fin Q)) ×ˢ (A.validChoices keys).attach).biUnion fun p =>
    (hybChoice S H p.2.1 (T p.1 ⟨p.2.1, ((A.mem_validChoices).1 p.2.2).1⟩)).toFinset

theorem card_hybridSet_le (T : A.CTable) :
    (A.hybridSet H keys T).card ≤ Q * (A.validChoices keys).card := by
  classical
  refine Finset.card_biUnion_le.trans ?_
  refine (Finset.sum_le_sum (g := fun _ => 1) fun p _ => Finset.card_le_one.2
    fun a ha b hb => by
      rw [Option.mem_toFinset] at ha hb
      exact Option.mem_unique ha hb).trans ?_
  rw [Finset.sum_const, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Finset.card_attach, smul_eq_mul, mul_one]

theorem hybrid_mem (T : A.CTable) (j : Fin Q) (h : Query k kN kS L → Out k e)
    (hist : PubHist S.Pub M.NIProof j) (x : SPBCS.WIChoice S.Stmt S.Wit)
    (hx : A.hybrid H keys T j h hist = some x) : x ∈ A.hybridSet H keys T := by
  classical
  unfold hybrid at hx
  split_ifs at hx with hA
  unfold hybridSet
  have hv : A.choose j keys H h hist ∈ A.validChoices keys :=
    (A.mem_validChoices).2 ⟨A.choose_mem j keys H h hist, A.choose_valid j keys H h hist⟩
  refine Finset.mem_biUnion.2 ⟨(j, ⟨_, hv⟩), Finset.mem_product.2 ⟨Finset.mem_univ _,
    Finset.mem_attach _ _⟩, ?_⟩
  rw [Option.mem_toFinset]
  exact hx

/-- **The hybrid choices are admissible.** -/
theorem hybridSet_admissible (T : A.CTable) :
    ∀ c ∈ A.hybridSet H keys T, (c.stmt, c.wit₀) ∈ S.rel H ∧ (c.stmt, c.wit₁) ∈ S.rel H := by
  classical
  intro x hx
  obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.1 hx
  rw [Option.mem_toFinset] at hp
  exact hybChoice_admissible H hp

/-- **In the experiment `0` the game selects as the hybrid answering with the first witnesses**
unless the signer admits the chosen ring and user `0`'s output of the chosen entry is invalid. -/
theorem selector_false_ne (T : A.CTable) (j : Fin Q) (h : Query k kN kS L → Out k e)
    (hist : PubHist S.Pub M.NIProof j)
    (hne : A.selector keys H false (A.side false T) j h hist ≠
      (A.hybrid H keys T).selector (fun _ => false) j h hist) :
    S.Admit H (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg ∧
      ¬ (A.choose j keys H h hist).ValidAt H false
        (T j ⟨_, A.choose_mem j keys H h hist⟩).1 := by
  by_cases hA : S.Admit H (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg
  · refine ⟨hA, fun h0 => hne ?_⟩
    simp only [selector, HistChoices.selector, hybrid, hybChoice, side, RingChoice.idx, hA,
      ite_true, h0, Option.map_some, Bool.false_eq_true, ite_false]
  · exact absurd (by simp [selector, HistChoices.selector, hybrid, hA]) hne

/-- **In the experiment `1` the game selects as the hybrid answering with the second witnesses**
unless the signer admits the chosen ring and, at the chosen entry, user `1`'s output is invalid or
the two public values differ. -/
theorem selector_true_ne (T : A.CTable) (j : Fin Q) (h : Query k kN kS L → Out k e)
    (hist : PubHist S.Pub M.NIProof j)
    (hne : A.selector keys H true (A.side true T) j h hist ≠
      (A.hybrid H keys T).selector (fun _ => true) j h hist) :
    S.Admit H (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg ∧
      (¬ (A.choose j keys H h hist).ValidAt H true (T j ⟨_, A.choose_mem j keys H h hist⟩).2 ∨
        (T j ⟨_, A.choose_mem j keys H h hist⟩).1.1 ≠
          (T j ⟨_, A.choose_mem j keys H h hist⟩).2.1) := by
  by_cases hA : S.Admit H (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg
  · refine ⟨hA, ?_⟩
    by_contra hc
    push Not at hc
    obtain ⟨h1, he⟩ := hc
    apply hne
    by_cases h0 : (A.choose j keys H h hist).ValidAt H false
        (T j ⟨_, A.choose_mem j keys H h hist⟩).1
    · simp only [selector, HistChoices.selector, hybrid, hybChoice, side, RingChoice.idx, hA,
        ite_true, h0, h1, he, and_self, Option.map_some]
    · simp only [selector, HistChoices.selector, hybrid, hybChoice, side, RingChoice.idx, hA,
        ite_true, h0, h1, ite_false, Option.map_some]
  · exact absurd (by simp [selector, HistChoices.selector, hybrid, hA]) hne

end Hybrid

/-! ### The bad events -/

section Bad

variable (E : (j : ι) → (M.comp j).Encoder) {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  (Qs : ∀ H x, M.IOPQueries (V H) x) {R : Type} [Fintype R] [Nonempty R]
  (honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt) (H : S.Orc) (keys : Fin n → S.KeyCoins)

/-- The experiment `b` at the table `T`. -/
noncomputable abbrev run (b : Bool) (T : A.Table) (j : ℕ) (hj : j ≤ Q) :
    PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof j) :=
  pubRun (proofLawAt E Qs honest H) S.stmtPub (A.selector keys H b T) j hj

/-- **The bad event `bad` of round `i`** at the coupled table `T`: in the experiment `b` before
round `i`, the signer admits the ring of round `i`'s chosen challenge and its entry is bad. -/
noncomputable def badProb (b : Bool)
    (bad : S.Choice n → (S.Pub × S.Sig) × (S.Pub × S.Sig) → Prop) (T : A.CTable) (i : Fin Q) :
    ℝ≥0∞ :=
  (A.run E Qs honest H keys b (A.side b T) i i.2.le).toOuterMeasure
    {s | S.Admit H (A.choose i keys H s.1 s.2).ring (A.choose i keys H s.1 s.2).msg ∧
      bad (A.choose i keys H s.1 s.2) (T i ⟨_, A.choose_mem i keys H s.1 s.2⟩)}

/-- The experiment before round `i` does not read row `i` of the table. -/
theorem run_side_update (b : Bool) (T : A.CTable) (i : Fin Q)
    (r : A.choices → (S.Pub × S.Sig) × (S.Pub × S.Sig)) :
    A.run E Qs honest H keys b (A.side b (Function.update T i r)) i i.2.le =
      A.run E Qs honest H keys b (A.side b T) i i.2.le := by
  refine pubRun_congr _ _ fun i' hi' => ?_
  have hne : i' ≠ i := fun h => by rw [h] at hi'; exact lt_irrefl _ hi'
  funext h hist
  simp only [selector, side, Function.update_of_ne hne]

open Classical in
/-- **The bad event of each round has probability at most `ε`** over the coupled table, when the
coupling of every valid admitted challenge gives the bad event probability at most `ε`. -/
theorem sum_coupledLaw_mul_badProb_le (b : Bool)
    (bad : S.Choice n → (S.Pub × S.Sig) × (S.Pub × S.Sig) → Prop) {ε : ℝ}
    (hε : ∀ c : A.choices, c.1.Valid S keys → S.Admit H c.1.ring c.1.msg →
      (A.coupling H keys c).toOuterMeasure {x | bad c.1 x} ≤ ENNReal.ofReal ε)
    (i : Fin Q) :
    ∑ T, A.coupledLaw H keys T * A.badProb E Qs honest H keys b bad T i ≤ ENNReal.ofReal ε := by
  let G : A.CTable → (A.choices → (S.Pub × S.Sig) × (S.Pub × S.Sig)) → ℝ≥0∞ := fun T row =>
    (A.run E Qs honest H keys b (A.side b T) i i.2.le).toOuterMeasure
      {s | S.Admit H (A.choose i keys H s.1 s.2).ring (A.choose i keys H s.1 s.2).msg ∧
        bad (A.choose i keys H s.1 s.2) (row ⟨_, A.choose_mem i keys H s.1 s.2⟩)}
  have hG : ∀ T r, G (Function.update T i r) = G T := fun T r => by
    funext row
    simp only [G, run_side_update]
  refine PMF.sum_pi_mul_apply_le _ i G hG fun T => ?_
  -- average the bad event of the chosen challenge over the row
  simp only [G, PMF.toOuterMeasure_apply]
  calc ∑ row, (PMF.pi fun c => A.coupling H keys c) row *
        ∑' s, {s : (Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof i |
          S.Admit H (A.choose i keys H s.1 s.2).ring (A.choose i keys H s.1 s.2).msg ∧
          bad (A.choose i keys H s.1 s.2) (row ⟨_, A.choose_mem i keys H s.1 s.2⟩)}.indicator
          (A.run E Qs honest H keys b (A.side b T) i i.2.le) s
      = ∑' s, A.run E Qs honest H keys b (A.side b T) i i.2.le s *
          ∑ row, (PMF.pi fun c => A.coupling H keys c) row *
            (if S.Admit H (A.choose i keys H s.1 s.2).ring (A.choose i keys H s.1 s.2).msg ∧
              bad (A.choose i keys H s.1 s.2) (row ⟨_, A.choose_mem i keys H s.1 s.2⟩)
              then 1 else 0) := by
        rw [← tsum_fintype (L := SummationFilter.unconditional _)]
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun s => ?_
        rw [tsum_fintype, Finset.mul_sum]
        refine Finset.sum_congr rfl fun row _ => ?_
        simp only [Set.indicator_apply, Set.mem_setOf_eq]
        split_ifs <;> ring
    _ ≤ ∑' s, A.run E Qs honest H keys b (A.side b T) i i.2.le s * ENNReal.ofReal ε := by
        refine ENNReal.tsum_le_tsum fun s => mul_le_mul_right ?_ _
        by_cases hA : S.Admit H (A.choose i keys H s.1 s.2).ring (A.choose i keys H s.1 s.2).msg
        swap
        · simp only [hA, false_and, ite_false, mul_zero, Finset.sum_const_zero]
          exact bot_le
        simp only [hA, true_and]
        set c : A.choices := ⟨_, A.choose_mem i keys H s.1 s.2⟩
        rw [PMF.sum_pi_mul_apply_coord (fun c => A.coupling H keys c) c
          (fun x => if bad c.1 x then 1 else 0)]
        have hm : ∑ x, A.coupling H keys c x * (if bad c.1 x then 1 else 0) =
            (A.coupling H keys c).toOuterMeasure {x | bad c.1 x} := by
          rw [PMF.toOuterMeasure_apply, tsum_fintype]
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [Set.indicator_apply, Set.mem_setOf_eq]
          split_ifs <;> simp
        rw [hm]
        exact hε c (A.choose_valid i keys H s.1 s.2) hA
    _ = ENNReal.ofReal ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Bad

/-! ### One oracle and one set of keys -/

section Fixed

variable {E : (j : ι) → (M.comp j).Encoder} {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
  {honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt}

/-- **A game and its hybrid at a coupled table are within the bad events of the rounds**: if the
selectors of the experiment `b` and of the hybrid answering with the witnesses of user `b` differ
only where the round's bad event `bad` holds (`hsel`), every event has probabilities within the
sum over the rounds of the bad events' probabilities. -/
theorem abs_run_sub_hybrid_le (H : S.Orc) (keys : Fin n → S.KeyCoins) (b : Bool) (T : A.CTable)
    (bad : S.Choice n → (S.Pub × S.Sig) × (S.Pub × S.Sig) → Prop)
    (hsel : ∀ j h hist, A.selector keys H b (A.side b T) j h hist ≠
      (A.hybrid H keys T).selector (fun _ => b) j h hist →
        S.Admit H (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg ∧
          bad (A.choose j keys H h hist) (T j ⟨_, A.choose_mem j keys H h hist⟩))
    (U : Set ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q)) :
    |((A.run E Qs honest H keys b (A.side b T) Q le_rfl).toOuterMeasure U).toReal -
      ((pubRun (proofLawAt E Qs honest H) S.stmtPub ((A.hybrid H keys T).selector fun _ => b) Q
        le_rfl).toOuterMeasure U).toReal| ≤
      ∑ i : Fin Q, (A.badProb E Qs honest H keys b bad T i).toReal := by
  refine (PMF.abs_toOuterMeasure_sub_le_tvDist _ _ _).trans ?_
  refine (tvDist_pubRun_le _ _ Q le_rfl).trans (Finset.sum_le_sum fun i _ => ?_)
  refine ENNReal.toReal_mono (ne_top_of_le_ne_top ENNReal.one_ne_top
    (PMF.toOuterMeasure_apply_le_one _ _)) (PMF.toOuterMeasure_mono _ ?_)
  rintro s ⟨hs, -⟩
  exact hsel _ s.1 s.2 hs

/-- **The experiments at a fixed oracle `H` and fixed users' coins are close**: for a compiled
argument whose honest prover has honest-verifier zero knowledge at error `δ` for the ring relation
at `H` (`hz`), at most `C` challenges of the set valid for `keys` (`hC`), an `ε` bounding the
distance of the two public-value laws of every valid challenge of the set whose ring the signer
admits at `H` (`hε`), and an `η` bounding the probability that either user's output of such a
challenge is invalid (`hη`), every event of the oracle of the compiled argument and the history
has probabilities within `Q · (ε + 2η) + Q · wiError δ (Q · C)`. A refused round is `⊥` in both
experiments and reads no signature. -/
theorem abs_condProb_sub_le (H : S.Orc) (keys : Fin n → S.KeyCoins)
    (Rv : M.Reveal E (Qs H)) {PubZ : Type} {pubZ : S.Stmt → PubZ}
    {sim : CausalJointSimulator Rv.MV PubZ} {δ : ℝ≥0}
    (hz : CausalHVZK Rv.MV (S.rel H) (honest H) pubZ sim δ) {C : ℕ}
    (hC : (A.validChoices keys).card ≤ C) {ε η : ℝ} (hε0 : 0 ≤ ε) (hη0 : 0 ≤ η)
    (hε : ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg →
      PMF.tvDist ((c.signLaw H keys false).map Prod.fst) ((c.signLaw H keys true).map Prod.fst) ≤ ε)
    (hη : ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg → ∀ b : Bool,
      (c.signLaw H keys b).toOuterMeasure {y | ¬ c.ValidAt H b y} ≤ ENNReal.ofReal η)
    (U : (Query k kN kS L → Out k e) → PubHist S.Pub M.NIProof Q → Prop) :
    |(((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
        {s | U s.1 s.2}).toReal -
      (((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure
        {s | U s.1 s.2}).toReal| ≤ Q * (ε + 2 * η) + Q * M.wiError δ (Q * C) := by
  classical
  set μ := A.coupledLaw H keys
  let law := proofLawAt E Qs honest H
  let U' : Set ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q) := {s | U s.1 s.2}
  let f : Bool → A.CTable → ℝ≥0∞ := fun b T =>
    (A.run E Qs honest H keys b (A.side b T) Q le_rfl).toOuterMeasure U'
  let g : Bool → A.CTable → ℝ≥0∞ := fun b T =>
    (pubRun law S.stmtPub ((A.hybrid H keys T).selector fun _ => b) Q le_rfl).toOuterMeasure U'
  have hcond : ∀ b, ((A.tableLaw H keys b).bind fun T =>
      A.run E Qs honest H keys b T Q le_rfl).toOuterMeasure U' = ∑ T, μ T * f b T := fun b => by
    rw [A.tableLaw_eq_map_side H keys b, PMF.bind_map, PMF.toOuterMeasure_bind_apply, tsum_fintype]
    rfl
  change |(((A.tableLaw H keys false).bind fun T =>
    A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure U').toReal - _| ≤ _
  rw [hcond false]
  change |(∑ T, μ T * f false T).toReal - (((A.tableLaw H keys true).bind fun T =>
    A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure U').toReal| ≤ _
  rw [hcond true]
  have hle1 : ∀ (p : PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q)),
      p.toOuterMeasure U' ≤ 1 := fun p => PMF.toOuterMeasure_apply_le_one _ _
  -- the bad events of the two experiments
  let bad₀ : S.Choice n → (S.Pub × S.Sig) × (S.Pub × S.Sig) → Prop := fun c x =>
    ¬ c.ValidAt H false x.1
  let bad₁ : S.Choice n → (S.Pub × S.Sig) × (S.Pub × S.Sig) → Prop := fun c x =>
    ¬ c.ValidAt H true x.2 ∨ x.1.1 ≠ x.2.1
  have hb₀ : ∀ c : A.choices, c.1.Valid S keys → S.Admit H c.1.ring c.1.msg →
      (A.coupling H keys c).toOuterMeasure {x | bad₀ c.1 x} ≤ ENNReal.ofReal η := fun c hc hA => by
    rw [show {x | bad₀ c.1 x} = {x | x.1 ∈ {y | ¬ c.1.ValidAt H false y}} from rfl,
      A.coupling_fst_eq H keys c]
    exact hη c.1 c.2 hc hA false
  have hb₁ : ∀ c : A.choices, c.1.Valid S keys → S.Admit H c.1.ring c.1.msg →
      (A.coupling H keys c).toOuterMeasure {x | bad₁ c.1 x} ≤ ENNReal.ofReal (η + ε) :=
    fun c hc hA => by
      have hu : {x | bad₁ c.1 x} = {x | x.2 ∈ {y | ¬ c.1.ValidAt H true y}} ∪
          {x : (S.Pub × S.Sig) × (S.Pub × S.Sig) | x.1.1 ≠ x.2.1} := rfl
      rw [hu, ENNReal.ofReal_add hη0 hε0]
      refine (MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_)
      · rw [A.coupling_snd_eq H keys c]
        exact hη c.1 c.2 hc hA true
      · rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top
          (PMF.toOuterMeasure_apply_le_one _ _))]
        exact ENNReal.ofReal_le_ofReal ((A.toReal_coupling_ne_le H keys c).trans
          (hε c.1 c.2 hc hA))
  -- the hybrid at the witnesses of user `0` and of user `1`
  have hwi : ∀ T, (μ T).toReal * |(g false T).toReal - (g true T).toReal| ≤
      (μ T).toReal * (Q * M.wiError δ (Q * C)) := fun T => by
    refine mul_le_mul_of_nonneg_left ?_ ENNReal.toReal_nonneg
    have hadv := gameAdvantage_pubRun_le (F := A.hybrid H keys T) S.stmtPub Rv hz
      (A.hybridSet H keys T) (A.hybridSet_admissible H keys T) (A.hybrid_mem H keys T) U
    refine hadv.trans (mul_le_mul_of_nonneg_left (SPBCS.wiError_mono δ ?_) (Nat.cast_nonneg _))
    exact (A.card_hybridSet_le H keys T).trans (Nat.mul_le_mul_left _ hC)
  -- the sum of a round's bad event over the coupled table
  have hsum : ∀ (b : Bool) (bad : S.Choice n → (S.Pub × S.Sig) × (S.Pub × S.Sig) → Prop) {ε' : ℝ},
      0 ≤ ε' → (∀ c : A.choices, c.1.Valid S keys → S.Admit H c.1.ring c.1.msg →
        (A.coupling H keys c).toOuterMeasure {x | bad c.1 x} ≤ ENNReal.ofReal ε') →
      ∑ T, (μ T).toReal * ∑ i : Fin Q, (A.badProb E Qs honest H keys b bad T i).toReal ≤
        Q * ε' := fun b bad ε' hε' hb => by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    calc ∑ i : Fin Q, ∑ T, (μ T).toReal * (A.badProb E Qs honest H keys b bad T i).toReal
        ≤ ∑ _i : Fin Q, ε' := Finset.sum_le_sum fun i _ => by
          have h := A.sum_coupledLaw_mul_badProb_le E Qs honest H keys b bad hb i
          have hne : ∀ T, μ T * A.badProb E Qs honest H keys b bad T i ≠ ⊤ := fun T =>
            ENNReal.mul_ne_top (μ.apply_ne_top T) (ne_top_of_le_ne_top ENNReal.one_ne_top
              (PMF.toOuterMeasure_apply_le_one _ _))
          simp_rw [← ENNReal.toReal_mul]
          rw [← ENNReal.toReal_sum fun T _ => hne T]
          exact ENNReal.toReal_le_of_le_ofReal hε' h
      _ = Q * ε' := by simp
  have hbad : ∀ b bad, (∀ T j h hist, A.selector keys H b (A.side b T) j h hist ≠
      (A.hybrid H keys T).selector (fun _ => b) j h hist →
        S.Admit H (A.choose j keys H h hist).ring (A.choose j keys H h hist).msg ∧
          bad (A.choose j keys H h hist) (T j ⟨_, A.choose_mem j keys H h hist⟩)) →
      ∀ T, (μ T).toReal * |(f b T).toReal - (g b T).toReal| ≤
        (μ T).toReal * ∑ i : Fin Q, (A.badProb E Qs honest H keys b bad T i).toReal :=
    fun b bad hsel T => mul_le_mul_of_nonneg_left
      (A.abs_run_sub_hybrid_le H keys b T bad (hsel T) U') ENNReal.toReal_nonneg
  have h0 := hbad false bad₀ fun T j h hist hne => A.selector_false_ne H keys T j h hist hne
  have h1 := hbad true bad₁ fun T j h hist hne => A.selector_true_ne H keys T j h hist hne
  have hs := fun (p q : A.CTable → ℝ≥0∞) =>
    PMF.abs_sum_mul_sub_sum_mul_le μ (f := p) (g := q)
  calc |(∑ T, μ T * f false T).toReal - (∑ T, μ T * f true T).toReal|
      ≤ |(∑ T, μ T * f false T).toReal - (∑ T, μ T * g false T).toReal| +
          |(∑ T, μ T * g false T).toReal - (∑ T, μ T * g true T).toReal| +
          |(∑ T, μ T * g true T).toReal - (∑ T, μ T * f true T).toReal| := by
        have h1 := abs_sub_le (∑ T, μ T * f false T).toReal (∑ T, μ T * g false T).toReal
          (∑ T, μ T * f true T).toReal
        have h2 := abs_sub_le (∑ T, μ T * g false T).toReal (∑ T, μ T * g true T).toReal
          (∑ T, μ T * f true T).toReal
        linarith
    _ ≤ Q * η + Q * M.wiError δ (Q * C) + Q * (η + ε) := by
        refine add_le_add (add_le_add ?_ ?_) ?_
        · refine ((PMF.abs_sum_mul_sub_sum_mul_le μ (fun _ => hle1 _) fun _ => hle1 _).trans
            (Finset.sum_le_sum fun T _ => h0 T)).trans ?_
          exact hsum false bad₀ hη0 hb₀
        · refine ((PMF.abs_sum_mul_sub_sum_mul_le μ (fun _ => hle1 _) fun _ => hle1 _).trans
            (Finset.sum_le_sum fun T _ => hwi T)).trans_eq ?_
          rw [← Finset.sum_mul, ← ENNReal.toReal_sum fun T _ => μ.apply_ne_top T, PMF.sum_coe,
            ENNReal.toReal_one, one_mul]
        · refine ((PMF.abs_sum_mul_sub_sum_mul_le μ (fun _ => hle1 _) fun _ => hle1 _).trans
            (Finset.sum_le_sum fun T _ => ?_)).trans (hsum true bad₁ (add_nonneg hη0 hε0) hb₁)
          rw [abs_sub_comm]
          exact h1 T
    _ = Q * (ε + 2 * η) + Q * M.wiError δ (Q * C) := by ring

end Fixed

/-! ### Anonymity -/

section Main

variable {E : (j : ι) → (M.comp j).Encoder} {V : S.Orc → S.Stmt → FullTr P τ → Bool}
  {Qs : ∀ H x, M.IOPQueries (V H) x} {R : Type} [Fintype R] [Nonempty R]
  {honest : S.Orc → S.Wit → R → CausalProver P τ S.Stmt}

/-- The probability of the event `D` in the experiment `b`, at the users' coins `keys` and the
oracle `H`. -/
theorem toOuterMeasure_game_eq (b : Bool)
    (D : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) :
    (A.game E Qs honest b).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2} =
      ∑ keys, PMF.uniformOfFintype _ keys * ∑ H, PMF.uniformOfFintype _ H *
        ((A.tableLaw H keys b).bind fun T => A.run E Qs honest H keys b T Q le_rfl).toOuterMeasure
          {s | D keys H s.1 s.2} := by
  rw [game, PMF.toOuterMeasure_bind_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun keys _ => ?_
  rw [PMF.toOuterMeasure_bind_apply, tsum_fintype]
  refine congrArg _ (Finset.sum_congr rfl fun H _ => ?_)
  rw [← PMF.map_bind, PMF.toOuterMeasure_map_apply]
  rfl

/-- The probabilities of an event in the two experiments at fixed users' coins and oracle differ by
at most one. -/
theorem abs_condProb_sub_le_one (H : S.Orc) (keys : Fin n → S.KeyCoins)
    (U : (Query k kN kS L → Out k e) → PubHist S.Pub M.NIProof Q → Prop) :
    |(((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
        {s | U s.1 s.2}).toReal -
      (((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure
        {s | U s.1 s.2}).toReal| ≤ 1 := by
  have key : ∀ p : PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q),
      0 ≤ (p.toOuterMeasure {s | U s.1 s.2}).toReal ∧ (p.toOuterMeasure {s | U s.1 s.2}).toReal ≤ 1 :=
    fun p => ⟨ENNReal.toReal_nonneg, ENNReal.toReal_le_of_le_ofReal zero_le_one
      (by rw [ENNReal.ofReal_one]; exact PMF.toOuterMeasure_apply_le_one _ _)⟩
  have h1 := key ((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl)
  have h2 := key ((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl)
  rw [abs_sub_le_iff]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

/-- A sum weighted by the uniform law is the average. -/
theorem _root_.PMF.sum_toReal_uniformOfFintype_mul {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) : ∑ x, (PMF.uniformOfFintype α x).toReal * f x = 𝔼 x, f x := by
  simp only [PMF.toReal_uniformOfFintype_apply, Fintype.expect_eq_sum_div_card]
  rw [← Finset.mul_sum, div_eq_inv_mul]

/-- **The bounds on the signers** of the adversary's challenges, at a good event `Good` of the
users' coins and the oracle: at good coins and oracles, for every challenge of the set valid for
the coins whose ring the signer admits, the two users' public-value laws are within `ε` (for the
generic ring of a scheme whose public value is a function of the signing coins, `ε = 0`), and each
user's output is invalid with probability at most `η` (the correctness error; `0` for a correct
signer). -/
structure SignerBounds (Good : (Fin n → S.KeyCoins) → S.Orc → Prop)
    (ε : (Fin n → S.KeyCoins) → S.Orc → ℝ) (η : ℝ) : Prop where
  /-- The distance bound is nonnegative. -/
  ε_nonneg : ∀ keys H, 0 ≤ ε keys H
  /-- The invalidity bound is nonnegative. -/
  η_nonneg : 0 ≤ η
  /-- The two users' public-value laws are within `ε`. -/
  tvDist_le : ∀ keys H, Good keys H → ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg →
    PMF.tvDist ((c.signLaw H keys false).map Prod.fst) ((c.signLaw H keys true).map Prod.fst) ≤
      ε keys H
  /-- Each user's output is invalid with probability at most `η`. -/
  invalid_le : ∀ keys H, Good keys H → ∀ c ∈ A.choices, c.Valid S keys → S.Admit H c.ring c.msg →
    ∀ b : Bool, (c.signLaw H keys b).toOuterMeasure {y | ¬ c.ValidAt H b y} ≤ ENNReal.ofReal η

/-- **Anonymity against full key exposure** (BKM06 Definition 4, ePrint 2005/304, p. 6, with the
keys given at the start as in CCLM22 Experiment 2, p. 21, `Q` adaptive challenges, signing
queries included, both oracles visible, deterministic adversaries; the adversary chooses any ring
holding the two users' keys and sees `⊥` for the rings the signer refuses): for the spBCS
compilation `M` whose honest prover has honest-verifier zero knowledge at error `δ` for the ring
relation at every oracle `H` (`hz`), every adversary with at most `C` challenges of its set valid
for any key vector (`hC`), and bounds `ε`, `η` on the signers at a good event `Good` of the users'
coins and the oracle (`hb`), the advantage of every distinguisher given the users' coins, both
oracles and the history is at most
`Q · (𝔼_{keys, H} ε + 2η) + Q · wiError δ (Q · C) + Pr_{keys, H}[¬ Good]`. Refused rounds are `⊥`
in both experiments, a function of `H`, the ring and the history, so they add nothing to the
bound. The bound is statistical except for what `wiError` assumes. -/
theorem advantage_le (Rv : ∀ H, M.Reveal E (Qs H)) {PubZ : Type}
    {pubZ : S.Stmt → PubZ} {sim : ∀ H, CausalJointSimulator (Rv H).MV PubZ} {δ : ℝ≥0}
    (hz : ∀ H, CausalHVZK (Rv H).MV (S.rel H) (honest H) pubZ (sim H) δ) {C : ℕ}
    (hC : A.ValidCountLe C) {Good : (Fin n → S.KeyCoins) → S.Orc → Prop}
    [∀ keys H, Decidable (Good keys H)] {ε : (Fin n → S.KeyCoins) → S.Orc → ℝ} {η : ℝ}
    (hb : A.SignerBounds Good ε η)
    (D : (Fin n → S.KeyCoins) → S.Orc → (Query k kN kS L → Out k e) →
      PubHist S.Pub M.NIProof Q → Prop) :
    A.advantage E Qs honest D ≤ Q * ((𝔼 keys, 𝔼 H, ε keys H) + 2 * η) +
      Q * M.wiError δ (Q * C) + 𝔼 keys, 𝔼 H, (if Good keys H then 0 else 1 : ℝ) := by
  unfold advantage GordieHowe.gameAdvantage GordieHowe.advantage
  change |((A.game E Qs honest false).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal -
    ((A.game E Qs honest true).toOuterMeasure {o | D o.1 o.2.1 o.2.2.1 o.2.2.2}).toReal| ≤ _
  rw [toOuterMeasure_game_eq, toOuterMeasure_game_eq]
  have hwi0 : 0 ≤ M.wiError δ (Q * C) := SPBCS.wiError_nonneg δ (Q * C)
  have hle : ∀ (p : PMF ((Query k kN kS L → Out k e) × PubHist S.Pub M.NIProof Q)) (s : Set _),
      p.toOuterMeasure s ≤ 1 := fun p s => PMF.toOuterMeasure_apply_le_one _ _
  have hle2 : ∀ b (keys : Fin n → S.KeyCoins), ∑ H, PMF.uniformOfFintype S.Orc H *
      ((A.tableLaw H keys b).bind fun T => A.run E Qs honest H keys b T Q le_rfl).toOuterMeasure
        {s | D keys H s.1 s.2} ≤ 1 := fun b keys =>
    (Finset.sum_le_sum fun H _ => mul_le_of_le_one_right' (hle _ _)).trans_eq
      (by rw [← tsum_fintype (L := SummationFilter.unconditional _)]; exact PMF.tsum_coe _)
  -- one oracle and one set of keys
  let φ : (Fin n → S.KeyCoins) → S.Orc → ℝ := fun keys H =>
    Q * (ε keys H + 2 * η) + Q * M.wiError δ (Q * C) + (if Good keys H then 0 else 1 : ℝ)
  have hpt : ∀ keys H,
      |(((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
        {s | D keys H s.1 s.2}).toReal -
      (((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure
        {s | D keys H s.1 s.2}).toReal| ≤ φ keys H := by
    intro keys H
    have hQε : 0 ≤ (Q : ℝ) * (ε keys H + 2 * η) :=
      mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hb.ε_nonneg keys H)
        (mul_nonneg zero_le_two hb.η_nonneg))
    have hQw : 0 ≤ (Q : ℝ) * M.wiError δ (Q * C) := mul_nonneg (Nat.cast_nonneg _) hwi0
    by_cases hG : Good keys H
    · simp only [φ, hG, ite_true, add_zero]
      exact A.abs_condProb_sub_le H keys (Rv H) (hz H) (hC keys) (hb.ε_nonneg keys H)
        hb.η_nonneg (hb.tvDist_le keys H hG) (hb.invalid_le keys H hG) (D keys H)
    · simp only [φ, hG, ite_false]
      linarith [A.abs_condProb_sub_le_one (E := E) (Qs := Qs) (honest := honest) H keys (D keys H)]
  refine (PMF.abs_sum_mul_sub_sum_mul_le _ (hle2 false) (hle2 true)).trans ?_
  have hinner : ∀ keys : Fin n → S.KeyCoins,
      |(∑ H, PMF.uniformOfFintype S.Orc H *
        ((A.tableLaw H keys false).bind fun T => A.run E Qs honest H keys false T Q le_rfl).toOuterMeasure
          {s | D keys H s.1 s.2}).toReal -
        (∑ H, PMF.uniformOfFintype S.Orc H *
        ((A.tableLaw H keys true).bind fun T => A.run E Qs honest H keys true T Q le_rfl).toOuterMeasure
          {s | D keys H s.1 s.2}).toReal| ≤ 𝔼 H, φ keys H := fun keys => by
    refine (PMF.abs_sum_mul_sub_sum_mul_le _ (fun _ => hle _ _) fun _ => hle _ _).trans ?_
    rw [← PMF.sum_toReal_uniformOfFintype_mul]
    exact Finset.sum_le_sum fun H _ => mul_le_mul_of_nonneg_left (hpt keys H)
      ENNReal.toReal_nonneg
  calc ∑ keys, (PMF.uniformOfFintype (Fin n → S.KeyCoins) keys).toReal * _
      ≤ ∑ keys, (PMF.uniformOfFintype (Fin n → S.KeyCoins) keys).toReal * 𝔼 H, φ keys H :=
        Finset.sum_le_sum fun keys _ => mul_le_mul_of_nonneg_left (hinner keys)
          ENNReal.toReal_nonneg
    _ = 𝔼 keys, 𝔼 H, φ keys H := PMF.sum_toReal_uniformOfFintype_mul _
    _ = _ := by
        simp only [φ, Finset.expect_add_distrib, ← Finset.mul_expect, Fintype.expect_const]

end Main

end PubAnonAdversary

end Game

/-! ### The generic ring signature of a signature scheme -/

section Scheme

variable {Sch : SigScheme} {RMsg : Type} [DecidableEq RMsg] {N : ℕ}

variable (Sch N) in
/-- **The signer of the generic ring signature** of the scheme `Sch` (`Scheme.lean`), as a
`PubSigner` with no oracle of the base scheme (`Orc = Unit`): user `i` signs the base message
`bind R m` with uniform signing coins, and the public value is the signature's (`Sch.pub σ`, read
off the signature: Falcon's salt, `Unit` for ML-DSA); statements `(R, m, v)` and witnesses
`(i, σ)` of the ring relation `ringRel adm bind`; the signer refuses the rings outside `adm`. -/
noncomputable abbrev schemeSigner (adm : List Sch.PK → Prop) [DecidablePred adm]
    (bind : List Sch.PK → RMsg → Sch.Msg) : PubSigner N RMsg where
  PK := Sch.PK
  SK := Sch.SK
  KeyCoins := Sch.KeyCoins
  Pub := Sch.Pub
  Sig := Sch.Sig
  Orc := Unit
  Stmt := RingStmt Sch RMsg N
  Wit := RingWit Sch
  keyGen := Sch.keyGen
  signLaw _ sk R _ m := (PMF.uniformOfFintype Sch.SignCoins).map fun sc =>
    (Sch.pub (Sch.signWith sk (bind R.1 m) sc), Sch.signWith sk (bind R.1 m) sc)
  stmt R m v := ⟨R, m, v⟩
  wit i σ := ⟨i, σ⟩
  stmtPub := RingStmt.pub
  stmtPub_stmt _ _ _ := rfl
  rel _ := ringRel adm bind
  Admit _ R _ := adm R.1
  instDecAdmit _ R _ := inferInstanceAs (Decidable (adm R.1))

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] (M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e)

/-- **An anonymity adversary against full key exposure for the generic ring signature** of `Sch`
(`PubAnonAdversary` at `schemeSigner`): `n` honest users, `Q` adaptive challenges, any ring of at
most `N` keys holding the two users' keys, `⊥` for the rings outside `adm`. -/
abbrev KeyedAnonAdversary (adm : List Sch.PK → Prop) [DecidablePred adm]
    (bind : List Sch.PK → RMsg → Sch.Msg) (n Q : ℕ) : Type :=
  PubAnonAdversary (schemeSigner Sch N adm bind) M n Q

/-- **The anonymity advantage for the generic ring signature** of the distinguisher `D`, given the
users' key-generation coins, the whole oracle of the compiled argument and the history of public
values and ring signatures (`PubAnonAdversary.advantage` at `schemeSigner`, whose oracle is
`Unit`), for the encoders `E`, the query phases `Qs` and the honest prover family `honest`. -/
noncomputable def keyedAnonAdvantage (E : (j : ι) → (M.comp j).Encoder)
    {V : RingStmt Sch RMsg N → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries V x) {R : Type}
    [Fintype R] [Nonempty R]
    (honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N))
    {adm : List Sch.PK → Prop} [DecidablePred adm] {bind : List Sch.PK → RMsg → Sch.Msg} {n Q : ℕ}
    (A : KeyedAnonAdversary M adm bind n Q)
    (D : (Fin n → Sch.KeyCoins) → (Query k kN kS L → Out k e) → PubHist Sch.Pub M.NIProof Q →
      Prop) : ℝ :=
  A.advantage (V := fun _ => V) E (fun _ => Qs) (fun _ => honest) fun keys _ => D keys

namespace KeyedAnonAdversary

variable {M} {adm : List Sch.PK → Prop} [DecidablePred adm] {bind : List Sch.PK → RMsg → Sch.Msg}
  {n Q : ℕ}

/-- **The two users' public-value laws agree** when the public value of an honest signature is a
function of the signing coins (`hpub`): both are the law of `pubOf` at uniform coins. -/
theorem map_fst_signLaw {pubOf : Sch.SignCoins → Sch.Pub} (hpub : Sch.PubOfCoins pubOf)
    (keys : Fin n → Sch.KeyCoins) (c : (schemeSigner Sch N adm bind).Choice n) (b : Bool) :
    (c.signLaw () keys b).map Prod.fst = (PMF.uniformOfFintype Sch.SignCoins).map pubOf := by
  change ((PMF.uniformOfFintype Sch.SignCoins).map _).map Prod.fst = _
  rw [PMF.map_comp]
  congr 1
  funext sc
  exact hpub _ _ sc

/-- **An honest signature is invalid only if it fails to verify**: at a valid challenge on an
admissible ring, the probability that user `b`'s output is invalid is at most the correctness
error. -/
theorem invalid_le {εc : ℝ≥0∞} (hcorr : Sch.CorrectWithin εc) (keys : Fin n → Sch.KeyCoins)
    (c : (schemeSigner Sch N adm bind).Choice n) (hc : c.Valid _ keys) (hA : adm c.ring.1)
    (b : Bool) : (c.signLaw () keys b).toOuterMeasure {y | ¬ c.ValidAt () b y} ≤ εc := by
  have hi : c.idx b < c.ring.1.length := by
    cases b
    · exact hc.idx₀_lt
    · exact hc.idx₁_lt
  have hR : c.ring.1[c.idx b] = Sch.pk (keys (c.user b)) := by
    cases b
    · exact hc.key₀
    · exact hc.key₁
  change ((PMF.uniformOfFintype Sch.SignCoins).map _).toOuterMeasure _ ≤ _
  rw [PMF.toOuterMeasure_map_apply]
  refine (PMF.toOuterMeasure_mono _ ?_).trans (hcorr (keys (c.user b)) (bind c.ring.1 c.msg))
  rintro sc ⟨hv, -⟩ hver
  exact hv ⟨hA, RingRel.of_signWith (m := c.msg) hi hR hver⟩

end KeyedAnonAdversary

/-- **Anonymity against full key exposure for the generic ring signature** (BKM06 Definition 4,
ePrint 2005/304, p. 6, with the keys given at the start as in CCLM22 Experiment 2, p. 21, `Q`
adaptive challenges, signing queries included; `PubAnonAdversary.advantage_le` at
`schemeSigner`), for a base scheme with correctness error `ε_c` (`hcorr`) whose public value is a
function `pubOf` of the signing coins (`hpub`: Falcon's salt, or `Pub = Unit`), so that the two
users' public values have the same law: for the spBCS compilation `M` of a ring composite, with
what the compiled proof reveals read off the composite view (`Rv`), whose honest prover has
honest-verifier zero knowledge (CY24 Definition 23.1.8 for composites, `CausalHVZK`) at error `δ`
for the ring relation (`h`): for every adversary with at most `C` challenges of its set valid for
any key vector (`hA`) and every distinguisher given the users' key-generation coins, the whole
oracle and the history, the advantage is at most `Q · wiError δ (Q · C) + 2 Q ε_c`: in each round
the two honest signatures are valid except with probability at most `2 ε_c`. -/
theorem keyedAnon_le_of_correctWithin {adm : List Sch.PK → Prop} [DecidablePred adm]
    {bind : List Sch.PK → RMsg → Sch.Msg} {E : (j : ι) → (M.comp j).Encoder}
    {V : RingStmt Sch RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries V x} {R : Type}
    [Fintype R] [Nonempty R]
    {honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N)}
    {Pub : Type} {pub : RingStmt Sch RMsg N → Pub} {εc : ℝ≥0} (hcorr : Sch.CorrectWithin εc)
    {pubOf : Sch.SignCoins → Sch.Pub} (hpub : Sch.PubOfCoins pubOf) (Rv : M.Reveal E Qs)
    {sim : CausalJointSimulator Rv.MV Pub} {δ : ℝ≥0}
    (h : CausalHVZK Rv.MV (ringRel adm bind) honest pub sim δ)
    {n Q C : ℕ} (A : KeyedAnonAdversary M adm bind n Q) (hA : A.ValidCountLe C)
    (D : (Fin n → Sch.KeyCoins) → (Query k kN kS L → Out k e) → PubHist Sch.Pub M.NIProof Q →
      Prop) :
    keyedAnonAdvantage M E Qs honest A D ≤ Q * M.wiError δ (Q * C) + 2 * Q * εc := by
  have hb : A.SignerBounds (fun _ _ => True) (fun _ _ => 0) εc :=
    { ε_nonneg := fun _ _ => le_rfl
      η_nonneg := εc.2
      tvDist_le := fun keys _ _ c _ _ _ => by
        rw [KeyedAnonAdversary.map_fst_signLaw hpub keys c false,
          KeyedAnonAdversary.map_fst_signLaw hpub keys c true, PMF.tvDist_self]
      invalid_le := fun keys _ _ c _ hc hA' b => by
        rw [ENNReal.ofReal_coe_nnreal]
        exact KeyedAnonAdversary.invalid_le hcorr keys c hc hA' b }
  have := A.advantage_le (V := fun _ => V) (E := E) (Qs := fun _ => Qs) (honest := fun _ => honest)
    (fun _ => Rv) (fun _ => h) hA hb fun keys _ => D keys
  unfold keyedAnonAdvantage
  simp only [Finset.expect_const_zero, ite_true, zero_add] at this
  linarith

/-- **Anonymity against full key exposure for the generic ring signature of a perfectly correct
scheme** (BKM06 Definition 4, ePrint 2005/304, p. 6; `keyedAnon_le_of_correctWithin` at
`ε_c = 0`): for a perfectly correct base scheme (`hcorr`) whose public value is a function of the
signing coins (`hpub`), the spBCS compilation `M` of a ring composite with what the compiled proof
reveals read off the composite view (`Rv`) and honest-verifier zero knowledge at error `δ` for the
ring relation (`h`), every adversary with at most `C` challenges of its set valid for any key
vector (`hA`) and every distinguisher, the advantage is at most `Q · wiError δ (Q · C)`. -/
@[headline]
theorem keyedAnon_le {adm : List Sch.PK → Prop} [DecidablePred adm]
    {bind : List Sch.PK → RMsg → Sch.Msg} {E : (j : ι) → (M.comp j).Encoder}
    {V : RingStmt Sch RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries V x} {R : Type}
    [Fintype R] [Nonempty R]
    {honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N)}
    {Pub : Type} {pub : RingStmt Sch RMsg N → Pub} (hcorr : Sch.Correct)
    {pubOf : Sch.SignCoins → Sch.Pub} (hpub : Sch.PubOfCoins pubOf) (Rv : M.Reveal E Qs)
    {sim : CausalJointSimulator Rv.MV Pub} {δ : ℝ≥0}
    (h : CausalHVZK Rv.MV (ringRel adm bind) honest pub sim δ)
    {n Q C : ℕ} (A : KeyedAnonAdversary M adm bind n Q) (hA : A.ValidCountLe C)
    (D : (Fin n → Sch.KeyCoins) → (Query k kN kS L → Out k e) → PubHist Sch.Pub M.NIProof Q →
      Prop) :
    keyedAnonAdvantage M E Qs honest A D ≤ Q * M.wiError δ (Q * C) := by
  have := keyedAnon_le_of_correctWithin M (εc := 0)
    (by rw [ENNReal.coe_zero]; exact hcorr.correctWithin) hpub Rv h A hA D
  simpa using this

end Scheme

end GordieHowe.Ring
