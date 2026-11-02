-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.Relations
public import GordieHowe.Model.Quantum.Interactive.ConstOut
public import GordieHowe.Foundations.ToMathlib.PMFFiber

@[expose] public section

/-!
# Named unforgeability assumptions

The assumptions on a base scheme that a theorem may take as hypotheses, each a bound `ε` on the
success probability of every adversary of a class `𝒜` in one of the games of
`GordieHowe/Model/Signature/`. The adversaries of the model (`MUAdversary`) need not be efficient:
over all adversaries, no bound below `1` holds for a scheme whose keys have verifying signatures
when the adversary reads the oracle as a table or verification does not read the oracle
(`not_muEufCmaHard_univ_whole`, `not_muEufCmaHard_univ_of_bverify_eq`). So every predicate names
its class.

- `MUEufCmaHard 𝒜 Q ε`, `MUSufCmaHard 𝒜 Q ε`, `MUEufNmaHard 𝒜 Q ε`: every adversary of `𝒜` has
  success probability at most `ε` with `Q` requests in MU-EUF-CMA^corr (Bader, Hofheinz, Jager,
  Kiltz, Li, TCC 2015, ePrint 2014/797, Definition 2), MU-SUF-CMA^corr (Diemert, Gellert, Jager,
  Lyu, PKC 2021, ePrint 2021/235, Definition 2) and MU-EUF-NMA^corr (`muEufNmaProb`).
  `SUEufCmaHard`, `SUSufCmaHard`, `SUEufNmaHard`: the same with one user, the games UF-CMA,
  sUF-CMA and UF-NMA of Kiltz, Lyubashevsky, Schaffner (EUROCRYPT 2018, ePrint 2017/916, §2.4,
  Definition 2.9 and Figure 7), with the differences listed in
  `GordieHowe/Model/Signature/SingleUser.lean`.
- `MUEufCmaHardWithin 𝒜 Q' Qs ε`, `MUSufCmaHardWithin 𝒜 Q' Qs ε`: every adversary of `𝒜`, against
  the challenger answering `Q'` requests, wins with at most `Qs` signing and corruption requests
  with probability at most `ε` (`muEufProbWithin`, `muSufProbWithin`): the games above with at most
  `Qs` signing and corruption requests counted, public-key requests not counted.
- Use and monotonicity: `MUEufCmaHard.le` (the bound for a member), `MUEufCmaHard.anti` (a smaller
  class), `MUEufCmaHard.mono` (a larger bound), and the same for the other predicates.
- Relations: `MUSufCmaHard.muEufCmaHard` (strong implies existential, on the same class);
  `MUEufCmaHard.muEufCmaHardWithin`, `MUSufCmaHard.muSufCmaHardWithin` (the game counting every
  request bounds the restricted one at every `Qs`), `MUSufCmaHardWithin.muEufCmaHardWithin`;
  `MUEufCmaHard.muEufNmaHard` (chosen-message implies no-message, for a class whose embeddings
  `nmaEmbed O i₀ A Q` lie in the chosen-message class), and the single-user forms.
- Satisfiability: `muEufCmaHard_one` and the others (`muEufCmaHardWithin_one`,
  `muSufCmaHardWithin_one`), every class at `ε = 1`.
  `constDrawAdversaries O n V t`: the adversaries that make no query and no request and output a
  draw from one law, independent of the public keys and the oracle (`QueryBoundedAdversary.ofLaw`,
  `GordieHowe/Model/Quantum/Interactive/ConstOut.lean`). `keyHitProb B n`: the largest probability
  that a key fixed in advance is some user's key; `keyHitProb_le`: at most `n` times the largest
  probability that the key of uniform key coins is a fixed key.
  `muEufCmaHard_constDrawAdversaries`, `muSufCmaHard_constDrawAdversaries`,
  `muEufNmaHard_constDrawAdversaries`: the class holds at `keyHitProb B n`.
- The unrestricted class fails.
  - With verification that does not read the oracle (`bverify H = bverify H'`, the base signers of
    ML-DSA and Falcon-512), at every view of the oracle: `drawAdversaries O n V t`, the draws from a
    law of the public keys, contain `drawBruteAdv O i₀ V t`, which outputs the key of user `i₀`
    with a base message and signature that verify under it (`muEufProb_drawBruteAdv`: probability
    `1` under `Signable`). `not_muEufCmaHard_drawAdversaries`,
    `not_muEufCmaHard_univ_of_bverify_eq`: no bound below `1`.
  - With the oracle as a table, for every verification: `bruteAdv O i₀ t`, the adversary with the
    whole oracle as its table (`OracleView.whole`) that outputs the key of user `i₀` with a
    verifying base message and signature under it at the oracle, if there is one.
    `muEufProb_bruteAdv`: if every key has a verifying signature at every oracle (`Signable`), it
    wins with probability `1`, with no query and no request. `not_muEufCmaHard_univ_whole`,
    `not_suEufCmaHard_univ_whole`.
  - `signable_of_correct`: `Signable` holds for a base scheme whose ordinary signer has correctness
    error `εc` and refusal rate `ρ` with `εc + ρ < 1` (`StdCorrectWithin`, `StdRefuseWithin`).
-/

namespace GordieHowe.Signature

open GordieHowe.Quantum GordieHowe.RingSignature
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TB : BaseTypes} {B : BaseSigner X Y N TB} {O : SignOracle B} {n : ℕ}

/-- With a user, the game has a request: the public key of user `0`. -/
instance [NeZero n] : Nonempty (MURequest O n) :=
  ⟨.publicKey 0⟩

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] {V : OracleView X Y} {t : ℕ}

/-! ### The predicates -/

/-- **MU-EUF-CMA^corr is `ε`-hard for the class `𝒜` with `Q` requests**: every adversary of `𝒜`
has success probability at most `ε` (`muEufProb`). -/
def MUEufCmaHard (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, muEufProb A Q ≤ ε

/-- **MU-SUF-CMA^corr is `ε`-hard for the class `𝒜` with `Q` requests** (`muSufProb`). -/
def MUSufCmaHard (𝒜 : Set (MUAdversary O n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, muSufProb A Q ≤ ε

/-- **MU-EUF-CMA^corr with at most `Qs` signing and corruption requests is `ε`-hard for the class
`𝒜` with `Q'` requests**: every adversary of `𝒜`, against the challenger answering `Q'` requests,
wins with at most `Qs` signing and corruption requests with probability at most `ε`
(`muEufProbWithin`). -/
def MUEufCmaHardWithin (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, muEufProbWithin A Q' Qs ≤ ε

/-- **MU-SUF-CMA^corr with at most `Qs` signing and corruption requests is `ε`-hard for the class
`𝒜` with `Q'` requests** (`muSufProbWithin`). -/
def MUSufCmaHardWithin (𝒜 : Set (MUAdversary O n V t)) (Q' Qs : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, muSufProbWithin A Q' Qs ≤ ε

/-- **MU-EUF-NMA^corr is `ε`-hard for the class `𝒜` with `Q` requests** (`muEufNmaProb`). -/
def MUEufNmaHard (𝒜 : Set (MUAdversary (SignOracle.none B) n V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, muEufNmaProb A Q ≤ ε

/-- **EUF-CMA is `ε`-hard for the class `𝒜` with `Q` requests** (`suEufProb`; KLS18 Figure 7,
UF-CMA). -/
def SUEufCmaHard (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, suEufProb A Q ≤ ε

/-- **SUF-CMA is `ε`-hard for the class `𝒜` with `Q` requests** (`suSufProb`; KLS18 Figure 7,
sUF-CMA). -/
def SUSufCmaHard (𝒜 : Set (SUAdversary O V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, suSufProb A Q ≤ ε

/-- **EUF-NMA is `ε`-hard for the class `𝒜` with `Q` requests** (`suEufNmaProb`; KLS18 Figure 7,
UF-NMA). -/
def SUEufNmaHard (𝒜 : Set (SUAdversary (SignOracle.none B) V t)) (Q : ℕ) (ε : ℝ≥0∞) : Prop :=
  ∀ A ∈ 𝒜, suEufNmaProb A Q ≤ ε

/-! ### Use and monotonicity -/

section Mono

variable {𝒜 𝒜' : Set (MUAdversary O n V t)} {Q : ℕ} {ε ε' : ℝ≥0∞}

/-- The bound for a member of the class. -/
theorem MUEufCmaHard.le (h : MUEufCmaHard 𝒜 Q ε) {A : MUAdversary O n V t} (hA : A ∈ 𝒜) :
    muEufProb A Q ≤ ε :=
  h A hA

/-- A smaller class keeps the bound. -/
theorem MUEufCmaHard.anti (h : MUEufCmaHard 𝒜 Q ε) (h𝒜 : 𝒜' ⊆ 𝒜) : MUEufCmaHard 𝒜' Q ε :=
  fun A hA => h A (h𝒜 hA)

/-- A larger bound holds. -/
theorem MUEufCmaHard.mono (h : MUEufCmaHard 𝒜 Q ε) (hε : ε ≤ ε') : MUEufCmaHard 𝒜 Q ε' :=
  fun A hA => (h A hA).trans hε

/-- The bound for a member of the class. -/
theorem MUSufCmaHard.le (h : MUSufCmaHard 𝒜 Q ε) {A : MUAdversary O n V t} (hA : A ∈ 𝒜) :
    muSufProb A Q ≤ ε :=
  h A hA

/-- A smaller class keeps the bound. -/
theorem MUSufCmaHard.anti (h : MUSufCmaHard 𝒜 Q ε) (h𝒜 : 𝒜' ⊆ 𝒜) : MUSufCmaHard 𝒜' Q ε :=
  fun A hA => h A (h𝒜 hA)

/-- A larger bound holds. -/
theorem MUSufCmaHard.mono (h : MUSufCmaHard 𝒜 Q ε) (hε : ε ≤ ε') : MUSufCmaHard 𝒜 Q ε' :=
  fun A hA => (h A hA).trans hε

/-- **Strong unforgeability gives existential unforgeability** on the same class. -/
theorem MUSufCmaHard.muEufCmaHard (h : MUSufCmaHard 𝒜 Q ε) : MUEufCmaHard 𝒜 Q ε :=
  fun A hA => (muEufProb_le_muSufProb A Q).trans (h A hA)

end Mono

section MonoWithin

variable {𝒜 𝒜' : Set (MUAdversary O n V t)} {Q' Qs : ℕ} {ε ε' : ℝ≥0∞}

/-- The bound for a member of the class. -/
theorem MUEufCmaHardWithin.le (h : MUEufCmaHardWithin 𝒜 Q' Qs ε) {A : MUAdversary O n V t}
    (hA : A ∈ 𝒜) : muEufProbWithin A Q' Qs ≤ ε :=
  h A hA

/-- A smaller class keeps the bound. -/
theorem MUEufCmaHardWithin.anti (h : MUEufCmaHardWithin 𝒜 Q' Qs ε) (h𝒜 : 𝒜' ⊆ 𝒜) :
    MUEufCmaHardWithin 𝒜' Q' Qs ε :=
  fun A hA => h A (h𝒜 hA)

/-- A larger bound holds. -/
theorem MUEufCmaHardWithin.mono (h : MUEufCmaHardWithin 𝒜 Q' Qs ε) (hε : ε ≤ ε') :
    MUEufCmaHardWithin 𝒜 Q' Qs ε' :=
  fun A hA => (h A hA).trans hε

/-- Fewer signing and corruption requests allowed keep the bound (`muEufProbWithin_mono`). -/
theorem MUEufCmaHardWithin.anti_count {Qs' : ℕ} (h : MUEufCmaHardWithin 𝒜 Q' Qs' ε)
    (hQs : Qs ≤ Qs') : MUEufCmaHardWithin 𝒜 Q' Qs ε :=
  fun A hA => (muEufProbWithin_mono A Q' hQs).trans (h A hA)

/-- The bound for a member of the class. -/
theorem MUSufCmaHardWithin.le (h : MUSufCmaHardWithin 𝒜 Q' Qs ε) {A : MUAdversary O n V t}
    (hA : A ∈ 𝒜) : muSufProbWithin A Q' Qs ≤ ε :=
  h A hA

/-- A smaller class keeps the bound. -/
theorem MUSufCmaHardWithin.anti (h : MUSufCmaHardWithin 𝒜 Q' Qs ε) (h𝒜 : 𝒜' ⊆ 𝒜) :
    MUSufCmaHardWithin 𝒜' Q' Qs ε :=
  fun A hA => h A (h𝒜 hA)

/-- A larger bound holds. -/
theorem MUSufCmaHardWithin.mono (h : MUSufCmaHardWithin 𝒜 Q' Qs ε) (hε : ε ≤ ε') :
    MUSufCmaHardWithin 𝒜 Q' Qs ε' :=
  fun A hA => (h A hA).trans hε

/-- Fewer signing and corruption requests allowed keep the bound (`muSufProbWithin_mono`). -/
theorem MUSufCmaHardWithin.anti_count {Qs' : ℕ} (h : MUSufCmaHardWithin 𝒜 Q' Qs' ε)
    (hQs : Qs ≤ Qs') : MUSufCmaHardWithin 𝒜 Q' Qs ε :=
  fun A hA => (muSufProbWithin_mono A Q' hQs).trans (h A hA)

/-- **Strong unforgeability gives existential unforgeability** with at most `Qs` signing and
corruption requests, on the same class (`muEufProbWithin_le_muSufProbWithin`). -/
theorem MUSufCmaHardWithin.muEufCmaHardWithin (h : MUSufCmaHardWithin 𝒜 Q' Qs ε) :
    MUEufCmaHardWithin 𝒜 Q' Qs ε :=
  fun A hA => (muEufProbWithin_le_muSufProbWithin A Q' Qs).trans (h A hA)

/-- **The game counting every request bounds the restricted one** at every number `Qs` of signing
and corruption requests (`muEufProbWithin_le_muEufProb`). -/
theorem MUEufCmaHard.muEufCmaHardWithin (h : MUEufCmaHard 𝒜 Q' ε) (Qs : ℕ) :
    MUEufCmaHardWithin 𝒜 Q' Qs ε :=
  fun A hA => (muEufProbWithin_le_muEufProb A Q' Qs).trans (h A hA)

/-- **The strong game counting every request bounds the restricted one** at every number `Qs` of
signing and corruption requests (`muSufProbWithin_le_muSufProb`). -/
theorem MUSufCmaHard.muSufCmaHardWithin (h : MUSufCmaHard 𝒜 Q' ε) (Qs : ℕ) :
    MUSufCmaHardWithin 𝒜 Q' Qs ε :=
  fun A hA => (muSufProbWithin_le_muSufProb A Q' Qs).trans (h A hA)

end MonoWithin

section MonoNma

variable {𝒜 𝒜' : Set (MUAdversary (SignOracle.none B) n V t)} {Q : ℕ} {ε ε' : ℝ≥0∞}

/-- The bound for a member of the class. -/
theorem MUEufNmaHard.le (h : MUEufNmaHard 𝒜 Q ε) {A : MUAdversary (SignOracle.none B) n V t}
    (hA : A ∈ 𝒜) : muEufNmaProb A Q ≤ ε :=
  h A hA

/-- A smaller class keeps the bound. -/
theorem MUEufNmaHard.anti (h : MUEufNmaHard 𝒜 Q ε) (h𝒜 : 𝒜' ⊆ 𝒜) : MUEufNmaHard 𝒜' Q ε :=
  fun A hA => h A (h𝒜 hA)

/-- A larger bound holds. -/
theorem MUEufNmaHard.mono (h : MUEufNmaHard 𝒜 Q ε) (hε : ε ≤ ε') : MUEufNmaHard 𝒜 Q ε' :=
  fun A hA => (h A hA).trans hε

/-- **Without messages, strong unforgeability is existential unforgeability.** -/
theorem muSufCmaHard_none_iff : MUSufCmaHard 𝒜 Q ε ↔ MUEufNmaHard 𝒜 Q ε := by
  simp only [MUSufCmaHard, MUEufNmaHard, muSufProb_none_eq_muEufNmaProb]

variable [Inhabited X]

/-- **Chosen-message hardness gives no-message hardness**: if the class `𝒜'` of the game at `O`
is `ε`-hard and contains the embedding `nmaEmbed O i₀ A Q` of every member `A` of `𝒜`, then `𝒜`
is `ε`-hard in the game without messages. -/
theorem MUEufCmaHard.muEufNmaHard {𝒜' : Set (MUAdversary O n V t)} (h : MUEufCmaHard 𝒜' Q ε)
    (i₀ : Fin n) (hemb : ∀ A ∈ 𝒜, nmaEmbed O i₀ A Q ∈ 𝒜') : MUEufNmaHard 𝒜 Q ε :=
  fun A hA => (muEufNmaProb_le_muEufProb_nmaEmbed i₀ A Q).trans (h _ (hemb A hA))

end MonoNma

section SingleUser

variable {Q : ℕ} {ε ε' : ℝ≥0∞}

/-- **Single-user strong unforgeability gives existential unforgeability.** -/
theorem SUSufCmaHard.suEufCmaHard {𝒜 : Set (SUAdversary O V t)} (h : SUSufCmaHard 𝒜 Q ε) :
    SUEufCmaHard 𝒜 Q ε :=
  MUSufCmaHard.muEufCmaHard h

variable [Inhabited X] in
/-- **Single-user chosen-message hardness gives no-message hardness**, user `0` idle. -/
theorem SUEufCmaHard.suEufNmaHard {𝒜 : Set (SUAdversary (SignOracle.none B) V t)}
    {𝒜' : Set (SUAdversary O V t)} (h : SUEufCmaHard 𝒜' Q ε)
    (hemb : ∀ A ∈ 𝒜, nmaEmbed O 0 A Q ∈ 𝒜') : SUEufNmaHard 𝒜 Q ε :=
  MUEufCmaHard.muEufNmaHard h 0 hemb

end SingleUser

/-! ### Satisfiability -/

section One

variable (Q : ℕ)

/-- Every class is `1`-hard in MU-EUF-CMA^corr. -/
theorem muEufCmaHard_one (𝒜 : Set (MUAdversary O n V t)) : MUEufCmaHard 𝒜 Q 1 :=
  fun A _ => muEufProb_le_one A Q

/-- Every class is `1`-hard in MU-SUF-CMA^corr. -/
theorem muSufCmaHard_one (𝒜 : Set (MUAdversary O n V t)) : MUSufCmaHard 𝒜 Q 1 :=
  fun A _ => muSufProb_le_one A Q

/-- Every class is `1`-hard in MU-EUF-CMA^corr with at most `Qs` signing and corruption
requests. -/
theorem muEufCmaHardWithin_one (Qs : ℕ) (𝒜 : Set (MUAdversary O n V t)) :
    MUEufCmaHardWithin 𝒜 Q Qs 1 :=
  fun A _ => muEufProbWithin_le_one A Q Qs

/-- Every class is `1`-hard in MU-SUF-CMA^corr with at most `Qs` signing and corruption
requests. -/
theorem muSufCmaHardWithin_one (Qs : ℕ) (𝒜 : Set (MUAdversary O n V t)) :
    MUSufCmaHardWithin 𝒜 Q Qs 1 :=
  fun A _ => muSufProbWithin_le_one A Q Qs

/-- Every class is `1`-hard in MU-EUF-NMA^corr. -/
theorem muEufNmaHard_one (𝒜 : Set (MUAdversary (SignOracle.none B) n V t)) :
    MUEufNmaHard 𝒜 Q 1 :=
  fun A _ => muEufProb_le_one A Q

/-- Every class is `1`-hard in EUF-CMA. -/
theorem suEufCmaHard_one (𝒜 : Set (SUAdversary O V t)) : SUEufCmaHard 𝒜 Q 1 :=
  muEufCmaHard_one Q 𝒜

/-- Every class is `1`-hard in SUF-CMA. -/
theorem suSufCmaHard_one (𝒜 : Set (SUAdversary O V t)) : SUSufCmaHard 𝒜 Q 1 :=
  muSufCmaHard_one Q 𝒜

/-- Every class is `1`-hard in EUF-NMA. -/
theorem suEufNmaHard_one (𝒜 : Set (SUAdversary (SignOracle.none B) V t)) :
    SUEufNmaHard 𝒜 Q 1 :=
  muEufNmaHard_one Q 𝒜

end One

section Draw

variable (B n) in
/-- **The best probability that a fixed key is a user's key**: the largest probability, over the
users' uniform key coins, that some user's public key is a key `pk` fixed in advance. -/
noncomputable def keyHitProb : ℝ≥0∞ :=
  ⨆ pk : B.PK,
    (PMF.uniformOfFintype (Fin n → B.KeyCoins)).toOuterMeasure {keys | ∃ i, B.pk (keys i) = pk}

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] in
/-- **A union bound over the users**: a fixed key is some user's key with probability at most `n`
times the largest probability that the key of uniform key coins is a fixed key. -/
theorem keyHitProb_le :
    keyHitProb B n ≤
      n * ⨆ pk : B.PK, (PMF.uniformOfFintype B.KeyCoins).toOuterMeasure {kc | B.pk kc = pk} := by
  refine iSup_le fun pk => ?_
  have hU : {keys : Fin n → B.KeyCoins | ∃ i, B.pk (keys i) = pk} =
      ⋃ i, {keys : Fin n → B.KeyCoins | B.pk (keys i) = pk} := by
    ext keys
    simp
  calc (PMF.uniformOfFintype (Fin n → B.KeyCoins)).toOuterMeasure
        {keys | ∃ i, B.pk (keys i) = pk}
      ≤ ∑' i : Fin n, (PMF.uniformOfFintype (Fin n → B.KeyCoins)).toOuterMeasure
          {keys | B.pk (keys i) = pk} := by
        rw [hU]
        exact MeasureTheory.measure_iUnion_le _
    _ = ∑' _i : Fin n, (PMF.uniformOfFintype B.KeyCoins).toOuterMeasure {kc | B.pk kc = pk} := by
        refine tsum_congr fun i => ?_
        rw [← PMF.uniformOfFintype_map_eval (C := B.KeyCoins) i, PMF.toOuterMeasure_map_apply]
        rfl
    _ ≤ ∑' _i : Fin n, ⨆ pk' : B.PK,
          (PMF.uniformOfFintype B.KeyCoins).toOuterMeasure {kc | B.pk kc = pk'} :=
        ENNReal.tsum_le_tsum fun _ => le_iSup (fun pk' : B.PK =>
          (PMF.uniformOfFintype B.KeyCoins).toOuterMeasure {kc | B.pk kc = pk'}) pk
    _ = _ := by
        rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

variable [NeZero n]

variable (O n V t) in
/-- **The adversaries that output a draw independent of their input**: on every start input,
`QueryBoundedAdversary.ofLaw` of one law `μ` on candidate forgeries. They make no query and no
request, and their output depends neither on the public keys nor on the oracle. -/
def constDrawAdversaries : Set (MUAdversary O n V t) :=
  {A | ∃ μ : PMF (B.PK × B.BMsg × B.BSig), ∀ inp,
    A inp = (QueryBoundedAdversary.ofLaw X Y (MURequest O n) (MUResponse B) μ).mono
      (Nat.zero_le t)}

/-- **A draw independent of the keys names a user's key with probability at most
`keyHitProb B n`**, in the run of the multi-user game with any number of requests. -/
theorem muLaw_keyHit_le {A : MUAdversary O n V t} (hA : A ∈ constDrawAdversaries O n V t)
    (Q : ℕ) :
    (muLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2, ∃ i, B.pk (x.1 i) = p.1.1} ≤ keyHitProb B n := by
  classical
  obtain ⟨μ, hμ⟩ := hA
  set E := {x : (Fin n → B.KeyCoins) × (X → Y) ×
    Option ((B.PK × B.BMsg × B.BSig) × MUHist O n) | ∃ p ∈ x.2.2, ∃ i, B.pk (x.1 i) = p.1.1}
  -- The run at the key coins `keys`: the oracle uniform, then the draw.
  have hlaw : ∀ (keys : Fin n → B.KeyCoins) (H : X → Y),
      ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw (muChallenger O n keys Q) H).map
        (fun o => (keys, H, o)) =
      μ.bind fun f => PMF.pure (keys, H, some (f, ([] : MUHist O n))) := by
    intro keys H
    have ht : (A (fun i => B.pk (keys i), V.view H)).transcriptLaw (muChallenger O n keys Q) H =
        μ.map fun o => some (o, []) := by
      rw [hμ]
      exact QueryBoundedAdversary.transcriptLaw_ofLaw _ _ _
    rw [ht, PMF.map_comp]
    rfl
  -- A fixed draw at fixed key coins wins for every oracle or for none.
  have hpt : ∀ (keys : Fin n → B.KeyCoins) (f : B.PK × B.BMsg × B.BSig),
      ((PMF.uniformOfFintype (X → Y)).bind fun H =>
        PMF.pure (keys, H, some (f, ([] : MUHist O n)))).toOuterMeasure E =
      if ∃ i, B.pk (keys i) = f.1 then 1 else 0 := by
    intro keys f
    split_ifs with h
    · refine (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun x hx => ?_
      obtain ⟨H, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
      rw [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨(f, []), rfl, h⟩
    · refine (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 fun x hx hE => ?_)
      obtain ⟨H, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
      rw [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      obtain ⟨p, hp, hi⟩ := hE
      cases hp
      exact h hi
  have hkeys : ∀ keys : Fin n → B.KeyCoins,
      ((PMF.uniformOfFintype (X → Y)).bind fun H =>
        ((A (fun i => B.pk (keys i), V.view H)).transcriptLaw (muChallenger O n keys Q) H).map
          fun o => (keys, H, o)).toOuterMeasure E =
      ∑' f, μ f * if ∃ i, B.pk (keys i) = f.1 then 1 else 0 := by
    intro keys
    simp only [hlaw]
    rw [PMF.bind_comm, PMF.toOuterMeasure_bind_apply]
    exact tsum_congr fun f => by rw [hpt]
  unfold muLaw runLaw
  rw [PMF.toOuterMeasure_bind_apply]
  simp only [hkeys]
  calc ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
        ∑' f, μ f * (if ∃ i, B.pk (keys i) = f.1 then 1 else 0)
      = ∑' f, μ f * ∑' keys, PMF.uniformOfFintype (Fin n → B.KeyCoins) keys *
          (if ∃ i, B.pk (keys i) = f.1 then 1 else 0) := by
        simp_rw [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        exact tsum_congr fun f => tsum_congr fun keys => by ring
    _ = ∑' f, μ f * (PMF.uniformOfFintype (Fin n → B.KeyCoins)).toOuterMeasure
          {keys | ∃ i, B.pk (keys i) = f.1} := by
        refine tsum_congr fun f => ?_
        rw [PMF.toOuterMeasure_apply]
        congr 1
        refine tsum_congr fun keys => ?_
        by_cases h : ∃ i, B.pk (keys i) = f.1 <;> simp [h]
    _ ≤ ∑' f, μ f * keyHitProb B n :=
        ENNReal.tsum_le_tsum fun f => by
          gcongr
          exact le_iSup (fun pk : B.PK => (PMF.uniformOfFintype (Fin n → B.KeyCoins)).toOuterMeasure
            {keys | ∃ i, B.pk (keys i) = pk}) f.1
    _ = keyHitProb B n := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **The key-independent draws are `keyHitProb B n`-hard in MU-EUF-CMA^corr.** -/
theorem muEufCmaHard_constDrawAdversaries (Q : ℕ) :
    MUEufCmaHard (constDrawAdversaries O n V t) Q (keyHitProb B n) :=
  fun A hA => by
    unfold muEufProb
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (muLaw_keyHit_le hA Q)
    rintro x ⟨⟨p, hp, hf⟩, -⟩
    obtain ⟨i, hi, -⟩ := hf.exists_user
    exact ⟨p, hp, i, hi⟩

/-- **The key-independent draws are `keyHitProb B n`-hard in MU-SUF-CMA^corr.** -/
theorem muSufCmaHard_constDrawAdversaries (Q : ℕ) :
    MUSufCmaHard (constDrawAdversaries O n V t) Q (keyHitProb B n) :=
  fun A hA => by
    unfold muSufProb
    refine le_trans (PMF.toOuterMeasure_mono _ ?_) (muLaw_keyHit_le hA Q)
    rintro x ⟨⟨p, hp, hf⟩, -⟩
    obtain ⟨i, hi, -⟩ := hf.exists_user
    exact ⟨p, hp, i, hi⟩

/-- **The key-independent draws are `keyHitProb B n`-hard in MU-EUF-NMA^corr.** -/
theorem muEufNmaHard_constDrawAdversaries (Q : ℕ) :
    MUEufNmaHard (constDrawAdversaries (SignOracle.none B) n V t) Q (keyHitProb B n) :=
  muEufCmaHard_constDrawAdversaries Q

variable (O n V t) in
/-- **The adversaries that output a draw from a distribution of the public keys**: on the public
keys `pks` and any table, `QueryBoundedAdversary.ofLaw` of `μ pks`, for one family `μ`. They make
no query and no request. When verification does not read the oracle, this class is not hard below
`1` (`not_muEufCmaHard_drawAdversaries`). -/
def drawAdversaries : Set (MUAdversary O n V t) :=
  {A | ∃ μ : (Fin n → B.PK) → PMF (B.PK × B.BMsg × B.BSig), ∀ inp,
    A inp = (QueryBoundedAdversary.ofLaw X Y (MURequest O n) (MUResponse B) (μ inp.1)).mono
      (Nat.zero_le t)}

end Draw

/-! ### The unrestricted class fails -/

section Brute

variable (B) in
/-- **Every key has a verifying signature at every oracle**: for every oracle and key-generation
coins, some base message and base signature verify under the key. -/
def Signable : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins), ∃ bm σ, B.bverify H (B.pk kc) bm σ = true

omit [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] in
/-- **Correct signing gives verifying signatures**: if the ordinary signer has correctness error
`εc` and refusal rate `ρ` with `εc + ρ < 1`, then at every oracle and key, every base message has a
verifying signature, so `Signable` holds when there is a base message. -/
theorem signable_of_correct [Nonempty B.BMsg] {εc ρ : ℝ≥0∞} (hc : B.StdCorrectWithin εc)
    (hr : B.StdRefuseWithin ρ) (h : εc + ρ < 1) : Signable B := by
  intro H kc
  obtain ⟨bm⟩ := ‹Nonempty B.BMsg›
  by_contra hne
  simp only [not_exists] at hne
  have hcov : (Set.univ : Set B.Coins) ⊆
      {c | ∃ σ, (B.ssign (B.sk kc) bm c).run H = some σ ∧ B.bverify H (B.pk kc) bm σ = false} ∪
        {c | (B.ssign (B.sk kc) bm c).run H = none} := by
    intro c _
    rcases hs : (B.ssign (B.sk kc) bm c).run H with _ | σ
    · exact Or.inr hs
    · exact Or.inl ⟨σ, hs, Bool.eq_false_iff.2 (hne bm σ)⟩
  have h1 : (1 : ℝ≥0∞) ≤ εc + ρ := by
    calc (1 : ℝ≥0∞) = (PMF.uniformOfFintype B.Coins).toOuterMeasure Set.univ :=
          ((PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)).symm
      _ ≤ _ := MeasureTheory.measure_mono hcov
      _ ≤ _ := MeasureTheory.measure_union_le _ _
      _ ≤ εc + ρ := add_le_add (hc H kc bm) (hr H kc bm)
  exact absurd h (not_lt.2 h1)

/-- **The brute-force output**: on the public keys `pks` and the oracle `H`, the key of user `i₀`
with a base message and a base signature that verify under it at `H`, if there are any. -/
noncomputable def bruteOut [Nonempty (B.BMsg × B.BSig)] (i₀ : Fin n)
    (inp : (Fin n → B.PK) × (X → Y)) : B.PK × B.BMsg × B.BSig :=
  (inp.1 i₀, Classical.epsilon fun p : B.BMsg × B.BSig => B.bverify inp.2 (inp.1 i₀) p.1 p.2 = true)

variable [NeZero n]

variable (O) in
/-- **The brute-force adversary with the oracle as a table**: it outputs `bruteOut i₀` of its start
input, with no query and no request. -/
noncomputable def bruteAdv [Nonempty (B.BMsg × B.BSig)] (i₀ : Fin n) (t : ℕ) :
    MUAdversary O n (OracleView.whole X Y) t := fun inp =>
  (QueryBoundedAdversary.ofLaw X Y (MURequest O n) (MUResponse B)
    (PMF.pure (bruteOut i₀ inp))).mono (Nat.zero_le t)

/-- **The brute-force adversary forges with probability `1`** when every key has a verifying
signature at every oracle (`Signable`). -/
theorem muEufProb_bruteAdv [Nonempty (B.BMsg × B.BSig)] (hs : Signable B) (i₀ : Fin n) (t Q : ℕ) :
    muEufProb (bruteAdv O i₀ t) Q = 1 := by
  refine le_antisymm (muEufProb_le_one _ Q) (le_of_eq ?_)
  symm
  unfold muEufProb muLaw runLaw
  refine (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun x hx => ?_
  obtain ⟨keys, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
  obtain ⟨H, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
  obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
  have ht : (bruteAdv O i₀ t (fun i => B.pk (keys i), (OracleView.whole X Y).view H)).transcriptLaw
      (muChallenger O n keys Q) H =
        (PMF.pure (bruteOut i₀ (fun i => B.pk (keys i), H))).map fun o => some (o, []) :=
    QueryBoundedAdversary.transcriptLaw_ofLaw _ _ _
  rw [ht, PMF.support_map, PMF.support_pure, Set.image_singleton, Set.mem_singleton_iff] at ho
  subst ho
  refine ⟨(bruteOut i₀ (fun i => B.pk (keys i), H), []), rfl, forges_nil ?_ ⟨i₀, rfl⟩⟩
  obtain ⟨bm, σ, hv⟩ := hs H (keys i₀)
  exact Classical.epsilon_spec (p := fun p : B.BMsg × B.BSig =>
    B.bverify H (B.pk (keys i₀)) p.1 p.2 = true) ⟨(bm, σ), hv⟩

/-- **With the oracle as a table, no bound below `1` holds for every adversary** of
MU-EUF-CMA^corr, when every key has a verifying signature at every oracle (`Signable`): the
brute-force adversary (`bruteAdv`), with no query and no request, wins with probability `1`. -/
theorem not_muEufCmaHard_univ_whole (hs : Signable B) {ε : ℝ≥0∞} (hε : ε < 1) (Q : ℕ) :
    ¬ MUEufCmaHard (Set.univ : Set (MUAdversary O n (OracleView.whole X Y) t)) Q ε := by
  intro h
  obtain ⟨bm, σ, -⟩ := hs (Classical.arbitrary _) (Classical.arbitrary _)
  have : Nonempty (B.BMsg × B.BSig) := ⟨(bm, σ)⟩
  have h1 := h _ (Set.mem_univ (bruteAdv O 0 t))
  rw [muEufProb_bruteAdv hs] at h1
  exact absurd hε (not_lt.2 h1)

/-- **The draw of a key-dependent forgery**: the key of user `i₀` with a base message and a base
signature that verify under it at a fixed oracle, if there are any. -/
noncomputable def drawOut [Nonempty (B.BMsg × B.BSig)] (i₀ : Fin n) (pks : Fin n → B.PK) :
    B.PK × B.BMsg × B.BSig :=
  (pks i₀, Classical.epsilon fun p : B.BMsg × B.BSig =>
    B.bverify (Classical.arbitrary (X → Y)) (pks i₀) p.1 p.2 = true)

variable (O) in
/-- **The drawing adversary that reads the public keys**: it outputs `drawOut i₀` of the public
keys, with no query and no request. -/
noncomputable def drawBruteAdv [Nonempty (B.BMsg × B.BSig)] (i₀ : Fin n) (V : OracleView X Y)
    (t : ℕ) : MUAdversary O n V t := fun inp =>
  (QueryBoundedAdversary.ofLaw X Y (MURequest O n) (MUResponse B)
    (PMF.pure (drawOut i₀ inp.1))).mono (Nat.zero_le t)

theorem drawBruteAdv_mem [Nonempty (B.BMsg × B.BSig)] (i₀ : Fin n) (V : OracleView X Y) (t : ℕ) :
    drawBruteAdv O i₀ V t ∈ drawAdversaries O n V t :=
  ⟨fun pks => PMF.pure (drawOut i₀ pks), fun _ => rfl⟩

/-- **The drawing adversary forges with probability `1`** when verification does not read the
oracle and every key has a verifying signature (`Signable`). -/
theorem muEufProb_drawBruteAdv [Nonempty (B.BMsg × B.BSig)]
    (hv : ∀ H H' : X → Y, B.bverify H = B.bverify H') (hs : Signable B) (i₀ : Fin n)
    (V : OracleView X Y) (t Q : ℕ) :
    muEufProb (drawBruteAdv O i₀ V t) Q = 1 := by
  refine le_antisymm (muEufProb_le_one _ Q) (le_of_eq ?_)
  symm
  unfold muEufProb muLaw runLaw
  refine (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun x hx => ?_
  obtain ⟨keys, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
  obtain ⟨H, -, hx⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
  obtain ⟨o, ho, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
  have ht : (drawBruteAdv O i₀ V t (fun i => B.pk (keys i), V.view H)).transcriptLaw
      (muChallenger O n keys Q) H =
        (PMF.pure (drawOut i₀ fun i => B.pk (keys i))).map fun o => some (o, []) :=
    QueryBoundedAdversary.transcriptLaw_ofLaw _ _ _
  rw [ht, PMF.support_map, PMF.support_pure, Set.image_singleton, Set.mem_singleton_iff] at ho
  subst ho
  refine ⟨(drawOut i₀ fun i => B.pk (keys i), []), rfl, forges_nil ?_ ⟨i₀, rfl⟩⟩
  obtain ⟨bm, σ, hvf⟩ := hs (Classical.arbitrary (X → Y)) (keys i₀)
  rw [hv H (Classical.arbitrary (X → Y))]
  exact Classical.epsilon_spec (p := fun p : B.BMsg × B.BSig =>
    B.bverify (Classical.arbitrary (X → Y)) (B.pk (keys i₀)) p.1 p.2 = true) ⟨(bm, σ), hvf⟩

/-- **When verification does not read the oracle, the drawing adversaries are not hard below `1`**
in MU-EUF-CMA^corr, for every view of the oracle: a draw that reads the public keys forges with
probability `1` (`muEufProb_drawBruteAdv`). The base signers of ML-DSA and Falcon-512 verify
without the oracle (their `bverify` ignores it). -/
theorem not_muEufCmaHard_drawAdversaries (hv : ∀ H H' : X → Y, B.bverify H = B.bverify H')
    (hs : Signable B) (V : OracleView X Y) {ε : ℝ≥0∞} (hε : ε < 1) (Q : ℕ) :
    ¬ MUEufCmaHard (drawAdversaries O n V t) Q ε := by
  intro h
  obtain ⟨bm, σ, -⟩ := hs (Classical.arbitrary _) (Classical.arbitrary _)
  have : Nonempty (B.BMsg × B.BSig) := ⟨(bm, σ)⟩
  have h1 := h _ (drawBruteAdv_mem 0 V t)
  rw [muEufProb_drawBruteAdv hv hs] at h1
  exact absurd hε (not_lt.2 h1)

/-- **When verification does not read the oracle, no bound below `1` holds for every adversary**
of MU-EUF-CMA^corr, for every view of the oracle, query access only included. -/
theorem not_muEufCmaHard_univ_of_bverify_eq (hv : ∀ H H' : X → Y, B.bverify H = B.bverify H')
    (hs : Signable B) (V : OracleView X Y) {ε : ℝ≥0∞} (hε : ε < 1) (Q : ℕ) :
    ¬ MUEufCmaHard (Set.univ : Set (MUAdversary O n V t)) Q ε := fun h =>
  not_muEufCmaHard_drawAdversaries hv hs V hε Q (h.anti (Set.subset_univ _))

end Brute

/-- **With the oracle as a table, no bound below `1` holds for every adversary of EUF-CMA**,
when every key has a verifying signature at every oracle (`not_muEufCmaHard_univ_whole` with one
user). -/
theorem not_suEufCmaHard_univ_whole (hs : Signable B) {ε : ℝ≥0∞} (hε : ε < 1) (Q : ℕ) :
    ¬ SUEufCmaHard (Set.univ : Set (SUAdversary O (OracleView.whole X Y) t)) Q ε :=
  not_muEufCmaHard_univ_whole hs hε Q


end GordieHowe.Signature
