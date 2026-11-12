-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Base
public import GordieHowe.Model.RingSignature.Completeness
public import GordieHowe.Foundations.ToMathlib.PMFTV

@[expose] public section

/-!
# Properties of a base signer: correctness, refusal, min-entropy, public values

The statistical properties of a `RingSignature.BaseSigner` (`GordieHowe/Model/RingSignature/Base.lean`)
that the ring-signature theorems take as hypotheses, each with an instance showing it can hold.

- `BaseScheme.pk`, `BaseScheme.sk`: the keys of key-generation coins of a base scheme.
- `BaseSigner.CorrectWithin B ε`: at every oracle, for every key-generation coins, every ring
  holding the key at position `i`, and every message, the ring-aware signer `bsign` at `i` outputs
  a base signature that fails base verification with probability at most `ε` over its coins.
  `BaseScheme.StdCorrectWithin B ε`: the same for the ordinary signer `ssign` on every base message.
- `BaseScheme.StdRefuseWithin B ρ`: the ordinary signer refuses (`none`) with probability at most
  `ρ` at every oracle, key and base message. `BaseSigner.honestRing`, `BaseScheme.RefusalDraw`: the
  ring of `r` honest users' keys and the draws of the refusal rate. `BaseSigner.refuseProb`,
  `BaseSigner.RefuseWithin`: the probability, over a uniform oracle, uniform key coins of `r`
  honest users and uniform signing coins, that the ring of their keys is supported and `bsign` of
  user `s` (at its key's first position, as `ofBase` signs) refuses; the refusal rate is at most
  `ρ` for every ring size, signer and message. `run_signAt_eq_none_iff`: signing of `ofBase` at a
  position refuses exactly when `bsign` does. `refuseProb_ofBase`, `refuseProb_ofBase_eq`: the
  refusal probability of the ring scheme `ofBase B PS adm` (`RingScheme.refuseProb`) is
  `refuseProb`.
- `BaseSigner.SigGivenPubLe B γ`: the conditional min-entropy of a base signature of `bsign` given
  its public value is at least `log₂ (1 / γ)`: every signature has conditional probability at most
  `γ` given its public value.
- `BaseSigner.SigGivenPubAvgLe B γ`: the average form (the average conditional min-entropy of
  Dodis–Ostrovsky–Reyzin–Smith): the best guess of a signature from its public value is right
  with probability at most `γ`. `SigGivenPubLe.sigGivenPubAvgLe` (the worst-case bound gives it),
  `sigGivenPubAvgLe_one`, `SigGivenPubAvgLe.mono`; `PMF.sum_toOuterMeasure_eq_some_le_one`.
- `BaseSigner.RefusalSound B refuses`, `RefusalOfCoins.refusalSound`, `refusalSound_false`: the
  ring-aware signer refuses whenever `refuses R i m c`.
- `BaseSigner.RefusalOfCoins B refuses`: the ring-aware signer refuses exactly when `refuses R i m c`
  holds, a predicate of the ring, the position, the message and the signing coins: refusal is decided
  without the secret key (`refuses = False` for a signer that never refuses an honest ring). The
  simulated ring signatures of the zero-knowledge reduction reproduce refusals this way.
- `BaseScheme.OracleFree C`: the scheme's `ssign` and `pub` make no oracle queries and base
  verification does not depend on the oracle. `BaseSigner.OracleFree B`: its scheme is oracle-free
  and `bsign` makes no oracle queries (`oracleFree_iff`, `oracleFree_ofCore`; the Falcon-512 and
  ML-DSA base signers: `falconBaseSigner_oracleFree`, `mldsaBaseSigner_oracleFree`,
  `GordieHowe/Applications/Ring/BaseSignerFacts.lean`).
  `OracleProg.run_eq_of_queriesLE_zero`: a program without queries has one result at every oracle;
  `OracleFree.run_bsign_eq`, `OracleFree.run_ssign_eq`, `OracleFree.run_pub_eq`,
  `OracleFree.ringRel_eq`: so the signers' outputs, the public values and the ring relation are the
  same at every oracle.
- `BaseSigner.PubOfCoins B pubOf`: the public value of every signature of `bsign` is `pubOf` of the
  signing coins (Falcon's salt, `falconBaseSigner_pubOfCoins`, for a signer carrying the salt;
  `Unit`, `pubOfCoins_unique`).
- Satisfiability: `correctWithin_one`, `stdCorrectWithin_one`, `stdRefuseWithin_one`,
  `refuseWithin_one`, `sigGivenPubLe_one` hold for every base signer; `pubOfCoins_unique` holds
  whenever the public values are a single value. `CorrectWithin.mono`, `SigGivenPubLe.mono`: the
  bounds hold at every larger value. `BaseSigner.uniformSig X Y N k`, the base
  signer whose signature is its uniform coin in `Fin (k + 1)` and whose verification accepts:
  `CorrectWithin 0`, `StdCorrectWithin 0`, `StdRefuseWithin 0`, `RefuseWithin adm 0`,
  `SigGivenPubLe (k + 1)⁻¹`, `PubOfCoins`, `RefusalOfCoins` and `OracleFree`
  (`uniformSig_correctWithin`, `uniformSig_stdCorrectWithin`, `uniformSig_stdRefuseWithin`,
  `uniformSig_refuseWithin`, `uniformSig_sigGivenPubLe`, `uniformSig_pubOfCoins`,
  `uniformSig_refusalOfCoins`,
  `uniformSig_oracleFree`), so every hypothesis here is satisfiable, and `γ` may be as small as
  the inverse of the number of signatures.

## Sources and deliberate differences

The definitions transcribe those of the interface `Ring.SigScheme`
(`GordieHowe/Applications/Ring/Scheme.lean`: `CorrectWithin`, `PubOfCoins`) to the ring-aware
signer. The differences:

1. **The signer reads the oracle, the ring and its position.** `bsign` is a classical oracle
   program; every property holds at every oracle `H` (the commitment hash and the check oracle
   of the ML-DSA ring publishing `w₁` are parts of the random oracle), for every ring holding the
   signer's key at the position. Correctness of an ordinary signature scheme (Goldwasser, Micali,
   Rivest, SIAM J. Comput. 17(2), 1988, section 2) requires verification of every honest
   signature; `CorrectWithin` bounds the failure probability instead (the bounded loops of FIPS 204
   and FIPS 206 can fail).
2. **Refusal is separate from rejection.** `bsign` and `ssign` may refuse; `CorrectWithin` counts
   only signatures that are output and rejected. The refusal of `ssign` is bounded at every input;
   the refusal of `bsign` depends on the ring (the ML-DSA ring publishing `w₁` refuses rings failing
   its public check), so its rate is averaged over honest rings, as the completeness game of
   `GordieHowe/Model/RingSignature/Completeness.lean` averages it.
3. **Min-entropy given the public value** (`SigGivenPubLe`) is the worst-case conditional
   min-entropy of the signature given its public value: the bound holds at every public value. For
   `Pub = Unit` it is the min-entropy of the signature.
-/

namespace GordieHowe.Signature.BaseScheme

open scoped ENNReal

/-! ### The keys and the ordinary signer's correctness and refusal bounds of a base scheme -/

variable {X Y : Type} {TB : SchemeTypes} (B : BaseScheme X Y TB)

/-- The public key generated from the coins `kc`. -/
def pk (kc : B.KeyCoins) : B.PK := (B.keyGen kc).pk

/-- The secret key generated from the coins `kc`. -/
def sk (kc : B.KeyCoins) : B.SK := (B.keyGen kc).sk

/-- The draws of the refusal rate with `r` members: the oracle, the members' key coins and the
signing coins. -/
abbrev RefusalDraw (r : ℕ) : Type := SigningDraw X Y (Fin r → B.KeyCoins) B.Coins

variable [Fintype TB.Coins] [Nonempty TB.Coins]

/-- **The correctness error of the ordinary signer is at most `ε`**: at every oracle, key and base
message, the ordinary signer `ssign` outputs a signature that fails base verification with
probability at most `ε` over uniform signing coins. -/
def StdCorrectWithin (ε : ℝ≥0∞) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (bm : B.BMsg), Pr[c ~ PMF.uniformOfFintype B.Coins :
    ∃ σ, (B.ssign (B.sk kc) bm c).run H = some σ ∧ B.bverify H (B.pk kc) bm σ = false] ≤ ε

/-- **The ordinary signer refuses with probability at most `ρ`** at every oracle, key and base
message, over uniform signing coins. -/
def StdRefuseWithin (ρ : ℝ≥0∞) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (bm : B.BMsg),
    Pr[c ~ PMF.uniformOfFintype B.Coins : (B.ssign (B.sk kc) bm c).run H = none] ≤ ρ

/-- Every ordinary signer has correctness error at most `1`. -/
theorem stdCorrectWithin_one : B.StdCorrectWithin 1 :=
  fun _ _ _ => PMF.toOuterMeasure_apply_le_one _ _

/-- Every ordinary signer refuses with probability at most `1`. -/
theorem stdRefuseWithin_one : B.StdRefuseWithin 1 :=
  fun _ _ _ => PMF.toOuterMeasure_apply_le_one _ _

/-- **An oracle-free base scheme**: the ordinary signer and the public value make no oracle
queries, and base verification is the same at every oracle. -/
structure OracleFree : Prop where
  /-- The ordinary signer makes no queries. -/
  ssign_noQuery : ∀ sk bm c, (B.ssign sk bm c).QueriesLE 0
  /-- The public value makes no queries. -/
  pub_noQuery : ∀ pk σ, (B.pub pk σ).QueriesLE 0
  /-- Base verification does not depend on the oracle. -/
  bverify_eq : ∀ H H', B.bverify H = B.bverify H'

end GordieHowe.Signature.BaseScheme

namespace GordieHowe.RingSignature

open scoped ENNReal

namespace BaseSigner

variable {X Y : Type} {N : ℕ} {T : Signature.SchemeTypes} {RMsg : Type}
  (B : BaseSigner X Y N T RMsg)

/-! ### Correctness and refusal -/

variable [Fintype T.Coins] [Nonempty T.Coins]

/-- **The correctness error of the ring-aware signer is at most `ε`**: at every oracle `H`, for
every key-generation coins `kc`, every ring `R` holding the public key of `kc` at position `i` and
every message `m`, over uniform signing coins, the probability that `bsign` outputs a base signature
on `bmsg R m` that fails base verification under the key is at most `ε`. Refusals are not
counted (`RefuseWithin`). -/
def CorrectWithin (ε : ℝ≥0∞) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (i : ℕ), R.HoldsAt i (B.pk kc) →
    ∀ m : B.Msg, Pr[c ~ PMF.uniformOfFintype B.Coins :
      ∃ σ, (B.bsign (B.sk kc) R i m c).run H = some σ ∧
        B.bverify H (B.pk kc) (B.bmsg R m) σ = false] ≤ ε

omit [Fintype T.Coins] [Nonempty T.Coins] in
/-- **The ring of `r` honest users** with key coins `keys`: their public keys in order. -/
def honestRing {r : ℕ} (hr : r ≤ N) (keys : Fin r → B.KeyCoins) : KeyRing B.PK N :=
  ⟨List.ofFn fun j => B.pk (keys j), by simpa using hr⟩

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

variable [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins]

/-- **The refusal probability of the ring-aware signer** for `r` members, signer `s` and message
`m` on the supported rings `adm`: over a uniform oracle, uniform key coins of the members and
uniform signing coins, the probability that the honest ring is supported and `bsign` of user `s`, at
the first position of its key (where `ofBase` signs), refuses. -/
noncomputable def refuseProb (adm : KeyRing B.PK N → Prop) {r : ℕ} (hr : r ≤ N) (s : Fin r)
    (m : B.Msg) : ℝ≥0∞ :=
  Pr[d ~ PMF.uniformOfFintype (B.RefusalDraw r) :
    adm (B.honestRing hr d.keys) ∧
      (B.bsign (B.sk (d.keys s)) (B.honestRing hr d.keys)
        ((B.honestRing hr d.keys).1.idxOf (B.pk (d.keys s))) m d.coins).run d.oracle = none]

/-- **The refusal rate of the ring-aware signer is at most `ρ`** on the supported rings `adm`: for
every ring size `r ≤ N`, signer and message, the refusal probability is at most `ρ`. -/
def RefuseWithin (adm : KeyRing B.PK N → Prop) (ρ : ℝ≥0∞) : Prop :=
  ∀ (r : ℕ) (hr : r ≤ N) (s : Fin r) (m : B.Msg), B.refuseProb adm hr s m ≤ ρ

/-! ### Public values -/

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [DecidableEq T.PK] [Fintype T.KeyCoins]
  [Nonempty T.KeyCoins]

/-- **A signature is guessed from its public value with probability at most `γ`**: at every oracle
`H`, for every key coins `kc`, ring `R` holding the key at position `i`, message `m`, public value
`y` and base signature `σ`, over uniform signing coins, the probability that `bsign` outputs `σ`
with public value `y` is at most `γ` times the probability that it outputs some signature with public
value `y`. That is, the conditional min-entropy of an honest signature given its public value is at
least `log₂ (1 / γ)`. -/
def SigGivenPubLe (γ : ℝ≥0∞) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (i : ℕ), R.HoldsAt i (B.pk kc) →
    ∀ (m : B.Msg) (y : B.Pub) (σ : B.BSig),
      Pr[c ~ PMF.uniformOfFintype B.Coins :
          (B.bsign (B.sk kc) R i m c).run H = some σ ∧ (B.pub (B.pk kc) σ).run H = y] ≤
        γ * Pr[c ~ PMF.uniformOfFintype B.Coins :
          ∃ σ', (B.bsign (B.sk kc) R i m c).run H = some σ' ∧ (B.pub (B.pk kc) σ').run H = y]

omit [Fintype T.Coins] [Nonempty T.Coins] in
/-- **The public value of an honest signature is a function of the signing coins**: at every
oracle, for every key coins, ring holding the key at position `i`, message and coins `c`, every
signature `bsign` outputs has public value `pubOf c`. For Falcon `pubOf` reads the salt off the
coins (`falconBaseSigner_pubOfCoins`, for a signer carrying the salt); for `Pub = Unit` it holds
for every base signer (`pubOfCoins_unique`). -/
def PubOfCoins (pubOf : B.Coins → B.Pub) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (i : ℕ), R.HoldsAt i (B.pk kc) →
    ∀ (m : B.Msg) (c : B.Coins) (σ : B.BSig), (B.bsign (B.sk kc) R i m c).run H = some σ →
      (B.pub (B.pk kc) σ).run H = pubOf c

omit [Fintype T.Coins] [Nonempty T.Coins] in
/-- **The refusals of the ring-aware signer are decided without the secret key**: at every oracle,
for every key coins, ring holding the key at position `i`, message and coins `c`, `bsign` refuses
exactly when `refuses R i m c`. -/
def RefusalOfCoins (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (i : ℕ), R.HoldsAt i (B.pk kc) →
    ∀ (m : B.Msg) (c : B.Coins), (B.bsign (B.sk kc) R i m c).run H = none ↔ refuses R i m c

/-- **A decision of a refusal predicate** at every ring, position, message and coins: the
`DecidablePred` of a four-argument predicate. A binder of this type is a local instance: it unfolds
reducibly to a `Decidable` family. -/
abbrev DecidableRefusal (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) : Type :=
  ∀ R i m c, Decidable (refuses R i m c)

omit [Fintype T.Coins] [Nonempty T.Coins] in
/-- **The predicted refusals are refusals of the ring-aware signer**: at every oracle, for every key
coins, ring holding the key at position `i`, message and coins `c` with `refuses R i m c`, `bsign`
refuses. It holds for the empty predicate (`refusalSound_false`) and under `RefusalOfCoins`
(`RefusalOfCoins.refusalSound`); the refusals it misses are counted separately. -/
def RefusalSound (refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (i : ℕ), R.HoldsAt i (B.pk kc) →
    ∀ (m : B.Msg) (c : B.Coins), refuses R i m c → (B.bsign (B.sk kc) R i m c).run H = none

omit [Fintype T.Coins] [Nonempty T.Coins] in
/-- **Refusals decided by the coins are sound.** -/
theorem RefusalOfCoins.refusalSound {refuses : KeyRing B.PK N → ℕ → B.Msg → B.Coins → Prop}
    (h : B.RefusalOfCoins refuses) : B.RefusalSound refuses :=
  fun H kc R i hi m c hr => (h H kc R i hi m c).2 hr

omit [Fintype T.Coins] [Nonempty T.Coins] in
/-- **Predicting no refusal is sound.** -/
theorem refusalSound_false : B.RefusalSound fun _ _ _ _ => False :=
  fun _ _ _ _ _ _ _ h => h.elim

/-! ### Satisfiability -/

/-- Every base signer has correctness error at most `1`. -/
theorem correctWithin_one : B.CorrectWithin 1 :=
  fun _ _ _ _ _ _ => PMF.toOuterMeasure_apply_le_one _ _

/-- **Every base signer satisfies `SigGivenPubLe 1`**: the event of one signature is contained in
the event of its public value. -/
theorem sigGivenPubLe_one : B.SigGivenPubLe 1 := by
  intro H kc R i _ m y σ
  rw [one_mul]
  refine PMF.toOuterMeasure_mono _ ?_
  intro c hc
  exact ⟨σ, hc.1⟩

omit [Fintype T.Coins] [Nonempty T.Coins] in
/-- **With a single public value every base signer has public values from its coins.** -/
theorem pubOfCoins_unique [Unique B.Pub] : B.PubOfCoins fun _ => default :=
  fun _ _ _ _ _ _ _ _ _ => Subsingleton.elim _ _

/-- Correctness at error `ε` gives correctness at every larger error. -/
theorem CorrectWithin.mono {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.Coins]
    [Nonempty T.Coins]
    {B : BaseSigner X Y N T RMsg} {ε ε' : ℝ≥0∞} (h : B.CorrectWithin ε)
    (hε : ε ≤ ε') : B.CorrectWithin ε' :=
  fun H kc R i hi m => (h H kc R i hi m).trans hε

/-- `SigGivenPubLe` at `γ` gives it at every larger `γ`. -/
theorem SigGivenPubLe.mono {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.Coins]
    [Nonempty T.Coins]
    {B : BaseSigner X Y N T RMsg} {γ γ' : ℝ≥0∞} (h : B.SigGivenPubLe γ)
    (hγ : γ ≤ γ') : B.SigGivenPubLe γ' :=
  fun H kc R i hi m y σ => (h H kc R i hi m y σ).trans (mul_le_mul_left hγ _)

/-- **A signature is guessed from its public value with probability at most `γ` on average**: at
every oracle `H`, for every key coins `kc`, ring `R` holding the key at position `i` and message
`m`, over uniform signing coins, the sum over the public values `y` of the largest probability that
`bsign` outputs one signature `σ` with public value `y` is at most `γ`. This is the probability
that the best guess of the signature from its public value is right, `2^(-H̃∞(σ | y))` for the
average conditional min-entropy `H̃∞` of Dodis, Ostrovsky, Reyzin, Smith, "Fuzzy Extractors",
SIAM J. Comput. 38(1), 2008, section 2.4, with a refusal counted as no signature. -/
def SigGivenPubAvgLe [Fintype T.Pub] (γ : ℝ≥0∞) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (i : ℕ), R.HoldsAt i (B.pk kc) →
    ∀ m : B.Msg, ∑ y : B.Pub, ⨆ σ : B.BSig,
      Pr[c ~ PMF.uniformOfFintype B.Coins :
          (B.bsign (B.sk kc) R i m c).run H = some σ ∧ (B.pub (B.pk kc) σ).run H = y] ≤ γ

/-- **The events of an optional value equal to each value have total probability at most `1`.** -/
theorem _root_.PMF.sum_toOuterMeasure_eq_some_le_one {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (μ : PMF α) (F : α → Option β) :
    ∑ y : β, μ.toOuterMeasure {c | F c = some y} ≤ 1 := by
  classical
  simp only [PMF.toOuterMeasure_apply_fintype, Set.indicator_apply, Set.mem_ofPred_eq]
  rw [Finset.sum_comm]
  calc ∑ c : α, ∑ y : β, (if F c = some y then μ c else 0) ≤ ∑ c : α, μ c := by
        refine Finset.sum_le_sum fun c _ => ?_
        rcases F c with _ | y₀
        · simp
        · simp [Finset.sum_ite_eq]
    _ = 1 := by rw [← tsum_fintype (L := SummationFilter.unconditional α), PMF.tsum_coe]

/-- **The worst-case bound gives the average bound**: `SigGivenPubLe γ` gives
`SigGivenPubAvgLe γ`. -/
theorem SigGivenPubLe.sigGivenPubAvgLe {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.Coins]
    [Nonempty T.Coins]
    [Fintype T.Pub] {B : BaseSigner X Y N T RMsg} {γ : ℝ≥0∞} (h : B.SigGivenPubLe γ) :
    B.SigGivenPubAvgLe γ := by
  classical
  intro H kc R i hi m
  have hset : ∀ y : B.Pub, (Set.ofPred fun c : B.Coins =>
      ∃ σ', (B.bsign (B.sk kc) R i m c).run H = some σ' ∧ (B.pub (B.pk kc) σ').run H = y) =
      {c | ((B.bsign (B.sk kc) R i m c).run H).map (fun σ' => (B.pub (B.pk kc) σ').run H) =
        some y} := by
    intro y
    ext c
    simp [Set.ofPred]
  calc ∑ y : B.Pub, ⨆ σ : B.BSig, Pr[c ~ PMF.uniformOfFintype B.Coins :
          (B.bsign (B.sk kc) R i m c).run H = some σ ∧ (B.pub (B.pk kc) σ).run H = y]
      ≤ ∑ y : B.Pub, γ * Pr[c ~ PMF.uniformOfFintype B.Coins :
          ∃ σ', (B.bsign (B.sk kc) R i m c).run H = some σ' ∧ (B.pub (B.pk kc) σ').run H = y] :=
        Finset.sum_le_sum fun y _ => iSup_le fun σ => h H kc R i hi m y σ
    _ = γ * ∑ y : B.Pub, Pr[c ~ PMF.uniformOfFintype B.Coins :
          ∃ σ', (B.bsign (B.sk kc) R i m c).run H = some σ' ∧ (B.pub (B.pk kc) σ').run H = y] :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ γ * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ zero_le
        simp only [hset]
        exact PMF.sum_toOuterMeasure_eq_some_le_one _ _
    _ = γ := mul_one γ

/-- **Every base signer has average guessing probability at most `1`.** -/
theorem sigGivenPubAvgLe_one [Fintype T.Pub] : B.SigGivenPubAvgLe 1 :=
  (sigGivenPubLe_one B).sigGivenPubAvgLe

/-- `SigGivenPubAvgLe` at `γ` gives it at every larger `γ`. -/
theorem SigGivenPubAvgLe.mono {T : Signature.SchemeTypes} {RMsg : Type} [Fintype T.Coins]
    [Nonempty T.Coins]
    [Fintype T.Pub]     {B : BaseSigner X Y N T RMsg} {γ γ' : ℝ≥0∞} (h : B.SigGivenPubAvgLe γ)
    (hγ : γ ≤ γ') : B.SigGivenPubAvgLe γ' :=
  fun H kc R i hi m => (h H kc R i hi m).trans hγ

section Refusal

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

variable [DecidableEq T.PK] [Fintype T.KeyCoins] [Nonempty T.KeyCoins]

/-- Every ring-aware signer has refusal rate at most `1`. -/
theorem refuseWithin_one (adm : KeyRing B.PK N → Prop) : B.RefuseWithin adm 1 :=
  fun _ _ _ _ => PMF.toOuterMeasure_apply_le_one _ _

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype T.KeyCoins]
  [Nonempty T.KeyCoins] [Fintype T.Coins] [Nonempty T.Coins] [DecidableEq T.PK] in
/-- **Signing of `ofBase` at a position refuses exactly when the base signer does.** -/
theorem run_signAt_eq_none_iff {TPS : PSTypes} (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS) {H : X → Y}
    {pk : B.PK} {sk : B.SK} {R : KeyRing B.PK N} {i : ℕ} {m : B.Msg} {c : B.Coins × PS.Coins} :
    (signAt B PS pk sk R i m c).run H = none ↔ (B.bsign sk R i m c.1).run H = none := by
  rcases h : (B.bsign sk R i m c.1).run H with _ | σ
  · simp only [signAt_eq, OracleProg.run_bind, h, OracleProg.run_pure]
  · rw [run_signAt_of_bsign B PS h]
    simp

/-- **The refusal rate of `ofBase` is that of its base signer**: the ring scheme refuses an honest
supported ring exactly when the base signer does, at the signer's first position. -/
theorem refuseProb_ofBase {TPS : PSTypes} [Fintype TPS.Coins] [Nonempty TPS.Coins]
    (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS)
    (adm : KeyRing B.PK N → Prop) [DecidablePred adm] {r : ℕ} (hr : r ≤ N) (s : Fin r)
    (m : B.Msg) :
    (ofBase B PS adm).refuseProb hr s m =
      Pr[d ~ PMF.uniformOfFintype ((X → Y) × (Fin r → B.KeyCoins) × (B.Coins × PS.Coins)) :
        adm (B.honestRing hr d.2.1) ∧
          (B.bsign (B.sk (d.2.1 s)) (B.honestRing hr d.2.1)
            ((B.honestRing hr d.2.1).1.idxOf (B.pk (d.2.1 s))) m d.2.2.1).run d.1 = none] := by
  unfold RingScheme.refuseProb
  congr 1
  ext d
  simp only [Set.mem_ofPred_eq]
  have hmem : (ofBase B PS adm).pk (d.2.1 s) ∈ ((ofBase B PS adm).honestRing hr d.2.1).1 :=
    RingScheme.pk_mem_honestRing _ hr d.2.1 s
  constructor
  · rintro ⟨ha, hn⟩
    refine ⟨ha, ?_⟩
    erw [sign_ofBase_of_mem B PS adm hmem ha] at hn
    exact (run_signAt_eq_none_iff B PS).1 hn
  · rintro ⟨ha, hn⟩
    refine ⟨ha, ?_⟩
    erw [sign_ofBase_of_mem B PS adm hmem ha]
    exact (run_signAt_eq_none_iff B PS).2 hn

/-- **The refusal rate of `ofBase` is that of its base signer** (`refuseProb_ofBase`), with the
prover's coins averaged out: the event reads only the base part of the signing coins. -/
theorem refuseProb_ofBase_eq {TPS : PSTypes} [Fintype TPS.Coins] [Nonempty TPS.Coins]
    (PS : ProofSystem X Y (RingStmt B) (RingWit B) TPS)
    (adm : KeyRing B.PK N → Prop) [DecidablePred adm] {r : ℕ} (hr : r ≤ N) (s : Fin r)
    (m : B.Msg) :
    (ofBase B PS adm).refuseProb hr s m = B.refuseProb adm hr s m := by
  classical
  have key : ∀ P : B.RefusalDraw r → Prop,
      Pr[d ~ PMF.uniformOfFintype ((X → Y) × (Fin r → B.KeyCoins) × (B.Coins × PS.Coins)) :
        P (d.1, d.2.1, d.2.2.1)] = Pr[d ~ PMF.uniformOfFintype (B.RefusalDraw r) : P d] := by
    intro P
    rw [PMF.toOuterMeasure_uniformOfFintype_apply, PMF.toOuterMeasure_uniformOfFintype_apply]
    have hc : Fintype.card (Set.ofPred fun d : (X → Y) × (Fin r → B.KeyCoins) ×
        (B.Coins × PS.Coins) => P (d.1, d.2.1, d.2.2.1)) =
        Fintype.card (Set.ofPred P) * Fintype.card PS.Coins := by
      rw [← Fintype.card_prod]
      exact Fintype.card_congr
        { toFun := fun d => (⟨(d.1.1, d.1.2.1, d.1.2.2.1), d.2⟩, d.1.2.2.2)
          invFun := fun p => ⟨(p.1.1.1, p.1.1.2.1, (p.1.1.2.2, p.2)), p.1.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [hc]
    simp only [Signature.BaseScheme.RefusalDraw, Fintype.card_prod, Nat.cast_mul]
    have h0 : (Fintype.card PS.Coins : ℝ≥0∞) ≠ 0 := by simp
    have h1 : (Fintype.card PS.Coins : ℝ≥0∞) ≠ ⊤ := by simp
    rw [show (Fintype.card (X → Y) : ℝ≥0∞) * ((Fintype.card (Fin r → B.KeyCoins) : ℝ≥0∞) *
        ((Fintype.card B.Coins : ℝ≥0∞) * (Fintype.card PS.Coins : ℝ≥0∞))) =
        (Fintype.card (X → Y) : ℝ≥0∞) * ((Fintype.card (Fin r → B.KeyCoins) : ℝ≥0∞) *
          (Fintype.card B.Coins : ℝ≥0∞)) * (Fintype.card PS.Coins : ℝ≥0∞) by ring]
    exact ENNReal.mul_div_mul_right _ _ h0 h1
  rw [refuseProb_ofBase B PS adm hr s m, refuseProb]
  exact key fun d => adm (B.honestRing hr d.2.1) ∧
    (B.bsign (B.sk (d.2.1 s)) (B.honestRing hr d.2.1)
      ((B.honestRing hr d.2.1).1.idxOf (B.pk (d.2.1 s))) m d.2.2).run d.1 = none

end Refusal

/-! ### Oracle-free base signers -/

omit [Fintype T.Coins] [Nonempty T.Coins]

/-- **A program without queries has one result at every oracle.** -/
theorem _root_.GordieHowe.OracleProg.run_eq_of_queriesLE_zero {A B R : Type*} {p : OracleProg A B R}
    (hp : p.QueriesLE 0) (h h' : A → B) : p.run h = p.run h' :=
  OracleProg.run_congr p fun a ha => absurd (List.length_pos_of_mem ha) (by have := hp h; omega)

/-- **An oracle-free base signer**: its scheme is oracle-free (`BaseScheme.OracleFree`: the
ordinary signer and the public value make no oracle queries, and base verification is the same at
every oracle), and the ring-aware signer makes no oracle queries. The Falcon-512 and ML-DSA base
signers are oracle-free (`falconBaseSigner_oracleFree`, `mldsaBaseSigner_oracleFree`). -/
structure OracleFree {T : Signature.SchemeTypes} {RMsg : Type} (B : BaseSigner X Y N T RMsg) : Prop
    extends core : B.core.OracleFree where
  /-- The ring-aware signer makes no queries. -/
  bsign_noQuery : ∀ sk R i m c, (B.bsign sk R i m c).QueriesLE 0

/-- **Oracle-freeness of a base signer is that of its scheme and of the ring-aware signer.** -/
theorem oracleFree_iff {T : Signature.SchemeTypes} {RMsg : Type} (B : BaseSigner X Y N T RMsg) :
    B.OracleFree ↔ B.core.OracleFree ∧ ∀ sk R i m c, (B.bsign sk R i m c).QueriesLE 0 :=
  ⟨fun h => ⟨h.core, h.bsign_noQuery⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **A base signer built from an oracle-free scheme is oracle-free** (`ofCore` signs with the
scheme's `ssign`). -/
theorem oracleFree_ofCore {S : Signature.SchemeTypes} {C : Signature.BaseScheme X Y S}
    (hC : C.OracleFree) {RMsg : Type} (bmsg : KeyRing S.PK N → RMsg → S.BMsg) :
    (ofCore C bmsg).OracleFree :=
  ⟨hC, fun sk R _ m c => hC.ssign_noQuery sk (bmsg R m) c⟩

namespace OracleFree

variable {B} (hB : B.OracleFree)
include hB

/-- The ring-aware signer has one output at every oracle. -/
theorem run_bsign_eq (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg) (c : B.Coins)
    (H H' : X → Y) : (B.bsign sk R i m c).run H = (B.bsign sk R i m c).run H' :=
  OracleProg.run_eq_of_queriesLE_zero (hB.bsign_noQuery sk R i m c) H H'

/-- The ordinary signer has one output at every oracle. -/
theorem run_ssign_eq (sk : B.SK) (bm : B.BMsg) (c : B.Coins) (H H' : X → Y) :
    (B.ssign sk bm c).run H = (B.ssign sk bm c).run H' :=
  OracleProg.run_eq_of_queriesLE_zero (hB.ssign_noQuery sk bm c) H H'

/-- The public value is the same at every oracle. -/
theorem run_pub_eq (pk : B.PK) (σ : B.BSig) (H H' : X → Y) :
    (B.pub pk σ).run H = (B.pub pk σ).run H' :=
  OracleProg.run_eq_of_queriesLE_zero (hB.pub_noQuery pk σ) H H'

/-- **The ring relation of an oracle-free base signer is the same at every oracle.** -/
theorem ringRel_eq (adm : KeyRing B.PK N → Prop) (H H' : X → Y) :
    ringRel B adm H = ringRel B adm H' := by
  ext ⟨x, w⟩
  constructor
  · rintro ⟨ha, hi, hv, hp⟩
    exact ⟨ha, hi, by rw [← hB.bverify_eq H H']; exact hv, by rw [← hB.run_pub_eq _ _ H H']; exact hp⟩
  · rintro ⟨ha, hi, hv, hp⟩
    exact ⟨ha, hi, by rw [hB.bverify_eq H H']; exact hv, by rw [hB.run_pub_eq _ _ H H']; exact hp⟩

end OracleFree

/-! ### A base signer meeting every hypothesis -/

/-- The types of `uniformSig k`: one key, one message and one public value; signatures and signing
coins in `Fin (k + 1)`. -/
abbrev uniformSigT (k : ℕ) : _root_.GordieHowe.Signature.SchemeTypes where
  PK := Unit
  SK := Unit
  KeyCoins := Unit
  BMsg := Unit
  BSig := Fin (k + 1)
  Pub := Unit
  Coins := Fin (k + 1)

variable (X Y N) in
/-- **The base signer with uniform signatures** in `Fin (k + 1)`: one key, one message, one public
value; the ring-aware and the ordinary signer output their coin as the signature, and verification
accepts. It satisfies every hypothesis of this file (`CorrectWithin 0`, `StdCorrectWithin 0`,
`StdRefuseWithin 0`, `RefuseWithin adm 0`, `SigGivenPubLe (k + 1)⁻¹`, `PubOfCoins`,
`OracleFree`). -/
def uniformSig (k : ℕ) : BaseSigner X Y N (uniformSigT k) Unit where
  keyGen _ := ((), ())
  bmsg _ _ := ()
  q := 0
  bsign _ _ _ _ c := .pure (some c)
  bsign_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _
  ssign _ _ c := .pure (some c)
  ssign_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  bverify _ _ _ _ := true
  qPub := 0
  pub _ _ := .pure ()
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

/-- The uniform-signature base signer has correctness error `0`. -/
theorem uniformSig_correctWithin (k : ℕ) : (uniformSig X Y N k).CorrectWithin 0 := by
  intro H kc R i _ m
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  obtain ⟨σ, -, hv⟩ := hc
  exact Bool.noConfusion hv

/-- The uniform-signature base signer's ordinary signer has correctness error `0`. -/
theorem uniformSig_stdCorrectWithin (k : ℕ) : (uniformSig X Y N k).StdCorrectWithin 0 := by
  intro H kc bm
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  obtain ⟨σ, -, hv⟩ := hc
  exact Bool.noConfusion hv

/-- The uniform-signature base signer's ordinary signer never refuses. -/
theorem uniformSig_stdRefuseWithin (k : ℕ) : (uniformSig X Y N k).StdRefuseWithin 0 := by
  intro H kc bm
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun c _ hc => ?_
  have h : (some c : Option (Fin (k + 1))) = none := hc
  exact Option.some_ne_none _ h

/-- **A signature of the uniform-signature base signer is guessed with probability
`(k + 1)⁻¹`**: `SigGivenPubLe` holds at the inverse of the number of signatures. -/
theorem uniformSig_sigGivenPubLe (k : ℕ) :
    (uniformSig X Y N k).SigGivenPubLe ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  intro H kc R i _ m y σ
  cases y
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin (k + 1), τ = σ := ⟨σ, rfl⟩
  subst hτ
  have h1 : Pr[c ~ PMF.uniformOfFintype (Fin (k + 1)) :
      (some c : Option (Fin (k + 1))) = some τ ∧ () = ()] =
        ((k + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
    have hs : (Set.ofPred fun c : Fin (k + 1) =>
        (some c : Option (Fin (k + 1))) = some τ ∧ () = ()) =
          ({τ} : Set (Fin (k + 1))) := by
      ext c
      simp
    rw [hs, PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_fin]
  have h2 : Pr[c ~ PMF.uniformOfFintype (Fin (k + 1)) :
      ∃ σ' : Fin (k + 1), (some c : Option (Fin (k + 1))) = some σ' ∧ () = ()] = 1 := by
    have hs : (Set.ofPred fun c : Fin (k + 1) =>
        ∃ σ' : Fin (k + 1), (some c : Option (Fin (k + 1))) = some σ' ∧ () = ()) = Set.univ := by
      ext c
      simp
    rw [hs]
    exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 (Set.subset_univ _)
  change Pr[c ~ PMF.uniformOfFintype (Fin (k + 1)) :
      (some c : Option (Fin (k + 1))) = some τ ∧ () = ()] ≤
    _ * Pr[c ~ PMF.uniformOfFintype (Fin (k + 1)) :
      ∃ σ' : Fin (k + 1), (some c : Option (Fin (k + 1))) = some σ' ∧ () = ()]
  rw [h1, h2, mul_one]

/-- The uniform-signature base signer's public values are a function of its coins. -/
theorem uniformSig_pubOfCoins (k : ℕ) : (uniformSig X Y N k).PubOfCoins fun _ => () :=
  fun _ _ _ _ _ _ _ _ _ => rfl

/-- The uniform-signature base signer never refuses: `RefusalOfCoins` holds with `False`. -/
theorem uniformSig_refusalOfCoins (k : ℕ) :
    (uniformSig X Y N k).RefusalOfCoins fun _ _ _ _ => False :=
  fun _ _ _ _ _ _ c => iff_of_false (Option.some_ne_none c) id

/-- The uniform-signature base signer is oracle-free: `OracleFree` is satisfiable. -/
theorem uniformSig_oracleFree (k : ℕ) : (uniformSig X Y N k).OracleFree where
  bsign_noQuery _ _ _ _ _ := OracleProg.QueriesLE.pure _ _
  ssign_noQuery _ _ _ := OracleProg.QueriesLE.pure _ _
  pub_noQuery _ _ := OracleProg.QueriesLE.pure _ _
  bverify_eq _ _ := rfl

/-- The uniform-signature base signer never refuses an honest ring. -/
theorem uniformSig_refuseWithin [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (k : ℕ)
    (adm : KeyRing Unit N → Prop) : (uniformSig X Y N k).RefuseWithin adm 0 := by
  intro r hr s m
  refine le_of_eq ((PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 ?_)
  refine Set.disjoint_left.2 fun d _ hd => ?_
  have h : (some d.2.2 : Option (Fin (k + 1))) = none := hd.2
  exact Option.some_ne_none _ h

end BaseSigner

end GordieHowe.RingSignature
