-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Scheme
public import GordieHowe.SPBCS.WitnessIndist
public import GordieHowe.Headline

@[expose] public section

/-!
# Anonymity of the ring signature: statistical, from unconditional witness indistinguishability

Two anonymity games for the ring signature of `GordieHowe/Applications/Ring/Scheme.lean` compiled by spBCS
(`GordieHowe/SPBCS/Basic.lean`; the ring signature on `(R, m, ρ)` with witness `(i, σ)` is
the compiled honest proof `GordieHowe.SPBCS.proofLaw`, `GordieHowe/SPBCS/WitnessIndist.lean`), both against
adversaries that see the whole random oracle and are not computationally bounded, before or
after the challenges, with `Q` adaptive challenges:

- `anonAdvantage`, adversary-supplied signatures (`AnonAdversary`): in each round the
  adversary chooses a ring `R` of arbitrary keys, a ring message `m`, a public value `ρ`, and two
  witnesses `(i₀, σ₀)`, `(i₁, σ₁)` valid for `(R, m, ρ)`; it receives the ring signature computed
  from `(i_b, σ_b)`. Nothing about the keys is assumed beyond the validity of both witnesses: the
  two keys may be adversarially generated, and the signatures may be any valid signatures (for
  example existing signatures converted into ring signatures). Both witnesses share the
  statement, so for Falcon they share the salt `ρ` (the salt is public: two signatures with
  different salts give different statements, and the salt would reveal `b`).
  `anon_suppliedSignatures`: advantage at most `Q · wiError δ C`.
- `keyedAnonAdvantage`, challenger-signed (`KeyedAnonAdversary`): BKM06 Definition 4 (anonymity
  against full key exposure) with the ring's other members adversarial and `Q` adaptive challenges:
  `n` honest keys from uniform key-generation coins, all of which the adversary receives at the
  start; in each round it chooses a ring of arbitrary keys containing the keys of two honest users
  `u₀`, `u₁`, and a message; the challenger draws a fresh salt and coins and returns the ring
  signature by `u_b`. A round with `u₀ = u₁` is a signing query. `keyedAnon_le`: advantage at most
  `Q · wiError δ C`, by `anon_suppliedSignatures` at the signatures the challenger would compute,
  averaged over the keys and the signing coins.

## Sources

BKM06 (Bender, Katz, Morselli, TCC 2006, LNCS pp. 60–79; ePrint 2005/304) Definition 4, anonymity
against full key exposure: the adversary receives the randomness used to generate all honest keys,
may query a signing oracle on rings containing adversarial keys, outputs `(M, i₀, i₁, R)` and
guesses the bit of `Sign_{i_b}(M, R)`. The keys are given at the start, as in CCLM22 (Chatterjee,
Chung, Liang, Malavolta, PKC 2022, ePrint 2021/1616) Experiment 2 (p. 21) and BKP20 (ePrint
2020/646, p. 7), stronger than BKM06's timing. The adversaries here are those of the
witness-indistinguishability theorem of spBCS
(`SPBCS.wiAdvantage_le`; CY24 Definition 33.1.1, p. 426, at unbounded queries): each
choice is a function of the whole oracle and the earlier signatures, and the distinguisher a
predicate of the whole oracle and all signatures. A randomized or quantum adversary with classical
challenges is a mixture of such adversaries, a decomposition not formalized here.
-/

namespace GordieHowe.Ring

open IOP GordieHowe.SPBCS GordieHowe.SPBCS GordieHowe.QROM
open scoped NNReal ENNReal

variable {Sch : SigScheme} {RMsg : Type} {N : ℕ}

/-! ### Adversary-supplied signatures -/

/-- **A challenge with adversary-supplied signatures**: a ring, a ring message, a public value
and two witnesses (a position and a base signature each). -/
structure AnonChoice (Sch : SigScheme) (RMsg : Type) (N : ℕ) where
  /-- The ring. -/
  ring : RingOf Sch.PK N
  /-- The ring message. -/
  msg : RMsg
  /-- The public value of both signatures (Falcon's salt). -/
  pub : Sch.Pub
  /-- The witness answered when `b = 0`. -/
  wit₀ : RingWit Sch
  /-- The witness answered when `b = 1`. -/
  wit₁ : RingWit Sch
deriving DecidableEq

namespace AnonChoice

/-- The statement of a challenge. -/
def stmt (c : AnonChoice Sch RMsg N) : RingStmt Sch RMsg N := ⟨c.ring, c.msg, c.pub⟩

/-- **A valid challenge**: the ring is admissible (`adm`) and both witnesses are witnesses of the
ring relation for the statement. -/
structure Valid (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg)
    (c : AnonChoice Sch RMsg N) : Prop where
  /-- The ring is admissible. -/
  adm : adm c.ring.1
  /-- The first witness is valid. -/
  wit₀ : RingRel bind c.stmt c.wit₀
  /-- The second witness is valid. -/
  wit₁ : RingRel bind c.stmt c.wit₁

/-- The challenge as a choice of the witness-indistinguishability game. -/
def toWIChoice (c : AnonChoice Sch RMsg N) :
    SPBCS.WIChoice (RingStmt Sch RMsg N) (RingWit Sch) :=
  ⟨c.stmt, c.wit₀, c.wit₁⟩

theorem toWIChoice_injective :
    Function.Injective (toWIChoice : AnonChoice Sch RMsg N → _) := by
  rintro ⟨R, m, ρ, w₀, w₁⟩ ⟨R', m', ρ', w₀', w₁'⟩ h
  simp only [toWIChoice, stmt, SPBCS.WIChoice.mk.injEq, RingStmt.mk.injEq] at h
  obtain ⟨⟨rfl, rfl, rfl⟩, rfl, rfl⟩ := h
  rfl

end AnonChoice

variable {k kN kS L e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] (M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e)

/-- **An anonymity adversary with adversary-supplied signatures**, with `Q` challenges: a finite
set of valid challenges and, in round `j`, a challenge from it chosen as a function of the whole
random oracle and the ring signatures of the earlier rounds. -/
structure AnonAdversary (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg) (Q : ℕ)
    where
  /-- The finite set of challenges the adversary may choose. -/
  choices : Finset (AnonChoice Sch RMsg N)
  /-- Every challenge of the set is valid. -/
  valid : ∀ c ∈ choices, c.Valid adm bind
  /-- The challenge of round `j` from the oracle and the earlier ring signatures. -/
  choose : (j : Fin Q) → (Query k kN kS L → Out k e) → (Fin j → M.NIProof) → AnonChoice Sch RMsg N
  /-- Every chosen challenge is in the set. -/
  choose_mem : ∀ j h πs, choose j h πs ∈ choices

variable {M}

/-- The adversary as an adversary of the witness-indistinguishability game.

Running time: the adversary's; each challenge is re-labelled as a statement and two witnesses
(`AnonChoice.toWIChoice`, constant time). This running time is argued here, not proved in Lean. -/
def AnonAdversary.toWIAdversary {adm : List Sch.PK → Prop} {bind : List Sch.PK → RMsg → Sch.Msg}
    {Q : ℕ}
    (A : AnonAdversary M adm bind Q) : M.WIAdversary (ringRel adm bind) Q where
  choices := A.choices.map ⟨_, AnonChoice.toWIChoice_injective⟩
  admissible c hc := by
    obtain ⟨c', hc', rfl⟩ := Finset.mem_map.1 hc
    exact ⟨⟨(A.valid c' hc').adm, (A.valid c' hc').wit₀⟩,
      ⟨(A.valid c' hc').adm, (A.valid c' hc').wit₁⟩⟩
  choose j h πs := (A.choose j h πs).toWIChoice
  choose_mem j h πs := Finset.mem_map_of_mem _ (A.choose_mem j h πs)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem AnonAdversary.card_choices_toWIAdversary {adm : List Sch.PK → Prop}
    {bind : List Sch.PK → RMsg → Sch.Msg} {Q : ℕ}
    (A : AnonAdversary M adm bind Q) : A.toWIAdversary.choices.card = A.choices.card :=
  Finset.card_map _

variable (M)

/-- **The anonymity advantage with adversary-supplied signatures** of the distinguisher `D`,
given the whole oracle and the `Q` ring signatures: the difference of the probabilities of `D`
when every round is answered with the ring signature of the first witness and when it is answered
with that of the second (the experiments `SPBCS.wiGame` at the ring relation), for the
encoders `E`, the query phases `Qs` and the honest prover family `honest`. -/
noncomputable def anonAdvantage (E : (j : ι) → (M.comp j).Encoder)
    {V : RingStmt Sch RMsg N → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries V x) {R : Type}
    [Fintype R] [Nonempty R]
    (honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N))
    {adm : List Sch.PK → Prop} {bind : List Sch.PK → RMsg → Sch.Msg} {Q : ℕ}
    (A : AnonAdversary M adm bind Q) (D : M.WIDistinguisher Q) : ℝ :=
  SPBCS.wiAdvantage E Qs honest A.toWIAdversary D

/-- **Statistical anonymity with adversary-supplied signatures** (BKM06 Definition 4, anonymity
against full key exposure, strengthened: the adversary chooses the ring and both witnesses, so the
two keys may be adversarially generated and the signatures any valid ones; `Q` adaptive
challenges; adversaries and distinguisher given the whole random oracle). For the spBCS
compilation `M` of a ring composite, with what the compiled proof reveals read off the composite
view (`Rv`), and whose honest prover has
honest-verifier zero knowledge (CY24 Definition 23.1.8 for composites, `CausalHVZK`) at error `δ`
for the ring relation (`h`): for every adversary with at most `C` challenges in its set and every
distinguisher, the advantage is at most `Q · M.wiError δ C`. No assumption on the keys or the base
scheme is used. -/
@[headline]
theorem anon_suppliedSignatures {adm : List Sch.PK → Prop} {bind : List Sch.PK → RMsg → Sch.Msg}
    {E : (j : ι) → (M.comp j).Encoder} {V : RingStmt Sch RMsg N → FullTr P τ → Bool}
    {Qs : ∀ x, M.IOPQueries V x} {R : Type} [Fintype R] [Nonempty R]
    {honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N)} {Pub : Type}
    {pub : RingStmt Sch RMsg N → Pub} (Rv : M.Reveal E Qs)
    {sim : CausalJointSimulator Rv.MV Pub} {δ : ℝ≥0}
    (h : CausalHVZK Rv.MV (ringRel adm bind) honest pub sim δ) {Q C : ℕ}
    (A : AnonAdversary M adm bind Q) (hA : A.choices.card ≤ C) (D : M.WIDistinguisher Q) :
    anonAdvantage M E Qs honest A D ≤ Q * M.wiError δ C :=
  SPBCS.witnessIndistinguishable Rv (Base.obsClose_of_causalHVZK Rv h) Q C
    A.toWIAdversary (A.card_choices_toWIAdversary.trans_le hA) D

/-! ### Challenger-signed challenges with exposed honest keys -/

/-- **A challenger-signed challenge**: a ring, a ring message, two honest users and the positions
of their keys in the ring. With `user₀ = user₁` and `idx₀ = idx₁` it is a signing query. -/
structure KeyedChoice (Sch : SigScheme) (RMsg : Type) (N n : ℕ) where
  /-- The ring. -/
  ring : RingOf Sch.PK N
  /-- The ring message. -/
  msg : RMsg
  /-- The user signing when `b = 0`. -/
  user₀ : Fin n
  /-- The user signing when `b = 1`. -/
  user₁ : Fin n
  /-- The position of `user₀`'s key in the ring. -/
  idx₀ : ℕ
  /-- The position of `user₁`'s key in the ring. -/
  idx₁ : ℕ
deriving DecidableEq

namespace KeyedChoice

variable {n : ℕ}

/-- **A valid challenger-signed challenge** for the users' key-generation coins `keys`: the ring is
admissible (`adm`) and the positions hold the two users' public keys. -/
structure Valid (adm : List Sch.PK → Prop) (keys : Fin n → Sch.KeyCoins)
    (c : KeyedChoice Sch RMsg N n) : Prop where
  /-- The ring is admissible. -/
  adm : adm c.ring.1
  /-- The first position is in the ring. -/
  idx₀_lt : c.idx₀ < c.ring.1.length
  /-- The first position holds `user₀`'s key. -/
  key₀ : c.ring.1[c.idx₀] = Sch.pk (keys c.user₀)
  /-- The second position is in the ring. -/
  idx₁_lt : c.idx₁ < c.ring.1.length
  /-- The second position holds `user₁`'s key. -/
  key₁ : c.ring.1[c.idx₁] = Sch.pk (keys c.user₁)

/-- `Valid` as a decidable proposition: positions in the ring holding the two users' keys. -/
theorem valid_iff {adm : List Sch.PK → Prop} {keys : Fin n → Sch.KeyCoins}
    {c : KeyedChoice Sch RMsg N n} :
    c.Valid adm keys ↔ adm c.ring.1 ∧
      (∃ h : c.idx₀ < c.ring.1.length, c.ring.1[c.idx₀] = Sch.pk (keys c.user₀)) ∧
      ∃ h : c.idx₁ < c.ring.1.length, c.ring.1[c.idx₁] = Sch.pk (keys c.user₁) :=
  ⟨fun h => ⟨h.adm, ⟨h.idx₀_lt, h.key₀⟩, ⟨h.idx₁_lt, h.key₁⟩⟩,
    fun ⟨ha, ⟨h₀, k₀⟩, ⟨h₁, k₁⟩⟩ => ⟨ha, h₀, k₀, h₁, k₁⟩⟩

instance (adm : List Sch.PK → Prop) [DecidablePred adm] (keys : Fin n → Sch.KeyCoins)
    (c : KeyedChoice Sch RMsg N n) : Decidable (c.Valid adm keys) :=
  decidable_of_iff _ valid_iff.symm

/-- **The challenge with the signatures the challenger computes**, at the users' coins `keys`,
the drawn public value `ρ` and private coins `sc`: each user signs `bind R m` with `ρ` and `sc`;
only the signature of `user_b` is used in the experiment `b`. -/
def withSignatures (bind : List Sch.PK → RMsg → Sch.Msg) (keys : Fin n → Sch.KeyCoins)
    (c : KeyedChoice Sch RMsg N n) (ρ : Sch.Pub) (sc : Sch.SignCoins) : AnonChoice Sch RMsg N :=
  ⟨c.ring, c.msg, ρ, ⟨c.idx₀, Sch.signWith (Sch.sk (keys c.user₀)) (bind c.ring.1 c.msg) ρ sc⟩,
    ⟨c.idx₁, Sch.signWith (Sch.sk (keys c.user₁)) (bind c.ring.1 c.msg) ρ sc⟩⟩

/-- **The signatures a correct scheme computes for a valid challenge are valid witnesses.** -/
theorem valid_withSignatures (hSch : Sch.Correct) {adm : List Sch.PK → Prop}
    {bind : List Sch.PK → RMsg → Sch.Msg}
    {keys : Fin n → Sch.KeyCoins} {c : KeyedChoice Sch RMsg N n} (hc : c.Valid adm keys)
    (ρ : Sch.Pub) (sc : Sch.SignCoins) : (c.withSignatures bind keys ρ sc).Valid adm bind where
  adm := hc.adm
  wit₀ := RingRel.of_signWith hSch hc.idx₀_lt hc.key₀ ρ sc
  wit₁ := RingRel.of_signWith hSch hc.idx₁_lt hc.key₁ ρ sc

end KeyedChoice

/-- **The challenger's draws**: the key-generation coins of the `n` honest users, and for each of
the `Q` rounds a public value and private signing coins, all uniform and independent. -/
abbrev KeyedDraw (Sch : SigScheme) (n Q : ℕ) : Type :=
  (Fin n → Sch.KeyCoins) × (Fin Q → Sch.Pub × Sch.SignCoins)

/-- **An anonymity adversary against full key exposure** with `n` honest users and `Q`
challenges: a finite set of challenges and, in round `j`, a challenge from it chosen as a function
of the honest users' key-generation coins (given at the start), the whole random oracle and the
earlier ring signatures; every chosen challenge is valid for the users' keys. -/
structure KeyedAnonAdversary (adm : List Sch.PK → Prop) (n Q : ℕ) where
  /-- The finite set of challenges the adversary may choose. -/
  choices : Finset (KeyedChoice Sch RMsg N n)
  /-- The challenge of round `j` from the users' coins, the oracle and the earlier signatures. -/
  choose : (j : Fin Q) → (Fin n → Sch.KeyCoins) → (Query k kN kS L → Out k e) →
    (Fin j → M.NIProof) → KeyedChoice Sch RMsg N n
  /-- Every chosen challenge is in the set. -/
  choose_mem : ∀ j keys h πs, choose j keys h πs ∈ choices
  /-- Every chosen challenge is valid for the users' keys. -/
  choose_valid : ∀ j keys h πs, (choose j keys h πs).Valid adm keys

namespace KeyedAnonAdversary

variable {M} {n Q : ℕ}

/-- **The adversary with the challenger's draws fixed**, as an adversary with supplied
signatures: round `j` is the chosen challenge with the signatures computed from the draw
(`KeyedChoice.withSignatures`), and the challenge set is the valid challenges of the set with
every public value and signing coins.

Running time: the adversary's choice in each round, then two key generations and two signings of
the base scheme (`withSignatures`) at the round's drawn public value and coins. The challenge set
is part of the adversary's description, not computed by the reduction.
This running time is argued here, not proved in Lean. -/
def toAnon [DecidableEq RMsg] (hSch : Sch.Correct) (adm : List Sch.PK → Prop) [DecidablePred adm]
    (bind : List Sch.PK → RMsg → Sch.Msg) (A : KeyedAnonAdversary (RMsg := RMsg) M adm n Q)
    (d : KeyedDraw Sch n Q) : AnonAdversary M adm bind Q where
  choices := ((A.choices.filter fun c => c.Valid adm d.1) ×ˢ
      (Finset.univ : Finset (Sch.Pub × Sch.SignCoins))).image
    fun p => p.1.withSignatures bind d.1 p.2.1 p.2.2
  valid c hc := by
    obtain ⟨⟨c', ρ, sc⟩, hp, rfl⟩ := Finset.mem_image.1 hc
    exact KeyedChoice.valid_withSignatures hSch
      (Finset.mem_filter.1 (Finset.mem_product.1 hp).1).2 ρ sc
  choose j h πs := (A.choose j d.1 h πs).withSignatures bind d.1 (d.2 j).1 (d.2 j).2
  choose_mem j h πs := Finset.mem_image.2 ⟨(⟨A.choose j d.1 h πs, d.2 j⟩ :
      KeyedChoice Sch RMsg N n × (Sch.Pub × Sch.SignCoins)),
    Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨A.choose_mem j d.1 h πs, A.choose_valid j d.1 h πs⟩,
      Finset.mem_univ _⟩, rfl⟩

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem card_choices_toAnon_le [DecidableEq RMsg] (hSch : Sch.Correct) (adm : List Sch.PK → Prop)
    [DecidablePred adm] (bind : List Sch.PK → RMsg → Sch.Msg)
    (A : KeyedAnonAdversary (RMsg := RMsg) M adm n Q) (d : KeyedDraw Sch n Q) :
    (A.toAnon hSch adm bind d).choices.card ≤
      A.choices.card * Fintype.card (Sch.Pub × Sch.SignCoins) := by
  refine Finset.card_image_le.trans ?_
  rw [Finset.card_product, Finset.card_univ]
  exact Nat.mul_le_mul_right _ (Finset.card_filter_le _ _)

end KeyedAnonAdversary

/-- **The experiment `b` of anonymity against full key exposure**: the honest users' coins and the
challenger's signing draws uniform, then the rounds of the adversary, round `j` answered with the
ring signature of `user_b` on its ring and message, signed with the draws of round `j`; the
outcome is the draw with the whole oracle and the `Q` ring signatures. -/
noncomputable def keyedAnonGame [DecidableEq RMsg] (E : (j : ι) → (M.comp j).Encoder)
    {V : RingStmt Sch RMsg N → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries V x) {R : Type}
    [Fintype R] [Nonempty R]
    (honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N))
    (hSch : Sch.Correct) (adm : List Sch.PK → Prop) [DecidablePred adm]
    (bind : List Sch.PK → RMsg → Sch.Msg) {n Q : ℕ}
    (A : KeyedAnonAdversary (RMsg := RMsg) M adm n Q)
    (b : Bool) : PMF (KeyedDraw Sch n Q × ((Query k kN kS L → Out k e) × (Fin Q → M.NIProof))) :=
  (PMF.uniformOfFintype (KeyedDraw Sch n Q)).bind fun d =>
    (SPBCS.wiGame E Qs honest (A.toAnon hSch adm bind d).toWIAdversary b).map fun s => (d, s)

/-- **The advantage of anonymity against full key exposure** of the distinguisher `D`, given the
honest users' key-generation coins, the whole oracle and the `Q` ring signatures. -/
noncomputable def keyedAnonAdvantage [DecidableEq RMsg] (E : (j : ι) → (M.comp j).Encoder)
    {V : RingStmt Sch RMsg N → FullTr P τ → Bool} (Qs : ∀ x, M.IOPQueries V x) {R : Type}
    [Fintype R] [Nonempty R]
    (honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N))
    (hSch : Sch.Correct) (adm : List Sch.PK → Prop) [DecidablePred adm]
    (bind : List Sch.PK → RMsg → Sch.Msg) {n Q : ℕ}
    (A : KeyedAnonAdversary (RMsg := RMsg) M adm n Q)
    (D : (Fin n → Sch.KeyCoins) → M.WIDistinguisher Q) : ℝ :=
  GordieHowe.gameAdvantage (keyedAnonGame M E Qs honest hSch adm bind A false)
    (keyedAnonGame M E Qs honest hSch adm bind A true)
    {p | D p.1.1 p.2.1 p.2.2}

/-- **Statistical anonymity against full key exposure with adversarial ring members** (BKM06
Definition 4, ePrint 2005/304, with the keys given at the start as in CCLM22 Experiment 2, p. 21,
and `Q` adaptive challenges, signing queries included): for a correct base scheme (`hSch`) and the
spBCS compilation `M` of a ring composite, with what the compiled proof reveals read off the
composite view (`Rv`), and whose honest prover has
honest-verifier zero knowledge (CY24 Definition 23.1.8 for composites, `CausalHVZK`) at error `δ`
(`h`): for every adversary whose challenge set, times the number of public values and signing
coins, is at most `C`, and every distinguisher given the users' key-generation coins, the whole
oracle and the ring signatures, the advantage is at most `Q · M.wiError δ C`. -/
@[headline]
theorem keyedAnon_le [DecidableEq RMsg] {adm : List Sch.PK → Prop} [DecidablePred adm]
    {bind : List Sch.PK → RMsg → Sch.Msg} {E : (j : ι) → (M.comp j).Encoder}
    {V : RingStmt Sch RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries V x} {R : Type}
    [Fintype R] [Nonempty R]
    {honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N)}
    {Pub : Type} {pub : RingStmt Sch RMsg N → Pub} (hSch : Sch.Correct) (Rv : M.Reveal E Qs) {sim : CausalJointSimulator Rv.MV Pub} {δ : ℝ≥0}
    (h : CausalHVZK Rv.MV (ringRel adm bind) honest pub sim δ)
    {n Q C : ℕ} (A : KeyedAnonAdversary (RMsg := RMsg) M adm n Q)
    (hA : A.choices.card * Fintype.card (Sch.Pub × Sch.SignCoins) ≤ C)
    (D : (Fin n → Sch.KeyCoins) → M.WIDistinguisher Q) :
    keyedAnonAdvantage M E Qs honest hSch adm bind A D ≤ Q * M.wiError δ C := by
  unfold keyedAnonAdvantage GordieHowe.gameAdvantage GordieHowe.advantage keyedAnonGame
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  refine PMF.abs_toReal_tsum_mul_sub_le _ (fun _ => PMF.toOuterMeasure_apply_le_one _ _)
    (fun _ => PMF.toOuterMeasure_apply_le_one _ _) fun d => ?_
  exact anon_suppliedSignatures M Rv h (A.toAnon hSch adm bind d)
    ((A.card_choices_toAnon_le hSch adm bind d).trans hA) (D d.1)

end GordieHowe.Ring
