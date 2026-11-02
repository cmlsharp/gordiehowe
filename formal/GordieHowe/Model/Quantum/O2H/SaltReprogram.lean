-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.WholeRun
public import GordieHowe.Model.Quantum.Pure.GameTape
public import GordieHowe.Model.Quantum.Pure.UntilBad

@[expose] public section

/-!
# Reprogramming the random oracle at hidden fresh salts, over a whole interaction

A challenger answers `Q` requests by reading the random oracle `H : X → Y` on the slices
`emb (ρ i, ·)` of `K` salts `ρ` that it draws itself, independently of everything else, and never
reveals, where `emb : S × U → X` is an injective embedding of the salted inputs into the oracle's
domain; it may also read `H` outside the range of `emb`. For example a hedged signer whose mask is
`H(K ‖ rnd ‖ µ)` at a fresh nonce `rnd` (FIPS 204 Algorithm 7, the mask seed
`ρ'' = H(K ‖ rnd ‖ µ)`), with its other hashes domain-separated from the mask derivation. The
adversary queries `H` in superposition and keeps its quantum state across all requests (a
distinguisher of the pure game, `GordieHowe/Model/Quantum/Pure/Game.lean`, with a query budget and
no final unitary; the interactive adversaries of `GordieHowe/Model/Quantum/Interactive` reach it
through their dilation, `GordieHowe/Model/Quantum/Interactive/SaltReprogram.lean`). The oracle is
drawn from a law `μH` whose values on the range of `emb` are uniform and independent of the rest
(`IsUniformOnRange`; the uniform law, `isUniformOnRange_uniform`, and the uniform law
conditioned on the values off the range, `isUniformOnRange_offRangeLaw`).
The challenger's reads at the salts may then be replaced by independent fresh functions: the
advantage is at most the probability that two salts collide plus `2 q √(n ε)`, for `q` query
slots of `n` parallel queries and `ε` bounding the probability that a given point of `S` is a
salt (`Distinguisher.advantage_salt_fresh_le`); for independent salts of min-entropy `κ`, at
most `C(K, 2) 2^{-κ} + 2 q √(n K 2^{-κ})` (`advantage_salt_fresh_le_of_pi`).

This is adaptive reprogramming in the quantum random-oracle model (Grilo, Hövelmanns, Hülsing
and Majenz, "Tight adaptive reprogramming in the QROM", ASIACRYPT 2021) for reprogrammed points
`emb (ρ i, u)` whose secret part `ρ i` is fresh and stays hidden, while the challenger chooses `u`
adaptively from the requests; the proof is one-way to hiding applied to the whole run as one
oracle algorithm (Ambainis, Hamburg, Unruh, CRYPTO 2019, Theorem 3). This library does not prove
the bound of Grilo et al. for reprogrammed points that are revealed.

## The games and the proof

The challenger's answer to request number `j` is `ans c j req g H`: a function of its other coins
`c`, the request, the values `g` of an oracle on the `K` slices, and the oracle `H` read only
outside the range of `emb` (`ReadsOffRange`).

- `saltEnv` (the real game): the adversary's oracle is `H`, and `g = slices emb H ρ`.
- `freshEnv` (the ideal game): the adversary's oracle is `H`, and `g = Z`, `K` fresh uniform
  functions on `U`.
- `reprogEnv` (the hybrid): the adversary's oracle is `H` reprogrammed on the slices to `Z`
  (`reprogSalts`), and `g = Z`.

`sum_vLaw_saltEnv_eq`: for distinct salts, the real game and the hybrid have the same
acceptance probability averaged over `H`, `Z` and the other coins (the proof exchanges `H`'s
values on the slices with `Z` by `resampleEquiv`). `advantage_salt_reprog_le`: so the two differ
by at most the collision probability. `advantage_fresh_reprog_le`: the hybrid and the
ideal game answer alike, and their oracles differ only on the slices (`saltSet`), which the ideal
game reads nowhere; one-way to hiding over the whole run
(`Distinguisher.advantage_acceptProb_le_of_fresh_secret_budget`) bounds the difference by
`2 q √(n ε)`.

`offRangeLaw emb H₀`, the uniform law conditioned on agreeing with `H₀` outside the range of
`emb`, is uniform on the range given the rest (`isUniformOnRange_offRangeLaw`), and the uniform
law is the average of these over a uniform `H₀` (`sum_uniform_eq_sum_offRangeLaw`).

The environments keep the oracle as their state (`keepsState_saltEnv`, `keepsState_freshEnv`,
`keepsState_reprogEnv`) and answer from the request number and the request.
`acceptProbOnAt_congr`, `acceptProbAt_congr` (from `Distinguisher.final_congr`,
`GordieHowe/Model/Quantum/Pure/UntilBad.lean`): the game reads an environment only through its
answers and oracles in force, so a challenger with any state type (`Challenger.toPureEnv`) that
gives the same answers and oracles has the same acceptance probabilities.

`toReal_pi_exists_eq_le`, `toReal_pi_not_injective_le`: for `K` independent salts with point
probabilities at most `δ`, a given point is a salt with probability at most `K δ`, and two salts
collide with probability at most `C(K, 2) δ`.
## Reprogramming only a component of the oracle's values

The oracle's values may split as `e : Y ≃ Y₁ × Y₂` (a plain equivalence), where the challenger
reads the oracle at the salts only through the first components and may read the second
components everywhere. Every object above has a counterpart for the split, and each statement
above is its counterpart at the split `wholeSplit Y : Y ≃ Y × Unit` with a trivial second
component, from which it is derived.

- `slicesOn`: the first components on the slices; `AgreeOffRangeOn`: agreement outside the
  range and in the second components everywhere (`AgreeOffRangeOn.refl`, `.symm`, `.trans`,
  `agreeOffRangeOn_wholeSplit_iff`); `IsUniformOnRangeOn` (`IsUniformOnRange.isUniformOnRangeOn`,
  `isUniformOnRangeOn_wholeSplit_iff`) and `ReadsOffRangeOn` (`ReadsOffRange.readsOffRangeOn`).
- `reprogSaltsOn`: the first components reprogrammed on the slices (`reprogSaltsOn_of_notMem`,
  `reprogSaltsOn_of_exists`, `snd_reprogSaltsOn`, `agreeOffRangeOn_reprogSaltsOn`,
  `slicesOn_reprogSaltsOn`, `reprogSaltsOn_slicesOn`); `resampleEquivOn`,
  `resampleEquivOn_apply`.
- `offRangeClassOn`, `offRangeLawOn`: the uniform law conditioned on the values outside the range
  and the second components (`mem_offRangeClassOn`, `offRangeLawOn_apply`, `offRangeClassOn_eq`,
  `isUniformOnRangeOn_offRangeLawOn`, `agreeOffRangeOn_of_offRangeLawOn_ne_zero`,
  `sum_uniform_eq_sum_offRangeLawOn`; `offRangeClass_eq_offRangeClassOn`,
  `offRangeLaw_eq_offRangeLawOn`).
- `SaltTapeOn`: the tape with fresh functions valued in `Y₁` (`vLaw`, `saltLaw` and `freshEnv`
  take fresh functions valued in any `Y₁`); `saltEnvOn`, `reprogEnvOn` (`keepsState_saltEnvOn`,
  `keepsState_reprogEnvOn`, `saltEnv_eq_saltEnvOn`, `reprogEnv_eq_reprogEnvOn`).
- `Distinguisher.advantage_fresh_reprogOn_le`, `acceptProbAt_saltEnvOn`,
  `acceptProbAt_reprogEnvOn`, `sum_vLaw_saltEnvOn_eq`, `advantage_saltOn_reprog_le`, and the
  bounds `advantage_saltOn_fresh_le` (`Pr[two salts collide] + 2 q √(n ε)`) and
  `advantage_saltOn_fresh_le_of_pi` (`C(K, 2) δ + 2 q √(n K δ)`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Environments read through a map of tapes -/

namespace Env

variable {Ω Ω' Req A X Y : Type*} {St : Type _} {Q : ℕ}

/-- **An environment read through a map of tapes**: the tape `τ ω'` for `ω' ← μ'`. -/
def comap (E : Env Ω Req A X Y Q St) (μ' : PMF Ω') (τ : Ω' → Ω) : Env Ω' Req A X Y Q St where
  μ := μ'
  oracle₀ ω' := E.oracle₀ (τ ω')
  respond ω' := E.respond (τ ω')

/-- The state of an environment read through a map of tapes is the state at the mapped tape. -/
theorem oracleIn_comap (E : Env Ω Req A X Y Q St) (μ' : PMF Ω') (τ : Ω' → Ω) (ω' : Ω')
    (rs : List Req) : (E.comap μ' τ).oracleIn ω' rs = E.oracleIn (τ ω') rs :=
  rfl

/-- The answers of an environment read through a map of tapes are the answers at the mapped
tape. -/
theorem answerAfter_comap (E : Env Ω Req A X Y Q St) (μ' : PMF Ω') (τ : Ω' → Ω) (ω' : Ω')
    (rs : List Req) (req : Req) :
    (E.comap μ' τ).answerAfter ω' rs req = E.answerAfter (τ ω') rs req :=
  rfl

/-- **An environment whose requests never change the oracle**: every reply keeps the state. -/
def KeepsState (E : Env Ω Req A X Y Q St) : Prop :=
  ∀ ω c req s, (E.respond ω c req s).state = s

/-- The state of an environment whose requests never change the oracle is its initial state. -/
theorem oracleIn_of_keepsState {E : Env Ω Req A X Y Q St} (hE : E.KeepsState) (ω : Ω)
    (rs : List Req) : E.oracleIn ω rs = E.oracle₀ ω := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs req ih =>
    rw [oracleIn_append_singleton, update, ih]
    split_ifs
    · exact hE _ _ _ _
    · rfl

end Env

/-! ### The acceptance probability reads an environment through its answers and oracles -/

namespace Distinguisher

variable {W X Y Req A : Type*} [Fintype W] [Fintype X] [Fintype Y] [Fintype Req] [Fintype A]
  {n m : ℕ} (D : Distinguisher W X Y Req A n m) [DecidableEq Req] [DecidableEq A] [AddGroup Y]
  {Ω Ω' : Type*} {St St' : Type _} {Q Q' : ℕ} [OracleState St X Y] [OracleState St' X Y]

/-- **The game reads an environment only through its answers and its oracles in force**: two
environments, with any states, that give the same answers and oracles in force on every log
at the tapes `ω` and `ω'` have the same acceptance probabilities there. -/
theorem acceptProbOnAt_congr (E : Env Ω Req A X Y Q St) (E' : Env Ω' Req A X Y Q' St')
    {ω : Ω} {ω' : Ω'} (hA : ∀ (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω' lg k)
    (hO : ∀ lg : LogReg Req m, E.oracle ω lg = E'.oracle ω' lg)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (L : Set (LogReg Req m)) :
    D.acceptProbOnAt E post L ω = D.acceptProbOnAt E' post L ω' := by
  simp only [acceptProbOnAt, D.final_congr E E' hA hO post]

/-- `acceptProbOnAt_congr` for the acceptance probability on every log. -/
theorem acceptProbAt_congr (E : Env Ω Req A X Y Q St) (E' : Env Ω' Req A X Y Q' St')
    {ω : Ω} {ω' : Ω'} (hA : ∀ (lg : LogReg Req m) k, E.answer ω lg k = E'.answer ω' lg k)
    (hO : ∀ lg : LogReg Req m, E.oracle ω lg = E'.oracle ω' lg)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A)) :
    D.acceptProbAt E post ω = D.acceptProbAt E' post ω' := by
  rw [← acceptProbOnAt_univ, ← acceptProbOnAt_univ]
  exact D.acceptProbOnAt_congr E E' hA hO post Set.univ

/-- The acceptance probability of an environment read through a map of tapes is the acceptance
probability at the mapped tape. -/
theorem acceptProbAt_comap (E : Env Ω Req A X Y Q St) (μ' : PMF Ω') (τ : Ω' → Ω)
    (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))
    (ω' : Ω') : D.acceptProbAt (E.comap μ' τ) post ω' = D.acceptProbAt E post (τ ω') :=
  D.acceptProbAt_congr _ _ (fun _ _ => rfl) (fun _ => rfl) post

end Distinguisher

/-! ### Challengers that read the oracle at hidden salts -/

section Salt

variable {X S U Y Req A C : Type*} {Y₁ Y₂ : Type*} {K Q : ℕ} (emb : S × U → X)

/-- **The tape of a salted game**: the random oracle, `K` fresh functions, the challenger's other
coins, and its `K` salts. -/
abbrev SaltTape (X S U Y C : Type*) (K : ℕ) := ((X → Y) × (Fin K → U → Y) × C) × (Fin K → S)

/-- **The tape of a salted game with fresh functions valued in `Y₁`**: the random oracle, `K`
fresh functions `U → Y₁`, the challenger's other coins, and its `K` salts. `SaltTape X S U Y C K`
is `SaltTapeOn X S U Y Y C K`. -/
abbrev SaltTapeOn (X S U Y Y₁ C : Type*) (K : ℕ) :=
  ((X → Y) × (Fin K → U → Y₁) × C) × (Fin K → S)

/-- **The values of the oracle on the slices of the salts**: on the slice `emb (ρ i, ·)` of salt
`i`. -/
def slices (H : X → Y) (ρ : Fin K → S) : Fin K → U → Y :=
  fun i u => H (emb (ρ i, u))

/-- **The points of the slices of the salts**: `emb (ρ i, u)` for every salt `i` and every `u`. -/
def saltSet (ρ : Fin K → S) : Set X :=
  {x | ∃ p : Fin K × U, emb (ρ p.1, p.2) = x}

/-- **Two oracles agree outside the range of the embedding.** -/
def AgreeOffRange (H H' : X → Y) : Prop :=
  ∀ x, x ∉ Set.range emb → H x = H' x

/-- **A law of the oracle that is uniform on the range of the embedding given the rest**: two
oracles that agree outside the range have the same probability. The uniform law satisfies it
(`isUniformOnRange_uniform`), and so does the uniform law conditioned on the values outside the
range (`isUniformOnRange_offRangeLaw`). -/
def IsUniformOnRange (μH : PMF (X → Y)) : Prop :=
  ∀ H H', AgreeOffRange emb H H' → μH H = μH H'

/-- **Answers that read the oracle only outside the range of the embedding**: the answer
function `ans c j req g H` (request number `j` of any index type `J`) gives the same answer for
two oracles `H` that agree outside the range. -/
def ReadsOffRange {J : Type*} (ans : C → J → Req → (Fin K → U → Y) → (X → Y) → Option A) :
    Prop :=
  ∀ c j req g H H', AgreeOffRange emb H H' → ans c j req g H = ans c j req g H'

open Classical in
/-- **The oracle reprogrammed on the slices of the salts** to the fresh functions: on a point of
a slice, the fresh function of an index and an input carrying it; elsewhere the oracle. -/
noncomputable def reprogSalts (H : X → Y) (ρ : Fin K → S) (Z : Fin K → U → Y) : X → Y :=
  fun x => if h : ∃ p : Fin K × U, emb (ρ p.1, p.2) = x then
    Z (Classical.choose h).1 (Classical.choose h).2 else H x

variable {emb}

/-- Off the slices of the salts, the reprogrammed oracle is the oracle. -/
theorem reprogSalts_of_notMem {H : X → Y} {ρ : Fin K → S} (Z : Fin K → U → Y) {x : X}
    (hx : x ∉ saltSet emb ρ) : reprogSalts emb H ρ Z x = H x := by
  rw [reprogSalts, dif_neg (show ¬ ∃ p : Fin K × U, emb (ρ p.1, p.2) = x from hx)]

/-- A point outside the range of the embedding is on no slice of the salts. -/
theorem notMem_saltSet_of_notMem_range {ρ : Fin K → S} {x : X} (hx : x ∉ Set.range emb) :
    x ∉ saltSet emb ρ := fun ⟨_, hp⟩ => hx ⟨_, hp⟩

/-- **Reprogramming on the slices changes the oracle only on the range of the embedding.** -/
theorem agreeOffRange_reprogSalts (H : X → Y) (ρ : Fin K → S) (Z : Fin K → U → Y) :
    AgreeOffRange emb (reprogSalts emb H ρ Z) H := fun _ hx =>
  reprogSalts_of_notMem Z (notMem_saltSet_of_notMem_range hx)

/-- For distinct salts and an injective embedding, the reprogrammed oracle at `emb (ρ i, u)` is
`Z i u`. -/
theorem reprogSalts_of_injective (hemb : Function.Injective emb) {H : X → Y} {ρ : Fin K → S}
    (hρ : Function.Injective ρ) (Z : Fin K → U → Y) (i : Fin K) (u : U) :
    reprogSalts emb H ρ Z (emb (ρ i, u)) = Z i u := by
  have h : ∃ p : Fin K × U, emb (ρ p.1, p.2) = emb (ρ i, u) := ⟨(i, u), rfl⟩
  rw [reprogSalts, dif_pos h]
  have hp := Prod.ext_iff.1 (hemb (Classical.choose_spec h))
  rw [hρ hp.1, hp.2]

/-- For distinct salts and an injective embedding, the slices of the reprogrammed oracle are the
fresh functions. -/
theorem slices_reprogSalts (hemb : Function.Injective emb) {H : X → Y} {ρ : Fin K → S}
    (hρ : Function.Injective ρ) (Z : Fin K → U → Y) : slices emb (reprogSalts emb H ρ Z) ρ = Z :=
  funext fun i => funext fun u => reprogSalts_of_injective hemb hρ Z i u

/-- Reprogramming the reprogrammed oracle back to the oracle's slices gives the oracle. -/
theorem reprogSalts_slices (ρ : Fin K → S) (H : X → Y) (Z : Fin K → U → Y) :
    reprogSalts emb (reprogSalts emb H ρ Z) ρ (slices emb H ρ) = H := by
  funext x
  by_cases hx : ∃ p : Fin K × U, emb (ρ p.1, p.2) = x
  · rw [reprogSalts, dif_pos hx]
    exact congrArg H (Classical.choose_spec hx)
  · rw [reprogSalts_of_notMem _ hx, reprogSalts_of_notMem _ hx]

/-- **Resampling at the salts** (for distinct salts and an injective embedding): exchanging the
oracle's values on the slices with the fresh functions is an involution of the pair of the oracle
and the fresh functions. -/
noncomputable def resampleEquiv (hemb : Function.Injective emb) {ρ : Fin K → S}
    (hρ : Function.Injective ρ) : Equiv.Perm ((X → Y) × (Fin K → U → Y)) :=
  Function.Involutive.toPerm (fun p => (reprogSalts emb p.1 ρ p.2, slices emb p.1 ρ)) fun p => by
    simp only [slices_reprogSalts hemb hρ, reprogSalts_slices]

/-- `resampleEquiv` reprograms the oracle to the fresh functions and takes the oracle's slices
as the fresh functions. -/
theorem resampleEquiv_apply (hemb : Function.Injective emb) {ρ : Fin K → S}
    (hρ : Function.Injective ρ) (p : (X → Y) × (Fin K → U → Y)) :
    resampleEquiv hemb hρ p = (reprogSalts emb p.1 ρ p.2, slices emb p.1 ρ) :=
  rfl

/-- **The uniform law is uniform on the range of the embedding.** -/
theorem isUniformOnRange_uniform [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] :
    IsUniformOnRange emb (PMF.uniformOfFintype (X → Y)) := fun _ _ _ => by
  simp only [PMF.uniformOfFintype_apply]

/-- An oracle agrees with itself outside the range. -/
theorem AgreeOffRange.refl (H : X → Y) : AgreeOffRange emb H H := fun _ _ => rfl

/-- Agreement outside the range is symmetric. -/
theorem AgreeOffRange.symm {H H' : X → Y} (h : AgreeOffRange emb H H') :
    AgreeOffRange emb H' H := fun x hx => (h x hx).symm

/-- Agreement outside the range is transitive. -/
theorem AgreeOffRange.trans {H H' H'' : X → Y} (h : AgreeOffRange emb H H')
    (h' : AgreeOffRange emb H' H'') : AgreeOffRange emb H H'' := fun x hx =>
  (h x hx).trans (h' x hx)

/-! ### Splitting the oracle's values into components

A plain equivalence `e : Y ≃ Y₁ × Y₂` splits each value of the oracle into a first component in
`Y₁` (the part a challenger reads at the salts) and a second component in `Y₂` (a part it may
read everywhere). `wholeSplit Y : Y ≃ Y × Unit` is the split with a trivial second component, at
which every definition below is its counterpart without a split. -/

/-- **The split with a trivial second component**: `y ↦ (y, ())`. -/
abbrev wholeSplit (Y : Type*) : Y ≃ Y × Unit := (Equiv.prodPUnit Y).symm

section Split

variable (emb) (e : Y ≃ Y₁ × Y₂)

/-- **The first components of the oracle on the slices of the salts**: on the slice
`emb (ρ i, ·)` of salt `i`, the first component under `e` of the oracle's value. -/
def slicesOn (H : X → Y) (ρ : Fin K → S) : Fin K → U → Y₁ :=
  fun i u => (e (H (emb (ρ i, u)))).1

/-- **Two oracles agree outside the range of the embedding and have the same second components
everywhere.** -/
def AgreeOffRangeOn (H H' : X → Y) : Prop :=
  AgreeOffRange emb H H' ∧ ∀ x, (e (H x)).2 = (e (H' x)).2

/-- **A law of the oracle whose first components on the range of the embedding are uniform given
the rest**: two oracles that agree outside the range and have the same second components
everywhere have the same probability. -/
def IsUniformOnRangeOn (μH : PMF (X → Y)) : Prop :=
  ∀ H H', AgreeOffRangeOn emb e H H' → μH H = μH H'

/-- **Answers that read the oracle's first components only outside the range of the
embedding**: the answer function `ans c j req g H` gives the same answer for two oracles `H` that
agree outside the range and have the same second components everywhere. -/
def ReadsOffRangeOn {J : Type*} (ans : C → J → Req → (Fin K → U → Y₁) → (X → Y) → Option A) :
    Prop :=
  ∀ c j req g H H', AgreeOffRangeOn emb e H H' → ans c j req g H = ans c j req g H'

/-- **The oracle with its first components reprogrammed on the slices of the salts** to the
fresh functions: at a point `emb (ρ i, u)` of a slice, the value whose first component is
`Z i u` and whose second component is the oracle's (`reprogSalts` at these values); elsewhere
the oracle. -/
noncomputable def reprogSaltsOn (H : X → Y) (ρ : Fin K → S) (Z : Fin K → U → Y₁) : X → Y :=
  reprogSalts emb H ρ fun i u => e.symm (Z i u, (e (H (emb (ρ i, u)))).2)

variable {emb e}

/-- An oracle agrees with itself off the range and in its second components. -/
theorem AgreeOffRangeOn.refl (H : X → Y) : AgreeOffRangeOn emb e H H :=
  ⟨.refl H, fun _ => rfl⟩

/-- `AgreeOffRangeOn` is symmetric. -/
theorem AgreeOffRangeOn.symm {H H' : X → Y} (h : AgreeOffRangeOn emb e H H') :
    AgreeOffRangeOn emb e H' H :=
  ⟨h.1.symm, fun x => (h.2 x).symm⟩

/-- `AgreeOffRangeOn` is transitive. -/
theorem AgreeOffRangeOn.trans {H H' H'' : X → Y} (h : AgreeOffRangeOn emb e H H')
    (h' : AgreeOffRangeOn emb e H' H'') : AgreeOffRangeOn emb e H H'' :=
  ⟨h.1.trans h'.1, fun x => (h.2 x).trans (h'.2 x)⟩

/-- At the split with a trivial second component, `AgreeOffRangeOn` is `AgreeOffRange`. -/
theorem agreeOffRangeOn_wholeSplit_iff {H H' : X → Y} :
    AgreeOffRangeOn emb (wholeSplit Y) H H' ↔ AgreeOffRange emb H H' :=
  ⟨And.left, fun h => ⟨h, fun _ => rfl⟩⟩

/-- A law uniform on the range given the rest is uniform in the first components, for every
split. -/
theorem IsUniformOnRange.isUniformOnRangeOn {μH : PMF (X → Y)} (h : IsUniformOnRange emb μH) :
    IsUniformOnRangeOn emb e μH :=
  fun H H' hH => h H H' hH.1

/-- At the split with a trivial second component, `IsUniformOnRangeOn` is
`IsUniformOnRange`. -/
theorem isUniformOnRangeOn_wholeSplit_iff {μH : PMF (X → Y)} :
    IsUniformOnRangeOn emb (wholeSplit Y) μH ↔ IsUniformOnRange emb μH :=
  ⟨fun h H H' hH => h H H' (agreeOffRangeOn_wholeSplit_iff.2 hH),
    IsUniformOnRange.isUniformOnRangeOn⟩

/-- Answers that read the oracle only outside the range read its first components only outside
the range, for every split `Y ≃ Y × Y₂`. -/
theorem ReadsOffRange.readsOffRangeOn {J : Type*}
    {ans : C → J → Req → (Fin K → U → Y) → (X → Y) → Option A} {e : Y ≃ Y × Y₂}
    (h : ReadsOffRange emb ans) : ReadsOffRangeOn emb e ans :=
  fun c j req g H H' hH => h c j req g H H' hH.1

/-- Off the slices of the salts, the oracle with reprogrammed first components is the oracle. -/
theorem reprogSaltsOn_of_notMem {H : X → Y} {ρ : Fin K → S} (Z : Fin K → U → Y₁) {x : X}
    (hx : x ∉ saltSet emb ρ) : reprogSaltsOn emb e H ρ Z x = H x :=
  reprogSalts_of_notMem _ hx

/-- On a slice of the salts, the oracle with reprogrammed first components has the first
component of the fresh function at an index and an input carrying the point, and the oracle's
second component. -/
theorem reprogSaltsOn_of_exists {H : X → Y} {ρ : Fin K → S} (Z : Fin K → U → Y₁) {x : X}
    (hx : ∃ p : Fin K × U, emb (ρ p.1, p.2) = x) :
    reprogSaltsOn emb e H ρ Z x =
      e.symm (Z (Classical.choose hx).1 (Classical.choose hx).2, (e (H x)).2) := by
  rw [reprogSaltsOn, reprogSalts, dif_pos hx]
  rw [Classical.choose_spec hx]

/-- **Reprogramming the first components keeps the second components.** -/
theorem snd_reprogSaltsOn (H : X → Y) (ρ : Fin K → S) (Z : Fin K → U → Y₁) (x : X) :
    (e (reprogSaltsOn emb e H ρ Z x)).2 = (e (H x)).2 := by
  by_cases hx : ∃ p : Fin K × U, emb (ρ p.1, p.2) = x
  · rw [reprogSaltsOn_of_exists Z hx, Equiv.apply_symm_apply]
  · rw [reprogSaltsOn_of_notMem Z hx]

/-- **Reprogramming the first components on the slices keeps the oracle outside the range and
its second components everywhere.** -/
theorem agreeOffRangeOn_reprogSaltsOn (H : X → Y) (ρ : Fin K → S) (Z : Fin K → U → Y₁) :
    AgreeOffRangeOn emb e (reprogSaltsOn emb e H ρ Z) H :=
  ⟨agreeOffRange_reprogSalts H ρ _, snd_reprogSaltsOn H ρ Z⟩

/-- For distinct salts and an injective embedding, the first components of the reprogrammed
oracle on the slices are the fresh functions. -/
theorem slicesOn_reprogSaltsOn (hemb : Function.Injective emb) {H : X → Y} {ρ : Fin K → S}
    (hρ : Function.Injective ρ) (Z : Fin K → U → Y₁) :
    slicesOn emb e (reprogSaltsOn emb e H ρ Z) ρ = Z :=
  funext fun i => funext fun u => by
    simp only [slicesOn, reprogSaltsOn, reprogSalts_of_injective hemb hρ, Equiv.apply_symm_apply]

/-- Reprogramming the reprogrammed oracle's first components back to the oracle's gives the
oracle. -/
theorem reprogSaltsOn_slicesOn (ρ : Fin K → S) (H : X → Y) (Z : Fin K → U → Y₁) :
    reprogSaltsOn emb e (reprogSaltsOn emb e H ρ Z) ρ (slicesOn emb e H ρ) = H := by
  funext x
  by_cases hx : ∃ p : Fin K × U, emb (ρ p.1, p.2) = x
  · rw [reprogSaltsOn_of_exists _ hx, snd_reprogSaltsOn]
    simp only [slicesOn]
    rw [Classical.choose_spec hx, Prod.mk.eta, Equiv.symm_apply_apply]
  · rw [reprogSaltsOn_of_notMem _ hx, reprogSaltsOn_of_notMem _ hx]

variable (e) in
/-- **Resampling the first components at the salts** (for distinct salts and an injective
embedding): exchanging the first components of the oracle's values on the slices with the fresh
functions is an involution of the pair of the oracle and the fresh functions. -/
noncomputable def resampleEquivOn (hemb : Function.Injective emb) {ρ : Fin K → S}
    (hρ : Function.Injective ρ) : Equiv.Perm ((X → Y) × (Fin K → U → Y₁)) :=
  Function.Involutive.toPerm (fun p => (reprogSaltsOn emb e p.1 ρ p.2, slicesOn emb e p.1 ρ))
    fun p => by simp only [slicesOn_reprogSaltsOn hemb hρ, reprogSaltsOn_slicesOn]

/-- `resampleEquivOn` reprograms the oracle's first components to the fresh functions and takes
the first components on the slices as the fresh functions. -/
theorem resampleEquivOn_apply (hemb : Function.Injective emb) {ρ : Fin K → S}
    (hρ : Function.Injective ρ) (p : (X → Y) × (Fin K → U → Y₁)) :
    resampleEquivOn e hemb hρ p = (reprogSaltsOn emb e p.1 ρ p.2, slicesOn emb e p.1 ρ) :=
  rfl

end Split

section Condition

variable [Fintype X] [DecidableEq X] [Fintype Y] (emb)

open Classical in
/-- **The oracles that agree with `H₀` outside the range of the embedding.** -/
noncomputable def offRangeClass (H₀ : X → Y) : Finset (X → Y) :=
  Finset.univ.filter fun H => AgreeOffRange emb H H₀

/-- Membership in `offRangeClass emb H₀` is agreement with `H₀` outside the range. -/
theorem mem_offRangeClass {H₀ H : X → Y} : H ∈ offRangeClass emb H₀ ↔ AgreeOffRange emb H H₀ := by
  classical
  simp [offRangeClass]

/-- **The uniform law conditioned on the values outside the range of the embedding**: uniform on
the oracles that agree with `H₀` outside the range. -/
noncomputable def offRangeLaw (H₀ : X → Y) : PMF (X → Y) :=
  PMF.uniformOfFinset (offRangeClass emb H₀)
    (show (offRangeClass emb H₀).Nonempty from ⟨H₀, (mem_offRangeClass emb).2 (.refl H₀)⟩)

variable {emb}

open Classical in
/-- The conditioned law gives each oracle that agrees with `H₀` outside the range the inverse of
their number, and every other oracle `0`. -/
theorem offRangeLaw_apply (H₀ H : X → Y) :
    offRangeLaw emb H₀ H =
      if AgreeOffRange emb H H₀ then ((offRangeClass emb H₀).card : ℝ≥0∞)⁻¹ else 0 := by
  rw [offRangeLaw, PMF.uniformOfFinset_apply]
  simp only [mem_offRangeClass]

/-- Two oracles that agree outside the range have the same class. -/
theorem offRangeClass_eq {H₀ H : X → Y} (h : AgreeOffRange emb H H₀) :
    offRangeClass emb H = offRangeClass emb H₀ := by
  ext H'
  simp only [mem_offRangeClass]
  exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

variable (emb) (e : Y ≃ Y₁ × Y₂)

open Classical in
/-- **The oracles that agree with `H₀` outside the range of the embedding and have its second
components everywhere.** -/
noncomputable def offRangeClassOn (H₀ : X → Y) : Finset (X → Y) :=
  Finset.univ.filter fun H => AgreeOffRangeOn emb e H H₀

/-- Membership in `offRangeClassOn emb e H₀` is `AgreeOffRangeOn` with `H₀`. -/
theorem mem_offRangeClassOn {H₀ H : X → Y} :
    H ∈ offRangeClassOn emb e H₀ ↔ AgreeOffRangeOn emb e H H₀ := by
  classical
  simp [offRangeClassOn]

/-- **The uniform law conditioned on the values outside the range of the embedding and the
second components everywhere**: uniform on the oracles that agree with `H₀` outside the range and
have its second components. -/
noncomputable def offRangeLawOn (H₀ : X → Y) : PMF (X → Y) :=
  PMF.uniformOfFinset (offRangeClassOn emb e H₀)
    (show (offRangeClassOn emb e H₀).Nonempty from
      ⟨H₀, (mem_offRangeClassOn emb e).2 (.refl H₀)⟩)

variable {emb e}

open Classical in
/-- The conditioned law gives each oracle in the class of `H₀` the inverse of the class's size,
and every other oracle `0`. -/
theorem offRangeLawOn_apply (H₀ H : X → Y) :
    offRangeLawOn emb e H₀ H =
      if AgreeOffRangeOn emb e H H₀ then ((offRangeClassOn emb e H₀).card : ℝ≥0∞)⁻¹ else 0 := by
  rw [offRangeLawOn, PMF.uniformOfFinset_apply]
  simp only [mem_offRangeClassOn]

/-- Two oracles related by `AgreeOffRangeOn` have the same class. -/
theorem offRangeClassOn_eq {H₀ H : X → Y} (h : AgreeOffRangeOn emb e H H₀) :
    offRangeClassOn emb e H = offRangeClassOn emb e H₀ := by
  ext H'
  simp only [mem_offRangeClassOn]
  exact ⟨fun h' => h'.trans h, fun h' => h'.trans h.symm⟩

/-- **The conditioned law is uniform in the first components on the range of the
embedding.** -/
theorem isUniformOnRangeOn_offRangeLawOn (H₀ : X → Y) :
    IsUniformOnRangeOn emb e (offRangeLawOn emb e H₀) :=
  fun H H' h => by
    classical
    have : AgreeOffRangeOn emb e H H₀ ↔ AgreeOffRangeOn emb e H' H₀ :=
      ⟨fun h' => h.symm.trans h', fun h' => h.trans h'⟩
    simp only [offRangeLawOn_apply, this]

/-- **The conditioned law is supported on the class of `H₀`.** -/
theorem agreeOffRangeOn_of_offRangeLawOn_ne_zero {H₀ H : X → Y}
    (h : offRangeLawOn emb e H₀ H ≠ 0) : AgreeOffRangeOn emb e H H₀ :=
  (mem_offRangeClassOn emb e).1 ((PMF.mem_support_uniformOfFinset_iff _ _).1 h)

/-- At the split with a trivial second component, the classes are those of `offRangeClass`. -/
theorem offRangeClass_eq_offRangeClassOn (H₀ : X → Y) :
    offRangeClass emb H₀ = offRangeClassOn emb (wholeSplit Y) H₀ := by
  ext H
  rw [mem_offRangeClass, mem_offRangeClassOn, agreeOffRangeOn_wholeSplit_iff]

/-- At the split with a trivial second component, the conditioned law is `offRangeLaw`. -/
theorem offRangeLaw_eq_offRangeLawOn (H₀ : X → Y) :
    offRangeLaw emb H₀ = offRangeLawOn emb (wholeSplit Y) H₀ := by
  classical
  ext H
  rw [offRangeLaw_apply, offRangeLawOn_apply, offRangeClass_eq_offRangeClassOn]
  simp only [agreeOffRangeOn_wholeSplit_iff]

/-- **Conditioning on the values outside the range of the embedding and the second components
everywhere**: an average over the uniform oracle is the average, over a uniform `H₀`, of the
average over the class of `H₀`. -/
theorem sum_uniform_eq_sum_offRangeLawOn [Nonempty Y] (f : (X → Y) → ℝ) :
    ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * f H =
      ∑ H₀, (PMF.uniformOfFintype (X → Y) H₀).toReal *
        ∑ H, (offRangeLawOn emb e H₀ H).toReal * f H := by
  classical
  let c : (X → Y) → ℝ := fun H => ((offRangeClassOn emb e H).card : ℝ)
  have hc0 : ∀ H, c H ≠ 0 := fun H => Nat.cast_ne_zero.2 (Finset.card_ne_zero.2
    ⟨H, (mem_offRangeClassOn emb e).2 (.refl H)⟩)
  have hlaw : ∀ H₀ H, (offRangeLawOn emb e H₀ H).toReal =
      if AgreeOffRangeOn emb e H H₀ then (c H₀)⁻¹ else 0 := fun H₀ H => by
    rw [offRangeLawOn_apply]
    split_ifs
    · rw [ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · rfl
  simp only [PMF.uniformOfFintype_apply, hlaw, Finset.mul_sum]
  rw [Finset.sum_comm]
  set u : ℝ := ((Fintype.card (X → Y) : ℝ≥0∞)⁻¹).toReal
  refine Finset.sum_congr rfl fun H _ => ?_
  have hterm : ∀ H₀, u * ((if AgreeOffRangeOn emb e H H₀ then (c H₀)⁻¹ else 0) * f H) =
      if AgreeOffRangeOn emb e H₀ H then u * (c H)⁻¹ * f H else 0 := fun H₀ => by
    by_cases h : AgreeOffRangeOn emb e H H₀
    · rw [if_pos h, if_pos h.symm, show c H₀ = c H from by
        simp only [c, offRangeClassOn_eq h]]
      ring
    · rw [if_neg h, if_neg fun h' => h h'.symm]
      ring
  simp only [hterm]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.filter fun H₀ => AgreeOffRangeOn emb e H₀ H).card : ℝ) = c H := by
    simp only [c, offRangeClassOn]
  rw [hcard]
  field_simp [hc0 H]

/-- **The conditioned law is uniform on the range of the embedding.** -/
theorem isUniformOnRange_offRangeLaw (H₀ : X → Y) : IsUniformOnRange emb (offRangeLaw emb H₀) := by
  rw [offRangeLaw_eq_offRangeLawOn]
  exact isUniformOnRangeOn_wholeSplit_iff.1 (isUniformOnRangeOn_offRangeLawOn H₀)

/-- **The conditioned law is supported on the oracles that agree with `H₀` outside the
range.** -/
theorem agreeOffRange_of_offRangeLaw_ne_zero {H₀ H : X → Y} (h : offRangeLaw emb H₀ H ≠ 0) :
    AgreeOffRange emb H H₀ := by
  rw [offRangeLaw_eq_offRangeLawOn] at h
  exact agreeOffRangeOn_wholeSplit_iff.1 (agreeOffRangeOn_of_offRangeLawOn_ne_zero h)

variable [Nonempty Y]

/-- **Conditioning on the values outside the range of the embedding**: an average over the
uniform oracle is the average, over a uniform `H₀`, of the average over the oracles that agree
with `H₀` outside the range. -/
theorem sum_uniform_eq_sum_offRangeLaw (f : (X → Y) → ℝ) :
    ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * f H =
      ∑ H₀, (PMF.uniformOfFintype (X → Y) H₀).toReal *
        ∑ H, (offRangeLaw emb H₀ H).toReal * f H := by
  simp only [offRangeLaw_eq_offRangeLawOn]
  exact sum_uniform_eq_sum_offRangeLawOn f

end Condition

variable [Fintype U] [DecidableEq U] [Fintype Y₁] [Nonempty Y₁]

/-- **The product of two laws**: `a ← p` and `b ← q`, independently. -/
noncomputable def prodLaw {α β : Type*} (p : PMF α) (q : PMF β) : PMF (α × β) :=
  p.bind fun a => q.map fun b => (a, b)

open Classical in
/-- The law of `(a, b)` for `b ← ν` at `(a', b)`: `ν b` if `a' = a`, and `0` otherwise. -/
theorem map_pair_apply {α β : Type*} (ν : PMF β) (a a' : α) (b : β) :
    (ν.map fun b' => (a, b')) (a', b) = if a' = a then ν b else 0 := by
  rw [PMF.map_apply]
  by_cases h : a' = a
  · subst h
    simp
  · rw [if_neg h]
    exact ENNReal.tsum_eq_zero.2 fun b' => if_neg fun e => h (Prod.ext_iff.1 e).1

/-- The product law at a pair is the product of the probabilities. -/
theorem prodLaw_apply {α β : Type*} (p : PMF α) (q : PMF β) (a : α) (b : β) :
    prodLaw p q (a, b) = p a * q b := by
  classical
  rw [prodLaw, PMF.bind_apply, tsum_eq_single a fun a' ha' => by
    rw [map_pair_apply, if_neg (Ne.symm ha'), mul_zero]]
  rw [map_pair_apply, if_pos rfl]

/-- The law of the oracle, the fresh functions and the other coins: `μH`, uniform, and `ζ`,
independently. -/
noncomputable def vLaw (μH : PMF (X → Y)) (ζ : PMF C) : PMF ((X → Y) × (Fin K → U → Y₁) × C) :=
  prodLaw μH (prodLaw (PMF.uniformOfFintype (Fin K → U → Y₁)) ζ)

/-- **The law of the tape of a salted game**: `vLaw μH ζ` and the salts `ρ ← ν`,
independently. -/
noncomputable def saltLaw (μH : PMF (X → Y)) (ζ : PMF C) (ν : PMF (Fin K → S)) :
    PMF (SaltTapeOn X S U Y Y₁ C K) :=
  prodLaw (vLaw μH ζ) ν

/-- The law of the tape at `(v, ρ)` is `vLaw μH ζ v * ν ρ`. -/
theorem saltLaw_apply (μH : PMF (X → Y)) (ζ : PMF C) (ν : PMF (Fin K → S))
    (v : (X → Y) × (Fin K → U → Y₁) × C) (ρ : Fin K → S) :
    saltLaw μH ζ ν (v, ρ) = vLaw μH ζ v * ν ρ :=
  prodLaw_apply _ _ _ _

/-- `vLaw μH ζ` at `(H, Z, c)` is `μH H` times the uniform probability of `Z` times `ζ c`. -/
theorem vLaw_apply (μH : PMF (X → Y)) (ζ : PMF C) (H : X → Y) (Z : Fin K → U → Y₁) (c : C) :
    vLaw μH ζ (H, Z, c) = μH H * ((Fintype.card (Fin K → U → Y₁) : ℝ≥0∞)⁻¹ * ζ c) := by
  rw [vLaw, prodLaw_apply, prodLaw_apply, PMF.uniformOfFintype_apply]

variable (emb) (e : Y ≃ Y₁ × Y₂) (ans : C → Fin Q → Req → (Fin K → U → Y) → (X → Y) → Option A)
  (ans₁ : C → Fin Q → Req → (Fin K → U → Y₁) → (X → Y) → Option A)
  (μH : PMF (X → Y)) (ζ : PMF C) (ν : PMF (Fin K → S))

/-- **The salted challenger reading first components** (the real game for a split
`e : Y ≃ Y₁ × Y₂`): as `saltEnv`, with the first components `g = slicesOn emb e H ρ` of the
oracle's values on the slices in place of the values. -/
noncomputable def saltEnvOn : Env (SaltTapeOn X S U Y Y₁ C K) Req A X Y Q where
  μ := saltLaw μH ζ ν
  oracle₀ ω := ω.1.1
  respond ω j req s := ⟨ans₁ ω.1.2.2 j req (slicesOn emb e ω.1.1 ω.2) ω.1.1, s⟩

/-- **The fresh challenger** (the ideal game): as `saltEnv`, with the fresh functions `Z` in place
of the oracle's values on the slices; the fresh functions take values in any `Y₁`. -/
noncomputable def freshEnv : Env (SaltTapeOn X S U Y Y₁ C K) Req A X Y Q where
  μ := saltLaw μH ζ ν
  oracle₀ ω := ω.1.1
  respond ω j req s := ⟨ans₁ ω.1.2.2 j req ω.1.2.1 ω.1.1, s⟩

/-- **The challenger reprogramming first components**: the adversary's oracle with its first
components reprogrammed on the slices of the salts to the fresh functions (`reprogSaltsOn`), and
the answers of the fresh challenger. -/
noncomputable def reprogEnvOn : Env (SaltTapeOn X S U Y Y₁ C K) Req A X Y Q where
  μ := saltLaw μH ζ ν
  oracle₀ ω := reprogSaltsOn emb e ω.1.1 ω.2 ω.1.2.1
  respond ω j req s := ⟨ans₁ ω.1.2.2 j req ω.1.2.1 ω.1.1, s⟩

/-- The fresh challenger's requests never change the oracle. -/
theorem keepsState_freshEnv : (freshEnv (Q := Q) ans₁ μH ζ ν).KeepsState := fun _ _ _ _ => rfl
/-- The salted challenger reading first components never changes the oracle. -/
theorem keepsState_saltEnvOn : (saltEnvOn (Q := Q) emb e ans₁ μH ζ ν).KeepsState :=
  fun _ _ _ _ => rfl
/-- The challenger reprogramming first components never changes the oracle. -/
theorem keepsState_reprogEnvOn : (reprogEnvOn (Q := Q) emb e ans₁ μH ζ ν).KeepsState :=
  fun _ _ _ _ => rfl

section Whole

variable [Fintype Y] [Nonempty Y]

/-- **The salted challenger** (the real game): the adversary's oracle is the random oracle `H`,
and the answer to request number `j` is `ans c j req g H`, from the other coins `c`, the request,
the oracle's values `g = slices emb H ρ` on the slices of the `K` salts `ρ`, and the oracle; the
salts enter only through `g`. Its requests never change the oracle (`keepsState_saltEnv`). -/
noncomputable def saltEnv : Env (SaltTape X S U Y C K) Req A X Y Q where
  μ := saltLaw μH ζ ν
  oracle₀ ω := ω.1.1
  respond ω j req s := ⟨ans ω.1.2.2 j req (slices emb ω.1.1 ω.2) ω.1.1, s⟩

/-- **The reprogramming challenger**: the adversary's oracle reprogrammed on the slices of the
salts to the fresh functions (`reprogSalts`), and the answers of the fresh challenger. For distinct
salts, averaged over the oracle, the fresh functions and the other coins, it has the acceptance
probability of the salted challenger (`sum_vLaw_saltEnv_eq`). -/
noncomputable def reprogEnv : Env (SaltTape X S U Y C K) Req A X Y Q where
  μ := saltLaw μH ζ ν
  oracle₀ ω := reprogSalts emb ω.1.1 ω.2 ω.1.2.1
  respond ω j req s := ⟨ans ω.1.2.2 j req ω.1.2.1 ω.1.1, s⟩

/-- The salted challenger is the one reading first components at the split with a trivial second
component. -/
theorem saltEnv_eq_saltEnvOn :
    saltEnv (Q := Q) emb ans μH ζ ν = saltEnvOn emb (wholeSplit Y) ans μH ζ ν :=
  rfl

/-- The reprogramming challenger is the one reprogramming first components at the split with a
trivial second component. -/
theorem reprogEnv_eq_reprogEnvOn :
    reprogEnv (Q := Q) emb ans μH ζ ν = reprogEnvOn emb (wholeSplit Y) ans μH ζ ν :=
  rfl

/-- The salted challenger's requests never change the oracle. -/
theorem keepsState_saltEnv : (saltEnv (Q := Q) emb ans μH ζ ν).KeepsState := fun _ _ _ _ => rfl
/-- The reprogramming challenger's requests never change the oracle. -/
theorem keepsState_reprogEnv : (reprogEnv (Q := Q) emb ans μH ζ ν).KeepsState :=
  fun _ _ _ _ => rfl

end Whole

end Salt

/-! ### Independent salts of bounded point probability -/

section Pi

open MeasureTheory

/-- **A cylinder event of independent coordinates**: the probability that every coordinate lies
in its set is the product of the probabilities. -/
theorem toOuterMeasure_pi_cylinder {ι : Type*} [Fintype ι] [DecidableEq ι] {β : ι → Type*}
    [∀ i, Fintype (β i)] (p : ∀ i, PMF (β i)) (A : ∀ i, Set (β i)) :
    (PMF.pi p).toOuterMeasure {f | ∀ i, f i ∈ A i} = ∏ i, (p i).toOuterMeasure (A i) := by
  classical
  simp only [PMF.toOuterMeasure_apply_fintype]
  rw [Fintype.prod_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  by_cases hf : ∀ i, f i ∈ A i
  · rw [Set.indicator_of_mem (show f ∈ {f | ∀ i, f i ∈ A i} from hf)]
    exact Finset.prod_congr rfl fun i _ => (Set.indicator_of_mem (hf i) _).symm
  · rw [Set.indicator_of_notMem (show f ∉ {f | ∀ i, f i ∈ A i} from hf)]
    push Not at hf
    obtain ⟨i, hi⟩ := hf
    exact (Finset.prod_eq_zero (Finset.mem_univ i) (Set.indicator_of_notMem hi _)).symm


section Const

variable {S : Type*} [Fintype S] [DecidableEq S] {K : ℕ}

/-- The law of one coordinate of independent coordinates. -/
theorem toOuterMeasure_pi_coord (p : Fin K → PMF S) (i : Fin K) (s : S) :
    (PMF.pi p).toOuterMeasure {ρ | ρ i = s} = p i s := by
  classical
  have h := toOuterMeasure_pi_cylinder p fun k => if k = i then {s} else Set.univ
  have hset : {f : Fin K → S | ∀ k, f k ∈ (if k = i then {s} else Set.univ : Set S)} =
      {ρ | ρ i = s} := by
    ext f
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hf
      simpa using hf i
    · intro hf k
      split_ifs with hk
      · subst hk; simpa using hf
      · trivial
  rw [hset] at h
  rw [h, Finset.prod_eq_single i (fun k _ hk => by simp [hk, PMF.sum_coe])
    (fun h => absurd (mem_univ i) h)]
  simp

/-- The law of two coordinates of independent coordinates at one point. -/
theorem toOuterMeasure_pi_pair (p : Fin K → PMF S) {i j : Fin K} (hij : j ≠ i) (s : S) :
    (PMF.pi p).toOuterMeasure {ρ | ρ j = s ∧ ρ i = s} = p j s * p i s := by
  classical
  have h := toOuterMeasure_pi_cylinder p fun k => if k = j ∨ k = i then {s} else Set.univ
  have hset : {f : Fin K → S | ∀ k, f k ∈ (if k = j ∨ k = i then {s} else Set.univ : Set S)} =
      {ρ | ρ j = s ∧ ρ i = s} := by
    ext f
    simp only [Set.mem_setOf_eq]
    constructor
    · intro hf
      exact ⟨by simpa using hf j, by simpa using hf i⟩
    · rintro ⟨h1, h2⟩ k
      split_ifs with hk
      · rcases hk with rfl | rfl <;> simpa
      · trivial
  rw [hset] at h
  rw [h, ← Finset.prod_subset (Finset.subset_univ {j, i}) (fun k _ hk => by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    simp [hk, PMF.sum_coe]), Finset.prod_pair hij]
  simp

/-- **A given point is one of `K` independent salts** with probability at most `K δ`, for salts
whose point probabilities are at most `δ` (min-entropy `κ`: `δ = 2^{-κ}`). -/
theorem toReal_pi_exists_eq_le (p : Fin K → PMF S) {δ : ℝ} (hδ : ∀ i s, (p i s).toReal ≤ δ)
    (s : S) : ((PMF.pi p).toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ K * δ := by
  have hU : {ρ : Fin K → S | ∃ i, ρ i = s} =
      ⋃ i ∈ (Finset.univ : Finset (Fin K)), {ρ | ρ i = s} := by
    ext ρ; simp
  have hle : (PMF.pi p).toOuterMeasure {ρ | ∃ i, ρ i = s} ≤ ∑ i, p i s := by
    rw [hU]
    refine (measure_biUnion_finset_le _ _).trans_eq ?_
    simp only [toOuterMeasure_pi_coord]
  have hfin : ∑ i, p i s ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => PMF.apply_ne_top _ _
  refine (ENNReal.toReal_mono hfin hle).trans ?_
  rw [ENNReal.toReal_sum fun i _ => PMF.apply_ne_top _ _]
  calc ∑ i, (p i s).toReal ≤ ∑ _i : Fin K, δ := Finset.sum_le_sum fun i _ => hδ i s
    _ = K * δ := by simp

/-- **Two of `K` independent salts collide** with probability at most `C(K, 2) δ`, for salts
whose point probabilities are at most `δ`. -/
theorem toReal_pi_not_injective_le (p : Fin K → PMF S) {δ : ℝ}
    (hδ : ∀ i s, (p i s).toReal ≤ δ) :
    ((PMF.pi p).toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal ≤ K.choose 2 * δ := by
  classical
  have hsub : {ρ : Fin K → S | ¬ Function.Injective ρ} ⊆
      ⋃ i ∈ (Finset.univ : Finset (Fin K)), ⋃ j ∈ Finset.Iio i,
        ⋃ s ∈ (Finset.univ : Finset S), {ρ | ρ j = s ∧ ρ i = s} := by
    intro ρ hρ
    simp only [Function.Injective, not_forall] at hρ
    obtain ⟨a, b, hab, hne⟩ := hρ
    rcases lt_or_gt_of_ne hne with h | h
    · exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ b)) (Set.mem_biUnion
        (Finset.mem_coe.2 (Finset.mem_Iio.2 h)) (Set.mem_biUnion
          (Finset.mem_coe.2 (Finset.mem_univ (ρ a))) ⟨rfl, hab.symm⟩))
    · exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ a)) (Set.mem_biUnion
        (Finset.mem_coe.2 (Finset.mem_Iio.2 h)) (Set.mem_biUnion
          (Finset.mem_coe.2 (Finset.mem_univ (ρ b))) ⟨rfl, hab⟩))
  have hle : (PMF.pi p).toOuterMeasure {ρ | ¬ Function.Injective ρ} ≤
      ∑ i, ∑ j ∈ Finset.Iio i, ∑ s, p j s * p i s := by
    refine (measure_mono hsub).trans ((measure_biUnion_finset_le _ _).trans
      (Finset.sum_le_sum fun i _ => (measure_biUnion_finset_le _ _).trans
        (Finset.sum_le_sum fun j hj => (measure_biUnion_finset_le _ _).trans_eq
          (Finset.sum_congr rfl fun s _ => toOuterMeasure_pi_pair p
            (ne_of_lt (Finset.mem_Iio.1 hj)) s))))
  have hfin : ∀ i j s, p j s * p i s ≠ ⊤ := fun i j s =>
    ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)
  refine (ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun i _ => ENNReal.sum_ne_top.2 fun j _ =>
    ENNReal.sum_ne_top.2 fun s _ => hfin i j s) hle).trans ?_
  simp only [ENNReal.toReal_sum fun _ _ => ENNReal.sum_ne_top.2 fun _ _ =>
    ENNReal.sum_ne_top.2 fun _ _ => hfin _ _ _, ENNReal.toReal_sum fun _ _ =>
    ENNReal.sum_ne_top.2 fun _ _ => hfin _ _ _, ENNReal.toReal_sum fun _ _ => hfin _ _ _,
    ENNReal.toReal_mul]
  have hpair : ∀ i j : Fin K, ∑ s, (p j s).toReal * (p i s).toReal ≤ δ := fun i j =>
    calc ∑ s, (p j s).toReal * (p i s).toReal ≤ ∑ s, δ * (p i s).toReal :=
          Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hδ j s) ENNReal.toReal_nonneg
      _ = δ := by rw [← Finset.mul_sum, PMF.sum_toReal, mul_one]
  calc ∑ i, ∑ j ∈ Finset.Iio i, ∑ s, (p j s).toReal * (p i s).toReal
      ≤ ∑ i : Fin K, ∑ _j ∈ Finset.Iio i, δ :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hpair i j
    _ = K.choose 2 * δ := by
      simp only [Finset.sum_const, Fin.card_Iio, nsmul_eq_mul]
      rw [← Finset.sum_mul]
      congr 1
      rw [Nat.choose_two_right, ← Finset.sum_range_id, ← Fin.sum_univ_eq_sum_range]
      push_cast
      rfl

end Const

end Pi

/-! ### The bound -/

namespace Distinguisher

variable {X S U Y Req A C W : Type*} [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S] [Fintype U]
  [DecidableEq U] [Fintype Y] [Nonempty Y] [AddGroup Y] [Fintype C] [Fintype W] [Fintype Req]
  [Fintype A] [DecidableEq Req] [DecidableEq A] {K Q n m : ℕ}
  (D : Distinguisher W X Y Req A n m) {emb : S × U → X}
  {Y₁ Y₂ : Type*} [Fintype Y₁] [Nonempty Y₁] (e : Y ≃ Y₁ × Y₂)
  (ans : C → Fin Q → Req → (Fin K → U → Y) → (X → Y) → Option A)
  (ans₁ : C → Fin Q → Req → (Fin K → U → Y₁) → (X → Y) → Option A) (μH : PMF (X → Y)) (ζ : PMF C)
  (ν : PMF (Fin K → S))

omit [Fintype X] [DecidableEq X] [DecidableEq S] [DecidableEq U] [Fintype Y] [Nonempty Y] [AddGroup Y]
  [Fintype C] in
/-- **A point is on a slice of the salts** with probability at most `max ε 0`, for an injective
embedding and `ε` bounding the probability that a given point of `S` is a salt. -/
theorem toReal_saltSet_le (hemb : Function.Injective emb) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) (x : X) :
    (ν.toOuterMeasure {ρ | x ∈ saltSet emb ρ}).toReal ≤ max ε 0 := by
  by_cases hx : x ∈ Set.range emb
  · obtain ⟨⟨s, u⟩, rfl⟩ := hx
    have hset : {ρ : Fin K → S | emb (s, u) ∈ saltSet emb ρ} = {ρ | ∃ i, ρ i = s} := by
      ext ρ
      simp only [saltSet, Set.mem_setOf_eq]
      constructor
      · rintro ⟨p, hp⟩
        exact ⟨p.1, (Prod.ext_iff.1 (hemb hp)).1⟩
      · rintro ⟨i, hi⟩
        exact ⟨(i, u), by rw [hi]⟩
    rw [hset]
    exact (hε s).trans (le_max_left _ _)
  · have hset : {ρ : Fin K → S | x ∈ saltSet emb ρ} = ∅ := by
      ext ρ
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      exact notMem_saltSet_of_notMem_range hx
    rw [hset, MeasureTheory.measure_empty, ENNReal.toReal_zero]
    exact le_max_right _ _

/-- `√(n ε)` is unchanged when a negative `ε` is replaced by `0`. -/
theorem sqrt_mul_max_zero (n : ℕ) (ε : ℝ) : √(n * max ε 0) = √(n * ε) := by
  rcases le_total 0 ε with h | h
  · rw [max_eq_left h]
  · rw [max_eq_right h, mul_zero, Real.sqrt_zero, eq_comm, Real.sqrt_eq_zero']
    exact mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg n) h

omit [DecidableEq S] [Nonempty Y] in
/-- **One-way to hiding over the whole run, for the reprogrammed first components** (Ambainis,
Hamburg, Unruh, CRYPTO 2019, Theorem 3, via `advantage_acceptProb_le_of_fresh_secret_budget`),
for an injective embedding and a split `e : Y ≃ Y₁ × Y₂`: the fresh challenger and the
challenger reprogramming first components answer alike and their oracles differ only on the
slices of the salts, which neither the fresh challenger's oracle nor its answers read; a
distinguisher with a budget of `q` query slots of `n` parallel queries tells them apart with
advantage at most `2 q √(n ε)`, for `ε` bounding the probability that a given point of `S` is a
salt. -/
theorem advantage_fresh_reprogOn_le (hemb : Function.Injective emb) {q : ℕ} (bud : D.Budget q)
    {ε : ℝ} (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) :
    GordieHowe.advantage (D.acceptProb (freshEnv ans₁ μH ζ ν) noPost)
      (D.acceptProb (reprogEnvOn emb e ans₁ μH ζ ν) noPost) ≤ 2 * q * √(n * ε) := by
  rw [← sqrt_mul_max_zero]
  refine D.advantage_acceptProb_le_of_fresh_secret_budget bud (freshEnv ans₁ μH ζ ν)
    (reprogEnvOn emb e ans₁ μH ζ ν) (μV := vLaw μH ζ) (ν := ν) (T := saltSet emb)
    (fun v σ => saltLaw_apply μH ζ ν v σ) rfl (fun ω rs req => rfl) (fun ω rs x hx => ?_)
    (fun v σ σ' rs => ?_) (fun v σ σ' rs req => rfl) (toReal_saltSet_le ν hemb hε)
  · rw [Env.oracleIn_of_keepsState (keepsState_freshEnv ans₁ μH ζ ν),
      Env.oracleIn_of_keepsState (keepsState_reprogEnvOn emb e ans₁ μH ζ ν)]
    exact (reprogSaltsOn_of_notMem _ hx).symm
  · rw [Env.oracleIn_of_keepsState (keepsState_freshEnv ans₁ μH ζ ν),
      Env.oracleIn_of_keepsState (keepsState_freshEnv ans₁ μH ζ ν)]
    rfl

omit [DecidableEq S] in
/-- **One-way to hiding over the whole run, for the reprogrammed slices**:
`advantage_fresh_reprogOn_le` at the split with a trivial second component. -/
theorem advantage_fresh_reprog_le (hemb : Function.Injective emb) {q : ℕ} (bud : D.Budget q)
    {ε : ℝ} (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) :
    GordieHowe.advantage (D.acceptProb (freshEnv ans μH ζ ν) noPost)
      (D.acceptProb (reprogEnv emb ans μH ζ ν) noPost) ≤ 2 * q * √(n * ε) :=
  D.advantage_fresh_reprogOn_le (wholeSplit Y) ans μH ζ ν hemb bud hε

variable (post : (X → Y) → QState (DReg W n X Y Req A) ≃ₗᵢ[ℂ] QState (DReg W n X Y Req A))

omit [DecidableEq X] [Fintype S] [DecidableEq S] [Fintype C] [Nonempty Y] in
/-- The salted challenger reading first components at the fresh functions `Z` is the fresh
challenger at the first components on the slices in place of `Z`. -/
theorem acceptProbAt_saltEnvOn (H : X → Y) (Z : Fin K → U → Y₁) (c : C) (ρ : Fin K → S) :
    D.acceptProbAt (saltEnvOn emb e ans₁ μH ζ ν) post ((H, Z, c), ρ) =
      D.acceptProbAt (freshEnv ans₁ μH ζ ν) post ((H, slicesOn emb e H ρ, c), ρ) :=
  D.acceptProbAt_congr _ _ (fun _ _ => rfl) (fun lg => by
    simp only [Env.oracle, Env.oracleIn_of_keepsState (keepsState_saltEnvOn emb e ans₁ μH ζ ν)])
    post

omit [DecidableEq X] [Fintype S] [DecidableEq S] [Fintype C] in
/-- The salted challenger at the fresh functions `Z` is the fresh challenger at the oracle's
slices in place of `Z`. -/
theorem acceptProbAt_saltEnv (H : X → Y) (Z : Fin K → U → Y) (c : C) (ρ : Fin K → S) :
    D.acceptProbAt (saltEnv emb ans μH ζ ν) post ((H, Z, c), ρ) =
      D.acceptProbAt (freshEnv ans μH ζ ν) post ((H, slices emb H ρ, c), ρ) :=
  D.acceptProbAt_saltEnvOn (wholeSplit Y) ans μH ζ ν post H Z c ρ

omit [DecidableEq X] [Fintype S] [DecidableEq S] [Fintype C] [Nonempty Y] in
/-- For answers that read the oracle's first components only outside the range, the
challenger reprogramming first components at the oracle `H` is the fresh challenger at the
reprogrammed oracle. -/
theorem acceptProbAt_reprogEnvOn (hans : ReadsOffRangeOn emb e ans₁) (H : X → Y)
    (Z : Fin K → U → Y₁) (c : C) (ρ : Fin K → S) :
    D.acceptProbAt (reprogEnvOn emb e ans₁ μH ζ ν) post ((H, Z, c), ρ) =
      D.acceptProbAt (freshEnv ans₁ μH ζ ν) post ((reprogSaltsOn emb e H ρ Z, Z, c), ρ) := by
  have hA : ∀ rs req, (reprogEnvOn emb e ans₁ μH ζ ν).answerAfter ((H, Z, c), ρ) rs req =
      (freshEnv ans₁ μH ζ ν).answerAfter ((reprogSaltsOn emb e H ρ Z, Z, c), ρ) rs req :=
    fun rs req => by
      simp only [Env.answerAfter, reprogEnvOn, freshEnv]
      split_ifs
      · exact hans _ _ _ _ _ _ (agreeOffRangeOn_reprogSaltsOn H ρ Z).symm
      · rfl
  refine D.acceptProbAt_congr _ _ (fun lg k => by
    unfold Env.answer
    exact congrArg ((lg k).elim none) (funext (hA _))) (fun lg => by
    simp only [Env.oracle, Env.oracleIn_of_keepsState (keepsState_reprogEnvOn emb e ans₁ μH ζ ν),
      Env.oracleIn_of_keepsState (keepsState_freshEnv ans₁ μH ζ ν)]
    rfl) post

omit [DecidableEq X] [Fintype S] [DecidableEq S] [Fintype C] in
/-- For answers that read the oracle only outside the range, the reprogramming challenger at
the oracle `H` is the fresh challenger at the reprogrammed oracle. -/
theorem acceptProbAt_reprogEnv (hans : ReadsOffRange emb ans) (H : X → Y) (Z : Fin K → U → Y)
    (c : C) (ρ : Fin K → S) :
    D.acceptProbAt (reprogEnv emb ans μH ζ ν) post ((H, Z, c), ρ) =
      D.acceptProbAt (freshEnv ans μH ζ ν) post ((reprogSalts emb H ρ Z, Z, c), ρ) :=
  D.acceptProbAt_reprogEnvOn (wholeSplit Y) ans μH ζ ν post hans.readsOffRangeOn H Z c ρ

omit [Fintype S] [DecidableEq S] [Nonempty Y] in
/-- **For distinct salts, reading the first components at the salts is reprogramming them
there**: averaged over the oracle, the fresh functions and the coins, the salted challenger
reading first components and the challenger reprogramming them give the same acceptance
probability at the salts `ρ` (`resampleEquivOn`: exchanging the first components on the slices
with the fresh functions preserves the law, which is uniform in the first components on the
range of the embedding). -/
theorem sum_vLaw_saltEnvOn_eq (hemb : Function.Injective emb) (hμH : IsUniformOnRangeOn emb e μH)
    (hans : ReadsOffRangeOn emb e ans₁) {ρ : Fin K → S} (hρ : Function.Injective ρ) :
    ∑ v, (vLaw μH ζ v).toReal * D.acceptProbAt (saltEnvOn emb e ans₁ μH ζ ν) post (v, ρ) =
      ∑ v, (vLaw μH ζ v).toReal * D.acceptProbAt (reprogEnvOn emb e ans₁ μH ζ ν) post (v, ρ) := by
  set u : ℝ := ((Fintype.card (Fin K → U → Y₁) : ℝ≥0∞)⁻¹).toReal
  have hw : ∀ (H : X → Y) (Z : Fin K → U → Y₁) (c : C),
      (vLaw μH ζ (H, Z, c)).toReal = (μH H).toReal * (u * (ζ c).toReal) := fun H Z c => by
    rw [vLaw_apply, ENNReal.toReal_mul, ENNReal.toReal_mul]
  let eA : ((X → Y) × (Fin K → U → Y₁)) × C ≃ (X → Y) × (Fin K → U → Y₁) × C :=
    Equiv.prodAssoc _ _ _
  have hsum : ∀ (E : Env (SaltTapeOn X S U Y Y₁ C K) Req A X Y Q),
      ∑ v, (vLaw μH ζ v).toReal * D.acceptProbAt E post (v, ρ) =
        ∑ c, ∑ p : (X → Y) × (Fin K → U → Y₁), (u * (ζ c).toReal) *
          ((μH p.1).toReal * D.acceptProbAt E post ((p.1, p.2, c), ρ)) := fun E => by
    rw [← eA.sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun p _ => ?_
    simp only [eA, Equiv.prodAssoc_apply, hw]
    ring
  rw [hsum, hsum]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [← Finset.mul_sum]
  congr 1
  let g : (X → Y) × (Fin K → U → Y₁) → ℝ := fun p =>
    (μH p.1).toReal * D.acceptProbAt (freshEnv ans₁ μH ζ ν) post ((p.1, slicesOn emb e p.1 ρ, c), ρ)
  have h1 : ∀ p : (X → Y) × (Fin K → U → Y₁),
      (μH p.1).toReal * D.acceptProbAt (saltEnvOn emb e ans₁ μH ζ ν) post ((p.1, p.2, c), ρ) =
        g p :=
    fun p => by rw [D.acceptProbAt_saltEnvOn e ans₁ μH ζ ν post p.1 p.2 c ρ]
  have h2 : ∀ p : (X → Y) × (Fin K → U → Y₁),
      (μH p.1).toReal * D.acceptProbAt (reprogEnvOn emb e ans₁ μH ζ ν) post ((p.1, p.2, c), ρ) =
        g (resampleEquivOn e hemb hρ p) := fun p => by
    rw [D.acceptProbAt_reprogEnvOn e ans₁ μH ζ ν post hans p.1 p.2 c ρ,
      resampleEquivOn_apply hemb hρ]
    simp only [g, slicesOn_reprogSaltsOn hemb hρ]
    rw [hμH _ _ (agreeOffRangeOn_reprogSaltsOn p.1 ρ p.2)]
  simp only [h1, h2]
  exact (Equiv.sum_comp (resampleEquivOn e hemb hρ) g).symm

omit [Fintype S] [DecidableEq S] in
/-- **For distinct salts, reading the oracle at the salts is reprogramming it there**:
`sum_vLaw_saltEnvOn_eq` at the split with a trivial second component. -/
theorem sum_vLaw_saltEnv_eq (hemb : Function.Injective emb) (hμH : IsUniformOnRange emb μH)
    (hans : ReadsOffRange emb ans) {ρ : Fin K → S} (hρ : Function.Injective ρ) :
    ∑ v, (vLaw μH ζ v).toReal * D.acceptProbAt (saltEnv emb ans μH ζ ν) post (v, ρ) =
      ∑ v, (vLaw μH ζ v).toReal * D.acceptProbAt (reprogEnv emb ans μH ζ ν) post (v, ρ) :=
  D.sum_vLaw_saltEnvOn_eq (wholeSplit Y) ans μH ζ ν post hemb hμH.isUniformOnRangeOn
    hans.readsOffRangeOn hρ

omit [Nonempty Y] in
/-- **Resampling the first components at distinct salts**: for an injective embedding, an
oracle law uniform in the first components on the range of the embedding given the rest, and
answers that read the first components only outside the range, the acceptance probabilities of
the salted challenger reading first components and the challenger reprogramming them differ by at
most the probability that two salts collide, for every distinguisher and post phase. -/
theorem advantage_saltOn_reprog_le (hemb : Function.Injective emb)
    (hμH : IsUniformOnRangeOn emb e μH) (hans : ReadsOffRangeOn emb e ans₁) :
    GordieHowe.advantage (D.acceptProb (saltEnvOn emb e ans₁ μH ζ ν) post)
      (D.acceptProb (reprogEnvOn emb e ans₁ μH ζ ν) post) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal := by
  classical
  have hsplit : ∀ E : Env (SaltTapeOn X S U Y Y₁ C K) Req A X Y Q, E.μ = saltLaw μH ζ ν →
      D.acceptProb E post =
        ∑ ρ, (ν ρ).toReal * ∑ v, (vLaw μH ζ v).toReal * D.acceptProbAt E post (v, ρ) :=
      fun E hE => by
    rw [acceptProb, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hE, saltLaw_apply, ENNReal.toReal_mul]
    ring
  rw [GordieHowe.advantage, hsplit _ rfl, hsplit _ rfl, ← Finset.sum_sub_distrib,
    PMF.toReal_toOuterMeasure_apply]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun ρ _ => ?_)
  rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  by_cases hρ : Function.Injective ρ
  · rw [sum_vLaw_saltEnvOn_eq D e ans₁ μH ζ ν post hemb hμH hans hρ, sub_self, abs_zero,
      mul_zero, if_neg (by simpa)]
  · rw [if_pos (by simpa)]
    refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ v, |(vLaw μH ζ v).toReal * D.acceptProbAt (saltEnvOn emb e ans₁ μH ζ ν) post (v, ρ) -
          (vLaw μH ζ v).toReal * D.acceptProbAt (reprogEnvOn emb e ans₁ μH ζ ν) post (v, ρ)|
        ≤ ∑ v, (vLaw μH ζ v).toReal := Finset.sum_le_sum fun v _ => by
          rw [← mul_sub, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
          refine mul_le_of_le_one_right ENNReal.toReal_nonneg ?_
          have h0 := D.acceptProbOnAt_nonneg post (saltEnvOn emb e ans₁ μH ζ ν) Set.univ (v, ρ)
          have h1 := D.acceptProbOnAt_le_one post (saltEnvOn emb e ans₁ μH ζ ν) Set.univ (v, ρ)
          have h0' := D.acceptProbOnAt_nonneg post (reprogEnvOn emb e ans₁ μH ζ ν) Set.univ (v, ρ)
          have h1' := D.acceptProbOnAt_le_one post (reprogEnvOn emb e ans₁ μH ζ ν) Set.univ (v, ρ)
          rw [acceptProbOnAt_univ] at h0 h1 h0' h1'
          rw [abs_sub_le_iff]
          constructor <;> linarith
      _ = 1 := PMF.sum_toReal _

/-- **Resampling at distinct salts**: `advantage_saltOn_reprog_le` at the split with a trivial
second component. For an injective embedding, an oracle law uniform on the range of the
embedding given the rest, and answers that read the oracle only outside the range, the
acceptance probabilities of the salted and the reprogramming challengers differ by at most the
probability that two salts collide, for every distinguisher and post phase. -/
theorem advantage_salt_reprog_le (hemb : Function.Injective emb) (hμH : IsUniformOnRange emb μH)
    (hans : ReadsOffRange emb ans) :
    GordieHowe.advantage (D.acceptProb (saltEnv emb ans μH ζ ν) post)
      (D.acceptProb (reprogEnv emb ans μH ζ ν) post) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal :=
  D.advantage_saltOn_reprog_le (wholeSplit Y) ans μH ζ ν post hemb hμH.isUniformOnRangeOn
    hans.readsOffRangeOn

omit [Nonempty Y] in
/-- **Reprogramming the first components of the random oracle at hidden fresh salts, over a
whole interaction with quantum memory.** The oracle's values split as `e : Y ≃ Y₁ × Y₂`. A
challenger answers each of `Q` requests with `ans₁ c j req g H` from its coins `c`, the request,
the first components `g` of the random oracle `H` on the slices `emb (ρ i, ·)` of `K` salts
`ρ ← ν` drawn independently of everything else and never revealed, and `H` read in its first
components only outside the range of the injective embedding `emb` (`ReadsOffRangeOn`: the
second components may be read everywhere); the oracle's law is uniform in the first components
on the range of `emb` given the rest (`IsUniformOnRangeOn`). The distinguisher has `H` by quantum
queries, a budget of `q` query slots of `n` parallel queries, and its quantum state across all
slots. Replacing the first components on the slices by independent fresh functions `U → Y₁`
changes its acceptance probability by at most `Pr[two salts collide] + 2 q √(n ε)`, for `ε`
bounding the probability that a given point of `S` is a salt. The proof resamples the first
components at the salts (exact for distinct salts, `advantage_saltOn_reprog_le`) and applies
one-way to hiding (Ambainis, Hamburg, Unruh, CRYPTO 2019, Theorem 3) to the whole run as one
oracle algorithm (`advantage_fresh_reprogOn_le`). -/
theorem advantage_saltOn_fresh_le (hemb : Function.Injective emb)
    (hμH : IsUniformOnRangeOn emb e μH) (hans : ReadsOffRangeOn emb e ans₁) {q : ℕ}
    (bud : D.Budget q) {ε : ℝ} (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) :
    GordieHowe.advantage (D.acceptProb (saltEnvOn emb e ans₁ μH ζ ν) noPost)
      (D.acceptProb (freshEnv ans₁ μH ζ ν) noPost) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * q * √(n * ε) := by
  refine (GordieHowe.advantage_le_add _
    (D.acceptProb (reprogEnvOn emb e ans₁ μH ζ ν) noPost) _).trans ?_
  rw [GordieHowe.advantage_comm (D.acceptProb (reprogEnvOn emb e ans₁ μH ζ ν) noPost)]
  exact add_le_add (D.advantage_saltOn_reprog_le e ans₁ μH ζ ν noPost hemb hμH hans)
    (D.advantage_fresh_reprogOn_le e ans₁ μH ζ ν hemb bud hε)

/-- **Reprogramming the random oracle at hidden fresh salts, over a whole interaction with
quantum memory** (`advantage_saltOn_fresh_le` at the split with a trivial second component). A
challenger answers each of `Q` requests with `ans c j req g H` from its coins
`c`, the request, the values `g` of the random oracle `H` on the slices `emb (ρ i, ·)` of `K`
salts `ρ ← ν` drawn independently of everything else and never revealed, and `H` read only
outside the range of the injective embedding `emb` (`ReadsOffRange`); the oracle's law is uniform
on the range of `emb` given the rest (`IsUniformOnRange`). The distinguisher has `H` by quantum
queries, a budget of `q` query slots of `n` parallel queries, and its quantum state across all
slots. Replacing the values on the slices by independent fresh functions changes its acceptance
probability by at most `Pr[two salts collide] + 2 q √(n ε)`, for `ε` bounding the probability
that a given point of `S` is a salt; for independent salts of min-entropy `κ`, `ε = K 2^{-κ}`
(`toReal_pi_exists_eq_le`). The proof resamples the oracle at the salts (exact for distinct
salts, `advantage_salt_reprog_le`) and applies one-way to hiding (Ambainis, Hamburg, Unruh,
CRYPTO 2019, Theorem 3) to the whole run as one oracle algorithm (`advantage_fresh_reprog_le`).
This is the adaptive reprogramming of Grilo, Hövelmanns, Hülsing and Majenz (ASIACRYPT 2021) for
points `emb (ρ i, u)` with a fresh secret part `ρ i` and a part `u` the challenger chooses
adaptively. This library does not prove the bound of Grilo et al. for salts that are
revealed. -/
theorem advantage_salt_fresh_le (hemb : Function.Injective emb) (hμH : IsUniformOnRange emb μH)
    (hans : ReadsOffRange emb ans) {q : ℕ} (bud : D.Budget q) {ε : ℝ}
    (hε : ∀ s, (ν.toOuterMeasure {ρ | ∃ i, ρ i = s}).toReal ≤ ε) :
    GordieHowe.advantage (D.acceptProb (saltEnv emb ans μH ζ ν) noPost)
      (D.acceptProb (freshEnv ans μH ζ ν) noPost) ≤
        (ν.toOuterMeasure {ρ | ¬ Function.Injective ρ}).toReal + 2 * q * √(n * ε) :=
  D.advantage_saltOn_fresh_le (wholeSplit Y) ans μH ζ ν hemb hμH.isUniformOnRangeOn
    hans.readsOffRangeOn bud hε

omit [Nonempty Y] in
/-- **`advantage_saltOn_fresh_le` for independent salts of min-entropy `κ`**: for salts drawn
independently with point probabilities at most `δ` (`δ = 2^{-κ}`), the advantage is at most
`C(K, 2) δ + 2 q √(n K δ)`. -/
theorem advantage_saltOn_fresh_le_of_pi (hemb : Function.Injective emb)
    (hμH : IsUniformOnRangeOn emb e μH) (hans : ReadsOffRangeOn emb e ans₁) {q : ℕ}
    (bud : D.Budget q) (p : Fin K → PMF S) {δ : ℝ} (hδ : ∀ i s, (p i s).toReal ≤ δ) :
    GordieHowe.advantage (D.acceptProb (saltEnvOn emb e ans₁ μH ζ (PMF.pi p)) noPost)
      (D.acceptProb (freshEnv ans₁ μH ζ (PMF.pi p)) noPost) ≤
        K.choose 2 * δ + 2 * q * √(n * (K * δ)) :=
  (D.advantage_saltOn_fresh_le e ans₁ μH ζ (PMF.pi p) hemb hμH hans bud
    (toReal_pi_exists_eq_le p hδ)).trans (add_le_add (toReal_pi_not_injective_le p hδ) le_rfl)

/-- **`advantage_salt_fresh_le` for independent salts of min-entropy `κ`**: for salts drawn
independently with point probabilities at most `δ` (`δ = 2^{-κ}`), the advantage is at most
`C(K, 2) δ + 2 q √(n K δ)`. -/
theorem advantage_salt_fresh_le_of_pi (hemb : Function.Injective emb)
    (hμH : IsUniformOnRange emb μH) (hans : ReadsOffRange emb ans) {q : ℕ} (bud : D.Budget q)
    (p : Fin K → PMF S) {δ : ℝ} (hδ : ∀ i s, (p i s).toReal ≤ δ) :
    GordieHowe.advantage (D.acceptProb (saltEnv emb ans μH ζ (PMF.pi p)) noPost)
      (D.acceptProb (freshEnv ans μH ζ (PMF.pi p)) noPost) ≤
        K.choose 2 * δ + 2 * q * √(n * (K * δ)) :=
  D.advantage_saltOn_fresh_le_of_pi (wholeSplit Y) ans μH ζ hemb
    hμH.isUniformOnRangeOn hans.readsOffRangeOn bud p hδ

end Distinguisher

end GordieHowe.Quantum
