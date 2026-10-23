-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Headline
public import GordieHowe.SPBCS.WitnessIndist
public import GordieHowe.SPBCS.ProverProg
public import GordieHowe.Foundations.ToMathlib.ListLength

@[expose] public section

/-!
# Witness indistinguishability against adaptively chosen statements of bounded length

CY24 Definition 33.1.1 (pp. 426-427, and p. 430 for the unbounded form) lets the adversary choose
the statement and the two witnesses as a function of the oracle. The spBCS compiler's
`GordieHowe.SPBCS.WitnessIndistinguishable` bounds the advantage of an adversary that chooses, in each
of its `Q` rounds, a triple from a finite set `choices` fixed in advance, at
`Q · wiError δ |choices|`. The set enters the proof only through the salt bound
(`GordieHowe.SPBCS.expect_sup'_fpDist_le`): an expected maximum over a fixed finite index type, which
needs neither independence of the indices nor a small set.

This file takes for `choices` every admissible triple `(x, w₀, w₁)` whose binary encoding has at
most `ℓ` bits in total. Under injective encodings of statements and witnesses there are at most
`choiceCount ℓ = (ℓ + 1)^2 · 2^(ℓ + 1)` such triples (`ncard_admissible_le`), so the adversary of
CY24's adaptive form, restricted to statements and witnesses of total length at most `ℓ`, has
advantage at most `Q · wiError δ (choiceCount ℓ)` (`GordieHowe.SPBCS.unconditionallyWitnessIndistinguishable`), with the
salt term `√(((ℓ + 1) log 2 + 2 log (ℓ + 1)) / (2 · 2^(8 kS)))` (`saltTerm_choiceCount`).
-/

namespace GordieHowe.SPBCS

open scoped ENNReal NNReal

/-- **A binary encoding** of `α`: an injective map to bit strings. Mathlib's
`Computability.Encoding` also asks for a decoder; only injectivity is used here. -/
structure BitEncoding (α : Type) where
  /-- The encoding of an element. -/
  encode : α → List Bool
  /-- Distinct elements have distinct encodings. -/
  encode_injective : Function.Injective encode

namespace WIChoice

variable {X W : Type} (eX : BitEncoding X) (eW : BitEncoding W)

/-- **The encoding length of a choice** `(x, w₀, w₁)`: the total number of bits of the encodings
of the statement and of the two witnesses. -/
def bitLength (c : WIChoice X W) : ℕ :=
  (eX.encode c.stmt).length + (eW.encode c.wit₀).length + (eW.encode c.wit₁).length

/-- **An admissible choice of length at most `ℓ`**: both witnesses are valid for the statement and
the choice has encoding length at most `ℓ`. -/
structure Admissible (rel : Set (X × W)) (ℓ : ℕ) (c : WIChoice X W) : Prop where
  /-- The first witness is valid. -/
  wit₀_mem : (c.stmt, c.wit₀) ∈ rel
  /-- The second witness is valid. -/
  wit₁_mem : (c.stmt, c.wit₁) ∈ rel
  /-- The encoding length is at most `ℓ`. -/
  bitLength_le : c.bitLength eX eW ≤ ℓ

/-- The lengths of the statement's and the first witness's encodings and the concatenation of the
three encodings, from which the choice is recovered (`code_injective`). -/
def code (c : WIChoice X W) : ℕ × ℕ × List Bool :=
  ((eX.encode c.stmt).length, (eW.encode c.wit₀).length,
    eX.encode c.stmt ++ eW.encode c.wit₀ ++ eW.encode c.wit₁)

theorem code_injective : Function.Injective (code eX eW) := by
  rintro ⟨x, w₀, w₁⟩ ⟨x', w₀', w₁'⟩ h
  simp only [code, Prod.mk.injEq] at h
  obtain ⟨hx, hw, happ⟩ := h
  obtain ⟨h01, h2⟩ := List.append_inj happ (by simp [hx, hw])
  obtain ⟨h0, h1⟩ := List.append_inj h01 hx
  rw [eX.encode_injective h0, eW.encode_injective h1, eW.encode_injective h2]

end WIChoice

/-- **The bound on the number of choices of encoding length at most `ℓ`**: `(ℓ + 1)^2` for the
lengths of the statement's and the first witness's encodings, times `2^(ℓ + 1)` for the
concatenated encoding (`ncard_admissible_le`). -/
def choiceCount (ℓ : ℕ) : ℕ := (ℓ + 1) ^ 2 * 2 ^ (ℓ + 1)

section Count

variable {X W : Type} (eX : BitEncoding X) (eW : BitEncoding W) (rel : Set (X × W)) (ℓ : ℕ)

/-- The codes of the admissible choices of length at most `ℓ`. -/
theorem code_mem_of_admissible {c : WIChoice X W} (hc : c.Admissible eX eW rel ℓ) :
    c.code eX eW ∈ ((Finset.range (ℓ + 1) : Set ℕ) ×ˢ (Finset.range (ℓ + 1) : Set ℕ) ×ˢ
      {l : List Bool | l.length ≤ ℓ}) := by
  have := hc.bitLength_le
  unfold WIChoice.bitLength at this
  simp only [WIChoice.code, Set.mem_prod, Finset.coe_range, Set.mem_Iio, Set.mem_ofPred_eq,
    List.length_append]
  omega

/-- **Finitely many choices have encoding length at most `ℓ`.** -/
theorem finite_admissible : {c : WIChoice X W | c.Admissible eX eW rel ℓ}.Finite :=
  Set.Finite.subset (Set.Finite.preimage (WIChoice.code_injective eX eW).injOn
    (Set.Finite.prod (Finset.range (ℓ + 1)).finite_toSet
      (Set.Finite.prod (Finset.range (ℓ + 1)).finite_toSet (List.finite_length_le Bool ℓ))))
    fun _ hc => code_mem_of_admissible eX eW rel ℓ hc

/-- **At most `choiceCount ℓ` choices have encoding length at most `ℓ`.** -/
theorem ncard_admissible_le :
    {c : WIChoice X W | c.Admissible eX eW rel ℓ}.ncard ≤ choiceCount ℓ := by
  have hT := Set.Finite.prod (Finset.range (ℓ + 1)).finite_toSet
    (Set.Finite.prod (Finset.range (ℓ + 1)).finite_toSet (List.finite_length_le Bool ℓ))
  refine (Set.ncard_le_ncard_of_injOn (WIChoice.code eX eW)
    (fun _ hc => code_mem_of_admissible eX eW rel ℓ hc)
    (WIChoice.code_injective eX eW).injOn hT).trans ?_
  rw [Set.ncard_prod, Set.ncard_prod, Set.ncard_coe_finset, Finset.card_range]
  have := List.ncard_length_le_bool ℓ
  unfold choiceCount
  rw [pow_two, mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this.le)

/-- **The admissible choices of encoding length at most `ℓ`**, as a finite set. -/
noncomputable def admissibleChoices : Finset (WIChoice X W) :=
  (finite_admissible eX eW rel ℓ).toFinset

theorem mem_admissibleChoices {c : WIChoice X W} :
    c ∈ admissibleChoices eX eW rel ℓ ↔ c.Admissible eX eW rel ℓ :=
  Set.Finite.mem_toFinset _

theorem card_admissibleChoices_le : (admissibleChoices eX eW rel ℓ).card ≤ choiceCount ℓ := by
  rw [admissibleChoices, ← Set.ncard_eq_toFinset_card _ (finite_admissible eX eW rel ℓ)]
  exact ncard_admissible_le eX eW rel ℓ

end Count

/-- **The salt term at `choiceCount ℓ` choices**:
`√(((ℓ + 1) log 2 + 2 log (ℓ + 1)) / (2 · 2^(8k)))`. -/
theorem saltTerm_choiceCount (k ℓ : ℕ) :
    saltTerm k (choiceCount ℓ) =
      √(((ℓ + 1) * Real.log 2 + 2 * Real.log (ℓ + 1)) / (2 * 2 ^ (8 * k))) := by
  have h1 : ((ℓ : ℝ) + 1) ^ 2 ≠ 0 := by positivity
  have h2 : (2 : ℝ) ^ (ℓ + 1) ≠ 0 := by positivity
  unfold saltTerm choiceCount
  push_cast
  rw [Real.log_mul h1 h2, Real.log_pow, Real.log_pow]
  push_cast
  ring_nf

end GordieHowe.SPBCS

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm
open scoped ENNReal NNReal

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)]
  [∀ j i, Nonempty ((P j).Challenge i)] {X W : Type} {M : SPBCS Mg P X k kN kS L e}

variable (M) in
/-- **An adaptive witness-indistinguishability adversary of encoding length at most `ℓ`** (CY24
Definition 33.1.1, pp. 426-427, for `Q` proof queries): in round `j` it chooses a statement and
two witnesses, both valid and of total encoding length at most `ℓ` under `eX` and `eW`, as a
function of the whole oracle and the earlier proofs. No choice set is fixed in advance. -/
structure WIAdversaryOfLength (eX : SPBCS.BitEncoding X) (eW : SPBCS.BitEncoding W)
    (rel : Set (X × W)) (ℓ Q : ℕ) where
  /-- The choice of round `j` from the oracle and the earlier proofs. -/
  choose : (j : Fin Q) → (Query k kN kS L → Out k e) → (Fin j → M.NIProof) → SPBCS.WIChoice X W
  /-- Every choice is admissible and of encoding length at most `ℓ`. -/
  admissible : ∀ j h πs, (choose j h πs).Admissible eX eW rel ℓ

variable {eX : SPBCS.BitEncoding X} {eW : SPBCS.BitEncoding W} {rel : Set (X × W)} {ℓ Q : ℕ}

/-- The adversary as one choosing from the admissible choices of length at most `ℓ`. -/
noncomputable def WIAdversaryOfLength.toWIAdversary (A : M.WIAdversaryOfLength eX eW rel ℓ Q) :
    M.WIAdversary rel Q where
  choices := SPBCS.admissibleChoices eX eW rel ℓ
  admissible _ hc := by
    have hc := (SPBCS.mem_admissibleChoices eX eW rel ℓ).1 hc
    exact ⟨hc.wit₀_mem, hc.wit₁_mem⟩
  choose := A.choose
  choose_mem j h πs := (SPBCS.mem_admissibleChoices eX eW rel ℓ).2 (A.admissible j h πs)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
theorem WIAdversaryOfLength.card_choices_le (A : M.WIAdversaryOfLength eX eW rel ℓ Q) :
    A.toWIAdversary.choices.card ≤ SPBCS.choiceCount ℓ :=
  SPBCS.card_admissibleChoices_le eX eW rel ℓ

variable (M) in
/-- **The law of the proof of a prover program** at the oracle `h`, the statement `x` and the
witness `w`: the program run against `h` (`NARG.Prover.toFn`) at coins drawn from its coin law, its
proof read as a proof of the compiler. -/
noncomputable def proverProofLaw {B : ℕ} {C : Type}
    (Pv : NARG.Prover (Query k kN kS L) (Out k e) X W (M.BProof B) C)
    (h : Query k kN kS L → Out k e) (x : X) (w : W) : PMF M.NIProof :=
  Pv.coins.map fun c => (Pv.toFn.prove h x w c).val

variable (M) in
/-- **Witness indistinguishability against adaptively chosen statements of encoding length at
most `ℓ`** (CY24 Definition 33.1.1, pp. 426-427, at unbounded queries, p. 430), with `Q` proof queries,
at advantage `ε`, of the prover program `Pv`: against every adversary making `Q` proof queries, each
a statement and two witnesses of `rel` of total encoding length at most `ℓ` chosen as a function of
the whole oracle and the earlier proofs, every distinguisher of the oracle and the proofs has
advantage at most `ε` (`Base.wiAdvantageWith` at the proof laws of `Pv`). -/
def WitnessIndistinguishableOfLength {B : ℕ} {C : Type}
    (Pv : NARG.Prover (Query k kN kS L) (Out k e) X W (M.BProof B) C) (eX : SPBCS.BitEncoding X)
    (eW : SPBCS.BitEncoding W) (rel : Set (X × W)) (Q ℓ : ℕ) (ε : ℝ) : Prop :=
  ∀ A : M.WIAdversaryOfLength eX eW rel ℓ Q,
    ∀ D : (Query k kN kS L → Out k e) → (Fin Q → M.NIProof) → Prop,
      Base.wiAdvantageWith (M.proverProofLaw Pv) A.toWIAdversary D ≤ ε

/-- **The proof law of the prover `niProver` is the law of the compiled proof** over uniform coins
(`proofLaw`). -/
theorem proverProofLaw_niProver (Λ : SiteLayout Mg) {E : (j : ι) → (M.comp j).Encoder}
    {V : X → FullTr P t → Bool} {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ}
    (hb : M.FormatBounds Qs B B) {R : Type} [Fintype R] [Nonempty R]
    (honest : W → R → CausalProver P t X) (h : Query k kN kS L → Out k e) (x : X) (w : W) :
    M.proverProofLaw (M.niProver Λ honest E hb) h x w = proofLaw E Qs h x (honest w) := by
  let eq : SaltedCoins (FiatShamirSalt kS) (M.ProverCoins R) ≃
      FiatShamirSalt kS × R × (M.Pos → MerkleSalt kN) :=
    (SaltedCoins.equivProd _ _).trans
      ((Equiv.refl _).prodCongr (Base.ProverCoins.equivProd M.toBase R))
  unfold proverProofLaw proofLaw
  rw [show (M.niProver Λ honest E hb).coins = PMF.uniformOfFintype _ from rfl,
    ← PMF.uniformOfFintype_map_equiv eq.symm, PMF.map_comp]
  congr 1
  funext c
  exact M.toFn_niProver Λ honest E VE hb h x w (eq.symm c)

/-- **Witness indistinguishability against adaptively chosen statements of bounded length**
(CY24 Definition 33.1.1, pp. 426-427, at unbounded queries, p. 430, for `Q` proof queries) of the
prover `niProver`: when the composite is honest-verifier zero knowledge at the joint simulator `Sim`
with error `δ` (`hvzk`, CY24 Definition 23.1.8), then for all injective binary encodings `eX`, `eW` of statements and witnesses and every
`ℓ`, every adversary choosing each of its `Q` statements and witness pairs adaptively, as a function
of the whole oracle and the earlier proofs, among those of total encoding length at most `ℓ`, has
advantage at most `Q · wiError δ (choiceCount ℓ)` with `choiceCount ℓ = (ℓ + 1)^2 · 2^(ℓ + 1)`.
The salt term of the error is `√(((ℓ + 1) log 2 + 2 log (ℓ + 1)) / (2 · 2^(8 kS)))`
(`SPBCS.saltTerm_choiceCount`). -/
@[headline]
theorem unconditionallyWitnessIndistinguishable [∀ j i, Fintype ((M.comp j).MessageWrite i)]
    (Λ : SiteLayout Mg) {E : (j : ι) → (M.comp j).Encoder} {V : X → FullTr P t → Bool}
    {Qs : ∀ x, M.IOPQueries V x} (VE : M.ViewEncoder E Qs) {B : ℕ} (hb : M.FormatBounds Qs B B)
    {R : Type} [Fintype R] [Nonempty R] {honest : W → R → CausalProver P t X} {Pub : Type}
    {pub : X → Pub} {Sim : CausalJointSimulator VE.MV Pub} {δ : ℝ≥0}
    (hvzk : CausalHVZK VE.MV rel honest pub Sim δ) (eX : SPBCS.BitEncoding X)
    (eW : SPBCS.BitEncoding W) (Q ℓ : ℕ) :
    M.WitnessIndistinguishableOfLength (M.niProver Λ honest E hb) eX eW rel Q ℓ
      (Q * M.wiError δ (SPBCS.choiceCount ℓ)) := fun A D => by
  rw [show M.proverProofLaw (M.niProver Λ honest E hb) = fun h x w => proofLaw E Qs h x (honest w)
    from funext fun h => funext fun x => funext fun w => proverProofLaw_niProver Λ VE hb honest h x w]
  exact witnessIndistinguishable VE.toReveal (Base.obsClose_of_causalHVZK VE.toReveal hvzk) Q
    _ A.toWIAdversary A.card_choices_le D

end

end GordieHowe.SPBCS
