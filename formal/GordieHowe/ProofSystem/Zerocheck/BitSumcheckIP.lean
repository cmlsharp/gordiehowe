-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.BitSumcheck
public import GordieHowe.ProofSystem.Zerocheck.SkipBatch
public import GordieHowe.Model.IOP.TranscriptEventReduction
public import GordieHowe.ProofSystem.FieldProof.ClaimSupport

@[expose] public section

/-!
# The masked bit sumcheck as a masked-reduction construction

A masked reduction with one claim on logical coordinates `V`, followed by the masked sumcheck over the
bit-index variables of `nw` words of `2^m` bits (`GordieHowe/ProofSystem/Zerocheck/BitSumcheck.lean`;
label `gordiehowe.batch.bit-phase`), whose claim replaces the masked reduction's.

* **The layout** (`BitLayout`): the bits as logical coordinates (`bit q b`, bit `b` of word `q`),
  the committed pads of the round messages (`pad i j`, one full-field cell per sent value) and the
  round's interpolation nodes.
* **The split of the claim** (`BitLayout.weights`, `BitLayout.rest`): the claim's coefficient at
  each bit coordinate, and the rest (its constant, the pad terms and every other coordinate), so
  that the claim is `Σ_{q,b} W_q[b] · bit q b + rest` (`eval_rest`). The weights are coefficients,
  so the layout need not be injective: a coordinate named twice is counted in `rest` with the
  opposite sign.
* **The claims** (`BitLayout.claimsForm`, `BitLayout.outClaim`): the verifier's running claims as
  affine forms in the pads, from `−rest`, each round's values unmasked by its pad cells; the
  output claim `Σ_q α_q Σ_b eq(ρ, b) · bit q b − claim_m` with `α_q = W̃_q(ρ)`, the dense weights'
  multilinear extension at `ρ`.
* **The construction** (`MaskedReduction.bitSumcheck`): the masked reduction's rounds, then `m` rounds of two
  masked values and a challenge (`HashCircuit.Skip.alt`); the rows unchanged, the claim replaced by
  the output claim. Its soundness (`Sound.bitSumcheck`) keeps the masked reduction's errors and adds
  `2/|K|` per round (`sum_bitSumcheckError`); its honest prover (`Honest.bitSumcheck`) sends the
  honest round values plus fresh uniform pads, simulated by uniform values
  (`SimBijective.bitSumcheck`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec
open GKR.Schedule (roundLength)
open HashCircuit.Skip (alt altValues altChallenge altIndex altChallenge_val altChallenge_type
  altIndex_altChallenge altValues_snd altValues_fst_congr altValues_snd_congr altFamily
  altFamily_fst alt_ext card_filter_cast_le update_agrees)
open scoped NNReal

/-! ### Alternating rounds with causal messages -/

section Alt

variable {M C : Type} {k : ℕ}

theorem HashCircuit.Skip.altChallenge_altIndex (i : (alt M C k).ChallengeIdx) :
    altChallenge M C k (altIndex M C k i) = i :=
  (altIndex M C k).injective (altIndex_altChallenge M C k _)

/-- The challenges of a challenge vector of the alternating rounds, by round. -/
def HashCircuit.Skip.altChals (ch : (alt M C k).Challenges) : Fin k → C :=
  fun j => cast (altChallenge_type M C k j) (ch (altChallenge M C k j))

/-- The challenges of a realized transcript are those it was run on. -/
theorem HashCircuit.Skip.altValues_snd_transcript (H : CausalTranscript (alt M C k))
    (ch : (alt M C k).Challenges) (j : Fin k) :
    (altValues M C k (H.transcript ch) j).2 = HashCircuit.Skip.altChals ch j := by
  rw [altValues_snd, H.challenge]
  rfl

/-- **Causal rounds send their values at the realized challenges**: when round `j`'s message reads
only the challenges before `j`, the honest rounds realize the transcript of the rounds sending
those messages as fixed values. -/
theorem HashCircuit.Skip.altFamily_eq_const [Zero C] (f : (Fin k → C) → Fin k → M)
    (hf : ∀ (s s' : Fin k → C) (j : Fin k), (∀ v, v < j → s v = s' v) → f s j = f s' j)
    (ch : (alt M C k).Challenges) :
    (altFamily k f).transcript ch =
      (altFamily k fun _ => f (HashCircuit.Skip.altChals ch)).transcript ch := by
  refine alt_ext M C k (funext fun j => Prod.ext ?_ ?_)
  · rw [altFamily_fst, altFamily_fst]
    refine hf _ _ j fun v hv => ?_
    simp only [hv, ↓reduceIte, HashCircuit.Skip.altValues_snd_transcript]
  · rw [HashCircuit.Skip.altValues_snd_transcript, HashCircuit.Skip.altValues_snd_transcript]

end Alt

/-! ### The layout -/

/-- **The layout of a bit sumcheck**: bit `b` of word `q` as a logical coordinate, the committed
pad cell of each sent value (`pad i 0` for `p_i(0)`, `pad i 1` for `p_i(g)`), and the round's
interpolation nodes `0, 1, g`. -/
structure BitLayout (K ι V : Type) [Field K] (m nw : ℕ) where
  /-- Bit `b` of word `q`. -/
  bit : Fin nw → Fin (2 ^ m) → V
  /-- The pad cell of value `j` of round `i`. -/
  pad : Fin m → Fin 2 → ι
  /-- The interpolation nodes. -/
  nodes : Sumcheck.Nodes K

namespace BitLayout

variable {K ι V : Type} [Field K] {m nw : ℕ} (L : BitLayout K ι V m nw)

/-- **The bit part of a claim** with weights `W`: `Σ_{q,b} W_q[b] · bit q b`. -/
def bitForm (W : Fin nw → Fin (2 ^ m) → K) : AffineForm K V :=
  AffineForm.sumFin fun q => AffineForm.sumFin fun b => W q b • AffineForm.var (L.bit q b)

@[simp] theorem eval_bitForm (W : Fin nw → Fin (2 ^ m) → K) (z : V → K) :
    (L.bitForm W).eval z = ∑ q, ∑ b, W q b * z (L.bit q b) := by
  simp [bitForm]

/-- The bits of the words in a logical assignment. -/
def bits (z : V → K) : Fin nw → Fin (2 ^ m) → K := fun q b => z (L.bit q b)

variable [DecidableEq V]

/-- **The weights of a claim** (dense): its coefficient at each bit coordinate, the sum of its
terms there. -/
def weights (A : AffineForm K V) (q : Fin nw) (b : Fin (2 ^ m)) : K :=
  (A.terms.map fun t => if t.2 = L.bit q b then t.1 else 0).sum

/-- **The rest of a claim**: the claim minus its bit part at its weights. -/
def rest (A : AffineForm K V) : AffineForm K V := A - L.bitForm (L.weights A)

theorem eval_rest (A : AffineForm K V) (z : V → K) :
    (L.rest A).eval z = A.eval z - ∑ q, ∑ b, L.weights A q b * L.bits z q b := by
  simp [rest, bits]

/-- The values of round `i` unmasked by the pad cells of `x`. -/
def unmasked (sent : Fin m → Fin 2 → K) (x : ι → K) : Fin m → Fin 2 → K :=
  fun i j => sent i j - x (L.pad i j)

/-- **Value `j` of round `i` unmasked**, as an affine form: the sent value minus its pad cell. -/
def unmaskedForm (Lv : Level K ι V) (sent : Fin m → Fin 2 → K) (i : Fin m) (j : Fin 2) :
    AffineForm K V :=
  AffineForm.ofConst (sent i j) - AffineForm.var (Lv.cell (L.pad i j))

/-- **One round's update on affine forms** (`BitSumcheck.step`). -/
def stepForm (r : K) (c p0 p2 : AffineForm K V) : AffineForm K V :=
  Sumcheck.Round.coefficients L.nodes r 1 • (c - p0) +
    Sumcheck.Round.coefficients L.nodes r 0 • p0 + Sumcheck.Round.coefficients L.nodes r 2 • p2

/-- **The verifier's claims as affine forms** in the pads, from `−rest` of the claim `A`
(computable). -/
def claimsForm (Lv : Level K ι V) (A : AffineForm K V) (sent : Fin m → Fin 2 → K)
    (ρ : Fin m → K) : Fin (m + 1) → AffineForm K V :=
  Fin.induction (-L.rest A) fun i c =>
    L.stepForm (ρ i) c (L.unmaskedForm Lv sent i 0) (L.unmaskedForm Lv sent i 1)

theorem eval_claimsForm (Lv : Level K ι V) (A : AffineForm K V) (sent : Fin m → Fin 2 → K)
    (ρ : Fin m → K) (x : ι → K) (j : Fin (m + 1)) :
    (L.claimsForm Lv A sent ρ j).eval (Lv.view x) =
      BitSumcheck.claims L.nodes (-(L.rest A).eval (Lv.view x)) (L.unmasked sent x) ρ j := by
  induction j using Fin.induction with
  | zero => simp [claimsForm]
  | succ i ih =>
    rw [BitSumcheck.claims_succ, ← ih]
    simp only [claimsForm, Fin.induction_succ, stepForm, unmaskedForm, unmasked, BitSumcheck.step,
      AffineForm.eval_add, AffineForm.eval_smul, AffineForm.eval_sub, AffineForm.eval_ofConst,
      AffineForm.eval_var, Lv.view_cell]

/-- **The output claim** of the bit sumcheck on the claim `A`:
`Σ_q α_q Σ_b eq(ρ, b) · bit q b − claim_m`, with `α_q = W̃_q(ρ)` from the dense weights. -/
def outClaim (Lv : Level K ι V) (A : AffineForm K V) (sent : Fin m → Fin 2 → K) (ρ : Fin m → K) :
    AffineForm K V :=
  L.bitForm (fun q b => GKR.ClaimEvaluation.evalTable (L.weights A q) ρ * PackedClaim.eqPt ρ b.val) -
    L.claimsForm Lv A sent ρ (Fin.last m)

/-- **The weights of a claim are its coefficients at the bits.** -/
theorem weights_eq_coeff (A : AffineForm K V) (q : Fin nw) (b : Fin (2 ^ m)) :
    L.weights A q b = A.coeff (L.bit q b) :=
  (AffineForm.coeff_eq_sum_terms A _).symm

/-- **The output claim reads what the claim reads, the pads and every bit of a word one of whose
bits it may read** (`hword`). -/
theorem readsOnly_outClaim (Lv : Level K ι V) {A : AffineForm K V} {T : V → Prop}
    (hA : A.ReadsOnly T) (hpad : ∀ i j, T (Lv.cell (L.pad i j)))
    (hword : ∀ q b b', T (L.bit q b') → T (L.bit q b)) (sent : Fin m → Fin 2 → K)
    (ρ : Fin m → K) : (L.outClaim Lv A sent ρ).ReadsOnly T := by
  have hbits : ∀ (W : Fin nw → Fin (2 ^ m) → K), (∀ q b, W q b ≠ 0 → T (L.bit q b)) →
      (L.bitForm W).ReadsOnly T := fun W hW =>
    AffineForm.ReadsOnly.sumFin fun q => AffineForm.ReadsOnly.sumFin fun b =>
      AffineForm.ReadsOnly.smul_of fun h => AffineForm.ReadsOnly.var (hW q b h)
  have hrest : (L.rest A).ReadsOnly T :=
    hA.sub (hbits _ fun q b h => by
      rw [weights_eq_coeff] at h
      exact hA _ h)
  have hun : ∀ i j, (L.unmaskedForm Lv sent i j).ReadsOnly T := fun i j =>
    (AffineForm.ReadsOnly.ofConst _).sub (AffineForm.ReadsOnly.var (hpad i j))
  have hclaims : ∀ j, (L.claimsForm Lv A sent ρ j).ReadsOnly T := fun j => by
    induction j using Fin.induction with
    | zero => simpa [claimsForm] using hrest.neg
    | succ i ih =>
      simp only [claimsForm, Fin.induction_succ, stepForm]
      exact (((ih.sub (hun i 0)).smul _).add ((hun i 0).smul _)).add ((hun i 1).smul _)
  refine (hbits _ fun q b h => ?_).sub (hclaims _)
  have hne : GKR.ClaimEvaluation.evalTable (L.weights A q) ρ ≠ 0 := left_ne_zero_of_mul h
  obtain ⟨b', -, hb'⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  have hw := right_ne_zero_of_mul hb'
  rw [weights_eq_coeff] at hw
  exact hword q b b' (hA _ hw)

theorem eval_outClaim (Lv : Level K ι V) (A : AffineForm K V) (sent : Fin m → Fin 2 → K)
    (ρ : Fin m → K) (x : ι → K) :
    (L.outClaim Lv A sent ρ).eval (Lv.view x) =
      BitSumcheck.summandEval (L.weights A) (L.bits (Lv.view x)) ρ -
        BitSumcheck.claims L.nodes (-(L.rest A).eval (Lv.view x)) (L.unmasked sent x) ρ
          (Fin.last m) := by
  rw [outClaim, AffineForm.eval_sub, eval_claimsForm, eval_bitForm]
  congr 1
  simp only [BitSumcheck.summandEval, GKR.ClaimEvaluation.evalTable, bits, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun b _ => ?_
  ring

/-- **The output claim holds** exactly when the last claim is the summand at `ρ`. -/
theorem eval_outClaim_eq_zero_iff (Lv : Level K ι V) (A : AffineForm K V)
    (sent : Fin m → Fin 2 → K) (ρ : Fin m → K) (x : ι → K) :
    (L.outClaim Lv A sent ρ).eval (Lv.view x) = 0 ↔
      BitSumcheck.claims L.nodes (-(L.rest A).eval (Lv.view x)) (L.unmasked sent x) ρ
          (Fin.last m) = BitSumcheck.summandEval (L.weights A) (L.bits (Lv.view x)) ρ := by
  rw [eval_outClaim, sub_eq_zero, eq_comm]

/-- **The input claim is the sum** `Σ_{q,b} W_q[b] t_{q,b}` against `−rest` exactly when it holds. -/
theorem neg_eval_rest_eq_iff (A : AffineForm K V) (z : V → K) :
    -(L.rest A).eval z = ∑ q, ∑ b, L.weights A q b * L.bits z q b ↔ A.eval z = 0 := by
  rw [eval_rest]
  constructor <;> intro h <;> linear_combination -h

/-- **The cells commit the honest bits and the round pads**: the pad cells hold the pads `φ`, and
the logical assignment's bits are the honest bits. -/
structure Commits (Lv : Level K ι V) (bits : Fin nw → Fin (2 ^ m) → K)
    (φ : Fin m → Fin 2 → K) (x : ι → K) : Prop where
  /-- The pad cells hold the pads. -/
  pads : ∀ i j, x (L.pad i j) = φ i j
  /-- The bits of the logical assignment are the honest bits. -/
  bits : L.bits (Lv.view x) = bits

end BitLayout

/-! ### The construction -/

namespace FieldProof.MaskedReduction

variable {K ι : Type} [Field K] [Fintype ι] [Fintype K] [DecidableEq K] {Pub Wit V : Type}
  {cells : Wit → ι → K} [DecidableEq V] {m nw : ℕ}

/-- The sent values of the bit rounds. -/
def bitSent (tr : (alt (Fin 2 → K) K m).Transcript (Fin.last (roundLength m))) :
    Fin m → Fin 2 → K :=
  fun i => (altValues _ _ m tr i).1

/-- The challenges of the bit rounds. -/
def bitChal (tr : (alt (Fin 2 → K) K m).Transcript (Fin.last (roundLength m))) : Fin m → K :=
  fun i => (altValues _ _ m tr i).2

/-- **The bit sumcheck after a masked reduction** (the C++ batch's bit phase, label
`gordiehowe.batch.bit-phase`): the masked reduction's rounds, then `m` rounds of two masked values and a
challenge; the rows on the cells are unchanged, and the claim is the output claim of the bit
sumcheck on the masked reduction's claim. -/
def bitSumcheck (M : MaskedReduction K ι Pub Wit cells V 1) (L : BitLayout K ι V m nw)
    (Lv : Level K ι V) : MaskedReduction K ι Pub Wit cells V 1 where
  n := M.n + roundLength m
  spec := M.spec ++ alt (Fin 2 → K) K m
  nonempty :=
    haveI : Nonempty K := ⟨0⟩
    @ProtocolSpec.append_challenge_nonempty _ _ _ _ M.nonempty
      (HashCircuit.Skip.alt_nonempty _ _ m)
  Lin := M.Lin
  linear p tr := M.linear p tr.left
  Q := M.Q
  products := M.products
  claims p tr _ := L.outClaim Lv (M.claims p tr.left 0) (bitSent tr.right) (bitChal tr.right)

/-- **The bit sumcheck's claim reads what the masked reduction's claim reads, the pads and every bit of
a word one of whose bits it may read.** -/
theorem ReadsOnly.bitSumcheck {M : MaskedReduction K ι Pub Wit cells V 1} {L : BitLayout K ι V m nw}
    {Lv : Level K ι V} {T : V → Prop} (hM : M.ReadsOnly fun _ => T)
    (hpad : ∀ i j, T (Lv.cell (L.pad i j))) (hword : ∀ q b b', T (L.bit q b') → T (L.bit q b)) :
    (M.bitSumcheck L Lv).ReadsOnly fun _ => T := fun p tr _ =>
  L.readsOnly_outClaim Lv (hM p tr.left 0) hpad hword _ _

omit [Fintype ι] [DecidableEq K] in
variable (m) in
/-- **The errors of the bit sumcheck**: the masked reduction's, then `2/|K|` at each round's challenge. -/
noncomputable def bitSumcheckError {n : ℕ} {P : ProtocolSpec n} (ε : P.ChallengeIdx → ℝ≥0) :
    (P ++ alt (Fin 2 → K) K m).ChallengeIdx → ℝ≥0 :=
  appendError ε fun _ => 2 / Fintype.card K

omit [Field K] [Fintype ι] [DecidableEq K] in
/-- **The bit sumcheck's errors sum** to the masked reduction's plus `2m/|K|`. -/
theorem sum_bitSumcheckError {n : ℕ} {P : ProtocolSpec n} (ε : P.ChallengeIdx → ℝ≥0) :
    ∑ i, bitSumcheckError (K := K) m ε i = ∑ i, ε i + ((2 * m : ℕ) : ℝ≥0) / Fintype.card K := by
  refine (sum_appendError (P₁ := P) (P₂ := alt (Fin 2 → K) K m) ε _).trans ?_
  congr 1
  rw [Fintype.sum_equiv (altIndex (Fin 2 → K) K m) _ (fun _ => (2 : ℝ≥0) / Fintype.card K)
    fun _ => rfl]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  ring

section Sound

variable (M : MaskedReduction K ι Pub Wit cells V 1) (L : BitLayout K ι V m nw) (Lv : Level K ι V)

/-- The masked reduction's claim in a context of the bit rounds. -/
def bitClaimOf (c : AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec) : AffineForm K V :=
  M.claims c.ctx.pub c.transcript 0

/-- **The event of round `i`** of the bit sumcheck in a context: the round is bad
(`BitSumcheck.RoundBad`) on the values unmasked by the committed pads, at the weights of the masked
reduction's claim and the committed bits. -/
def bitBad (i : (alt (Fin 2 → K) K m).ChallengeIdx)
    (c : AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec)
    (tr : (alt (Fin 2 → K) K m).Transcript (Fin.last (roundLength m))) : Prop :=
  BitSumcheck.RoundBad (L.weights (bitClaimOf M c)) (L.bits (Lv.view (cells c.ctx.wit))) L.nodes
    (-(L.rest (bitClaimOf M c)).eval (Lv.view (cells c.ctx.wit)))
    (L.unmasked (bitSent tr) (cells c.ctx.wit)) (bitChal tr) (altIndex _ _ m i)

omit [Fintype ι] [Fintype K] [DecidableEq K] [DecidableEq V] in
/-- The unmasked values of rounds through `j` read the entries through `2j + 1`. -/
theorem unmasked_congr {x : ι → K} {tr tr' : (alt (Fin 2 → K) K m).Transcript (Fin.last (roundLength m))}
    {j : Fin m} (h : ∀ l, l.val ≤ 2 * j.val + 1 → tr l = tr' l) :
    ∀ v : Fin m, v ≤ j → L.unmasked (bitSent tr) x v = L.unmasked (bitSent tr') x v := by
  intro v hv
  have hv' : v.val ≤ j.val := hv
  funext i
  simp only [BitLayout.unmasked, bitSent,
    altValues_fst_congr _ _ m v tr tr' fun l hl => h l (by omega)]

omit [Field K] [Fintype ι] [Fintype K] [DecidableEq K] [DecidableEq V] in
/-- The challenges through `j` read the entries through `2j + 1`. -/
theorem bitChal_congr {tr tr' : (alt (Fin 2 → K) K m).Transcript (Fin.last (roundLength m))}
    {j : Fin m} (h : ∀ l, l.val ≤ 2 * j.val + 1 → tr l = tr' l) :
    ∀ v : Fin m, v ≤ j → bitChal tr v = bitChal tr' v := by
  intro v hv
  have hv' : v.val ≤ j.val := hv
  exact altValues_snd_congr _ _ m v tr tr' fun l hl => h l (by omega)

omit [Fintype K] [DecidableEq K] in
/-- **Causality**: the event at each round reads only the entries through its challenge. -/
theorem bitBad_causal : TranscriptEventReduction.Causal (alt (Fin 2 → K) K m) (bitBad M L Lv) := by
  intro i c tr tr' h
  obtain ⟨j, rfl⟩ : ∃ j, i = altChallenge (Fin 2 → K) K m j :=
    ⟨_, (HashCircuit.Skip.altChallenge_altIndex i).symm⟩
  rw [altChallenge_val] at h
  simp only [bitBad, altIndex_altChallenge]
  exact BitSumcheck.roundBad_congr _ _ _ _ j (unmasked_congr L h) (bitChal_congr h)

omit [DecidableEq K] in
open Classical in
/-- **The count at each round**: replacing round `j`'s challenge in any complete transcript makes
its event true for at most a `2/|K|` fraction of values (`BitSumcheck.card_roundBad_le`). -/
theorem bitBad_count (c : AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec)
    (i : (alt (Fin 2 → K) K m).ChallengeIdx)
    (tr : (alt (Fin 2 → K) K m).Transcript (Fin.last (roundLength m))) :
    ((Finset.univ.filter fun x : (alt (Fin 2 → K) K m).Challenge i =>
        bitBad M L Lv i c (Function.update tr i.1 x)).card : ℝ≥0) ≤
      2 / Fintype.card K * Fintype.card ((alt (Fin 2 → K) K m).Challenge i) := by
  obtain ⟨j, rfl⟩ : ∃ j, i = altChallenge (Fin 2 → K) K m j :=
    ⟨_, (HashCircuit.Skip.altChallenge_altIndex i).symm⟩
  have hx : ∀ x : (alt (Fin 2 → K) K m).Challenge (altChallenge (Fin 2 → K) K m j),
      bitBad M L Lv (altChallenge (Fin 2 → K) K m j) c
          (Function.update tr (altChallenge (Fin 2 → K) K m j).1 x) ↔
        BitSumcheck.RoundBad (L.weights (bitClaimOf M c)) (L.bits (Lv.view (cells c.ctx.wit)))
          L.nodes (-(L.rest (bitClaimOf M c)).eval (Lv.view (cells c.ctx.wit)))
          (L.unmasked (bitSent tr) (cells c.ctx.wit))
          (Function.update (bitChal tr) j (cast (altChallenge_type (Fin 2 → K) K m j) x)) j := by
    intro x
    simp only [bitBad, altIndex_altChallenge]
    refine BitSumcheck.roundBad_congr _ _ _ _ j (fun v hv' => ?_) (fun v hv' => ?_)
    · have hvj : v.val ≤ j.val := hv'
      funext i'
      simp only [BitLayout.unmasked, bitSent]
      rw [altValues_fst_congr _ _ m v _ tr fun l hl =>
        update_agrees tr _ x (k := 2 * j.val) (by rw [altChallenge_val]; omega) l (by omega)]
    · rcases lt_or_eq_of_le hv' with hlt | rfl
      · have hvj : v.val < j.val := hlt
        rw [Function.update_of_ne (ne_of_lt hlt)]
        exact altValues_snd_congr _ _ m v _ tr fun l hl =>
          update_agrees tr _ x (k := 2 * j.val) (by rw [altChallenge_val]; omega) l (by omega)
      · rw [Function.update_self]
        exact (altValues_snd _ _ m _ v).trans (congrArg _ (Function.update_self _ _ _))
  have hc := card_filter_cast_le (altChallenge_type (Fin 2 → K) K m j)
    (fun y => BitSumcheck.RoundBad (L.weights (bitClaimOf M c)) (L.bits (Lv.view (cells c.ctx.wit)))
      L.nodes (-(L.rest (bitClaimOf M c)).eval (Lv.view (cells c.ctx.wit)))
      (L.unmasked (bitSent tr) (cells c.ctx.wit)) (Function.update (bitChal tr) j y) j)
    (BitSumcheck.card_roundBad_le _ _ _ _ _ _ j)
  refine le_of_eq_of_le ?_ hc
  congr 2
  exact Finset.filter_congr fun x _ => hx x

/-- **The bit rounds as a claim reduction**: from the masked reduction's output on the context's cells
to the rows and the output claim, round `i`'s event `bitBad` at error `2/|K|`. -/
noncomputable def bitReduction :
    ClaimReduction (alt (Fin 2 → K) K m) (AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec)
      (fun _ => 2 / Fintype.card K) :=
  letI : Inhabited K := ⟨0⟩
  TranscriptEventReduction.reduction (alt (Fin 2 → K) K m) (bitBad M L Lv) (bitBad_causal M L Lv)
    (fun c => M.OutHolds Lv.view c.ctx.pub c.transcript (cells c.ctx.wit))
    (fun c tr => RowsHold (M.linear c.ctx.pub c.transcript) M.products (cells c.ctx.wit) ∧
      (L.outClaim Lv (bitClaimOf M c) (bitSent tr) (bitChal tr)).eval
        (Lv.view (cells c.ctx.wit)) = 0)
    (fun _ => 2 / Fintype.card K) (fun c i tr => bitBad_count M L Lv c i tr)
    (fun c tr h => by
      rw [BitLayout.eval_outClaim_eq_zero_iff] at h
      rcases BitSumcheck.sound _ _ _ _ _ _ h.2 with h0 | ⟨j, hj⟩
      · refine Or.inl ⟨h.1, fun c' => ?_⟩
        rw [Fin.fin_one_eq_zero c']
        exact (L.neg_eval_rest_eq_iff _ _).mp h0
      · refine Or.inr ⟨altChallenge (Fin 2 → K) K m j, ?_⟩
        simp only [bitBad, altIndex_altChallenge]
        exact hj)

variable {M L Lv}

/-- **Soundness of the bit sumcheck after a masked reduction**: the masked reduction's reduction, then the bit
rounds (`bitReduction`), each round at error `2/|K|`; the relation is the masked reduction's. The
sumcheck adds no witness: the reduction carries no extractor, only the masked reduction's claims and the
round events, and it is noncomputable only through `ClaimReduction.seq`'s state function, a
proposition. -/
noncomputable def Sound.bitSumcheck {sat : Pub → Wit → Prop} {ε : M.spec.ChallengeIdx → ℝ≥0}
    (S : M.Sound Lv.view sat ε) :
    (M.bitSumcheck L Lv).Sound Lv.view sat (bitSumcheckError (K := K) m ε) where
  reduction := S.reduction.seq (bitReduction M L Lv) fun c tr h =>
    (S.claimOut_iff c.pub c.wit tr).mpr h
  claim_iff := S.claim_iff
  claimOut_iff _ _ _ := ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.rows, h.claims 0⟩⟩

end Sound

/-! ### The honest prover -/

section Honest

open HashCircuit.Skip (altChals altFamily_eq_const)

variable {M : MaskedReduction K ι Pub Wit cells V 1} {L : BitLayout K ι V m nw} {Lv : Level K ι V}

variable (L) in
/-- **The honest bit rounds** at the weights `W`, the bits `t` and the pads `φ`: round `i` sends
the honest values (`BitSumcheck.honestMsg`) plus its pads. -/
def bitFamily (W t : Fin nw → Fin (2 ^ m) → K) (φ : Fin m → Fin 2 → K) :
    CausalTranscript (alt (Fin 2 → K) K m) :=
  altFamily m fun s i => BitSumcheck.honestMsg W t L.nodes s i + φ i

/-- **The simulated bit rounds** at values `v`: the rounds sending `v`. No prover runs. -/
def bitValueFamily (v : Fin m → Fin 2 → K) : CausalTranscript (alt (Fin 2 → K) K m) :=
  altFamily m fun _ i => v i

omit [Fintype ι] [Fintype K] [DecidableEq K] [DecidableEq V] in
/-- The honest bit rounds send the honest values at the realized challenges plus the pads. -/
theorem bitFamily_eq (W t : Fin nw → Fin (2 ^ m) → K) (φ : Fin m → Fin 2 → K)
    (ch : (alt (Fin 2 → K) K m).Challenges) :
    (bitFamily L W t φ).transcript ch =
      (bitValueFamily (fun i => BitSumcheck.honestMsg W t L.nodes (altChals ch) i + φ i)).transcript
        ch :=
  altFamily_eq_const _ (fun _ _ j h => by rw [BitSumcheck.honestMsg_congr W t L.nodes h]) ch

omit [Field K] [Fintype ι] [Fintype K] [DecidableEq K] [DecidableEq V] in
/-- The challenges of a realized bit transcript are those it was run on. -/
theorem bitChal_transcript (H : CausalTranscript (alt (Fin 2 → K) K m))
    (ch : (alt (Fin 2 → K) K m).Challenges) : bitChal (H.transcript ch) = altChals ch :=
  funext fun j => HashCircuit.Skip.altValues_snd_transcript H ch j

omit [Fintype ι] [Fintype K] [DecidableEq K] [DecidableEq V] in
/-- The values of the simulated bit rounds are its values. -/
theorem bitSent_bitValueFamily (v : Fin m → Fin 2 → K) (ch : (alt (Fin 2 → K) K m).Challenges) :
    bitSent ((bitValueFamily v).transcript ch) = v :=
  funext fun i => altFamily_fst m _ ch i

omit [Fintype ι] [DecidableEq K] [DecidableEq V] in
/-- **Hiding of the bit rounds**: for fixed challenges, the honest rounds under uniform pads have
the law of the simulated rounds under uniform values. -/
theorem bitFamily_identDistrib (W t : Fin nw → Fin (2 ^ m) → K)
    (ch : (alt (Fin 2 → K) K m).Challenges) :
    (fun φ => (bitFamily L W t φ).transcript ch) =ᵈ
      (fun v => (bitValueFamily v).transcript ch) :=
  IdentDistrib.of_equiv
    (Equiv.addLeft fun i => BitSumcheck.honestMsg W t L.nodes (altChals ch) i)
    fun φ => bitFamily_eq W t φ ch

variable (L) in
/-- **The simulator of the bit sumcheck after a masked reduction**: the masked reduction's
simulator, then uniform values (`bitValueFamily`).

Running time: the masked reduction's simulator's and a copy of its `2m` coins. This running time is
argued here, not proved in Lean. -/
def Sim.bitSumcheck (SM : M.Sim) : (M.bitSumcheck L Lv).Sim where
  SimCoins := SM.SimCoins × (Fin m → Fin 2 → K)
  sim p ch s := Transcript.join (SM.sim p ch.left s.1) ((bitValueFamily s.2).transcript ch.right)

variable (L) in
/-- **The honest prover of the bit sumcheck after a masked reduction** at honest bits `bits`: the masked
reduction's prover, then the honest bit rounds at the weights of the masked reduction's claim, the honest bits
and fresh uniform pads; the cells commit the masked reduction's honest input, the pads and the honest
bits (`BitLayout.Commits`). It is simulated by `Sim.bitSumcheck`. -/
def Honest.bitSumcheck {In : Type} {dom : Pub → In → Prop} {SM : M.Sim}
    (H : M.Honest Lv.view In dom SM) (bits : Pub → In → Fin nw → Fin (2 ^ m) → K) :
    (M.bitSumcheck L Lv).Honest Lv.view In dom (Sim.bitSumcheck L SM) where
  Pads := H.Pads × (Fin m → Fin 2 → K)
  prover p x π := (H.prover p x π.1).append fun tr =>
    bitFamily L (L.weights (M.claims p tr 0)) (bits p x) π.2
  Commits p x π w := H.Commits p x π.1 w ∧ L.Commits Lv (bits p x) π.2 (cells w)
  complete p x hx π w hw ch := by
    have e₁ := CausalTranscript.append_left (H.prover p x π.1)
      (fun tr => bitFamily L (L.weights (M.claims p tr 0)) (bits p x) π.2) ch
    have e₂ := CausalTranscript.append_right (H.prover p x π.1)
      (fun tr => bitFamily L (L.weights (M.claims p tr 0)) (bits p x) π.2) ch
    have hM := H.complete p x hx π.1 w hw.1 ch.left
    refine ⟨?_, fun _ => ?_⟩
    · exact (congrArg (fun tr => RowsHold (M.linear p tr) M.products (cells w)) e₁).mpr hM.rows
    · change (L.outClaim Lv (M.claims p _ 0) (bitSent _) (bitChal _)).eval _ = 0
      rw [e₁, e₂, BitLayout.eval_outClaim_eq_zero_iff, bitFamily_eq, bitSent_bitValueFamily,
        bitChal_transcript, hw.2.bits]
      set A := M.claims p ((H.prover p x π.1).transcript ch.left) 0
      have hu : L.unmasked (fun i => BitSumcheck.honestMsg (L.weights A) (bits p x) L.nodes
          (altChals ch.right) i + π.2 i) (cells w) =
          BitSumcheck.honestMsg (L.weights A) (bits p x) L.nodes (altChals ch.right) := by
        funext i j
        simp only [BitLayout.unmasked, Pi.add_apply, hw.2.pads, add_sub_cancel_right]
      rw [hu]
      refine BitSumcheck.claims_honest _ _ _ _ _ ?_
      rw [← hw.2.bits]
      exact (L.neg_eval_rest_eq_iff A _).mpr (hM.claims 0)
  identDistrib p x ch :=
    (IdentDistrib.dependent (f₁ := fun π₁ => (H.prover p x π₁).transcript ch.left)
      (g₁ := SM.sim p ch.left)
      (f₂ := fun π₁ φ => (bitFamily L (L.weights (M.claims p
        ((H.prover p x π₁).transcript ch.left) 0)) (bits p x) φ).transcript ch.right)
      (g₂ := fun _ v => (bitValueFamily v).transcript ch.right)
      (H.identDistrib p x ch.left) fun _ => bitFamily_identDistrib _ _ ch.right).comp
      fun v => Transcript.join v.1 v.2

omit [Fintype ι] [Fintype K] [DecidableEq K] [DecidableEq V] in
/-- **The simulated bit rounds are bijective**: as a function of the challenges and the values,
a bijection onto the full transcripts. -/
theorem bitValueFamily_bijective :
    CausalTranscript.ValuesBijective (bitValueFamily (K := K) (m := m)) :=
  BatchedZerocheck.altFamily_const_bijective m

/-- **The bit sumcheck keeps a bijective simulator**: the masked reduction's, then the bit rounds'
values. -/
theorem Honest.SimBijective.bitSumcheck {In : Type} {dom : Pub → In → Prop} {SM : M.Sim}
    {H : M.Honest Lv.view In dom SM} (h : H.SimBijective)
    (bits : Pub → In → Fin nw → Fin (2 ^ m) → K) :
    (H.bitSumcheck L bits).SimBijective := fun p =>
  bijective_join (f₁ := fun y => SM.sim p y.1 y.2)
    (f₂ := fun y => (bitValueFamily y.2).transcript y.1) (h p) bitValueFamily_bijective

end Honest

/-! ### Finite message types -/

section Types

variable {M : MaskedReduction K ι Pub Wit cells V 1} {L : BitLayout K ι V m nw} {Lv : Level K ι V}

/-- The message types of the bit sumcheck after a masked reduction are finite when the masked reduction's are. -/
instance bitSumcheck_typeFintype [∀ i, Fintype (M.spec.Type i)] :
    ∀ i, Fintype ((M.bitSumcheck L Lv).spec.Type i) :=
  ProtocolSpec.appendTypeFintype (P₁ := M.spec) (P₂ := alt (Fin 2 → K) K m)

/-- The message types of the bit sumcheck after a masked reduction are nonempty when the masked reduction's
are. -/
instance bitSumcheck_typeNonempty [∀ i, Nonempty (M.spec.Type i)] :
    ∀ i, Nonempty ((M.bitSumcheck L Lv).spec.Type i) :=
  haveI : Nonempty K := ⟨0⟩
  ProtocolSpec.appendTypeNonempty (P₁ := M.spec) (P₂ := alt (Fin 2 → K) K m)

end Types

end FieldProof.MaskedReduction

end GordieHowe
