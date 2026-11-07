-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Zerocheck.MergedAffineBatch
public import GordieHowe.ProofSystem.FieldProof.MaskedReductionFuse

@[expose] public section

/-!
# A merged batch with its first two challenges in one verifier message

The C++ (`batch.h`, `BatchKernel::reduce`) draws the merging coefficient `γ` from the challenge
point that also yields the zerocheck point `ρ` of the batch phase, with no prover message between
them; paper `lem:batch` charges the merged batch at one verifier message `(γ, ρ)`.
`MergedAffineBatch.ip` sends them as two adjacent verifier moves; `fusedIp` is the same masked
reduction with the two moves fused (`MaskedReduction.fuse`). The program's masked reduction of a
merged batch is `fusedIp` on columns and `bitIp` (`fusedIp` with the bit sumcheck) on bits, so a
merged batch has the rounds of an unmerged one.

* **Soundness** (`fusedSound`): the errors `(np − 1 + n)/|K|` at `(γ, ρ)` (`fusedError_gammaRho`),
  then the batch phase's: `D(w − 1)/|K|` at `r`, `(D + 1)/|K|` at each `s_j` and `1/|K|` at `u`
  (`fusedError_shift`); they sum to `(n(D + 2) + D(w − 1) + max np 1)/|K|` (`fusedError_sum`), the
  sum of `ip`'s errors (`sum_fusedError`).
* **Honest prover** (`fusedHonest`): the honest prover and simulator of `honest`, read through the
  transcript bijection (`GordieHowe.IOP.fuseEquiv`).
* **The bit sumcheck** (`bitIp`): `fusedIp`, then the masked sumcheck over the bit-index variables
  of the words, with its soundness (`bitSumcheckSound`), honest prover (`bitHonest`) and zero
  knowledge (`bitHvzk`).
-/

namespace GordieHowe.BatchedZerocheck

open IOP GKR.Schedule Sumcheck.FieldSkip Sumcheck.FieldSkipMasked
open HashCircuit.Skip (alt alt_decidableEq alt_nonempty)
open scoped NNReal

namespace MergedAffineBatch

variable {K Pub V : Type} [Field K] (B : MergedAffineBatch K Pub V)

/-- **The moves after `(γ, ρ)`**: the skip message, `r`, the sumcheck rounds, the terminal claims
and `u`. -/
abbrev tail : ProtocolSpec (1 + (1 + (roundLength B.n + (1 + (1 + 0))))) :=
  one .P_to_V (Fin B.e → K) ++ (one .V_to_P K ++ (alt (Fin B.D → K) K B.n ++ Tail K B.k empty))

omit [Field K] in
/-- The challenges after `(γ, ρ)` have decidable equality. -/
instance tail_decidableEq [DecidableEq K] :
    ∀ i : B.tail.ChallengeIdx, DecidableEq (B.tail.Challenge i) :=
  @ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq
    (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq
      (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ (alt_decidableEq _ _ B.n)
        (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq
          (@ProtocolSpec.append_challenge_decidableEq _ _ _ _ one_decidableEq inferInstance))))

/-- The challenges after `(γ, ρ)` are nonempty. -/
instance tail_nonempty : ∀ i : B.tail.ChallengeIdx, Nonempty (B.tail.Challenge i) :=
  haveI : Nonempty K := ⟨0⟩
  @ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty
    (@ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty
      (@ProtocolSpec.append_challenge_nonempty _ _ _ _ (alt_nonempty _ _ B.n)
        (@ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty
          (@ProtocolSpec.append_challenge_nonempty _ _ _ _ one_nonempty inferInstance))))

variable {ι : Type} [Fintype ι] [Fintype K] [DecidableEq K]

/-- The batch's masked reduction is `γ`, then `ρ`, then `tail`. -/
theorem ip_specIs (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.ip Pub e Lv).SpecIs K (Fin B.n → K) B.tail :=
  rfl

variable (Pub)

/-- **The batch's masked reduction with `(γ, ρ)` in one verifier message** (`MaskedReduction.fuse`). -/
abbrev fusedIp (e : B.Pad → ι) (Lv : Level K ι V) : FieldProof.MaskedReduction K ι Pub (ι → K) id V 1 :=
  (B.ip Pub e Lv).fuse (B.ip_specIs e Lv)

/-- **The fused batch's claim reads what its forms read and the pads** (`readsOnly_ip`). -/
theorem readsOnly_fusedIp [DecidableEq V] (e : B.Pad → ι) (Lv : Level K ι V) {T : V → Prop}
    (h : ∀ p t j, (B.form p t j).ReadsOnly T) (hT : ∀ i, T (Lv.cell i)) :
    (B.fusedIp Pub e Lv).ReadsOnly fun _ => T :=
  (B.readsOnly_ip Pub e Lv h hT).fuse _

variable {Pub}

/-- **The fused round errors**: `(np − 1)/|K| + n/|K|` at `(γ, ρ)`, then the batch phase's. -/
noncomputable abbrev fusedError :
    (fused K (Fin B.n → K) B.tail).ChallengeIdx → ℝ≥0 :=
  fuseError B.error

omit [DecidableEq K] in
/-- The error at `(γ, ρ)` is `(np − 1 + n)/|K|`. -/
theorem fusedError_gammaRho :
    B.fusedError (fusedIdx₀ K (Fin B.n → K) B.tail) =
      ((B.np - 1 + B.n : ℕ) : ℝ≥0) / Fintype.card K := by
  unfold fusedError
  rw [fuseError_fusedIdx₀]
  have h₀ : idx₀ K (Fin B.n → K) B.tail = ProtocolSpec.ChallengeIdx.inl ⟨0, rfl⟩ := rfl
  have h₁ : idx₁ K (Fin B.n → K) B.tail =
      ProtocolSpec.ChallengeIdx.inr (idxRho K B.e B.D B.n B.k empty) := rfl
  rw [h₀, h₁]
  simp only [MergedAffineBatch.error]
  erw [ProtocolSpec.appendError_inl, ProtocolSpec.appendError_inr]
  simp only [BatchedZerocheck.error, index_idxRho, Sum.elim_inl]
  push_cast
  rw [add_div]

omit [DecidableEq K] in
/-- After `(γ, ρ)`, each fused move has the error of the batch phase's move one position later:
`D(w − 1)/|K|` at `r`, `(D + 1)/|K|` at each `s_j`, `1/|K|` at `u`. -/
theorem fusedError_shift (i : (fused K (Fin B.n → K) B.tail).ChallengeIdx) (h : i.1.val ≠ 0) :
    B.fusedError i = B.error (shiftIdx i h) :=
  fuseError_shiftIdx _ i h

omit [DecidableEq K] in
/-- **The fused errors sum to the errors of `ip`** (`GordieHowe.IOP.sum_fuseError`):
`(np − 1)/|K|`, then `n/|K|`, `D(w − 1)/|K|`, `(D + 1)n/|K|` and `1/|K|` (`error_sum`). -/
theorem sum_fusedError : ∑ i, B.fusedError i = ((B.np - 1 : ℕ) : ℝ≥0) / Fintype.card K +
    ((B.n : ℝ≥0) / Fintype.card K + ((B.D * (B.w - 1) : ℕ) : ℝ≥0) / Fintype.card K +
      ((B.D + 1 : ℕ) : ℝ≥0) * B.n / Fintype.card K + 1 / Fintype.card K) :=
  (sum_fuseError _).trans B.error_sum

omit [DecidableEq K] in
/-- **Paper `lem:batch` (1), the errors**: the fused errors sum to
`errbatch = (n(D + 2) + D(w − 1) + nQ)/|K|` with `nQ = max np 1`, which is `np` for every batch of
at least one relation (the paper's `Q_0, …, Q_{nQ − 1}`). With no relation, `γ` costs nothing and
the opening combination still costs `1/|K|`. -/
@[headline]
theorem fusedError_sum :
    ∑ i, B.fusedError i =
      ((B.n * (B.D + 2) + B.D * (B.w - 1) + max B.np 1 : ℕ) : ℝ≥0) / Fintype.card K := by
  rw [sum_fuseError, error_sum]
  rcases Nat.eq_zero_or_pos B.np with h0 | hpos
  · rw [h0, show max 0 1 = 1 from rfl]
    push_cast
    ring
  · obtain ⟨q, hq⟩ : ∃ q, B.np = q + 1 := ⟨B.np - 1, by omega⟩
    rw [hq, Nat.add_sub_cancel, max_eq_left (by omega)]
    push_cast
    ring

/-- **Paper `lem:batch` (1)**: soundness of the batch's masked reduction with `(γ, ρ)` in one verifier
message, from the batch on the logical assignment and the pads' products, with the errors
`fusedError` (`MaskedReduction.Sound.fuse` of `sound`). -/
noncomputable def fusedSound (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.fusedIp Pub e Lv).Sound Lv.view (B.Sat e Lv) B.fusedError :=
  FieldProof.MaskedReduction.Sound.fuse (B.ip_specIs e Lv) (B.sound e Lv)

variable (Pub)

/-- **The simulator of the batch masked reduction with `(γ, ρ)` in one verifier message**
(`MaskedReduction.Sim.fuse` of `sim`).

Running time: `sim`'s and a relabelling of the first two transcript entries, linear in the batch
transcript. This running time is argued here, not proved in Lean. -/
def fusedSim (e : B.Pad → ι) (Lv : Level K ι V) : (B.fusedIp Pub e Lv).Sim :=
  FieldProof.MaskedReduction.Sim.fuse (B.ip_specIs e Lv) (B.sim Pub e Lv)

/-- **Paper `lem:batch` (2)**: the honest batch masked reduction with `(γ, ρ)` in one verifier message,
on assignments where the batch holds (`MaskedReduction.Honest.fuse` of `honest`), simulated by
`fusedSim`. -/
noncomputable def fusedHonest (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.fusedIp Pub e Lv).Honest Lv.view (V → K) (fun p z => B.Holds p z) (B.fusedSim Pub e Lv) :=
  FieldProof.MaskedReduction.Honest.fuse (B.ip_specIs e Lv) (B.honest Pub e Lv)

variable {Pub} in
/-- **Cells holding the honest pad values commit the honest assignment** (`commits_of`). -/
theorem fusedCommits_of (e : B.Pad → ι) (Lv : Level K ι V) (p : Pub) (z : V → K)
    (φ : FreePads K B.w B.D B.n B.k) (x : ι → K) (hz : B.map.ops p (Lv.view x) = B.map.ops p z)
    (hp : x ∘ e = B.padValue φ) : (B.fusedHonest Pub e Lv).Commits p z φ x :=
  B.commits_of e Lv p z φ x hz hp

/-- The message types of the fused batch's masked reduction are finite. -/
instance fusedIp_typeFintype (e : B.Pad → ι) (Lv : Level K ι V) :
    ∀ i, Fintype ((B.fusedIp Pub e Lv).spec.Type i) :=
  @ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype
    (@ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype
      (@ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype
        (@ProtocolSpec.appendTypeFintype _ _ _ _ (alt_typeFintype B.n)
          (@ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype
            (@ProtocolSpec.appendTypeFintype _ _ _ _ GKR.Schedule.one_typeFintype inferInstance)))))

/-- The message types of the fused batch's masked reduction are nonempty. -/
instance fusedIp_typeNonempty (e : B.Pad → ι) (Lv : Level K ι V) :
    ∀ i, Nonempty ((B.fusedIp Pub e Lv).spec.Type i) :=
  haveI : Nonempty K := ⟨0⟩
  @ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
    (@ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
      (@ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
        (@ProtocolSpec.appendTypeNonempty _ _ _ _ (alt_typeNonempty B.n)
          (@ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
            (@ProtocolSpec.appendTypeNonempty _ _ _ _ GKR.Schedule.one_typeNonempty
              inferInstance)))))

/-- The fused batch's simulator is bijective (`MaskedReduction.Honest.SimBijective.fuse` of
`honest_simBijective`). -/
theorem fusedHonest_simBijective (e : B.Pad → ι) (Lv : Level K ι V) :
    (B.fusedHonest Pub e Lv).SimBijective :=
  (B.honest_simBijective e Lv).fuse (B.ip_specIs e Lv)

/-- **Paper `lem:batch` (3)**: honest-verifier zero knowledge with error `0` with respect to the
uniform simulator (paper `def:red-sec` (c)) of the batch with `(γ, ρ)` in one verifier message: at
every public input and every logical assignment, the honest transcript under uniform challenges and
uniform free pads is a uniform full transcript. -/
@[headline]
theorem fusedHvzk (e : B.Pad → ι) (Lv : Level K ι V) : (B.fusedHonest Pub e Lv).UniformHVZK :=
  (B.fusedHonest_simBijective Pub e Lv).uniformHVZK

/-! ### The bit sumcheck -/

section BitSumcheck

variable {Pub} [DecidableEq V] {m nw : ℕ}

variable (Pub) in
/-- **The merged batch's masked reduction with the bit sumcheck** (`MaskedReduction.bitSumcheck`) at the bit
layout `L`: the merged batch's masked reduction with `(γ, ρ)` in one verifier message (`fusedIp`), then
the masked sumcheck over the bit-index variables of its words, whose output claim replaces the opening
claim. -/
def bitIp (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    FieldProof.MaskedReduction K ι Pub (ι → K) id V 1 :=
  (B.fusedIp Pub e Lv).bitSumcheck L Lv

omit [DecidableEq K] [DecidableEq V] in
variable (m) in
/-- **The errors of the merged batch with the bit sumcheck**: the fused merged batch's
(`fusedError`), then `2/|K|` per bit round. -/
noncomputable abbrev bitError :
    (fused K (Fin B.n → K) B.tail ++ HashCircuit.Skip.alt (Fin 2 → K) K m).ChallengeIdx → ℝ≥0 :=
  FieldProof.MaskedReduction.coordSumcheckError (K := K) m B.fusedError

omit [DecidableEq K] [DecidableEq V] in
/-- **The total error of the merged batch with the bit sumcheck**: `(np − 1)/|K|` for `γ`, the
batch phase's, plus `2m/|K|` for the `m` bit rounds. -/
theorem bitError_sum : ∑ i, B.bitError m i = ((B.np - 1 : ℕ) : ℝ≥0) / Fintype.card K +
    ((B.n : ℝ≥0) / Fintype.card K + ((B.D * (B.w - 1) : ℕ) : ℝ≥0) / Fintype.card K +
      ((B.D + 1 : ℕ) : ℝ≥0) * B.n / Fintype.card K + 1 / Fintype.card K) +
        ((2 * m : ℕ) : ℝ≥0) / Fintype.card K := by
  rw [FieldProof.MaskedReduction.sum_coordSumcheckError, B.sum_fusedError]

/-- **Soundness of the merged batch with the bit sumcheck**: the merged batch's relation, with
the fused merged batch's errors and `2/|K|` per bit round. -/
noncomputable def bitSumcheckSound (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitIp Pub e Lv L).Sound Lv.view (B.Sat e Lv) (B.bitError m) :=
  (B.fusedSound e Lv).bitSumcheck

variable (Pub) in
/-- **The simulator of the merged batch with the bit sumcheck**: the fused merged batch's simulator
(`fusedSim`), then uniform values (`MaskedReduction.Sim.coordSumcheck`).

Running time: the merged batch's simulator's and a copy of `2m` coins, linear in the transcript.
This running time is argued here, not proved in Lean. -/
def bitSim (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) : (B.bitIp Pub e Lv L).Sim :=
  FieldProof.MaskedReduction.Sim.coordSumcheck L (B.fusedSim Pub e Lv)

variable (Pub) in
/-- **The honest merged batch with the bit sumcheck**, on assignments where the batch holds: the
honest fused merged batch (`fusedHonest`), then the honest bit rounds at the assignment's bits,
simulated by `bitSim`. -/
noncomputable def bitHonest (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitIp Pub e Lv L).Honest Lv.view (V → K) (fun p z => B.Holds p z) (B.bitSim Pub e Lv L) :=
  (B.fusedHonest Pub e Lv).bitSumcheck L fun _ z => L.values z

/-- **The cells commit the honest merged batch with the bit sumcheck** when they commit the
honest fused merged batch, the bit rounds' pads and the assignment's bits. -/
theorem bitCommits_of (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) (p : Pub)
    (z : V → K) (φ : FreePads K B.w B.D B.n B.k) (ψ : Fin m → Fin 2 → K) (x : ι → K)
    (hb : (B.fusedHonest Pub e Lv).Commits p z φ x) (hl : L.Commits Lv (L.values z) ψ x) :
    (B.bitHonest Pub e Lv L).Commits p z (φ, ψ) x :=
  ⟨hb, hl⟩

/-- The message types of the merged batch's masked reduction with the bit sumcheck are finite. -/
instance bitIp_typeFintype (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    ∀ i, Fintype ((B.bitIp Pub e Lv L).spec.Type i) :=
  FieldProof.MaskedReduction.coordSumcheck_typeFintype (M := B.fusedIp Pub e Lv)

/-- The message types of the merged batch's masked reduction with the bit sumcheck are nonempty. -/
instance bitIp_typeNonempty (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    ∀ i, Nonempty ((B.bitIp Pub e Lv L).spec.Type i) :=
  FieldProof.MaskedReduction.coordSumcheck_typeNonempty (M := B.fusedIp Pub e Lv)

/-- The simulator of the merged batch with the bit sumcheck is a bijection onto the full
transcripts. -/
theorem bitHonest_simBijective (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitHonest Pub e Lv L).SimBijective :=
  (B.fusedHonest_simBijective Pub e Lv).bitSumcheck _

/-- **Honest-verifier zero knowledge of the merged batch with the bit sumcheck** with error `0`
with respect to the uniform simulator (paper `def:red-sec` (c)): at every public input and every
logical assignment, the honest transcript under uniform challenges, uniform free pads and uniform
bit-round pads is a uniform full transcript. -/
@[headline]
theorem bitHvzk (e : B.Pad → ι) (Lv : Level K ι V) (L : BitLayout K ι V m nw) :
    (B.bitHonest Pub e Lv L).UniformHVZK :=
  (B.bitHonest_simBijective e Lv L).uniformHVZK

end BitSumcheck

end MergedAffineBatch

end GordieHowe.BatchedZerocheck
