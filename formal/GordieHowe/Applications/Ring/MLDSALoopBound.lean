-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.BaseSignerFacts
public import GordieHowe.Applications.MLDSA.Spec.ExpandMask

@[expose] public section

/-!
# The refusal terms of the hedged FIPS 204 signer

The hedged FIPS 204 signer (`fipsSignWith`, Algorithm 7 with at most `T` attempts and the bounded
samplers of Appendix C) refuses when a bounded sampler runs out of bytes or every attempt is
rejected. The refusal rates the generic ML-DSA ring needs (`mldsaBaseSigner`:
`BaseSigner.RefuseWithin` in completeness, `BaseSigner.RefuseAvgWithin` in anonymity and in the
zero-knowledge route of unforgeability) are stated here as two named terms, defined exactly and
left symbolic; the theorems that use them carry the terms in their bounds.

- `loopRefuseProb p prims T seed msg`: over a uniform 32-byte `rnd`, the probability that the
  signer of the key of `seed` (`keyGenFromSeed`, Algorithm 6) refuses the message `msg`.
- `mldsaRefuseAvg p prims T`: **the worst-message refusal term**. Averaged over a uniform key seed,
  the largest refusal probability over all messages. `refuseAvgWithin_mldsaRefuseAvg`: the base
  signer `mldsaBaseSigner p prims T bmsg` has averaged refusal rate `RefuseAvgWithin adm` at this
  term, for every base message `bmsg` and set `adm` of supported rings (the base signer reads no
  oracle and the ring only through the base message).
- `mldsaRefuseMsg p prims T bmsg`: **the per-message refusal term**. For every ring size `r`,
  signer position and ring message `m`, the refusal probability of the signer at the base message
  `bmsg R m` of the ring `R` of `r` honest members, averaged over the members' uniform key seeds;
  the largest such value. `refuseWithin_mldsaRefuseMsg`: the base signer has refusal rate
  `RefuseWithin adm` at this term. The term reads `bmsg` because the base message holds the ring,
  which holds the signer's own key: an average over the key at a message fixed in advance does
  not bound it.
- `mldsaRefuseMsg_le_mldsaRefuseAvg`, `mldsaRefuseAvg_le_one`: the per-message term is at most the
  worst-message term, which is at most `1`.

## Expected size

NIST FIPS 204 (August 2024), Appendix C "Loop Bounds": "If an implementation bounds the number of
iterations or the number of bytes that may be extracted from the XOF, it shall not use a limit
lower than those presented in Table 3. The limits yield a probability of approximately 2^-256 (or
less) of being reached in a correct implementation of this standard. The probability is
calculated under standard assumptions about the output distributions of XOFs and hash
functions." Table 3 gives 814 loop iterations as the minimum allowable limit for
ML-DSA.Sign_internal. The appendix treats the attempts as independent with the average acceptance
probability of Table 1 (expected repetitions 4.25, 5.1 and 3.85 for ML-DSA-44, 65 and 87) at
every key and message. That heuristic speaks to the per-message term: at `T = 814` it puts
`mldsaRefuseMsg` near `2^-256`. This is a remark about the term's expected size; no theorem here
assumes it.

The worst-message term is larger. Under the same heuristic, for one key and one message
representative `µ = H(tr ‖ M′)` the number of refusing values of `rnd` among the `2^256` is
binomial with mean `2^256` times the per-message refusal probability, and the supremum over
messages ranges over the `2^512` values of `µ`. Over that many independent counts the largest
count exceeds the mean by a large factor at every key, so `mldsaRefuseAvg` is well above
`mldsaRefuseMsg`.

## Why the terms average over keys

A per-key bound (`BaseSigner.RefuseAtWithin` at a small `ρ`) fails for some keys of the ML-DSA key
space. When `HighBits(Â·y)` is the same for every mask `y` (for instance `Â = 0`), every attempt
gets the same challenge `c`; if `c` fails the ct₀-check or the hint check, every attempt is
rejected and the signer refuses with probability `1`. Whether honest key generation outputs such
keys is a property of SHAKE. So both terms average the refusal rate over the key seed.

## Why the terms are not bounded here

Averaged over keys, the refusal rate `𝔼_key (1 - a(key))^T` (with `a(key)` the per-attempt
acceptance probability) is dominated by atypical keys, since `x ↦ x^T` is convex. A bound near
FIPS's figure therefore amounts to the claim that all but a tiny fraction of honest keys have
near-average per-attempt acceptance. In the game where `ExpandA`, `ExpandS`, `SampleInBall`, the
commitment hash and the mask derivation are random oracles, the regularity bounds of
`GordieHowe/Applications/MLDSA/Regularity/` establish a key's typicality only to a much weaker
error (`sum_abs_realMass_sub_le_mldsa44_box`), and they bound the hint check's acceptance only
through its mean over the challenge (the acceptance floors of `WeightLowerBound.lean` and
`WeightTail44.lean`).
-/

namespace GordieHowe.Ring

open GordieHowe.RingSignature GordieHowe.IOP _root_.MLDSA GordieHowe.MLDSA
open scoped ENNReal

section Generic

variable (p : Params) (prims : Primitives p) [NTTRingOps]

/-- **The refusal probability of the hedged FIPS 204 signer** of the key of `seed` on the message
`msg`, with at most `T` attempts: over a uniform 32-byte `rnd`, the probability that the signer
refuses (`fipsSignWith … = none`). -/
noncomputable def loopRefuseProb (T : ℕ) (seed : Bytes 32) (msg : List Byte) : ℝ≥0∞ :=
  Pr[rnd ~ PMF.uniformOfFintype (Bytes 32) :
    fipsSignWith p prims T (keyGenFromSeed p prims seed).2 msg rnd = none]

/-- **The worst-message refusal term of the hedged FIPS 204 signer** with at most `T` attempts:
averaged over a uniform key seed, the largest refusal probability over all messages
(`loopRefuseProb`). The averaged refusal rate `RefuseAvgWithin` of the ML-DSA base signer holds at
it (`refuseAvgWithin_mldsaRefuseAvg`). -/
noncomputable def mldsaRefuseAvg (T : ℕ) : ℝ≥0∞ :=
  ∑' seed, PMF.uniformOfFintype (Bytes 32) seed *
    ⨆ msg : List Byte, loopRefuseProb p prims T seed msg

/-- **The ring of `r` honest members with key seeds `seeds`**: their ML-DSA public keys
(`keyGenFromSeed`, Algorithm 6) in order. It is the honest ring `BaseSigner.honestRing` of the
ML-DSA base signer. -/
def seedRing {N r : ℕ} (hr : r ≤ N) (seeds : Fin r → Bytes 32) : KeyRing (PublicKey p prims) N :=
  ⟨List.ofFn fun j => (keyGenFromSeed p prims (seeds j)).1, by simpa using hr⟩

/-- **The per-message refusal term of the hedged FIPS 204 signer** with at most `T` attempts at
the base message `bmsg`: over the ring sizes `r ≤ N`, signer positions `s` and ring messages `m`,
the largest average over uniform key seeds of the `r` members of the refusal probability of member
`s` at the base message `bmsg R m` of their ring `R` (`seedRing`). The refusal rate `RefuseWithin`
of the ML-DSA base signer holds at it (`refuseWithin_mldsaRefuseMsg`). -/
noncomputable def mldsaRefuseMsg (T : ℕ) {N len : ℕ} {RMsg : Type}
    (bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len) : ℝ≥0∞ :=
  ⨆ (r : ℕ) (hr : r ≤ N) (s : Fin r) (m : RMsg),
    ∑' seeds : Fin r → Bytes 32, PMF.uniformOfFintype (Fin r → Bytes 32) seeds *
      loopRefuseProb p prims T (seeds s) (bmsg (seedRing p prims hr seeds) m).toList

/-- The worst-message refusal term is at most `1`. -/
theorem mldsaRefuseAvg_le_one (T : ℕ) : mldsaRefuseAvg p prims T ≤ 1 := by
  refine (ENNReal.tsum_le_tsum fun seed => mul_le_mul_of_nonneg_left
    (iSup_le fun _ => PMF.toOuterMeasure_apply_le_one _ _) zero_le).trans ?_
  simp only [mul_one, PMF.tsum_coe, le_refl]

/-- **The per-message refusal term is at most the worst-message term**: each member's refusal
probability is at most its largest over messages, and the average over the members' seeds of a
function of member `s`'s seed is its average over one seed (`tsum_uniformOfFintype_pi_eval`). -/
theorem mldsaRefuseMsg_le_mldsaRefuseAvg (T : ℕ) {N len : ℕ} {RMsg : Type}
    (bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len) :
    mldsaRefuseMsg p prims T bmsg ≤ mldsaRefuseAvg p prims T := by
  unfold mldsaRefuseMsg mldsaRefuseAvg
  refine iSup_le fun r => iSup_le fun hr => iSup_le fun s => iSup_le fun m => ?_
  calc _ ≤ ∑' seeds : Fin r → Bytes 32, PMF.uniformOfFintype (Fin r → Bytes 32) seeds *
          ⨆ msg : List Byte, loopRefuseProb p prims T (seeds s) msg :=
        ENNReal.tsum_le_tsum fun seeds => mul_le_mul_of_nonneg_left
          (le_iSup (fun msg => loopRefuseProb p prims T (seeds s) msg) _) zero_le
    _ = _ := BaseSigner.tsum_uniformOfFintype_pi_eval s
          fun seed => ⨆ msg : List Byte, loopRefuseProb p prims T seed msg

variable [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] {p prims} {X Y : Type} {N len : ℕ} {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg]

variable (p prims) in
/-- **The ML-DSA base signer has averaged refusal rate `mldsaRefuseAvg`** at every base message
`bmsg` and set `adm` of supported rings: the base signer reads no oracle and signs the message
`bmsg R m`, so its refusal probability at every oracle, ring and message is a value of
`loopRefuseProb` at its key seed. -/
theorem refuseAvgWithin_mldsaRefuseAvg (T : ℕ)
    (bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len)
    (adm : KeyRing (PublicKey p prims) N → Prop) :
    (mldsaBaseSigner (X := X) (Y := Y) p prims T bmsg).RefuseAvgWithin adm
      (mldsaRefuseAvg p prims T) := by
  refine ENNReal.tsum_le_tsum fun seed => mul_le_mul_of_nonneg_left ?_ zero_le
  exact iSup_le fun _ => iSup_le fun R => iSup_le fun _ => iSup_le fun _ => iSup_le fun m =>
    le_iSup_of_le (bmsg R m).toList le_rfl

variable (p prims) in
/-- **The ML-DSA base signer has refusal rate `mldsaRefuseMsg`** (`RefuseWithin`) at every base
message `bmsg` and set `adm` of supported rings: for an honest ring of `r` members, the refusal
probability of member `s` given the members' key seeds is at most `loopRefuseProb` at its seed
and the base message of the ring (the base signer reads no oracle), and its average over the seeds
is a term of the supremum `mldsaRefuseMsg`. -/
theorem refuseWithin_mldsaRefuseMsg [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] (T : ℕ)
    (bmsg : KeyRing (PublicKey p prims) N → RMsg → Bytes len)
    (adm : KeyRing (PublicKey p prims) N → Prop) :
    (mldsaBaseSigner (X := X) (Y := Y) p prims T bmsg).RefuseWithin adm
      (mldsaRefuseMsg p prims T bmsg) := by
  intro r hr s m
  let B := mldsaBaseSigner (X := X) (Y := Y) p prims T bmsg
  let eqv : (Fin r → B.KeyCoins) × ((X → Y) × B.Coins) ≃ B.RefusalDraw r :=
    { toFun := fun z => (z.2.1, z.1, z.2.2)
      invFun := fun d => (d.2.1, d.1, d.2.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  unfold BaseSigner.refuseProb
  change probUniform _ (fun d : B.RefusalDraw r => adm (B.honestRing hr d.2.1) ∧
    (B.bsign (B.sk (d.2.1 s)) (B.honestRing hr d.2.1)
      ((B.honestRing hr d.2.1).1.idxOf (B.pk (d.2.1 s))) m d.2.2).run d.1 = none) ≤ _
  rw [← QROM.probUniform_equiv eqv, probUniform_prod_eq_tsum]
  refine le_trans ?_ (le_iSup_of_le r (le_iSup_of_le hr (le_iSup_of_le s (le_iSup_of_le m le_rfl))))
  refine ENNReal.tsum_le_tsum fun seeds => mul_le_mul_of_nonneg_left ?_ zero_le
  refine ROM.probUniform_prod_le fun H => ?_
  exact QROM.probUniform_mono fun c hc => hc.2

end Generic

end GordieHowe.Ring
