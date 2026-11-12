-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Scheme
public import GordieHowe.Model.Signature.Scheme
public import GordieHowe.Foundations.Probability.Advantage

@[expose] public section

/-!
# Completeness of a ring signature scheme

The completeness game of a `RingScheme` (BKM06, ePrint 2005/304, Definition 1, p. 3: "for any
`{(PK_i, SK_i)}` output by `Gen`, any `s ∈ [n]`, and any `M`, `Vrfy_R(M, Sign_{s,SK_s}(M, R)) = 1`
where `R = (PK_1, …, PK_n)`").

- `RingScheme.honestRing`: the ring of the public keys of `r` honest users, in order.
- `RingScheme.refuseProb`, `RingScheme.rejectProb`: for a ring size `r`, a signer position `s` and
  a message, the probability over the oracle, the members' key coins and the signing coins that the
  ring is supported and the honest signer refuses it, and that the ring is supported, the signer
  signs and verification rejects. `refuseProb_add_rejectProb`: their sum is the probability that a
  supported honest ring yields no verifying signature.
- `RingScheme.CompleteWithin S εr εv`: refusal at most `εr` and rejection at most `εv` for every
  supported honest ring, signer and message.
- `RingScheme.trivial`, `trivial_completeWithin`: a scheme with errors `0` and `0` (the hypothesis is
  satisfiable).

## Comparison with BKM06 Definition 1

1. **An error, reported in two parts.** BKM06 requires verification to accept always. Here the
   signer may refuse (the bounded loops of Falcon and ML-DSA, the public ring check of the ML-DSA
   ring publishing `w₁`) and verification may reject (the bounded `HashToPoint`, the completeness
   error of the proof system); `CompleteWithin` bounds the two probabilities separately, so a
   refusal is never hidden in the rejection error.
2. **Averaged over the honest keys and the oracle.** BKM06 quantifies over every key output by
   `Gen`; here the members' key coins are uniform, as are the oracle and the signing coins, and the
   bound holds for every ring size, position and message. A scheme whose signer refuses rings of
   rare keys (the ML-DSA ring publishing `w₁` refuses rings of high defect) has a small error in
   this sense and is not complete in BKM06's.
3. **Supported rings only.** Rings outside `Supported` are excluded (BKM06's `c`-user schemes, p. 4:
   "correctness is only required to hold for such rings"); the event includes `Supported R`, so the
   probability needs no conditioning.
4. **Rings of honest keys in any order, with repetitions** (`honestRing` lists the `r` users'
   keys; two users may share a key only when their coins give the same key).
-/

namespace GordieHowe.RingSignature

open scoped ENNReal

namespace RingScheme

variable {X Y : Type} {N : ℕ} {TS : RingTypes} (S : RingScheme X Y N TS)

/-- **The ring of `r` honest users** with key coins `keys`: their public keys in order. -/
def honestRing {r : ℕ} (hr : r ≤ N) (keys : Fin r → S.KeyCoins) : KeyRing S.PK N :=
  ⟨List.ofFn fun j => S.pk (keys j), by simpa using hr⟩

/-- **The signer's key is in an honest ring**: user `s`'s public key is a member. -/
theorem pk_mem_honestRing {r : ℕ} (hr : r ≤ N) (keys : Fin r → S.KeyCoins) (s : Fin r) :
    S.pk (keys s) ∈ (S.honestRing hr keys).1 :=
  List.mem_ofFn.2 ⟨s, rfl⟩

/-- The draws of the completeness game with `r` members: the oracle, the members' key coins and
the signing coins. -/
abbrev CompletenessDraw (r : ℕ) : Type :=
  Signature.SigningDraw X Y (Fin r → S.KeyCoins) S.SignCoins

variable [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [Fintype TS.KeyCoins]
  [Nonempty TS.KeyCoins] [Fintype TS.SignCoins] [Nonempty TS.SignCoins]

/-- **The refusal probability** for `r` members, signer position `s` and message `m`: over a
uniform oracle, uniform key coins of the members and uniform signing coins, the probability that
the honest ring is supported and user `s` refuses to sign `m` on it. -/
noncomputable def refuseProb {r : ℕ} (hr : r ≤ N) (s : Fin r) (m : S.Msg) : ℝ≥0∞ :=
  Pr[d ~ PMF.uniformOfFintype (S.CompletenessDraw r) :
    S.Supported (S.honestRing hr d.keys) ∧
      (S.sign (S.keyGen (d.keys s)) (S.honestRing hr d.keys) m d.coins).run
        d.oracle = none]

/-- **The rejection probability** for `r` members, signer position `s` and message `m`: the
probability that the honest ring is supported, user `s` signs `m` on it, and verification rejects
the signature. -/
noncomputable def rejectProb {r : ℕ} (hr : r ≤ N) (s : Fin r) (m : S.Msg) : ℝ≥0∞ :=
  Pr[d ~ PMF.uniformOfFintype (S.CompletenessDraw r) :
    S.Supported (S.honestRing hr d.keys) ∧
      ∃ σ, (S.sign (S.keyGen (d.keys s)) (S.honestRing hr d.keys) m d.coins).run
        d.oracle = some σ ∧
        S.verify d.oracle (S.honestRing hr d.keys) m σ = false]

/-- **The scheme is complete with refusal error `εr` and rejection error `εv`**: for every ring
size `r ≤ N`, signer position and message, the refusal probability is at most `εr` and the rejection
probability at most `εv`. -/
structure CompleteWithin (εr εv : ℝ≥0∞) : Prop where
  /-- The refusal probability is at most `εr`. -/
  refuseProb_le : ∀ (r : ℕ) (hr : r ≤ N) (s : Fin r) (m : S.Msg), S.refuseProb hr s m ≤ εr
  /-- The rejection probability is at most `εv`. -/
  rejectProb_le : ∀ (r : ℕ) (hr : r ≤ N) (s : Fin r) (m : S.Msg), S.rejectProb hr s m ≤ εv

variable {S} in
/-- Completeness at errors `εr, εv` gives completeness at every larger errors. -/
theorem CompleteWithin.mono {εr εv εr' εv' : ℝ≥0∞} (h : S.CompleteWithin εr εv) (hr : εr ≤ εr')
    (hv : εv ≤ εv') : S.CompleteWithin εr' εv' :=
  ⟨fun r h' s m => (h.refuseProb_le r h' s m).trans hr,
    fun r h' s m => (h.rejectProb_le r h' s m).trans hv⟩

/-- **Refusal and rejection split the failure**: their probabilities sum to the probability that the
honest ring is supported and the signer does not output a verifying signature. -/
theorem refuseProb_add_rejectProb {r : ℕ} (hr : r ≤ N) (s : Fin r) (m : S.Msg) :
    S.refuseProb hr s m + S.rejectProb hr s m =
      Pr[d ~ PMF.uniformOfFintype (S.CompletenessDraw r) :
        S.Supported (S.honestRing hr d.keys) ∧
          ¬ ∃ σ, (S.sign (S.keyGen (d.keys s)) (S.honestRing hr d.keys) m d.coins).run
              d.oracle = some σ ∧
            S.verify d.oracle (S.honestRing hr d.keys) m σ = true] := by
  classical
  rw [refuseProb, rejectProb, PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply,
    PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine tsum_congr fun d => ?_
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  by_cases hs : S.Supported (S.honestRing hr d.keys)
  · rcases Option.eq_none_or_eq_some
      ((S.sign (S.keyGen (d.keys s)) (S.honestRing hr d.keys) m d.coins).run
        d.oracle) with h | ⟨σ, h⟩
    · simp [hs, h]
    · cases hv : S.verify d.oracle (S.honestRing hr d.keys) m σ <;> simp [hs, h, hv]
  · simp [hs]

/-! ### A complete scheme -/

/-- The types of `trivial`: one key, one message, one signature, trivial coins. -/
abbrev trivialT : RingTypes where
  PK := Unit
  SK := Unit
  Msg := Unit
  Sig := Unit
  KeyCoins := Unit
  SignCoins := Unit

variable (X Y N) in
/-- **The trivial ring signature scheme**: one key, one message, one signature; the signer signs
exactly the rings holding its key, verification accepts everything, every ring is supported. It is
complete with errors `0` and `0` (`trivial_completeWithin`), so `CompleteWithin` is satisfiable. -/
def trivial : RingScheme X Y N trivialT where
  keyGen _ := ((), ())
  q := 0
  sign kp R _ _ := .pure (if kp.1 ∈ R.1 then some () else none)
  sign_queries _ _ _ _ := OracleProg.QueriesLE.pure _ _
  verify _ _ _ _ := true
  Supported _ := True

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] in
/-- The trivial scheme refuses outside its rings. -/
theorem trivial_refusesOutside : (trivial X Y N).RefusesOutside := by
  refine (RingScheme.refusesOutside_iff _).2 ?_
  rintro kp R m c H (h | h)
  · change (if kp.1 ∈ R.1 then some () else none) = none
    simp [h]
  · exact absurd True.intro h

/-- **The trivial scheme is complete with errors `0` and `0`.** -/
theorem trivial_completeWithin : (trivial X Y N).CompleteWithin 0 0 := by
  constructor
  · intro r hr s m
    refine le_of_eq ?_
    rw [refuseProb, PMF.toOuterMeasure_apply_eq_zero_iff]
    refine Set.disjoint_left.2 fun d _ hd => ?_
    have hmem := (trivial X Y N).pk_mem_honestRing hr d.keys s
    simp only [Set.mem_ofPred_eq] at hd
    have h2 := hd.2
    change (if _ ∈ _ then some () else none) = none at h2
    split_ifs at h2
  · intro r hr s m
    refine le_of_eq ?_
    rw [rejectProb, PMF.toOuterMeasure_apply_eq_zero_iff]
    refine Set.disjoint_left.2 fun d _ hd => ?_
    simp only [Set.mem_ofPred_eq] at hd
    obtain ⟨σ, -, hv⟩ := hd.2
    exact Bool.noConfusion hv

end RingScheme

end GordieHowe.RingSignature
