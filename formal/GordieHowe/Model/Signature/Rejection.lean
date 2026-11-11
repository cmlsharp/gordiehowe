-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Signature.MultiUser
public import GordieHowe.Foundations.ToMathlib.PMFUniform

@[expose] public section

/-!
# Ring-aware signers that are a standard signer followed by a public rejection

A ring-aware base signer may be a standard signer followed by a rejection step that reads only
public data (the ML-DSA ring publishing `w₁`: a public check of the ring, then attempts of the
standard signer, each kept or rejected by a decision on the members' published values). This file
defines that form and proves what it gives: each ring-aware signature is a public post-processing
of at most `K` independent standard signatures, its output law is the law of a kept standard
attempt times the expected number of attempts, it refuses after the check with probability `qᴷ`
(`q` the probability that an attempt is not kept), and correctness and min-entropy carry over.

- `Rejection B`: a standard signer `std` on base messages with its own coins `StdCoins`, a public
  ring check `check R` and a public keep decision `keep R i m σ u` with its own public coin
  `u : KeepCoins`, classical oracle programs with query bounds. Neither `check` nor `keep` takes a
  secret key: the rejection reads only public data, by their types.
- `firstKept ps`: the first output of the attempts `ps` (each a program and its keep decision)
  that is a signature its keep decision keeps; `run_firstKept`, `firstKept_queries`.
  `Rejection.rejectWith J R i m ks sgn`: the check, then the first of the `K` attempts `sgn` kept
  with the keep coins `ks`; it reads no key. `Rejection.rejectSign J K sk R i m cs`: `rejectWith`
  with attempt `j` the standard signature of `sk` on `bmsg R m` with the standard coins
  `(cs j).1`, kept with the keep coin `(cs j).2`. `rejectSign_queries`: at most
  `qCheck + K · (qStd + qKeep)` queries. `Rejection.att`: the kept outcome of one standard attempt
  on a pair of standard and keep coins; `run_rejectSign` (after a passed check, the first kept
  attempt), `Rejection.att_eq_some` (a kept attempt is a standard signature).
- `IsRejection B J K e`: the ring-aware signer of `B` is `rejectSign J K` at every oracle and input,
  its coins read through the equivalence `e` with `K` independent pairs of standard and keep
  coins. `IsRejectionOn B J K e`: the same on honest keys only (the secret key of key coins `kc`,
  a ring holding its public key, the first position of that key), the only signing calls of the
  multi-user challenger; `IsRejection.isRejectionOn`. `IsStdOn B J K e hK`: on honest keys the
  ordinary signer `ssign` is `std` at the standard coins of attempt `0`. Satisfiable:
  `bitSigner_isRejection` (`bitSigner` with its rejection form `bitRejection`, a uniform bit kept
  when `true`, trivial keep coins, `bitCoinsEquiv`); `keepBitSigner_isRejection`,
  `keepBitSigner_isRejectionOn`, `keepBitSigner_isStdOn` (`keepBitSigner` with `keepBitRejection`,
  a uniform bit kept when a uniform keep bit is `true`).
- `Rejection.stdOracle J`: the standard signer as a signing oracle on base messages.
  `ring_sign_run_eq` (**the per-request simulation**): under `IsRejection`, the ring-aware oracle's
  reply to `(R, m)` is `rejectWith` of `K` replies of `J.stdOracle` to the same user on `bmsg R m`,
  with independent coins.
- **The law of one request.** At a fixed oracle and input, with `att c` the kept outcome of the
  standard attempt with the pair of standard and keep coins `c` (uniform: the laws below average
  over the keep coin) and `q = Pr[att c = none]`:
  `pr_findSome_none` / `pr_bsign_none_eq` (refusal: `qᴷ` after a passed check, `1` after a failed
  one), `pr_findSome_kept` / `pr_bsign_kept_eq` (for every set `T` of signatures, the probability
  of a signature in `T` is `Pr[att c ∈ T] · attemptsMean q K`, after a passed check for `bsign`),
  `attemptsUsed`, `expected_attemptsUsed` (the expected number of attempts is
  `attemptsMean q K = Σ_{j<K} qʲ`), `attemptsMean_zero`, `attemptsMean_succ`, `attemptsMean_le`
  (at most `K`), `attemptsMean_le_inv` (at most `(1 - q)⁻¹`, the inverse keep probability). The
  inductions run through `findSome_ofFn_cons`, `attemptsUsed_ofFn_cons` and the uniform-draw
  identities `pr_uniform_eq_sum`, `sum_uniform_eq_one`, `sum_uniform_ite`, `pr_uniform_equiv`,
  `uniform_pi_apply`, `sum_uniform_pi_succ`.
- **Transfer of the hypotheses.** `pr_uniform_prod_fst`: an event of the first component of a
  uniform pair. `correctWithin_of_isRejection`: a standard signer with
  correctness error `ε` gives `B.CorrectWithin (K · ε)`. `sigGivenPubLe_of_isRejection`: if a
  kept attempt's signature has conditional probability at most `γ` given its public value, so has
  `bsign`'s (the factor `attemptsMean` cancels).

## The lifting lemma

The lifting lemma is proved in `GordieHowe/Model/Signature/RejectionCtx.lean`, with the relay's
objects in `GordieHowe/Model/Signature/RejectionRelay.lean`: the keep coins are absorbed into the
adversary as side coins (`GordieHowe/Model/Quantum/Interactive/Absorb.lean`), then the requests are
relayed (`GordieHowe/Model/Quantum/Interactive/MultiRelay.lean`). For `B`
with `IsRejectionOn B J K e`, `0 < K` and a user `i₀`, every adversary `A` of the ring-aware game
(`SignOracle.ring B`) with `Q` requests and at most `t` queries has the explicit adversary
`A' = relayMUAdversary J K n hK i₀ A Q` of the standard game (`J.stdOracle`) with at most
`t + Q · (qCheck + K · qKeep)` queries. `A'` draws uniform keep coins for every request, and relays
each ring request `(R, m)` of user `s` as `K` standard requests: the standard requests of user `s`
on `bmsg R m` that `rejectWith` asks for, padded with the public-key request of user `i₀`. It
post-processes their replies by `rejectWith` with the drawn keep coins.
Against the standard challenger with `K · Q` requests:

- `muEufProb (SignOracle.ring B) A Q ≤ muEufProb J.stdOracle A' (K · Q)` (`muEufProb_le_relay`);
- `muSufProb (SignOracle.ring B) A Q ≤ muVerifyProb A' (K · Q)`
  (`muSufProb_le_muVerifyProb_relay`), with `muVerifyProb A' (K · Q)` the probability that `A'`'s
  output is a signature verifying under the key of an uncorrupted user. This is not a lifting lemma
  for MU-SUF-CMA^corr: the event of `muVerifyProb` contains the outputs repeating a signature `A'`
  passed on to `A`, so no strong-unforgeability assumption bounds it.

Not proved: the form with `Q · δ` for a `bsign` within total-variation distance `δ` of
`rejectSign J K` per request, and the lifting lemma for MU-SUF-CMA^corr, whose extra term counts
only the outputs repeating a rejected attempt that `A'` obtained and did not pass on. The relay's
event form (`AdaptiveIAlg.toOuterMeasure_le_relayAdv`) gives both games'
registers at the placement; reading the ring-aware challenger's replies off the relayed
adversary's registers there, next to the standard replies, is not formalized.
-/

namespace GordieHowe.Signature

open GordieHowe.RingSignature
open scoped ENNReal

/-! ### Independent attempts -/

section Attempts

variable {C α : Type} [Fintype C] [Nonempty C]

/-- **An event of a uniform draw as a sum**: the probability is the sum of the point masses on the
event. -/
theorem pr_uniform_eq_sum {T : Type} [Fintype T] [Nonempty T] (E : T → Prop) [DecidablePred E] :
    Pr[x ~ PMF.uniformOfFintype T : E x] =
      ∑ x, PMF.uniformOfFintype T x * (if E x then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply, tsum_fintype]
  refine Finset.sum_congr rfl fun x _ => ?_
  by_cases h : E x
  · simp [Set.mem_ofPred_eq, h]
  · simp [Set.mem_ofPred_eq, h]

/-- The point masses of a uniform draw sum to `1`. -/
theorem sum_uniform_eq_one {T : Type} [Fintype T] [Nonempty T] :
    ∑ x, PMF.uniformOfFintype T x = 1 := by
  have h := PMF.tsum_coe (PMF.uniformOfFintype T)
  rwa [tsum_fintype] at h

/-- **A constant on an event, averaged**: `∑ x, μ x · [E x] · a = Pr[E] · a`. -/
theorem sum_uniform_ite {T : Type} [Fintype T] [Nonempty T] (E : T → Prop) [DecidablePred E]
    (a : ℝ≥0∞) :
    ∑ x, PMF.uniformOfFintype T x * (if E x then a else 0) =
      Pr[x ~ PMF.uniformOfFintype T : E x] * a := by
  rw [pr_uniform_eq_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- **A uniform draw read through an equivalence is uniform.** -/
theorem pr_uniform_equiv {T T' : Type} [Fintype T] [Nonempty T] [Fintype T'] [Nonempty T']
    (e : T ≃ T') (E : T' → Prop) :
    Pr[x ~ PMF.uniformOfFintype T : E (e x)] = Pr[x ~ PMF.uniformOfFintype T' : E x] := by
  classical
  rw [pr_uniform_eq_sum, pr_uniform_eq_sum, ← e.sum_comp]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [PMF.uniformOfFintype_apply, PMF.uniformOfFintype_apply, Fintype.card_congr e]

/-- The point mass of a uniform draw of `K` independent coins. -/
theorem uniform_pi_apply (K : ℕ) (cs : Fin K → C) :
    PMF.uniformOfFintype (Fin K → C) cs = ((Fintype.card C : ℝ≥0∞) ^ K)⁻¹ := by
  rw [PMF.uniformOfFintype_apply]
  congr 1
  simp [Fintype.card_pi]

/-- **`K + 1` independent uniform coins are a uniform coin and `K` independent ones**: a sum against
the uniform draw of `Fin (K + 1) → C` splits along `Fin.cons`. -/
theorem sum_uniform_pi_succ (K : ℕ) (g : (Fin (K + 1) → C) → ℝ≥0∞) :
    ∑ cs, PMF.uniformOfFintype (Fin (K + 1) → C) cs * g cs =
      ∑ c, PMF.uniformOfFintype C c *
        ∑ cs, PMF.uniformOfFintype (Fin K → C) cs * g (Fin.cons c cs) := by
  rw [← (Fin.consEquiv fun _ : Fin (K + 1) => C).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun cs _ => ?_
  rw [← mul_assoc]
  congr 1
  rw [uniform_pi_apply, uniform_pi_apply, PMF.uniformOfFintype_apply, pow_succ',
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]

/-- **The number of attempts made** on the coins `l`: attempts run until one is kept (`att c` is a
signature), at most `l.length`. -/
def attemptsUsed (att : C → Option α) : List C → ℕ
  | [] => 0
  | c :: l => 1 + match att c with
    | some _ => 0
    | none => attemptsUsed att l

/-- **The expected number of attempts** with at most `K` attempts, each failing with probability
`q`: `Σ_{j<K} qʲ`. -/
noncomputable def attemptsMean (q : ℝ≥0∞) (K : ℕ) : ℝ≥0∞ := ∑ j ∈ Finset.range K, q ^ j

/-- With no attempts, the expected number of attempts is `0`. -/
theorem attemptsMean_zero (q : ℝ≥0∞) : attemptsMean q 0 = 0 := by
  simp [attemptsMean]

/-- **One more attempt**: `attemptsMean q (K + 1) = 1 + q · attemptsMean q K`. -/
theorem attemptsMean_succ (q : ℝ≥0∞) (K : ℕ) : attemptsMean q (K + 1) = 1 + q * attemptsMean q K := by
  rw [attemptsMean, Finset.sum_range_succ', attemptsMean, Finset.mul_sum, pow_zero, add_comm]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pow_succ']

/-- **At most `K` attempts on average**, when an attempt fails with probability at most `1`. -/
theorem attemptsMean_le {q : ℝ≥0∞} (hq : q ≤ 1) (K : ℕ) : attemptsMean q K ≤ K := by
  calc attemptsMean q K ≤ ∑ _j ∈ Finset.range K, (1 : ℝ≥0∞) :=
        Finset.sum_le_sum fun j _ => pow_le_one₀ zero_le hq
    _ = K := by simp

/-- **At most the inverse keep probability on average**: `Σ_{j<K} qʲ ≤ (1 - q)⁻¹`. -/
theorem attemptsMean_le_inv (q : ℝ≥0∞) (K : ℕ) : attemptsMean q K ≤ (1 - q)⁻¹ := by
  rw [← ENNReal.tsum_geometric]
  exact ENNReal.sum_le_tsum _

omit [Fintype C] [Nonempty C] in
/-- The first kept outcome of `K + 1` attempts: the first, if kept, else the first kept of the
rest. -/
theorem findSome_ofFn_cons (att : C → Option α) {K : ℕ} (c : C) (cs : Fin K → C) :
    (List.ofFn (Fin.cons c cs : Fin (K + 1) → C)).findSome? att =
      match att c with
      | some a => some a
      | none => (List.ofFn cs).findSome? att := by
  rw [List.ofFn_succ, List.findSome?_cons]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rfl

omit [Fintype C] [Nonempty C] in
/-- The attempts made on `K + 1` coins: one, then those on the rest if the first is not kept. -/
theorem attemptsUsed_ofFn_cons (att : C → Option α) {K : ℕ} (c : C) (cs : Fin K → C) :
    attemptsUsed att (List.ofFn (Fin.cons c cs : Fin (K + 1) → C)) =
      1 + match att c with
        | some _ => 0
        | none => attemptsUsed att (List.ofFn cs) := by
  rw [List.ofFn_succ, attemptsUsed]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- **All `K` independent attempts fail with probability `qᴷ`.** -/
theorem pr_findSome_none (att : C → Option α) : ∀ K : ℕ,
    Pr[cs ~ PMF.uniformOfFintype (Fin K → C) : (List.ofFn cs).findSome? att = none] =
      Pr[c ~ PMF.uniformOfFintype C : att c = none] ^ K
  | 0 => by
    classical
    rw [pr_uniform_eq_sum, pow_zero]
    simp only [List.ofFn_zero, List.findSome?_nil, if_true, mul_one]
    exact sum_uniform_eq_one
  | K + 1 => by
    classical
    rw [pr_uniform_eq_sum, sum_uniform_pi_succ]
    have hc : ∀ c, ∑ cs, PMF.uniformOfFintype (Fin K → C) cs *
        (if (List.ofFn (Fin.cons c cs : Fin (K + 1) → C)).findSome? att = none then 1 else 0) =
        if att c = none then
          Pr[cs ~ PMF.uniformOfFintype (Fin K → C) : (List.ofFn cs).findSome? att = none]
        else 0 := by
      intro c
      simp only [findSome_ofFn_cons]
      rcases h : att c with _ | a
      · simp only [if_true]
        rw [pr_uniform_eq_sum]
      · simp
    simp only [hc]
    rw [sum_uniform_ite, pr_findSome_none att K, pow_succ, mul_comm]

/-- **The kept outcome of `K` independent attempts lies in `T` with probability
`Pr[att c ∈ T] · attemptsMean q K`**: the law of the first kept attempt is the law of one kept
attempt, scaled by the expected number of attempts. -/
theorem pr_findSome_kept (att : C → Option α) (T : α → Prop) : ∀ K : ℕ,
    Pr[cs ~ PMF.uniformOfFintype (Fin K → C) : ∃ a, (List.ofFn cs).findSome? att = some a ∧ T a] =
      Pr[c ~ PMF.uniformOfFintype C : ∃ a, att c = some a ∧ T a] *
        attemptsMean (Pr[c ~ PMF.uniformOfFintype C : att c = none]) K
  | 0 => by
    rw [attemptsMean_zero, mul_zero]
    refine (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 fun cs _ h => ?_)
    obtain ⟨a, ha, -⟩ := h
    simp at ha
  | K + 1 => by
    classical
    rw [pr_uniform_eq_sum, sum_uniform_pi_succ, attemptsMean_succ]
    have hc : ∀ c, PMF.uniformOfFintype C c * ∑ cs, PMF.uniformOfFintype (Fin K → C) cs *
        (if ∃ a, (List.ofFn (Fin.cons c cs : Fin (K + 1) → C)).findSome? att = some a ∧ T a
          then 1 else 0) =
        PMF.uniformOfFintype C c * (if ∃ a, att c = some a ∧ T a then 1 else 0) +
          PMF.uniformOfFintype C c * (if att c = none then
            Pr[cs ~ PMF.uniformOfFintype (Fin K → C) :
              ∃ a, (List.ofFn cs).findSome? att = some a ∧ T a] else 0) := by
      intro c
      simp only [findSome_ofFn_cons]
      rcases h : att c with _ | a
      · simp only [if_true, reduceCtorEq, false_and, exists_false, if_false, mul_zero, zero_add]
        rw [pr_uniform_eq_sum]
      · simp only [Option.some.injEq, exists_eq_left', reduceCtorEq, if_false, mul_zero, add_zero]
        rw [← Finset.sum_mul, sum_uniform_eq_one, one_mul]
    simp only [hc]
    rw [Finset.sum_add_distrib, ← pr_uniform_eq_sum, sum_uniform_ite, pr_findSome_kept att T K]
    ring

/-- **The expected number of attempts is `attemptsMean q K`.** -/
theorem expected_attemptsUsed (att : C → Option α) : ∀ K : ℕ,
    ∑ cs, PMF.uniformOfFintype (Fin K → C) cs * (attemptsUsed att (List.ofFn cs) : ℝ≥0∞) =
      attemptsMean (Pr[c ~ PMF.uniformOfFintype C : att c = none]) K
  | 0 => by simp [attemptsUsed, attemptsMean_zero]
  | K + 1 => by
    classical
    rw [sum_uniform_pi_succ, attemptsMean_succ]
    have hc : ∀ c, PMF.uniformOfFintype C c * ∑ cs, PMF.uniformOfFintype (Fin K → C) cs *
        (attemptsUsed att (List.ofFn (Fin.cons c cs : Fin (K + 1) → C)) : ℝ≥0∞) =
        PMF.uniformOfFintype C c + PMF.uniformOfFintype C c * (if att c = none then
          ∑ cs, PMF.uniformOfFintype (Fin K → C) cs * (attemptsUsed att (List.ofFn cs) : ℝ≥0∞)
          else 0) := by
      intro c
      simp only [attemptsUsed_ofFn_cons]
      rcases h : att c with _ | a
      · simp only [if_true, Nat.cast_add, Nat.cast_one, mul_add, mul_one, Finset.sum_add_distrib,
          sum_uniform_eq_one]
      · simp only [add_zero, Nat.cast_one, mul_one, reduceCtorEq, if_false, mul_zero]
        rw [sum_uniform_eq_one, mul_one]
    simp only [hc]
    rw [Finset.sum_add_distrib, sum_uniform_eq_one, sum_uniform_ite, expected_attemptsUsed att K,
      mul_comm]

end Attempts

/-! ### The rejection form -/

variable {X Y : Type} {N : ℕ}

/-- **The first kept output** of the attempts `ps`, each a program and its keep decision: run them in
order; the first program that outputs a signature its keep decision keeps gives the result, `none`
if none does. -/
def firstKept {α : Type} :
    List (OracleProg X Y (Option α) × (α → OracleProg X Y Bool)) → OracleProg X Y (Option α)
  | [] => .pure none
  | pk :: ps => pk.1.bind fun
    | none => firstKept ps
    | some σ => (pk.2 σ).bind fun b => if b then .pure (some σ) else firstKept ps

/-- **The run of `firstKept`** is the first kept outcome of the attempts' runs. -/
theorem run_firstKept {α : Type} (H : X → Y) :
    ∀ ps : List (OracleProg X Y (Option α) × (α → OracleProg X Y Bool)), (firstKept ps).run H =
      ps.findSome? fun pk => match pk.1.run H with
        | none => none
        | some σ => if (pk.2 σ).run H then some σ else none
  | [] => rfl
  | pk :: ps => by
    rw [List.findSome?_cons, firstKept, OracleProg.run_bind]
    rcases hp : pk.1.run H with _ | σ
    · exact run_firstKept H ps
    · simp only [OracleProg.run_bind]
      rcases hk : (pk.2 σ).run H
      · simp only [Bool.false_eq_true, if_false]
        exact run_firstKept H ps
      · simp

/-- **`firstKept` makes at most `|ps| · (q₁ + q₂)` queries** when each program makes at most `q₁`
and each keep decision at most `q₂`. -/
theorem firstKept_queries {α : Type} {q₁ q₂ : ℕ} :
    ∀ ps : List (OracleProg X Y (Option α) × (α → OracleProg X Y Bool)),
      (∀ pk ∈ ps, pk.1.QueriesLE q₁ ∧ ∀ σ, (pk.2 σ).QueriesLE q₂) →
      (firstKept ps).QueriesLE (ps.length * (q₁ + q₂))
  | [], _ => OracleProg.QueriesLE.pure _ _
  | pk :: ps, hps => by
    have ih := firstKept_queries ps fun p' hp' => hps p' (List.mem_cons_of_mem _ hp')
    obtain ⟨hp, hk⟩ := hps pk List.mem_cons_self
    refine (hp.bind (q₂ := q₂ + ps.length * (q₁ + q₂)) fun o => ?_).mono
      (by rw [List.length_cons]; nlinarith)
    rcases o with _ | σ
    · exact ih.mono (Nat.le_add_left _ _)
    · refine (hk σ).bind fun b => ?_
      split_ifs
      · exact (OracleProg.QueriesLE.pure _ _).mono (Nat.zero_le _)
      · exact ih

variable {TB : BaseTypes} (B : BaseSigner X Y N TB)

/-- **A standard signer followed by a public rejection**, for the base signer `B`: the standard
signer `std` on base messages with its own coins, the public ring check `check R` and the public keep
decision `keep R i m σ u` on a signature for the ring `R`, the position `i` and the message `m`, with
its own public coin `u` (`KeepCoins`), with their query bounds. Neither `check` nor `keep` takes a
secret key. -/
structure Rejection where
  /-- The coins of one standard signature. -/
  StdCoins : Type
  /-- The coins of one keep decision. -/
  KeepCoins : Type
  /-- The bound on the standard signer's queries. -/
  qStd : ℕ
  /-- The standard signer. -/
  std : B.SK → B.BMsg → StdCoins → OracleProg X Y (Option B.BSig)
  /-- It makes at most `qStd` queries. -/
  std_queries : ∀ sk bm c, (std sk bm c).QueriesLE qStd
  /-- The bound on the check's queries. -/
  qCheck : ℕ
  /-- The public ring check. -/
  check : KeyRing B.PK N → OracleProg X Y Bool
  /-- It makes at most `qCheck` queries. -/
  check_queries : ∀ R, (check R).QueriesLE qCheck
  /-- The bound on the keep decision's queries. -/
  qKeep : ℕ
  /-- The public keep decision, with its coin. -/
  keep : KeyRing B.PK N → ℕ → B.Msg → B.BSig → KeepCoins → OracleProg X Y Bool
  /-- It makes at most `qKeep` queries. -/
  keep_queries : ∀ R i m σ u, (keep R i m σ u).QueriesLE qKeep

namespace Rejection

variable {B} (J : Rejection B)

/-- **The rejection step on given attempts**: the check of the ring `R`, then the first of the
attempts `sgn` whose signature the keep decision for `(R, i, m)` with the keep coin `ks j` of
attempt `j` keeps; `none` if the check fails or no attempt is kept. It takes no key: the attempts
are the only access to the signer. -/
def rejectWith (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg) {K : ℕ} (ks : Fin K → J.KeepCoins)
    (sgn : Fin K → OracleProg X Y (Option B.BSig)) : OracleProg X Y (Option B.BSig) :=
  (J.check R).bind fun ok =>
    if ok then firstKept (List.ofFn fun j => (sgn j, fun σ => J.keep R i m σ (ks j)))
    else .pure none

/-- **The ring-aware signer of the rejection form** with `K` attempts: `rejectWith` with attempt `j`
the standard signature of `sk` on `bmsg R m` with the standard coins `(cs j).1`, kept by the keep
decision with the keep coin `(cs j).2`. -/
def rejectSign (K : ℕ) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (cs : Fin K → J.StdCoins × J.KeepCoins) : OracleProg X Y (Option B.BSig) :=
  J.rejectWith R i m (fun j => (cs j).2) fun j => J.std sk (B.bmsg R m) (cs j).1

/-- The rejection signer makes at most `qCheck + K · (qStd + qKeep)` queries. -/
theorem rejectSign_queries (K : ℕ) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (cs : Fin K → J.StdCoins × J.KeepCoins) :
    (J.rejectSign K sk R i m cs).QueriesLE (J.qCheck + K * (J.qStd + J.qKeep)) := by
  refine (J.check_queries R).bind fun ok => ?_
  split_ifs
  · have h := firstKept_queries (q₁ := J.qStd) (q₂ := J.qKeep)
      (List.ofFn fun j => (J.std sk (B.bmsg R m) (cs j).1, fun σ => J.keep R i m σ (cs j).2))
      (fun p hp => by
        obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hp
        exact ⟨J.std_queries _ _ _, fun σ => J.keep_queries _ _ _ _ _⟩)
    rwa [List.length_ofFn] at h
  · exact (OracleProg.QueriesLE.pure _ _).mono (Nat.zero_le _)

/-- **The standard signer as a signing oracle** on base messages. -/
@[reducible] def stdOracle : SignOracle B.core where
  SMsg := B.BMsg
  Coins := J.StdCoins
  q := J.qStd
  sign kp bm c := J.std kp.2 bm c
  sign_queries kp bm c := J.std_queries kp.2 bm c
  base bm := bm

/-- **The kept outcome of one standard attempt** at the oracle `H` with the standard coins `c.1`
and the keep coin `c.2`: its signature if the standard signer outputs one and the keep decision
keeps it, else `none`. -/
def att (H : X → Y) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (c : J.StdCoins × J.KeepCoins) : Option B.BSig :=
  match (J.std sk (B.bmsg R m) c.1).run H with
  | none => none
  | some σ => if (J.keep R i m σ c.2).run H then some σ else none

/-- **The run of the rejection signer**: after a passed check, the first kept attempt. -/
theorem run_rejectSign (H : X → Y) (K : ℕ) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg)
    (cs : Fin K → J.StdCoins × J.KeepCoins) :
    (J.rejectSign K sk R i m cs).run H =
      if (J.check R).run H then (List.ofFn cs).findSome? (J.att H sk R i m) else none := by
  rw [rejectSign, rejectWith, OracleProg.run_bind]
  split_ifs
  · rw [run_firstKept, show (List.ofFn fun j =>
        (J.std sk (B.bmsg R m) (cs j).1, fun σ => J.keep R i m σ (cs j).2)) =
        (List.ofFn cs).map (fun c => (J.std sk (B.bmsg R m) c.1, fun σ => J.keep R i m σ c.2)) by
        rw [List.map_ofFn]; rfl,
      List.findSome?_map]
    congr 1
    funext c
    simp only [Function.comp, att]
    rcases (J.std sk (B.bmsg R m) c.1).run H with _ | σ <;> rfl
  · rfl

end Rejection

/-- **The ring-aware signer of `B` is the rejection form `J` with `K` attempts**: at every oracle and
input its run is that of `rejectSign J K`, its coins read as `K` independent pairs of standard and
keep coins through `e`. -/
def IsRejection (J : Rejection B) (K : ℕ) (e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)) :
    Prop :=
  ∀ (H : X → Y) (sk : B.SK) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg) (c : B.Coins),
    (B.bsign sk R i m c).run H = (J.rejectSign K sk R i m (e c)).run H

/-- **The ring-aware signer of `B` is the rejection form `J` on honest keys**: at every oracle, key
coins `kc`, ring `R` holding the public key of `kc`, message and coins, the run of `bsign` with the
secret key of `kc` at the first position of its public key in `R` is that of `rejectSign J K`, its
coins read through `e`. These are the only signing calls of the multi-user challenger with the
ring-aware oracle (`SignOracle.ring`). -/
def IsRejectionOn [DecidableEq TB.PK] (J : Rejection B) (K : ℕ)
    (e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)) :
    Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N), B.pk kc ∈ R.1 → ∀ (m : B.Msg) (c : B.Coins),
    (B.bsign (B.sk kc) R (R.1.idxOf (B.pk kc)) m c).run H =
      (J.rejectSign K (B.sk kc) R (R.1.idxOf (B.pk kc)) m (e c)).run H

/-- **The ordinary signer of `B` is the standard signer on honest keys**, for `0 < K`: at every
oracle, key coins `kc`, base message and coins `c`, the run of `ssign` with the secret key of `kc`
is that of `J.std` with the standard coins of attempt `0` of `e c`. -/
def IsStdOn (J : Rejection B) (K : ℕ) (e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins))
    (hK : 0 < K) : Prop :=
  ∀ (H : X → Y) (kc : B.KeyCoins) (bm : B.BMsg) (c : B.Coins),
    (B.ssign (B.sk kc) bm c).run H = (J.std (B.sk kc) bm (e c ⟨0, hK⟩).1).run H

variable {B} {J : Rejection B} {K : ℕ} {e : B.Coins ≃ (Fin K → J.StdCoins × J.KeepCoins)}

/-- **The rejection form at every key is the rejection form on honest keys.** -/
theorem IsRejection.isRejectionOn [DecidableEq TB.PK] (h : IsRejection B J K e) :
    IsRejectionOn B J K e :=
  fun H kc R _ m c => h H (B.sk kc) R _ m c

/-- **The per-request simulation**: under `IsRejection`, the ring-aware oracle's reply to `(R, m)`
by the key pair `kp` is `rejectWith` of `K` replies of the standard oracle to the same key pair on
`bmsg R m`, with the independent standard coins `(e c j).1` and keep coins `(e c j).2`; refused when
the key is not in the ring. -/
theorem ring_sign_run_eq [DecidableEq TB.PK]
    (h : IsRejection B J K e) (H : X → Y) (kp : B.PK × B.SK)
    (R : KeyRing B.PK N) (m : B.Msg) (c : B.Coins) :
    ((SignOracle.ring B).sign kp (R, m) c).run H =
      if kp.1 ∈ R.1 then
        (J.rejectWith R (R.1.idxOf kp.1) m (fun j => (e c j).2) fun j =>
          J.stdOracle.sign kp (B.bmsg R m) (e c j).1).run H
      else none := by
  change (if kp.1 ∈ R.1 then B.bsign kp.2 R (R.1.idxOf kp.1) m c else .pure none).run H = _
  split_ifs
  · exact h H kp.2 R _ m c
  · rfl

variable [Fintype J.StdCoins] [Nonempty J.StdCoins] [Fintype J.KeepCoins] [Nonempty J.KeepCoins]

/-- **The refusal of a rejection signer**: `qᴷ` after a passed check, with `q` the probability that
an attempt is not kept (over its standard and keep coins); `1` after a failed check. -/
theorem pr_bsign_none_eq [Fintype TB.Coins] [Nonempty TB.Coins] (h : IsRejection B J K e) (H : X → Y)
    (sk : B.SK) (R : KeyRing B.PK N)
    (i : ℕ) (m : B.Msg) :
    Pr[c ~ PMF.uniformOfFintype B.Coins : (B.bsign sk R i m c).run H = none] =
      if (J.check R).run H then
        Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) : J.att H sk R i m c = none] ^ K
      else 1 := by
  simp only [h H sk R i m, Rejection.run_rejectSign]
  rw [pr_uniform_equiv e (fun cs => (if (J.check R).run H then
    (List.ofFn cs).findSome? (J.att H sk R i m) else none) = none)]
  split_ifs
  · exact pr_findSome_none _ K
  · exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).2 fun _ _ => rfl

/-- **The output law of a rejection signer is a kept attempt's law times the expected number of
attempts**: for every set `T` of signatures, after a passed check the probability that `bsign`
outputs a signature in `T` is the probability that one standard attempt is kept with a signature in
`T` (over its standard and keep coins), times `attemptsMean q K`; after a failed check it is `0`. -/
theorem pr_bsign_kept_eq [Fintype TB.Coins] [Nonempty TB.Coins] (h : IsRejection B J K e) (H : X → Y)
    (sk : B.SK) (R : KeyRing B.PK N)
    (i : ℕ) (m : B.Msg) (T : B.BSig → Prop) :
    Pr[c ~ PMF.uniformOfFintype B.Coins : ∃ σ, (B.bsign sk R i m c).run H = some σ ∧ T σ] =
      (if (J.check R).run H then 1 else 0) *
        Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) :
          ∃ σ, J.att H sk R i m c = some σ ∧ T σ] *
          attemptsMean (Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) :
            J.att H sk R i m c = none]) K := by
  simp only [h H sk R i m, Rejection.run_rejectSign]
  rw [pr_uniform_equiv e (fun cs => ∃ σ, (if (J.check R).run H then
    (List.ofFn cs).findSome? (J.att H sk R i m) else none) = some σ ∧ T σ)]
  split_ifs
  · rw [one_mul]
    exact pr_findSome_kept _ T K
  · rw [zero_mul, zero_mul]
    refine (PMF.toOuterMeasure_apply_eq_zero_iff _ _).2 (Set.disjoint_left.2 fun cs _ hc => ?_)
    obtain ⟨σ, hσ, -⟩ := hc
    simp_all

/-- **A kept attempt is a standard signature** on the attempt's standard coins. -/
theorem Rejection.att_eq_some (J : Rejection B) {H : X → Y} {sk : B.SK} {R : KeyRing B.PK N}
    {i : ℕ} {m : B.Msg} {c : J.StdCoins × J.KeepCoins} {σ : B.BSig}
    (h : J.att H sk R i m c = some σ) : (J.std sk (B.bmsg R m) c.1).run H = some σ := by
  unfold Rejection.att at h
  rcases hs : (J.std sk (B.bmsg R m) c.1).run H with _ | σ'
  · rw [hs] at h
    simp at h
  · rw [hs] at h
    simp only at h
    split_ifs at h
    exact h

/-- **An event of the first component of a uniform pair** has the probability of the event under
the uniform first component. -/
theorem pr_uniform_prod_fst {T U : Type} [Fintype T] [Nonempty T] [Fintype U] [Nonempty U]
    (E : T → Prop) :
    Pr[c ~ PMF.uniformOfFintype (T × U) : E c.1] = Pr[x ~ PMF.uniformOfFintype T : E x] := by
  rw [← PMF.map_fst_uniformOfFintype (α := T) (β := U), PMF.toOuterMeasure_map_apply]
  rfl

/-- **Correctness of a rejection signer from the standard signer's**: if the standard signer outputs
a signature that fails base verification with probability at most `ε` at every oracle, key and base
message, the ring-aware signer has correctness error at most `K · ε`. -/
theorem correctWithin_of_isRejection [Fintype TB.Coins] [Nonempty TB.Coins] (h : IsRejection B J K e)
    {ε : ℝ≥0∞}
    (hstd : ∀ (H : X → Y) (kc : B.KeyCoins) (bm : B.BMsg),
      Pr[c ~ PMF.uniformOfFintype J.StdCoins :
        ∃ σ, (J.std (B.sk kc) bm c).run H = some σ ∧ B.bverify H (B.pk kc) bm σ = false] ≤ ε) :
    B.CorrectWithin (K * ε) := by
  intro H kc R i _ m
  rw [pr_bsign_kept_eq h H _ R i m (fun σ => B.bverify H (B.pk kc) (B.bmsg R m) σ = false)]
  have hq : Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) :
      J.att H (B.sk kc) R i m c = none] ≤ 1 :=
    PMF.toOuterMeasure_apply_le_one _ _
  have h1 : Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) :
      ∃ σ, J.att H (B.sk kc) R i m c = some σ ∧ B.bverify H (B.pk kc) (B.bmsg R m) σ = false] ≤
      ε :=
    (PMF.toOuterMeasure_mono _ fun c hc => by
      obtain ⟨⟨σ, hσ, hv⟩, -⟩ := hc
      exact ⟨σ, J.att_eq_some hσ, hv⟩).trans
      ((pr_uniform_prod_fst (U := J.KeepCoins) (fun c => ∃ σ,
        (J.std (B.sk kc) (B.bmsg R m) c).run H = some σ ∧
          B.bverify H (B.pk kc) (B.bmsg R m) σ = false)).le.trans (hstd H kc (B.bmsg R m)))
  calc (if (J.check R).run H then 1 else 0) * _ * _ ≤ 1 * ε * K := by
        refine mul_le_mul' (mul_le_mul' (by split_ifs <;> simp) h1) (attemptsMean_le hq K)
    _ = K * ε := by ring

/-- **Min-entropy of a rejection signer from a kept attempt's**: if, at every oracle and input, a
kept standard attempt (over its standard and keep coins) outputs `σ` with public value `y` with
probability at most `γ` times the probability that it is kept with public value `y`, the ring-aware
signer satisfies `SigGivenPubLe γ` (the expected number of attempts multiplies both sides). -/
theorem sigGivenPubLe_of_isRejection [Fintype TB.Coins] [Nonempty TB.Coins] (h : IsRejection B J K e)
    {γ : ℝ≥0∞}
    (hatt : ∀ (H : X → Y) (kc : B.KeyCoins) (R : KeyRing B.PK N) (i : ℕ) (m : B.Msg) (y : B.Pub)
      (σ : B.BSig),
      Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) :
          J.att H (B.sk kc) R i m c = some σ ∧ (B.pub (B.pk kc) σ).run H = y] ≤
        γ * Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) :
          ∃ σ', J.att H (B.sk kc) R i m c = some σ' ∧ (B.pub (B.pk kc) σ').run H = y]) :
    B.SigGivenPubLe γ := by
  intro H kc R i _ m y σ
  have hl : ∀ {Ω : Type} (f : Ω → Option B.BSig) (μ : PMF Ω),
      μ.toOuterMeasure (Set.ofPred fun c => f c = some σ ∧ (B.pub (B.pk kc) σ).run H = y) =
        μ.toOuterMeasure (Set.ofPred fun c =>
          ∃ σ', f c = some σ' ∧ (σ' = σ ∧ (B.pub (B.pk kc) σ').run H = y)) := by
    intro Ω f μ
    congr 1
    ext c
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hc, hy⟩
      exact ⟨σ, hc, rfl, hy⟩
    · rintro ⟨σ', hc, rfl, hy⟩
      exact ⟨hc, hy⟩
  rw [hl, pr_bsign_kept_eq h H _ R i m (fun σ' => σ' = σ ∧ (B.pub (B.pk kc) σ').run H = y),
    pr_bsign_kept_eq h H _ R i m (fun σ' => (B.pub (B.pk kc) σ').run H = y),
    ← hl (J.att H (B.sk kc) R i m)]
  calc (if (J.check R).run H then 1 else 0) * _ * _ ≤
      (if (J.check R).run H then 1 else 0) *
        (γ * Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) :
          ∃ σ', J.att H (B.sk kc) R i m c = some σ' ∧ (B.pub (B.pk kc) σ').run H = y]) *
        attemptsMean (Pr[c ~ PMF.uniformOfFintype (J.StdCoins × J.KeepCoins) :
          J.att H (B.sk kc) R i m c = none]) K :=
        mul_le_mul' (mul_le_mul' le_rfl (hatt H kc R i m y σ)) le_rfl
    _ = _ := by ring

/-! ### Rejection signers -/

/-- The types of `bitSigner K`: one key, one message and one public value; bit signatures; `K` coin
bits. -/
abbrev bitSignerT (K : ℕ) : BaseTypes where
  PK := Unit
  SK := Unit
  KeyCoins := Unit
  Msg := Unit
  BMsg := Unit
  BSig := Bool
  Pub := Unit
  Coins := Fin K → Bool

variable (X Y N) in
/-- **A base signer of the rejection form**: one key, one message, one public value; a signature is
a bit; each of `K` attempts draws a uniform bit and keeps it when it is `true` (keep probability
`1/2`); the ring check passes. -/
def bitSigner (K : ℕ) : BaseSigner X Y N (bitSignerT K) where
  keyGen _ := ((), ())
  bmsg _ _ := ()
  q := 0
  bsign _ _ _ _ cs := .pure ((List.ofFn cs).findSome? fun b => if b then some b else none)
  bsign_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _
  ssign _ _ _ := .pure (some true)
  ssign_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  bverify _ _ _ _ := true
  qPub := 0
  pub _ _ := .pure ()
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

variable (X Y N) in
/-- The rejection form of `bitSigner`: a uniform bit as the standard signature, kept when `true`;
the keep coins are trivial (`Unit`). -/
@[reducible] def bitRejection (K : ℕ) : Rejection (bitSigner X Y N K) where
  StdCoins := Bool
  KeepCoins := Unit
  qStd := 0
  std _ _ c := .pure (some c)
  std_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  qCheck := 0
  check _ := .pure true
  check_queries _ := OracleProg.QueriesLE.pure _ _
  qKeep := 0
  keep _ _ _ σ _ := .pure σ
  keep_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _

/-- The coins of `bitSigner` as pairs of a standard coin and a trivial keep coin. -/
def bitCoinsEquiv (K : ℕ) : (Fin K → Bool) ≃ (Fin K → Bool × Unit) where
  toFun cs j := (cs j, ())
  invFun cs j := (cs j).1
  left_inv _ := rfl
  right_inv _ := rfl

/-- **`IsRejection` is satisfiable**: `bitSigner` is its rejection form with `K` attempts. -/
theorem bitSigner_isRejection (K : ℕ) :
    IsRejection (bitSigner X Y N K) (bitRejection X Y N K) K (bitCoinsEquiv K) := by
  intro H sk R i m (c : Fin K → Bool)
  rw [Rejection.run_rejectSign]
  change (List.ofFn c).findSome? (fun b => if b then some b else none) =
    (List.ofFn fun j => (c j, ())).findSome? _
  rw [show (List.ofFn fun j => (c j, ())) = (List.ofFn c).map fun b => (b, ()) by
    rw [List.map_ofFn]; rfl]
  generalize List.ofFn c = l
  induction l with
  | nil => rfl
  | cons b l ih =>
    cases b
    · exact ih
    · rfl

/-- The types of `keepBitSigner K`: one key, one message and one public value; bit signatures; `K`
pairs of a signature bit and a keep bit. -/
abbrev keepBitSignerT (K : ℕ) : BaseTypes where
  PK := Unit
  SK := Unit
  KeyCoins := Unit
  Msg := Unit
  BMsg := Unit
  BSig := Bool
  Pub := Unit
  Coins := Fin K → Bool × Bool

variable (X Y N) in
/-- **A base signer of the rejection form with a public keep coin**: as `bitSigner`, but each of
`K` attempts draws a uniform signature bit and a uniform keep bit, and keeps the signature when the
keep bit is `true`; the ordinary signer outputs the signature bit of the first attempt. -/
def keepBitSigner (K : ℕ) : BaseSigner X Y N (keepBitSignerT K) where
  keyGen _ := ((), ())
  bmsg _ _ := ()
  q := 0
  bsign _ _ _ _ cs := .pure ((List.ofFn cs).findSome? fun c => if c.2 then some c.1 else none)
  bsign_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _
  ssign _ _ cs := .pure ((List.ofFn cs).head?.map Prod.fst)
  ssign_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  bverify _ _ _ _ := true
  qPub := 0
  pub _ _ := .pure ()
  pub_queries _ _ := OracleProg.QueriesLE.pure _ _

variable (X Y N) in
/-- The rejection form of `keepBitSigner`: a uniform bit as the standard signature, kept when the
uniform keep bit is `true`. -/
@[reducible] def keepBitRejection (K : ℕ) : Rejection (keepBitSigner X Y N K) where
  StdCoins := Bool
  KeepCoins := Bool
  qStd := 0
  std _ _ c := .pure (some c)
  std_queries _ _ _ := OracleProg.QueriesLE.pure _ _
  qCheck := 0
  check _ := .pure true
  check_queries _ := OracleProg.QueriesLE.pure _ _
  qKeep := 0
  keep _ _ _ _ u := .pure u
  keep_queries _ _ _ _ _ := OracleProg.QueriesLE.pure _ _

/-- `keepBitSigner` is its rejection form with `K` attempts. -/
theorem keepBitSigner_isRejection (K : ℕ) :
    IsRejection (keepBitSigner X Y N K) (keepBitRejection X Y N K) K (Equiv.refl _) := by
  intro H sk R i m c
  rw [Rejection.run_rejectSign]
  rfl

/-- **`IsRejectionOn` is satisfiable with nontrivial keep coins**: `keepBitSigner`, whose keep
decision reads a uniform keep bit, is its rejection form on honest keys. -/
theorem keepBitSigner_isRejectionOn (K : ℕ) :
    IsRejectionOn (keepBitSigner X Y N K) (keepBitRejection X Y N K) K (Equiv.refl _) :=
  (keepBitSigner_isRejection K).isRejectionOn

/-- **`IsStdOn` is satisfiable**: the ordinary signer of `keepBitSigner` with `K + 1` attempts is
the standard signer at the coins of the first attempt. -/
theorem keepBitSigner_isStdOn (K : ℕ) :
    IsStdOn (keepBitSigner X Y N (K + 1)) (keepBitRejection X Y N (K + 1)) (K + 1) (Equiv.refl _)
      K.succ_pos := by
  intro H kc bm (c : Fin (K + 1) → Bool × Bool)
  change ((List.ofFn c).head?.map Prod.fst) = some (c 0).1
  rw [List.ofFn_succ]
  rfl

end GordieHowe.Signature
