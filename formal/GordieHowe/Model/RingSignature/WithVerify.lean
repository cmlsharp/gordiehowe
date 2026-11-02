-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.KeyReuse
public import GordieHowe.Model.Quantum.Interactive.RelabelAdversary

@[expose] public section

/-!
# A ring scheme with another verifier

The unforgeability games of a ring scheme `S` and of `S.withVerify v`, the same scheme with the
verifier `v`, have the same run: the challenger answers requests by the signer, which does not
change. A forgery against `S` outside an event `E` of the forgery is a forgery against
`S.withVerify v` whenever `v` accepts what `S.verify` accepts outside `E`. The adversary of one
game is one of the other relabelled through the identical requests and replies
(`GameAdversary.relabel`).

- `RingScheme.withVerify`, `RingScheme.pk_withVerify`, `SideOracle.withVerify`: the scheme with
  the verifier `v` and its public keys, and a side oracle of `S` read as one of `S.withVerify v`.
- `withVerifyReq`, `withVerifyResp`: the requests and the replies of the two games.
- `forgeProbOn`: the probability of a forgery in an event `E` of the forgery.
- `UnforgeAdversary.withVerify`: an adversary of the game of `S` as one of the game of
  `S.withVerify v`.
- `relabel_unforgeChallenger_withVerify`: the challenger of `S.withVerify v` relabelled is the
  challenger of `S`.
- `forges_withVerify`: a forgery against `S` outside `E` is one against `S.withVerify v` for the
  relabelled history.
- `forgeProb_withVerify_eq`: the forgery probability of the relabelled adversary against
  `S.withVerify v` as an event of the run against `S`.
- `forgeProb_le_withVerify`, `insiderForgeProb_le_withVerify`: the forgery probability against `S`
  is at most that against `S.withVerify v` plus the forgery probability in `E`.
- `forgeProbOn_le_forgeProb`: the forgery probability in `E` is at most the forgery probability.
-/

namespace GordieHowe.RingSignature

open GordieHowe.Quantum
open scoped ENNReal

variable {X Y : Type} {N : ℕ}

/-- **The ring scheme `S` with the verifier `v`**: every other field of `S`. -/
abbrev RingScheme.withVerify {TS : RingTypes} (S : RingScheme X Y N TS)
    (v : (X → Y) → KeyRing S.PK N → S.Msg → S.Sig → Bool) : RingScheme X Y N TS :=
  { S with verify := v }

variable {TS : RingTypes} {S : RingScheme X Y N TS} (v : (X → Y) → KeyRing S.PK N → S.Msg → S.Sig → Bool)

/-- The public keys of `S.withVerify v` are those of `S`. -/
@[simp] theorem RingScheme.pk_withVerify (kc : S.KeyCoins) : (S.withVerify v).pk kc = S.pk kc :=
  rfl

/-- **A side oracle of `S` as one of `S.withVerify v`**: the same messages, signatures, signer
and covering. -/
abbrev SideOracle.withVerify (O : SideOracle S) : SideOracle (S.withVerify v) where
  BMsg := O.BMsg
  BSig := O.BSig
  q := O.q
  sign := O.sign
  sign_queries := O.sign_queries
  Covers := O.Covers

variable (O : SideOracle S) (n : ℕ)

/-- The requests of the two unforgeability games: the same constructors. -/
def withVerifyReq : UnforgeRequest n O ≃ UnforgeRequest (S := S.withVerify v) n (O.withVerify v)
    where
  toFun
    | .corrupt i => .corrupt i
    | .sign s R m => .sign s R m
    | .sideSign i bm => .sideSign i bm
  invFun
    | .corrupt i => .corrupt i
    | .sign s R m => .sign s R m
    | .sideSign i bm => .sideSign i bm
  left_inv r := by cases r <;> rfl
  right_inv r := by cases r <;> rfl

/-- The replies of the two unforgeability games: the same constructors. -/
def withVerifyResp : UnforgeResponse O ≃ UnforgeResponse (S := S.withVerify v) (O.withVerify v)
    where
  toFun
    | .keyCoins kc => .keyCoins kc
    | .signature σ => .signature σ
    | .sideSignature τ => .sideSignature τ
  invFun
    | .keyCoins kc => .keyCoins kc
    | .signature σ => .signature σ
    | .sideSignature τ => .sideSignature τ
  left_inv r := by cases r <;> rfl
  right_inv r := by cases r <;> rfl

private theorem mapOutput_bind {A B R R' R'' : Type} (p : OracleProg A B R)
    (g : R → OracleProg A B R') (f : R' → R'') :
    (p.bind g).mapOutput f = p.bind fun r => (g r).mapOutput f := by
  induction p with
  | pure r => rfl
  | query a k ih =>
    change OracleProg.query a (fun b => ((k b).bind g).mapOutput f) = _
    simp only [ih]
    rfl

/-- **The challenger of `S.withVerify v` relabelled is the challenger of `S`**: it answers by the
signer of `S`, which `withVerify` keeps. -/
theorem relabel_unforgeChallenger_withVerify (keys : Fin n → S.KeyCoins) (Q : ℕ) :
    (unforgeChallenger (S.withVerify v) n (O.withVerify v) keys Q).relabel
      (withVerifyReq v O n) (withVerifyResp v O) = unforgeChallenger S n O keys Q := by
  have hr : ∀ ω hist r,
      ((unforgeChallenger (S.withVerify v) n (O.withVerify v) keys Q).respond ω
          (hist.map (HistoryEntry.relabel (withVerifyReq v O n) (withVerifyResp v O)))
          (withVerifyReq v O n r)).mapOutput
        (fun o => (⟨o.response.map (withVerifyResp v O).symm, o.assignments⟩ :
          Reply X Y (UnforgeResponse O))) =
        (unforgeChallenger S n O keys Q).respond ω hist r := by
    intro ω hist r
    rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩ <;>
      simp only [unforgeChallenger, List.length_map, withVerifyReq, Equiv.coe_fn_mk,
        RingScheme.pk_withVerify] <;>
      split_ifs <;>
      first
        | rfl
        | (rw [mapOutput_bind]; exact congrArg _ (funext fun o => by cases o <;> rfl))
  unfold Challenger.relabel
  simp only [hr]
  rfl

variable {O n}

/-- **A forgery against `S` outside `E` is a forgery against `S.withVerify v`** for the relabelled
history, when `v` accepts the signatures `S.verify` accepts outside `E` (`hv`). -/
theorem forges_withVerify {E : KeyRing S.PK N × S.Msg × S.Sig → Prop}
    (hv : ∀ H R m σ, S.verify H R m σ = true → ¬ E (R, m, σ) → v H R m σ = true)
    {keys : Fin n → S.KeyCoins} {H : X → Y} {out : KeyRing S.PK N × S.Msg × S.Sig}
    {hist : UnforgeHist n O} (hf : Forges keys H out hist) (hE : ¬ E out) :
    Forges (S := S.withVerify v) (O := O.withVerify v) keys H out
      (hist.map (HistoryEntry.relabel (withVerifyReq v O n) (withVerifyResp v O))) := by
  have hreq : ∀ (e : HistoryEntry (UnforgeRequest n O) (UnforgeResponse O))
      (r : UnforgeRequest (S := S.withVerify v) n (O.withVerify v)),
      (e.relabel (withVerifyReq v O n) (withVerifyResp v O)).request = r →
        e.request = (withVerifyReq v O n).symm r :=
    fun e r h => (Equiv.eq_symm_apply _).2 h
  refine ⟨hv H out.1 out.2.1 out.2.2 hf.verify_eq hE, fun pk hpk => ?_, ?_, ?_⟩
  · obtain ⟨i, hi, hc⟩ := hf.fresh.honest_ring pk hpk
    refine ⟨i, hi, ?_⟩
    rintro ⟨e', he', hr⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact hc ⟨e, he, hreq e _ hr⟩
  · rintro ⟨e', he', s, hr⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact hf.fresh.not_signQueried ⟨e, he, s, hreq e _ hr⟩
  · rintro ⟨e', he', i, bm, hr, hmem, hcov⟩
    obtain ⟨e, he, rfl⟩ := List.mem_map.1 he'
    exact hf.fresh.not_sideCovered ⟨e, he, i, bm, hreq e _ hr, hmem, hcov⟩

variable [Fintype X] [DecidableEq X] [Nonempty X] [Fintype Y] [DecidableEq Y] [AddGroup Y]
  [Nonempty Y] {V : OracleView X Y} {t : ℕ}

/-- **The probability of a forgery in the event `E`** of the forgery: the adversary terminates
with a forgery (`Forges`) whose ring, message and signature lie in `E`. -/
noncomputable def forgeProbOn (A : UnforgeAdversary S n O V t) (Q : ℕ)
    (E : KeyRing S.PK N × S.Msg × S.Sig → Prop) : ℝ≥0∞ :=
  (unforgeLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2 ∧ E p.1}

/-- **The forgery probability in an event is at most the forgery probability.** -/
theorem forgeProbOn_le_forgeProb (A : UnforgeAdversary S n O V t) (Q : ℕ)
    (E : KeyRing S.PK N × S.Msg × S.Sig → Prop) : forgeProbOn A Q E ≤ forgeProb A Q :=
  MeasureTheory.measure_mono fun _ ⟨p, hp, hf, _⟩ => ⟨p, hp, hf⟩

variable [NeZero n]

variable (O) in
/-- **The adversary `A` of the game of `S` as one of the game of `S.withVerify v`**: `A` relabelled
through the identical requests and replies (`GameAdversary.relabel`). -/
noncomputable abbrev UnforgeAdversary.withVerify (A : UnforgeAdversary S n O V t) :
    UnforgeAdversary (S.withVerify v) n (O.withVerify v) V t :=
  GameAdversary.relabel (withVerifyReq v O n) (withVerifyResp v O) A

/-- **The relabelled adversary against `S.withVerify v`** has the forgery probability of the event,
in the run of the adversary against `S`, that its output is a forgery against `S.withVerify v` for
the relabelled history. -/
theorem forgeProb_withVerify_eq (A : UnforgeAdversary S n O V t) (Q : ℕ) :
    forgeProb (UnforgeAdversary.withVerify v O A) Q =
      (unforgeLaw A Q).toOuterMeasure {x | ∃ p ∈ x.2.2,
        Forges (S := S.withVerify v) (O := O.withVerify v) x.1 x.2.1 p.1
          (p.2.map (HistoryEntry.relabel (withVerifyReq v O n) (withVerifyResp v O)))} := by
  unfold forgeProb unforgeLaw
  change (runLaw (fun (keys : Fin n → S.KeyCoins) H =>
    (A (fun i => S.pk (keys i), V.view H)).relabel (withVerifyReq v O n) (withVerifyResp v O))
    fun (keys : Fin n → S.KeyCoins) =>
      unforgeChallenger (S.withVerify v) n (O.withVerify v) keys Q).toOuterMeasure _ = _
  rw [runLaw_relabel]
  simp only [relabel_unforgeChallenger_withVerify]
  refine (PMF.toOuterMeasure_map_apply _ _ _).trans ?_
  congr 1
  ext ⟨keys, H, x⟩
  rcases x with _ | ⟨out, hist⟩
  · simp
  · simp only [Set.mem_preimage, Set.mem_ofPred_eq, Option.map_some, Option.mem_def,
      Option.some.injEq, exists_eq_left']

/-- **A forgery against `S` is a forgery against `S.withVerify v` or a forgery in `E`**: for a
verifier `v` accepting what `S.verify` accepts outside the event `E` of the forgery (`hv`), the
forgery probability of an adversary against `S` with `Q` requests is at most that of the relabelled
adversary against `S.withVerify v` plus the forgery probability in `E`. -/
theorem forgeProb_le_withVerify {E : KeyRing S.PK N × S.Msg × S.Sig → Prop}
    (hv : ∀ H R m σ, S.verify H R m σ = true → ¬ E (R, m, σ) → v H R m σ = true)
    (A : UnforgeAdversary S n O V t) (Q : ℕ) :
    forgeProb A Q ≤
      forgeProb (UnforgeAdversary.withVerify v O A) Q + forgeProbOn A Q E := by
  rw [forgeProb_withVerify_eq, forgeProb, forgeProbOn]
  refine le_trans (MeasureTheory.measure_mono ?_) (MeasureTheory.measure_union_le _ _)
  rintro x ⟨p, hp, hf⟩
  by_cases hE : E p.1
  · exact Or.inr ⟨p, hp, hf, hE⟩
  · exact Or.inl ⟨p, hp, forges_withVerify v hv hf hE⟩

/-- **`forgeProb_le_withVerify` in BKM06 Definition 7** (no side oracle). -/
theorem insiderForgeProb_le_withVerify {E : KeyRing S.PK N × S.Msg × S.Sig → Prop}
    (hv : ∀ H R m σ, S.verify H R m σ = true → ¬ E (R, m, σ) → v H R m σ = true)
    (A : InsiderAdversary S n V t) (Q : ℕ) :
    insiderForgeProb A Q ≤
      insiderForgeProb (S := S.withVerify v)
          (UnforgeAdversary.withVerify v (SideOracle.none S) A) Q +
        forgeProbOn A Q E :=
  forgeProb_le_withVerify v hv A Q

end GordieHowe.RingSignature
