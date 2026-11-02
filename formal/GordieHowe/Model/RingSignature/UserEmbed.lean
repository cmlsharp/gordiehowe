-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.RingSignature.Unforgeability
public import GordieHowe.Model.RingSignature.TranscriptAbsorb
public import GordieHowe.Model.RingSignature.Schedule
public import GordieHowe.Foundations.ToMathlib.UniformFunction
public import GordieHowe.Foundations.ToMathlib.PMFUniform

@[expose] public section

/-!
# Embedding an adversary into a game with more users

An adversary of the unforgeability game of `GordieHowe/Model/RingSignature/Unforgeability.lean`
with `n` honest users is an adversary of the game with `n' ≥ n` users that ignores the last
`n' - n`: it reads the first `n` public keys, and its requests name users through
`Fin.castLE`. Its forgery probability does not decrease (`forgeProb_le_embedAdversary`): the first
`n` users' key coins are uniform, the challenger with `n'` users answers the embedded requests as
the challenger with `n` users answers the requests, and a forgery fresh for the `n` users is fresh
for the `n'` users.

- `FreshReq`, `fresh_iff_freshReq`: freshness read from the requests of the history.
- `embReq`, `userRelay`, `relaysChallenger_userRelay`: the requests naming users through
  `Fin.castLE`, and the challenger with `n` users at the first `n` users' key coins relays the
  challenger with `n'` users.
- `embedAdversary`, `forgeProb_le_embedAdversary`.
- `neZero_max_two`, `one_ne_zero_max_two`, `scheduleLE_embedAdversary`: for the embedding into
  at least two users.
-/

namespace GordieHowe.RingSignature

open Quantum
open scoped ENNReal

variable {X Y : Type} {N : ℕ} {TS : RingTypes} {S : RingScheme X Y N TS} {O : SideOracle S} {n n' : ℕ}

/-! ### Freshness read from the requests -/

/-- **A fresh ring and message for the requests `rs`**: every key of the ring is the key of a user
no request corrupts, no request asks for a ring signature on the ring and message, and no member is
asked for a side signature covering them. -/
def FreshReq (keys : Fin n → S.KeyCoins) (rs : List (UnforgeRequest n O)) (R : KeyRing S.PK N)
    (m : S.Msg) : Prop :=
  (∀ pk ∈ R.1, ∃ i, S.pk (keys i) = pk ∧ UnforgeRequest.corrupt i ∉ rs) ∧
    (∀ s, UnforgeRequest.sign s R m ∉ rs) ∧
      ∀ i bm, UnforgeRequest.sideSign i bm ∈ rs → S.pk (keys i) ∈ R.1 → ¬ O.Covers bm R m

/-- **Freshness reads only the requests of the history.** -/
theorem fresh_iff_freshReq (keys : Fin n → S.KeyCoins) (hist : UnforgeHist n O)
    (R : KeyRing S.PK N) (m : S.Msg) :
    Fresh keys hist R m ↔ FreshReq keys (hist.map HistoryEntry.request) R m := by
  constructor
  · intro h
    refine ⟨fun pk hpk => ?_, fun s hs => ?_, fun i bm hs hR hc => ?_⟩
    · obtain ⟨i, hi, hc⟩ := h.honest_ring pk hpk
      exact ⟨i, hi, fun hm => hc (by obtain ⟨e, he, hr⟩ := List.mem_map.1 hm; exact ⟨e, he, hr⟩)⟩
    · obtain ⟨e, he, hr⟩ := List.mem_map.1 hs
      exact h.not_signQueried ⟨e, he, s, hr⟩
    · obtain ⟨e, he, hr⟩ := List.mem_map.1 hs
      exact h.not_sideCovered ⟨e, he, i, bm, hr, hR, hc⟩
  · rintro ⟨h1, h2, h3⟩
    refine ⟨fun pk hpk => ?_, fun ⟨e, he, s, hr⟩ => h2 s (hr ▸ List.mem_map_of_mem he),
      fun ⟨e, he, i, bm, hr, hR, hc⟩ => h3 i bm (hr ▸ List.mem_map_of_mem he) hR hc⟩
    obtain ⟨i, hi, hc⟩ := h1 pk hpk
    exact ⟨i, hi, fun ⟨e, he, hr⟩ => hc (hr ▸ List.mem_map_of_mem he)⟩

/-! ### The embedded requests -/

/-- **A request naming its users through `Fin.castLE`.** -/
def embReq (h : n ≤ n') : UnforgeRequest n O → UnforgeRequest n' O
  | .corrupt i => .corrupt (Fin.castLE h i)
  | .sign s R m => .sign (Fin.castLE h s) R m
  | .sideSign i bm => .sideSign (Fin.castLE h i) bm

theorem embReq_injective (h : n ≤ n') : Function.Injective (embReq (O := O) h) := by
  intro a b hab
  rcases a with i | ⟨s, R, m⟩ | ⟨i, bm⟩ <;> rcases b with j | ⟨s', R', m'⟩ | ⟨j, bm'⟩ <;>
    simp only [embReq, UnforgeRequest.corrupt.injEq, UnforgeRequest.sign.injEq,
      UnforgeRequest.sideSign.injEq, reduceCtorEq] at hab ⊢
  · exact Fin.castLE_injective h hab
  · exact ⟨Fin.castLE_injective h hab.1, hab.2⟩
  · exact ⟨Fin.castLE_injective h hab.1, hab.2⟩

/-- **The relay of the requests to the game with `n'` users**: each request with its users named
through `Fin.castLE`, the reply passed on. -/
def userRelay (h : n ≤ n') :
    SideRelay (UnforgeRequest n O) (UnforgeResponse O) (UnforgeRequest n' O)
      (UnforgeResponse O) where
  route _ r := embReq h r
  answer _ _ a := a

theorem relayList_userRelay (h : n ≤ n') (rs : List (UnforgeRequest n O)) :
    (userRelay (O := O) h).relayList rs = rs.map (embReq h) := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [SideRelay.relayList_append_singleton, ih, List.map_append]
    rfl

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y]

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] in
/-- **The challenger with `n` users at the first `n` users' key coins relays the challenger with
`n'` users** through `userRelay`, at the same coins. -/
theorem relaysChallenger_userRelay (h : n ≤ n') (keys : Fin n' → S.KeyCoins) (Q : ℕ)
    (ω : Fin Q → S.SignCoins) :
    (userRelay (O := O) h).RelaysChallenger (unforgeChallenger S n O (keys ∘ Fin.castLE h) Q) ω
      (unforgeChallenger S n' O keys Q) ω where
  Q_eq := rfl
  run_eq hist hist' r G hrel hlt := by
    have hl : hist'.length = hist.length := by
      have := congrArg List.length hrel
      simpa using this
    have hlt' : hist.length < Q := hlt
    have hl' : hist'.length < Q := hl ▸ hlt'
    have hc : ω ⟨hist'.length, hl'⟩ = ω ⟨hist.length, hlt'⟩ := congrArg ω (Fin.ext hl)
    simp only [unforgeChallenger, dif_pos hlt', dif_pos hl', userRelay]
    rcases r with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · rfl
    · simp only [embReq, Function.comp_apply, hc]
    · simp only [embReq, Function.comp_apply, hc]
  answer_none _ _ _ := rfl

/-! ### The embedded adversary -/

/-- **The restriction of a uniform function along an embedding is uniform** (`splitAlong`). -/
theorem map_uniform_comp_embedding {A A' Z : Type} [Fintype A] [DecidableEq A] [Fintype A']
    [DecidableEq A'] [Fintype Z] [Nonempty Z] (e : A' ↪ A) :
    (PMF.uniformOfFintype (A → Z)).map (fun g a => g (e a)) = PMF.uniformOfFintype (A' → Z) := by
  rw [← PMF.map_uniformOfFintype_equiv (GordieHowe.splitAlong (Y' := Z) e).symm, PMF.map_comp]
  have h : ((fun g a => g (e a)) ∘ (GordieHowe.splitAlong (Y' := Z) e).symm) = Prod.snd := by
    funext q a
    exact GordieHowe.splitAlong_symm_apply_embed e q.1 q.2 a
  rw [h, PMF.map_snd_uniformOfFintype]

/-- **A coin average of a function of `v c` is the average over the law of `v`.** -/
theorem sum_mul_map_apply {κ U : Type} [Fintype κ] [Fintype U] [DecidableEq U] (μ : PMF κ)
    (v : κ → U) (F : U → ℝ≥0∞) : ∑ u, (μ.map v) u * F u = ∑ c, μ c * F (v c) := by
  simp only [PMF.map_apply, tsum_fintype (L := .unconditional _), Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_eq_single (v c) (fun u _ hu => by simp [hu])
    (fun h => absurd (Finset.mem_univ _) h)]
  simp

variable [Nonempty X] [AddGroup Y] {V : OracleView X Y} {t : ℕ}

/-- **The adversary in the game with `n' ≥ n` users**: on the `n'` public keys, the adversary on the
first `n`, its requests naming users through `Fin.castLE`. -/
noncomputable def embedAdversary [NeZero n'] (h : n ≤ n') (A : UnforgeAdversary S n O V t) :
    UnforgeAdversary S n' O V t := fun inp =>
  (A (inp.1 ∘ Fin.castLE h, inp.2)).absorbQB (userRelay h) fun _ => embReq_injective h

omit [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty Y] [Nonempty X]
  [AddGroup Y] in
/-- **A forgery fresh for `n` users is fresh for `n'` users** at the embedded requests. -/
theorem FreshReq.embed (h : n ≤ n') {keys : Fin n' → S.KeyCoins} {rs : List (UnforgeRequest n O)}
    {R : KeyRing S.PK N} {m : S.Msg} (hf : FreshReq (keys ∘ Fin.castLE h) rs R m) :
    FreshReq keys (rs.map (embReq h)) R m := by
  obtain ⟨h1, h2, h3⟩ := hf
  refine ⟨fun pk hpk => ?_, fun s hs => ?_, fun i bm hs hR => ?_⟩
  · obtain ⟨i, hi, hc⟩ := h1 pk hpk
    refine ⟨Fin.castLE h i, hi, fun hm => hc ?_⟩
    obtain ⟨r, hr, he⟩ := List.mem_map.1 hm
    rcases r with j | ⟨s', R', m'⟩ | ⟨j, bm'⟩ <;>
      simp only [embReq, UnforgeRequest.corrupt.injEq, reduceCtorEq] at he
    rw [← Fin.castLE_injective h he]
    exact hr
  · obtain ⟨r, hr, he⟩ := List.mem_map.1 hs
    rcases r with j | ⟨s', R', m'⟩ | ⟨j, bm'⟩ <;>
      simp only [embReq, UnforgeRequest.sign.injEq, reduceCtorEq] at he
    obtain ⟨-, rfl, rfl⟩ := he
    exact h2 s' hr
  · obtain ⟨r, hr, he⟩ := List.mem_map.1 hs
    rcases r with j | ⟨s', R', m'⟩ | ⟨j, bm'⟩ <;>
      simp only [embReq, UnforgeRequest.sideSign.injEq, reduceCtorEq] at he
    obtain ⟨rfl, rfl⟩ := he
    exact h3 j bm' hr hR

/-- **Embedding into a game with more users does not decrease the forgery probability**: the
adversary's forgery probability with `n` users is at most that of `embedAdversary h A` with
`n' ≥ n` users, both with `Q` requests. -/
theorem forgeProb_le_embedAdversary [NeZero n'] (h : n ≤ n') (A : UnforgeAdversary S n O V t)
    (Q : ℕ) : forgeProb A Q ≤ forgeProb (embedAdversary h A) Q := by
  classical
  simp only [forgeProb, unforgeLaw, runLaw, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_map_apply]
  rw [tsum_fintype (L := .unconditional _), tsum_fintype (L := .unconditional _)]
  rw [← map_uniform_comp_embedding (Z := S.KeyCoins) (Fin.castLEEmb h),
    sum_mul_map_apply]
  refine Finset.sum_le_sum fun keys _ => mul_le_mul' le_rfl
    (ENNReal.tsum_le_tsum fun H => mul_le_mul' le_rfl ?_)
  have hL : (fun o => ((fun a => keys (Fin.castLEEmb h a)), H, o)) ⁻¹'
      {x : (Fin n → S.KeyCoins) × (X → Y) × Option ((KeyRing S.PK N × S.Msg × S.Sig) ×
        UnforgeHist n O) | ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2} =
      {x | ∃ p ∈ x, (fun o rs => S.verify H o.1 o.2.1 o.2.2 = true ∧
        FreshReq (keys ∘ Fin.castLE h) rs o.1 o.2.1) p.1 (p.2.map HistoryEntry.request)} := by
    ext x
    refine exists_congr fun p => and_congr_right fun _ => ?_
    exact ⟨fun hf => ⟨hf.verify_eq, (fresh_iff_freshReq _ _ _ _).1 hf.fresh⟩,
      fun hf => ⟨hf.1, (fresh_iff_freshReq _ _ _ _).2 hf.2⟩⟩
  have hR : (fun o => (keys, H, o)) ⁻¹'
      {x : (Fin n' → S.KeyCoins) × (X → Y) × Option ((KeyRing S.PK N × S.Msg × S.Sig) ×
        UnforgeHist n' O) | ∃ p ∈ x.2.2, Forges x.1 x.2.1 p.1 p.2} =
      {x | ∃ p ∈ x, (fun o rs => S.verify H o.1 o.2.1 o.2.2 = true ∧
        FreshReq keys rs o.1 o.2.1) p.1 (p.2.map HistoryEntry.request)} := by
    ext x
    refine exists_congr fun p => and_congr_right fun _ => ?_
    exact ⟨fun hf => ⟨hf.verify_eq, (fresh_iff_freshReq _ _ _ _).1 hf.fresh⟩,
      fun hf => ⟨hf.1, (fresh_iff_freshReq _ _ _ _).2 hf.2⟩⟩
  rw [hL, hR]
  exact (A ((fun i => S.pk (keys (Fin.castLE h i))), V.view H)).transcriptLaw_le_absorbQB
    (userRelay h) (fun _ => embReq_injective h)
    (unforgeChallenger S n O (keys ∘ Fin.castLE h) Q) (unforgeChallenger S n' O keys Q)
    (Equiv.refl _) (fun _ => rfl) (fun ω => relaysChallenger_userRelay h keys Q ω) H
    (fun o rs => S.verify H o.1 o.2.1 o.2.2 = true ∧ FreshReq (keys ∘ Fin.castLE h) rs o.1 o.2.1)
    (fun o rs => S.verify H o.1 o.2.1 o.2.2 = true ∧ FreshReq keys rs o.1 o.2.1)
    fun o rs ⟨hv, hf⟩ => ⟨hv, by
      rw [relayList_userRelay, ← List.map_take]
      exact hf.embed h⟩

/-! ### The embedding into at least two users -/

/-- At least two users are at least one. -/
instance neZero_max_two (n : ℕ) : NeZero (max n 2) := ⟨by omega⟩

/-- **User `1` is not user `0`** among at least two users. -/
theorem one_ne_zero_max_two (n : ℕ) : (1 : Fin (max n 2)) ≠ 0 := by
  intro h
  have := congrArg Fin.val h
  rw [Fin.val_one', Fin.val_zero, Nat.one_mod_eq_one.2 (by omega)] at this
  exact absurd this one_ne_zero

/-- **The embedding into more users keeps the schedule bound** (`embedAdversary` absorbs each
algorithm, keeping its slots, width and post batches). -/
theorem scheduleLE_embedAdversary [NeZero n'] (h : n ≤ n') {A : UnforgeAdversary S n O V t}
    {Sb w P : ℕ} (hS : GameAdversary.ScheduleLE A Sb w P) :
    GameAdversary.ScheduleLE (embedAdversary h A) Sb w P :=
  ⟨fun _ a => hS.slots_le _ a, fun _ a => hS.width_le _ a, fun _ a => hS.post_le _ a⟩

end GordieHowe.RingSignature
