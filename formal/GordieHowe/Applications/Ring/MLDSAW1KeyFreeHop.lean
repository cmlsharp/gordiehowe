-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1FreshHop
public import GordieHowe.Model.Quantum.Interactive.PreReprog
public import GordieHowe.Model.RingSignature.RevealedReprogramAvg
public import GordieHowe.Applications.Ring.MLDSAW1Guess
public import GordieHowe.Applications.MLDSA.Regularity.CommitPoint

@[expose] public section

/-!
# The points of the fresh-mask signer's attempts

The first step towards key-free signing in the ring game of the ML-DSA ring publishing `w₁` with
fresh masks (`freshScheme`, `GordieHowe/Applications/Ring/MLDSAW1Anonymity.lean`) reprograms the
commitment hash at every attempted point (revealed-point reprogramming,
`GordieHowe/Model/Quantum/Interactive/RevealedPair.lean`; the reprogramming challenger
`Challenger.preReprog`, `GordieHowe/Model/Quantum/Interactive/PreReprog.lean`). At a signing
request of user `s` on `(R, m)` with `pk_s ∈ R`, the points are `chPt (µ_s, w₁(y_{c,t}))` for the
masks `y_{c,t} = M.ans (g_c (t, key, tr, bmsg R m))` of the `k` calls and `T` attempts (all of
them, executed or not), `µ_s = muAns (H (muPt (tr_s, bmsg R m)))` read from the oracle.

- `w1Pts`: the points as a classical program of one query (`µ_s`); `card_w1Pts_le` (at most
  `k · T` points), `w1Pts_queries` (at most one query).
- `toReal_w1Pts_le`: **a given point is among the points of a request with probability at most
  `k · T · Σ_s commitPointMax(Â_s)`** over that request's signing coins, for a uniform mask
  decoding and an injective commitment-hash point map (a union bound over the masks).
- `w1RevealedPair`: **the ring game's challenger with fresh masks and its counterpart that
  reprograms the commitment hash at all the attempted points form a `RevealedPair`**
  (`Challenger.RevealedPair.ofPreReprog`), with `B` the commitment-hash points and point bound
  `k · T · Σ_s commitPointMax(Â_s)`, when the message-representative points are not
  commitment-hash points (`hdisj`).
- `insiderForgeProb_fresh_le_reprog`: **BKM06 Definition 7 for the fresh-mask ring is at most the
  game against the reprogramming challenger** (its forgery read at the final oracle in force) plus
  `Q · (√(ε̄ W) + ε̄ W / 2)`, `W = t + q_C · Q`, at the average over the key coins `ε̄` of the point
  bounds (`gameAdvantage_runLawIn_revealed_le_avg`).
-/

namespace GordieHowe.RingSignature

open Quantum

variable {X Y : Type} {N : ℕ} {TS : RingTypes} {S : RingScheme X Y N TS} {n : ℕ} {O : SideOracle S}

/-- An existence over the entries of a history reads only its requests. -/
theorem exists_request_iff {P : UnforgeRequest (S := S) n O → Prop} {hist hist' : UnforgeHist n O}
    (h : hist.map HistoryEntry.request = hist'.map HistoryEntry.request) :
    (∃ e ∈ hist, P e.request) ↔ ∃ e ∈ hist', P e.request := by
  have key : ∀ l : UnforgeHist n O, (∃ e ∈ l, P e.request) ↔
      ∃ r ∈ l.map HistoryEntry.request, P r := fun l => by
    simp [List.mem_map]
  rw [key, key, h]

/-- **A forgery reads the history only through its requests.** -/
theorem forges_iff_of_requests {keys : Fin n → S.KeyCoins} {H : X → Y}
    {out : KeyRing S.PK N × S.Msg × S.Sig} {hist hist' : UnforgeHist n O}
    (h : hist.map HistoryEntry.request = hist'.map HistoryEntry.request) :
    Forges keys H out hist ↔ Forges keys H out hist' := by
  have hc : ∀ i, Corrupted hist i ↔ Corrupted hist' i := fun i =>
    exists_request_iff (P := fun r => r = .corrupt i) h
  have hs : ∀ R m, SignQueried hist R m ↔ SignQueried hist' R m := fun R m => by
    unfold SignQueried
    exact exists_request_iff (P := fun r => ∃ s, r = .sign s R m) h
  have hside : ∀ R m, SideCovered keys hist R m ↔ SideCovered keys hist' R m := fun R m => by
    unfold SideCovered
    exact exists_request_iff
      (P := fun r => ∃ i bm, r = .sideSign i bm ∧ S.pk (keys i) ∈ R.1 ∧ O.Covers bm R m) h
  constructor
  · rintro ⟨hv, ⟨hr, hq, hsd⟩⟩
    exact ⟨hv, ⟨fun pk hpk => let ⟨i, hi, hci⟩ := hr pk hpk; ⟨i, hi, (hc i).not.1 hci⟩,
      (hs _ _).not.1 hq, (hside _ _).not.1 hsd⟩⟩
  · rintro ⟨hv, ⟨hr, hq, hsd⟩⟩
    exact ⟨hv, ⟨fun pk hpk => let ⟨i, hi, hci⟩ := hr pk hpk; ⟨i, hi, (hc i).not.2 hci⟩,
      (hs _ _).not.2 hq, (hside _ _).not.2 hsd⟩⟩

end GordieHowe.RingSignature

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.Quantum
open GordieHowe.MLDSA.Regularity
open scoped ENNReal NNReal BigOperators

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section Points

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [DecidableEq X]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop} [DecidablePred adm]
  {Of : SideOracle (freshScheme prims O M βmin tol enc k D bmsg PS adm)} {n : ℕ}

local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm
local notation "Bf" => freshBase prims O M βmin tol enc k D bmsg

variable (Of) in
/-- **The points of the attempts of a signing request** (module docstring), at the users' key
coins `keys` and the signing coins `c` of request number `|hist|`: none for other requests, for
requests numbered `Q` or later, and for signers outside the ring. -/
noncomputable def w1Pts (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) : OracleProg X Y (Finset X) :=
  if h : hist.length < Q then
    match req with
    | .sign s R m =>
      if (Bf).pk (keys s) ∈ R.1 then
        .query (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m)) fun y =>
          .pure ((Finset.univ : Finset (Fin k × Fin T)).image fun ct =>
            O.chPt (O.muAns y, realBuckets (prims.expandA ((Sf).sk (keys s)).rho)
              (M.ans ((c ⟨hist.length, h⟩).1.1 ct.1
                (ct.2, (((Sf).sk (keys s)).key, (((Sf).sk (keys s)).tr, bmsg R m)))))))
      else .pure ∅
    | _ => .pure ∅
  else .pure ∅

/-- **At most `k · T` points.** -/
theorem card_w1Pts_le (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins) hist req
    (H : X → Y) : ((w1Pts Of keys c hist req).run H).card ≤ k * T := by
  unfold w1Pts
  split_ifs with h
  · rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · simp
    · dsimp only
      split_ifs
      · rw [OracleProg.run_query, OracleProg.run_pure]
        exact Finset.card_image_le.trans (by simp)
      · simp
    · simp
  · simp

/-- **One query** (the signer's message representative). -/
theorem w1Pts_queries (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins) hist req :
    (w1Pts Of keys c hist req).QueriesLE 1 := by
  intro H
  unfold w1Pts
  split_ifs with h
  · rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · simp
    · dsimp only
      split_ifs
      · simp [OracleProg.trace_query]
      · simp
    · simp
  · simp

/-- **A given point is among the points of a request with probability at most
`k · T · Σ_s commitPointMax(Â_s)`** over that request's signing coins (module docstring). -/
theorem toReal_w1Pts_le
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (keys : Fin n → (Sf).KeyCoins) {Q : ℕ}
    (c : Fin Q → (Sf).SignCoins) (rs : List (UnforgeRequest (S := Sf) n Of))
    (req : UnforgeRequest (S := Sf) n Of) (H : X → Y) (x : X) (h : rs.length < Q) :
    ((PMF.uniformOfFintype (Sf).SignCoins).toOuterMeasure {c' | x ∈ (w1Pts Of keys
        (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) req).run H}).toReal ≤
      (k * T : ℝ) * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := by
  classical
  have hlen : (Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs).length = rs.length := by
    simp [Challenger.histOf]
  have hnn : 0 ≤ (k * T : ℝ) * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := by
    refine mul_nonneg (by positivity) (Finset.sum_nonneg fun s _ => ?_)
    exact (ENNReal.toReal_nonneg).trans
      (toReal_map_realBuckets_le_commitPointMax _ (Classical.arbitrary _))
  rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
  · refine le_of_eq_of_le ?_ hnn
    simp [w1Pts]
  · by_cases hR : (Bf).pk (keys s) ∈ R.1
    · -- the points of the masks, a union bound, and one mask at a time
      set Â := prims.expandA ((Sf).sk (keys s)).rho
      set μ := O.muAns (H (O.muPt (pubTr prims ((Bf).pk (keys s)), bmsg R m)))
      set u : Fin T → MaskPt T Msg := fun t => (t, (((Sf).sk (keys s)).key,
        (((Sf).sk (keys s)).tr, bmsg R m)))
      have hset : {c' : (Sf).SignCoins | x ∈ (w1Pts Of keys (Function.update c ⟨rs.length, h⟩ c')
          (Challenger.histOf rs) (.sign s R m)).run H} ⊆
          ⋃ ct ∈ (Finset.univ : Finset (Fin k × Fin T)),
            {c' | O.chPt (μ, realBuckets Â (M.ans (c'.1.1 ct.1 (u ct.2)))) = x} := by
        intro c' hc'
        simp only [Set.mem_ofPred_eq, w1Pts, hlen, h, ↓reduceDIte, hR, ↓reduceIte,
          OracleProg.run_query, OracleProg.run_pure, Finset.mem_image, Finset.mem_univ, true_and,
          Function.update_self] at hc'
        obtain ⟨ct, hct⟩ := hc'
        exact Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_univ ct)) hct
      have hone : ∀ ct : Fin k × Fin T,
          ((PMF.uniformOfFintype (Sf).SignCoins).toOuterMeasure
            {c' | O.chPt (μ, realBuckets Â (M.ans (c'.1.1 ct.1 (u ct.2)))) = x}).toReal ≤
            commitPointMax Â := by
        intro ct
        have hmap : (PMF.uniformOfFintype (Sf).SignCoins).map
            (fun c' : (Sf).SignCoins => M.ans (c'.1.1 ct.1 (u ct.2))) =
            PMF.uniformOfFintype (MaskBox p) := by
          have hc : (PMF.uniformOfFintype (Sf).SignCoins).map
              (fun c' : (Sf).SignCoins => M.ans (c'.1.1 ct.1 (u ct.2))) =
              ((PMF.uniformOfFintype (Sf).SignCoins).map Prod.fst).map
                (fun cb : (freshBase prims O M βmin tol enc k D bmsg).Coins =>
                  M.ans (cb.1 ct.1 (u ct.2))) :=
            (PMF.map_comp Prod.fst _ (fun cb : (freshBase prims O M βmin tol enc k D bmsg).Coins =>
              M.ans (cb.1 ct.1 (u ct.2)))).symm
          have hfst : (PMF.uniformOfFintype (Sf).SignCoins).map Prod.fst =
              PMF.uniformOfFintype (freshBase prims O M βmin tol enc k D bmsg).Coins :=
            PMF.map_fst_uniformOfFintype
          rw [hc, hfst]
          exact map_uniform_freshCoins_eq (M := M) (k := k) (D := D) hMask ct.1 (u ct.2)
        by_cases hx : ∃ w, O.chPt (μ, w) = x
        · obtain ⟨w, rfl⟩ := hx
          have hiff : {c' : (Sf).SignCoins |
              O.chPt (μ, realBuckets Â (M.ans (c'.1.1 ct.1 (u ct.2)))) = O.chPt (μ, w)} =
              (fun c' : (Sf).SignCoins => M.ans (c'.1.1 ct.1 (u ct.2))) ⁻¹'
                {y | realBuckets Â y = w} := by
            ext c'
            simp only [Set.mem_ofPred_eq, Set.mem_preimage]
            exact ⟨fun he => (Prod.mk.inj (hch he)).2, fun he => by rw [he]⟩
          rw [hiff, ← PMF.toOuterMeasure_map_apply, hmap]
          have : (PMF.uniformOfFintype (MaskBox p)).toOuterMeasure {y | realBuckets Â y = w} =
              ((maskUniform p).map (realBuckets Â)) w := by
            rw [PMF.map_apply, PMF.toOuterMeasure_apply, maskUniform]
            refine tsum_congr fun y => ?_
            by_cases hy : realBuckets Â y = w
            · simp [Set.indicator, hy]
            · have hy' : ¬ w = realBuckets Â y := fun h => hy h.symm
              simp [Set.indicator, hy, hy']
          rw [this]
          exact toReal_map_realBuckets_le_commitPointMax Â w
        · push Not at hx
          have hemp : {c' : (Sf).SignCoins |
              O.chPt (μ, realBuckets Â (M.ans (c'.1.1 ct.1 (u ct.2)))) = x} = ∅ :=
            Set.eq_empty_of_forall_notMem fun c' hc' => hx _ hc'
          rw [hemp, MeasureTheory.measure_empty, ENNReal.toReal_zero]
          exact (ENNReal.toReal_nonneg).trans
            (toReal_map_realBuckets_le_commitPointMax Â (Classical.arbitrary _))
      have hsum : ((PMF.uniformOfFintype (Sf).SignCoins).toOuterMeasure {c' | x ∈ (w1Pts Of keys
          (Function.update c ⟨rs.length, h⟩ c') (Challenger.histOf rs) (.sign s R m)).run H}).toReal
          ≤ ∑ ct : Fin k × Fin T, ((PMF.uniformOfFintype (Sf).SignCoins).toOuterMeasure
            {c' | O.chPt (μ, realBuckets Â (M.ans (c'.1.1 ct.1 (u ct.2)))) = x}).toReal := by
        rw [← ENNReal.toReal_sum fun _ _ => (PMF.toOuterMeasure_apply_le_one _ _).trans_lt
          ENNReal.one_lt_top |>.ne]
        refine ENNReal.toReal_mono (ENNReal.sum_ne_top.2 fun _ _ =>
          ((PMF.toOuterMeasure_apply_le_one _ _).trans_lt ENNReal.one_lt_top).ne) ?_
        exact (MeasureTheory.measure_mono hset).trans (MeasureTheory.measure_biUnion_finset_le _ _)
      refine hsum.trans ((Finset.sum_le_sum fun ct _ => hone ct).trans ?_)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Finset.single_le_sum
        (f := fun s => commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))
        (fun s _ => (ENNReal.toReal_nonneg).trans
          (toReal_map_realBuckets_le_commitPointMax _ (Classical.arbitrary _))) (Finset.mem_univ s)
    · refine le_of_eq_of_le ?_ hnn
      simp [w1Pts, hlen, h, hR]
  · refine le_of_eq_of_le ?_ hnn
    simp [w1Pts]

omit [DecidableEq X] in
/-- The challenger of the unforgeability game assigns nothing. -/
theorem unforgeChallenger_plain (keys : Fin n → (Sf).KeyCoins) (Q : ℕ) c hist req (H : X → Y) :
    (((unforgeChallenger Sf n Of keys Q).respond c hist req).run H).assignments = [] := by
  unfold unforgeChallenger
  dsimp only
  split_ifs with h
  · rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · rfl
    · dsimp only
      split_ifs
      · rw [OracleProg.run_bind]
        rfl
      · rfl
    · dsimp only
      rw [OracleProg.run_bind]
      rfl
  · rfl

omit [DecidableEq X] in
/-- The challenger of the unforgeability game reads the history only through its length. -/
theorem unforgeChallenger_respond_congr (keys : Fin n → (Sf).KeyCoins) (Q : ℕ) c
    (hist hist' :
      List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    req (hl : hist.length = hist'.length) :
    (unforgeChallenger Sf n Of keys Q).respond c hist req =
      (unforgeChallenger Sf n Of keys Q).respond c hist' req := by
  unfold unforgeChallenger
  simp only [hl]

/-- The points read the history only through its length. -/
theorem w1Pts_congr (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (hist hist' :
      List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    req (hl : hist.length = hist'.length) :
    w1Pts Of keys c hist req = w1Pts Of keys c hist' req := by
  unfold w1Pts
  simp only [hl]

/-- The coins of the unforgeability challenger: the uniform signing coins of each request. -/
theorem unforgeChallenger_coins_eq (keys : Fin n → (Sf).KeyCoins) (Q : ℕ) :
    (PMF.uniformOfFintype (Fin Q → (Sf).SignCoins)) =
      (prodLaw (PMF.pure ()) (PMF.pi fun _ : Fin Q => PMF.uniformOfFintype (Sf).SignCoins)).map
        (fun ω : Unit × (Fin Q → (Sf).SignCoins) => ω.2) := by
  rw [prodLaw, PMF.pure_bind, PMF.map_comp, PMF.pi_uniformOfFintype]
  exact (PMF.map_id _).symm

omit [DecidableEq X] in
/-- The reply to request `|hist|` reads only that request's signing coins. -/
theorem unforgeChallenger_causal (keys : Fin n → (Sf).KeyCoins) (Q : ℕ)
    (c c' : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of)
    (hc : ∀ i : Fin Q, (i : ℕ) ≤ hist.length → c i = c' i) :
    (unforgeChallenger Sf n Of keys Q).respond c hist req =
      (unforgeChallenger Sf n Of keys Q).respond c' hist req := by
  unfold unforgeChallenger
  dsimp only
  split_ifs with h
  · rw [hc ⟨hist.length, h⟩ le_rfl]
  · rfl

/-- The points read only the signing coins of request `|rs|`. -/
theorem w1Pts_causal (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c c' : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (req : UnforgeRequest (S := Sf) n Of) (H : X → Y)
    (hc : ∀ i : Fin Q, (i : ℕ) ≤ rs.length → c i = c' i) :
    (w1Pts Of keys c (Challenger.histOf rs) req).run H =
      (w1Pts Of keys c' (Challenger.histOf rs) req).run H := by
  have hlen : (Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs).length = rs.length := by
    simp [Challenger.histOf]
  unfold w1Pts
  split_ifs with h
  · rw [hc ⟨_, h⟩ (le_of_eq hlen)]
  · rfl

/-- The points are commitment-hash points. -/
theorem w1Pts_subset (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (rs : List (UnforgeRequest (S := Sf) n Of)) (req : UnforgeRequest (S := Sf) n Of) (H : X → Y) :
    (((w1Pts Of keys c (Challenger.histOf rs) req).run H : Finset X) : Set X) ⊆
      Set.range O.chPt := by
  intro x hx
  simp only [w1Pts] at hx
  split_ifs at hx with h
  · rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · simp at hx
    · dsimp only at hx
      split_ifs at hx
      · rw [OracleProg.run_query, OracleProg.run_pure] at hx
        obtain ⟨ct, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hx)
        exact ⟨_, rfl⟩
      · simp at hx
    · simp at hx
  · simp at hx

/-- The points read the oracle only at a message-representative point, not a commitment-hash
point when the two kinds of points differ (`hdisj`). -/
theorem w1Pts_reads (hdisj : ∀ a b, O.muPt a ≠ O.chPt b) (keys : Fin n → (Sf).KeyCoins) {Q : ℕ}
    (c : Fin Q → (Sf).SignCoins) (rs : List (UnforgeRequest (S := Sf) n Of))
    (req : UnforgeRequest (S := Sf) n Of) (O₁ O₂ : X → Y)
    (hoff : ∀ x ∉ Set.range O.chPt, O₁ x = O₂ x) :
    (w1Pts Of keys c (Challenger.histOf rs) req).run O₁ =
      (w1Pts Of keys c (Challenger.histOf rs) req).run O₂ := by
  unfold w1Pts
  split_ifs with h
  · rcases req with i | ⟨s, R, m⟩ | ⟨i, bm⟩
    · rfl
    · dsimp only
      split_ifs
      · rw [OracleProg.run_query, OracleProg.run_query,
          hoff _ (fun ⟨b, hb⟩ => hdisj _ b hb.symm)]
        rfl
      · rfl
    · rfl
  · rfl

variable [Fintype X] {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁]
  [DecidableEq Y₁]

/-- **The ring game's challenger with fresh masks and its counterpart that reprograms the
commitment hash at all the attempted points form a `RevealedPair`** (module docstring). -/
noncomputable def w1RevealedPair (sp : Y ≃+ Y₁ × Y₂)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (keys : Fin n → (Sf).KeyCoins) (Q : ℕ) :
    Challenger.RevealedPair sp (Set.range O.chPt)
      ((k * T : ℝ) * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))
      (unforgeChallenger Sf n Of keys Q)
      ((unforgeChallenger Sf n Of keys Q).preReprog sp (w1Pts Of keys) 1 (k * T)
        (w1Pts_queries keys) (card_w1Pts_le keys)) :=
  Challenger.RevealedPair.ofPreReprog (unforgeChallenger Sf n Of keys Q) sp (w1Pts Of keys) 1
    (k * T) (w1Pts_queries keys) (card_w1Pts_le keys) (PMF.pure ())
    (PMF.uniformOfFintype (Sf).SignCoins) (fun ω => ω.2) (unforgeChallenger_coins_eq keys Q)
    (unforgeChallenger_plain keys Q)
    (fun c hist hist' req hh => unforgeChallenger_respond_congr keys Q c hist hist' req
      (by simpa using congrArg List.length hh))
    (fun _ c c' hist req hc => unforgeChallenger_causal keys Q c c' hist req hc)
    (fun c hist hist' req hh => w1Pts_congr keys c hist hist' req
      (by simpa using congrArg List.length hh))
    (fun _ c rs req H => w1Pts_subset keys c rs req H)
    (fun _ c c' rs req H hc => w1Pts_causal keys c c' rs req H hc)
    (fun _ c rs req O₁ O₂ hoff _ => w1Pts_reads hdisj keys c rs req O₁ O₂ hoff)
    (fun _ c rs req H x h => toReal_w1Pts_le hMask hch keys c rs req H x h)

omit [Fintype X] [AddGroup Y] in
/-- The point bound is nonnegative. -/
theorem w1PointBound_nonneg (keys : Fin n → (Sf).KeyCoins) :
    0 ≤ (k * T : ℝ) * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) :=
  mul_nonneg (by positivity) (Finset.sum_nonneg fun _ _ => (ENNReal.toReal_nonneg).trans
    (toReal_map_realBuckets_le_commitPointMax _ (Classical.arbitrary _)))

/-- **BKM06 Definition 7 for the fresh-mask ring is at most the game against the reprogramming
challenger plus the reprogramming error** (module docstring). -/
theorem insiderForgeProb_fresh_le_reprog [Nonempty X] [Nonempty Y₁] [NeZero n] (sp : Y ≃+ Y₁ × Y₂)
    (h : W1SplitMask O M) {t : ℕ}
    (A : InsiderAdversary Sf n (OracleView.queriesOnly X Y) t) (Q : ℕ) :
    (insiderForgeProb A Q).toReal ≤
      ((runLawIn (fun keys H => A (fun i => (Bf).pk (keys i), (OracleView.queriesOnly X Y).view H))
          (fun keys => (unforgeChallenger Sf n (SideOracle.none Sf) keys Q).preReprog sp
            (w1Pts (SideOracle.none Sf) keys) 1 (k * T) (w1Pts_queries keys)
            (card_w1Pts_le keys))).toOuterMeasure
          {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)}).toReal +
        Q * (√((∑ keys : Fin n → (Sf).KeyCoins, (Fintype.card (Fin n → (Sf).KeyCoins) : ℝ)⁻¹ *
            ((k * T : ℝ) * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))) *
              (t + max (Sf).q (SideOracle.none Sf).q * Q)) +
          (∑ keys : Fin n → (Sf).KeyCoins, (Fintype.card (Fin n → (Sf).KeyCoins) : ℝ)⁻¹ *
            ((k * T : ℝ) * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))) *
              (t + max (Sf).q (SideOracle.none Sf).q * Q) / 2) := by
  classical
  have hP := gameAdvantage_runLawIn_revealed_le_avg
    (fun keys H => A (fun i => (Bf).pk (keys i), (OracleView.queriesOnly X Y).view H))
    (fun _ _ _ _ => rfl)
    (fun keys => w1RevealedPair (Of := SideOracle.none Sf) sp h.hMask h.hch h.hdisj keys Q)
    (qc := max (Sf).q (SideOracle.none Sf).q) (fun _ => rfl) (fun _ => le_rfl)
    (fun keys => w1PointBound_nonneg keys)
    {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)} (fun _ _ _ _ _ => Iff.rfl)
  rw [gameAdvantage, advantage_le_iff] at hP
  simp only [Set.setOf_mem_eq] at hP
  -- the plain game's probability is the insider forgery probability
  have h₀ : (runLawIn (fun keys H => A (fun i => (Bf).pk (keys i),
      (OracleView.queriesOnly X Y).view H))
      (fun keys => unforgeChallenger Sf n (SideOracle.none Sf) keys Q)).toOuterMeasure
      {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)} = insiderForgeProb A Q := by
    rw [runLawIn_eq_map _ (fun keys => unforgeChallenger_plain (Of := SideOracle.none Sf) keys Q),
      PMF.toOuterMeasure_map_apply]
    unfold insiderForgeProb forgeProb unforgeLaw
    congr 1
    ext x
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Option.mem_def, Option.map_eq_some_iff]
    constructor
    · rintro ⟨_, ⟨q, hq, rfl⟩, hf⟩
      exact ⟨q, hq, (forges_iff_of_requests (Challenger.map_request_histOf _)).1 hf⟩
    · rintro ⟨q, hq, hf⟩
      exact ⟨_, ⟨q, hq, rfl⟩, (forges_iff_of_requests (Challenger.map_request_histOf _)).2 hf⟩
  rw [h₀] at hP
  have h1 := hP.1
  rw [sub_le_iff_le_add] at h1
  linarith [h1]

end Points

end GordieHowe.Ring.MLDSAW1
