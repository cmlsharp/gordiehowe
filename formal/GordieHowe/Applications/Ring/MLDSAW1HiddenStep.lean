-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1HiddenPoints
public import GordieHowe.Model.Quantum.Interactive.PreReprogHidden

@[expose] public section

/-!
# The kept-only reprogramming challenger of the fresh-mask ring game

The ring game of the ML-DSA ring publishing `w₁` with fresh masks against the challenger that
reprograms the commitment hash at every attempted point of a signing request
(`Challenger.preReprog`, `w1Pts`; `GordieHowe/Applications/Ring/MLDSAW1KeyFreeHop.lean`) and
against the challenger that keeps in force only the assignments at the kept points
(`Challenger.preReprogKeep` with `w1KeptPts`): the two form a hidden-reads pair
(`Challenger.HiddenReadsPair.ofPreReprogKeep`,
`GordieHowe/Model/Quantum/Interactive/PreReprogHidden.lean`) with the fresh base values among the
shared coins, for honest keys.

- `w1Pts_congr_hist`, `unforgeChallenger_respond_congr_coins`: the points and the challenger read
  the history only through its length and each request's coins only at that request.
- `w1Pts_eq_histOf`, `unforgeChallenger_respond_of_le`: the canonical history; no coins read
  from request `Q` on.
- `w1HiddenPair`: **the hidden-reads pair** of the two challengers.
- `hfind_w1HiddenPair`: the hidden-point condition of the pair, at
  `2 k T Σ_s commitPointMax(Â_s)` per request (`toReal_guess_mem_hidden_le`).
- `advantage_outLaw_w1Hidden_le`: **the kept-only against the full reprogramming challenger**,
  against an interactive adversary's output.
-/

open Finset
open scoped ENNReal BigOperators

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.MLDSA.Regularity GordieHowe.RingSignature
open GordieHowe.Quantum

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section Pair

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y] [Fintype X] [DecidableEq X]
  {O : W1Oracles X Y p prims Msg N reps} {M : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins] [DecidableEq TPS.Coins] [Nonempty TPS.Coins] {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O M βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm]
  {Of : SideOracle (freshScheme prims O M βmin tol enc k D bmsg PS adm)} {n : ℕ}
  {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]

local notation "Sf" => freshScheme prims O M βmin tol enc k D bmsg PS adm

omit [Fintype X] [AddGroup Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] in
/-- The points of a request read the history only through its length (`w1Pts_congr`), so they
are those at the canonical history of its requests. -/
theorem w1Pts_eq_histOf (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) :
    w1Pts Of keys c hist req =
      w1Pts Of keys c (Challenger.histOf (hist.map HistoryEntry.request)) req :=
  w1Pts_congr keys c _ _ req (by simp [Challenger.histOf])

omit [Fintype X] [AddGroup Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof] [Fintype TPS.Coins]
  [DecidableEq TPS.Coins] [Nonempty TPS.Coins] [Fintype Msg] [DecidableEq Msg] [Fintype Y]
  [DecidableEq Y] [Nonempty Y] in
/-- **The points read request `|hist|`'s coins only.** -/
theorem w1Pts_congr_coins (keys : Fin n → (Sf).KeyCoins) {Q : ℕ} (c c' : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) (h : hist.length < Q)
    (hc : c ⟨hist.length, h⟩ = c' ⟨hist.length, h⟩) :
    w1Pts Of keys c hist req = w1Pts Of keys c' hist req := by
  unfold w1Pts
  simp only [h, ↓reduceDIte, hc]

omit [Fintype X] [DecidableEq X] [AddGroup Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof] in
/-- **The challenger reads request `|hist|`'s coins only.** -/
theorem unforgeChallenger_respond_congr_coins (keys : Fin n → (Sf).KeyCoins) {Q : ℕ}
    (c c' : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) (h : hist.length < Q)
    (hc : c ⟨hist.length, h⟩ = c' ⟨hist.length, h⟩) :
    (unforgeChallenger Sf n Of keys Q).respond c hist req =
      (unforgeChallenger Sf n Of keys Q).respond c' hist req := by
  unfold unforgeChallenger
  simp only [h, ↓reduceDIte, hc]

omit [Fintype X] [DecidableEq X] [AddGroup Y] [Fintype TPS.Proof] [DecidableEq TPS.Proof] in
/-- **From request `Q` on the challenger reads no coins.** -/
theorem unforgeChallenger_respond_of_le (keys : Fin n → (Sf).KeyCoins) {Q : ℕ}
    (c c' : Fin Q → (Sf).SignCoins)
    (hist : List (HistoryEntry (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)))
    (req : UnforgeRequest (S := Sf) n Of) (h : Q ≤ hist.length) :
    (unforgeChallenger Sf n Of keys Q).respond c hist req =
      (unforgeChallenger Sf n Of keys Q).respond c' hist req := by
  unfold unforgeChallenger
  simp only [not_lt.2 h, ↓reduceDIte]

variable (Of) in
/-- **The kept-only and the full reprogramming challenger of the fresh-mask ring game form a
hidden-reads pair** (module docstring): `Challenger.HiddenReadsPair.ofPreReprogKeep` at the
unforgeability challenger with no shared coins and the signing coins of each request, the points
`w1Pts` (one query, at most `k · T` points) among the commitment-hash points, and the kept points
`w1KeptPts`, which a request's response determines for honest keys (`w1Pts_inter_w1KeptPts_eq`). -/
noncomputable def w1HiddenPair (sp : Y ≃+ Y₁ × Y₂)
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (Q : ℕ) :
    ((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
        (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).HiddenReadsPair
      ((unforgeChallenger Sf n Of keys Q).preReprog sp (w1Pts Of keys) 1 (k * T)
        (w1Pts_queries keys) (card_w1Pts_le keys))
      (1 + k * T + (unforgeChallenger Sf n Of keys Q).q) :=
  by
  refine Challenger.HiddenReadsPair.ofPreReprogKeep (unforgeChallenger Sf n Of keys Q) sp
    (w1Pts Of keys) 1 (k * T) (w1Pts_queries keys) (card_w1Pts_le keys) (B := Set.range O.chPt)
    (PMF.pure ()) (PMF.uniformOfFintype (Sf).SignCoins)
    (fun ω : Unit × (Fin Q → (Sf).SignCoins) => ω.2)
    ?_ (w1KeptPts Of) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact unforgeChallenger_coins_eq keys Q
  · exact unforgeChallenger_plain keys Q
  · exact fun c hist hist' req hh => unforgeChallenger_respond_congr keys Q c hist hist' req
      (by simpa using congrArg List.length hh)
  · exact fun c hist hist' req hh => w1Pts_congr keys c hist hist' req
      (by simpa using congrArg List.length hh)
  · exact fun _ _ _ _ _ => rfl
  · exact fun _ c c' hist req h hc =>
      ⟨unforgeChallenger_respond_congr_coins keys c c' hist req h hc,
        w1Pts_congr_coins keys c c' hist req h hc, rfl⟩
  · exact fun _ c c' hist req h => unforgeChallenger_respond_of_le keys c c' hist req h
  · intro c hist req H'
    rw [w1Pts_eq_histOf keys c hist req]
    exact w1Pts_subset keys c _ req H'
  · intro c hist req O₁ O₂ hoff _
    rw [w1Pts_eq_histOf keys c hist req]
    exact w1Pts_reads hdisj keys c _ req O₁ O₂ hoff
  · exact w1Pts_inter_w1KeptPts_eq sp hch hdisj hdisjg hPS h_laws hv henc keys hs2

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] in
/-- **The hidden-point condition of the pair** (`toReal_guess_mem_hidden_le`): a guess from the
kept-only challenger's response to request number `j` is a hidden point of that request with
probability at most `2 k T Σ_s commitPointMax(Â_s)` over its signing coins; the oracle in force
before the request does not read them. -/
theorem hfind_w1HiddenPair (sp : Y ≃+ Y₁ × Y₂)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (Q : ℕ) (j : Fin Q) (H : X → Y) (ω₀ : (Fin Q → X → Y₁) × Unit) (c : Fin Q → (Sf).SignCoins)
    (rs₀ : List (UnforgeRequest (S := Sf) n Of)) (req : UnforgeRequest (S := Sf) n Of)
    (hl : rs₀.length = (j : ℕ)) (g : Option (UnforgeResponse (S := Sf) Of) → X) :
    ((PMF.uniformOfFintype (Sf).SignCoins).toOuterMeasure {a | g
      (((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
        (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).respAt
          (ω₀.1, Function.update c j a) H rs₀ req) ∈
      ((unforgeChallenger Sf n Of keys Q).hiddenKeep sp (w1Pts Of keys) 1 (k * T)
        (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of) (ω₀.1, Function.update c j a) H
          rs₀ req : Set X)}).toReal ≤
      2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho) := by
  have hlt : rs₀.length < Q := hl ▸ j.2
  obtain rfl : j = ⟨rs₀.length, hlt⟩ := Fin.ext hl.symm
  -- the oracle in force before request `j` does not read its coins
  have hO : ∀ a, ((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
      (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).oracleByReq
        (ω₀.1, Function.update c ⟨rs₀.length, hlt⟩ a) H rs₀ =
      ((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
        (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).oracleByReq (ω₀.1, c) H rs₀ :=
    fun a => by
      have h := Challenger.oracleByReq_preReprogKeep_update (C₀ := unforgeChallenger Sf n Of keys Q)
        (pts := w1Pts Of keys) (sp := sp) (qp := 1) (K := k * T)
        (hqp := w1Pts_queries keys) (hK := card_w1Pts_le keys)
        (fun ω : Unit × (Fin Q → (Sf).SignCoins) => ω.2) (w1KeptPts Of)
        (unforgeChallenger_plain keys Q)
        (fun _ c c' hist req h hc =>
          ⟨unforgeChallenger_respond_congr_coins keys c c' hist req h hc,
            w1Pts_congr_coins keys c c' hist req h hc, rfl⟩)
        (fun _ c c' hist req h => unforgeChallenger_respond_of_le keys c c' hist req h)
        (w1Pts_inter_w1KeptPts_eq sp hch hdisj hdisjg hPS h_laws hv henc keys hs2)
        ω₀.1 () c ⟨rs₀.length, hlt⟩ a (c ⟨rs₀.length, hlt⟩) H rs₀
        (fun rs' req' hp hlen' => absurd (hp.length_le) (by simp [hlen']))
        rs₀ (List.prefix_refl _)
      have hcc : Function.update c ⟨rs₀.length, hlt⟩ (c ⟨rs₀.length, hlt⟩) = c :=
        Function.update_eq_self _ _
      exact h.trans (congrArg (fun d => ((unforgeChallenger Sf n Of keys Q).preReprogKeep sp
        (w1Pts Of keys) 1 (k * T) (w1Pts_queries keys) (card_w1Pts_le keys)
          (w1KeptPts Of)).oracleByReq (ω₀.1, d) H rs₀) hcc)
  have hlen : (Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs₀).length < Q := by
    simpa [Challenger.histOf] using hlt
  have hr' : ∀ a, ((((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
      (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).respond
        (ω₀.1, Function.update c ⟨rs₀.length, hlt⟩ a) (Challenger.histOf rs₀) req).run
          (((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
            (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).oracleByReq
              (ω₀.1, c) H rs₀)).response =
      w1Resp Of sp keys (Function.update c ⟨rs₀.length, hlt⟩ a) (Challenger.histOf rs₀) req
        (ω₀.1 ⟨(Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs₀).length, hlen⟩)
        (((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
          (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).oracleByReq (ω₀.1, c) H rs₀) :=
    fun a => (Challenger.response_preReprogKeep (C₀ := unforgeChallenger Sf n Of keys Q)
      (sp := sp) (pts := w1Pts Of keys) (qp := 1) (K := k * T) (hqp := w1Pts_queries keys)
      (hK := card_w1Pts_le keys) (w1KeptPts Of) (ω₀.1, Function.update c ⟨rs₀.length, hlt⟩ a)
      (Challenger.histOf rs₀) req _).trans
      (congrArg (fun r => r.response) (Challenger.run_respond_preReprog
        (C₀ := unforgeChallenger Sf n Of keys Q)
        (sp := sp) (pts := w1Pts Of keys) (qp := 1) (K := k * T) (hqp := w1Pts_queries keys)
        (hK := card_w1Pts_le keys) ω₀.1 (Function.update c ⟨rs₀.length, hlt⟩ a)
        (Challenger.histOf rs₀) req _ hlen))
  have hr : ∀ a, ((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
      (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).respAt
        (ω₀.1, Function.update c ⟨rs₀.length, hlt⟩ a) H rs₀ req =
      w1Resp Of sp keys (Function.update c ⟨rs₀.length, hlt⟩ a) (Challenger.histOf rs₀) req
        (ω₀.1 ⟨(Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs₀).length, hlen⟩)
        (((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
          (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).oracleByReq (ω₀.1, c) H rs₀) :=
    fun a => by
      unfold Challenger.respAt
      rw [hO a]
      exact hr' a
  have hh : ∀ a, (unforgeChallenger Sf n Of keys Q).hiddenKeep sp (w1Pts Of keys) 1 (k * T)
      (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)
        (ω₀.1, Function.update c ⟨rs₀.length, hlt⟩ a) H rs₀ req =
      (w1Pts Of keys (Function.update c ⟨rs₀.length, hlt⟩ a) (Challenger.histOf rs₀) req).run
          (((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
            (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).oracleByReq (ω₀.1, c) H rs₀) \
        w1KeptPts Of (Function.update c ⟨rs₀.length, hlt⟩ a) (Challenger.histOf rs₀) req
          (w1Resp Of sp keys (Function.update c ⟨rs₀.length, hlt⟩ a) (Challenger.histOf rs₀) req
            (ω₀.1 ⟨(Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs₀).length, hlen⟩)
            (((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
              (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).oracleByReq
                (ω₀.1, c) H rs₀)) := fun a => by
    unfold Challenger.hiddenKeep
    rw [hO a]
    congr 2
    exact hr' a
  refine le_of_eq_of_le (congrArg ENNReal.toReal (congrArg _ (Set.ext fun a => ?_)))
    (toReal_guess_mem_hidden_le sp hMask hch hdisj hdisjg hPS h_laws hv henc keys hs2 c rs₀ req
      hlt (ω₀.1 ⟨(Challenger.histOf (Resp := UnforgeResponse (S := Sf) Of) rs₀).length, hlen⟩)
      (((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
        (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of)).oracleByReq (ω₀.1, c) H rs₀) g)
  change _ ∈ (_ : Set X) ↔ _
  rw [hh a, hr a]
  rfl

omit [Fintype TPS.Proof] [DecidableEq TPS.Proof] in
/-- **The kept-only against the full reprogramming challenger** (hidden points with the
challenger's reads as queries, `AdaptiveIAlg.advantage_outLaw_le_of_hiddenReadsPair`, at the
pair `w1HiddenPair` and the point bound of `hfind_w1HiddenPair`): the probabilities that an
interactive adversary outputs `o`, averaged over the uniform oracle, differ by at most
`2 √(q + Q) √((width · q + q_C · Q) · Q · 2 k T Σ_s commitPointMax(Â_s))`, `q = budget + post`,
`q_C = 1 + k T + q_S` the reads of a request. -/
theorem advantage_outLaw_w1Hidden_le [Nonempty X]
    [Fintype (UnforgeRequest (S := Sf) n Of)] [DecidableEq (UnforgeRequest (S := Sf) n Of)]
    [Fintype (UnforgeResponse (S := Sf) Of)] [DecidableEq (UnforgeResponse (S := Sf) Of)]
    [Nonempty (UnforgeRequest (S := Sf) n Of)] {Ot : Type} [DecidableEq Ot]
    (sp : Y ≃+ Y₁ × Y₂)
    (hMask : (PMF.uniformOfFintype Y).map M.ans = PMF.uniformOfFintype (MaskBox p))
    (hch : Function.Injective O.chPt) (hdisj : ∀ a b, O.muPt a ≠ O.chPt b)
    (hdisjg : ∀ a b, O.gPt a ≠ O.chPt b) (hPS : ProverReadsPub O PS sp)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (keys : Fin n → (Sf).KeyCoins) (hs2 : ∀ s, polyVecBounded (keyGen prims (keys s)).2.s2 p.eta)
    (Q : ℕ)
    {shA : AlgShape X Y (UnforgeRequest (S := Sf) n Of) (UnforgeResponse (S := Sf) Of)} (A : AdaptiveIAlg shA Ot)
    (o : Ot) :
    GordieHowe.advantage
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ((A.compose ((unforgeChallenger Sf n Of keys Q).preReprogKeep sp (w1Pts Of keys) 1 (k * T)
          (w1Pts_queries keys) (card_w1Pts_le keys) (w1KeptPts Of))).outLaw H (some o)).toReal)
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ((A.compose ((unforgeChallenger Sf n Of keys Q).preReprog sp (w1Pts Of keys) 1 (k * T)
          (w1Pts_queries keys) (card_w1Pts_le keys))).outLaw H (some o)).toReal) ≤
      2 * √((A.budget + A.post : ℕ) +
          ((if 1 + k * T + (unforgeChallenger Sf n Of keys Q).q = 0 then 0 else Q : ℕ) : ℝ)) *
        √((A.width * (A.budget + A.post : ℕ) +
            ((1 + k * T + (unforgeChallenger Sf n Of keys Q).q : ℕ) : ℝ) * Q) *
          ∑ _j : Fin Q, 2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho)) :=
  A.advantage_outLaw_le_of_hiddenReadsPair
    (w1HiddenPair Of sp hch hdisj hdisjg hPS h_laws hv henc keys hs2 Q)
    (fun _ => 2 * k * T * ∑ s, commitPointMax (prims.expandA ((Sf).sk (keys s)).rho))
    (fun j H ω₀ c rs₀ req hl g =>
      hfind_w1HiddenPair sp hMask hch hdisj hdisjg hPS h_laws hv henc keys hs2 Q j H ω₀ c rs₀ req
        hl g) o

end Pair

end GordieHowe.Ring.MLDSAW1
