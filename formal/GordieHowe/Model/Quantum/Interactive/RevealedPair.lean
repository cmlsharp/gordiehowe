-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.O2H.RevealedAvg
public import GordieHowe.Model.Quantum.Interactive.SaltReprogram

@[expose] public section

/-!
# A plain challenger and its counterpart reprogramming at revealed points

`reprogBase sp S z H` sets the first component of the values of `H` on `S` to `z`, through the
splitting `sp : Y ≃+ Y₁ × Y₂`; `mixB` does the same on a set `B` with values from a function.

`Challenger.RespondsByRequests` says a challenger reads its history only through the requests.
For such a challenger, `RespondsByRequests.toPureEnv` computes the oracle in force in the pure game
after the requests `rs` as `oracleByReq` (the assignments of the replies at the canonical
histories `histOf`, applied in order) and the answers from it; `toPureEnv_congr` derives that two
such challengers with the same request bound and the same replies at canonical histories have the
same answers and oracles in force.

`Challenger.RevealedPair` relates a plain challenger `C₀`, which reprograms nothing, to a
counterpart `C₁` that at each request sets the first component of the oracle on a few points to
fresh uniform values and replies as `C₀` at the reprogrammed oracle; this is the setting of
adaptive reprogramming at points revealed to the adversary (Grilo, Hövelmanns, Hülsing, Majenz,
"Tight adaptive reprogramming in the QROM", ASIACRYPT 2021). The hybrid `hyb e` behaves as `C₀`
for the requests numbered below `e` and as `C₁` from then on, and reads the history only through
its requests (`byRequests_hyb`).

`Distinguisher.acceptWithAt_congr` says environments with the same answers and oracles in force
accept with the same probability. Averaged over the coins, the hybrid `0` accepts as `C₁`
(`sum_acceptWithAt_hyb_zero`) and the hybrid `Q` as `C₀` (`sum_acceptWithAt_hyb_Q`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Reprogramming the first component of a split oracle -/

section Split

variable {X Y Y₁ Y₂ : Type*} [DecidableEq X] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

/-- **The oracle `H` with the first component of its values on `S` set to `z`**: on `S`, the
value with first component `z x` and the second component of `H x`; elsewhere `H`. -/
def reprogBase (sp : Y ≃+ Y₁ × Y₂) (S : Finset X) (z : X → Y₁) (H : X → Y) : X → Y :=
  fun x => if x ∈ S then sp.symm (z x, (sp (H x)).2) else H x

/-- **The oracle `H` with the first component of its values on `B` taken from `g`.** -/
def mixB (sp : Y ≃+ Y₁ × Y₂) (B : Set X) [DecidablePred (· ∈ B)] (H : X → Y) (g : X → Y₁) :
    X → Y :=
  fun x => if x ∈ B then sp.symm (g x, (sp (H x)).2) else H x

end Split

/-! ### Challengers that read the history through its requests -/

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C : Challenger X Y Req Resp)

/-- **A challenger that reads the history only through its requests.** -/
def RespondsByRequests : Prop :=
  ∀ c (hist hist' : List (HistoryEntry Req Resp)) req,
    hist.map HistoryEntry.request = hist'.map HistoryEntry.request →
      C.respond c hist req = C.respond c hist' req

/-- The history with the requests `rs` and no responses. -/
def histOf (rs : List Req) : List (HistoryEntry Req Resp) :=
  rs.map fun r => ⟨r, none⟩

/-- **The oracle in force after the requests `rs`**, for a challenger that reads the history only
through its requests: each request numbered below `Q` applies its assignments to the oracle in
force. -/
noncomputable def oracleByReq (c : C.Coins) (H : X → Y) (rs : List Req) : X → Y :=
  (rs.foldl (fun (p : (X → Y) × List Req) req =>
    (if p.2.length < C.Q then p.1.reprogram ((C.respond c (histOf p.2) req).run p.1).assignments
      else p.1, p.2 ++ [req])) (H, [])).1

variable {C}

/-- A left fold whose second component appends each element ends with the list appended. -/
theorem foldl_snd_eq_append {β γ : Type*} (f : β × List γ → γ → β × List γ)
    (hf : ∀ p a, (f p a).2 = p.2 ++ [a]) (rs : List γ) (p : β × List γ) :
    (rs.foldl f p).2 = p.2 ++ rs := by
  induction rs generalizing p with
  | nil => simp
  | cons a rs ih => rw [List.foldl_cons, ih, hf, List.append_assoc, List.singleton_append]

/-- The canonical history of `rs` has the requests `rs`. -/
@[simp] theorem map_request_histOf (rs : List Req) :
    (histOf (Resp := Resp) rs).map HistoryEntry.request = rs := by
  simp [histOf, Function.comp_def]

omit [Fintype X] [Fintype Y] [Nonempty Y] in
/-- **`oracleByReq` request by request**: a request numbered below `Q` applies its assignments. -/
theorem oracleByReq_append_singleton (c : C.Coins) (H : X → Y) (rs : List Req) (req : Req) :
    C.oracleByReq c H (rs ++ [req]) = if rs.length < C.Q then
      (C.oracleByReq c H rs).reprogram
        ((C.respond c (histOf rs) req).run (C.oracleByReq c H rs)).assignments
    else C.oracleByReq c H rs := by
  unfold oracleByReq
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil,
    foldl_snd_eq_append _ (fun _ _ => rfl), List.nil_append]

omit [Fintype X] [Fintype Y] [Nonempty Y] in
/-- **Challengers with the same responses at canonical histories have the same `oracleByReq`.** -/
theorem oracleByReq_congr {C' : Challenger X Y Req Resp} (hQ : C.Q = C'.Q) {c : C.Coins}
    {c' : C'.Coins} (h : ∀ rs req, rs.length < C.Q →
      C.respond c (histOf rs) req = C'.respond c' (histOf rs) req) (H : X → Y) (rs : List Req) :
    C.oracleByReq c H rs = C'.oracleByReq c' H rs := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs req ih =>
    rw [oracleByReq_append_singleton, oracleByReq_append_singleton, ← hQ, ih]
    split_ifs with hq
    · rw [h _ _ hq]
    · rfl

/-- **The pure game's challenger, for a challenger that reads the history only through its
requests**: the oracle in force after `rs` is `oracleByReq`, and the answer to `req` after `rs`
is the response of the program at the canonical history and that oracle. -/
theorem RespondsByRequests.toPureEnv (hC : C.RespondsByRequests) (H : X → Y) (c : C.Coins)
    (rs : List Req) :
    (OracleState.toOracle (C.toPureEnv.oracleIn (H, c) rs) : X → Y) = C.oracleByReq c H rs ∧
      ∀ req, C.toPureEnv.answerAfter (H, c) rs req = if rs.length < C.Q then
        ((C.respond c (histOf rs) req).run (C.oracleByReq c H rs)).response else none := by
  have key : ∀ rs : List Req, (C.toPureEnv.oracleIn (H, c) rs).base = H ∧
      (C.toPureEnv.oracleIn (H, c) rs).hist.map HistoryEntry.request = rs.take C.Q ∧
      (C.toPureEnv.oracleIn (H, c) rs).base.reprogram (C.toPureEnv.oracleIn (H, c) rs).ass =
        C.oracleByReq c H rs := by
    intro rs
    induction rs using List.reverseRecOn with
    | nil => exact ⟨rfl, by simp [Env.oracleIn_nil, Challenger.toPureEnv], by
        simp [Env.oracleIn_nil, Challenger.toPureEnv, oracleByReq, Function.reprogram]⟩
    | append_singleton rs req ih =>
      obtain ⟨hb, hh, ho⟩ := ih
      rw [Env.oracleIn_append_singleton, Env.update, oracleByReq_append_singleton]
      by_cases hq : rs.length < C.Q
      · simp only [hq, ↓reduceDIte, ↓reduceIte]
        have hhist : (C.toPureEnv.oracleIn (H, c) rs).hist.map HistoryEntry.request =
            (histOf (Resp := Resp) rs).map HistoryEntry.request := by
          rw [hh, List.take_of_length_le hq.le, map_request_histOf]
        have hr := hC c _ _ req hhist
        generalize C.toPureEnv.oracleIn (H, c) rs = s at hb hh ho hr
        simp only [Challenger.toPureEnv]
        refine ⟨hb, ?_, ?_⟩
        · rw [List.map_append, hh, List.take_of_length_le hq.le,
            List.take_of_length_le (by simp; omega)]
          rfl
        · rw [QROM.reprogram_append, ho, hr]
      · simp only [hq, ↓reduceDIte, ↓reduceIte]
        exact ⟨hb, by rw [hh, List.take_append_of_le_length (not_lt.1 hq)], ho⟩
  refine ⟨(key rs).2.2, fun req => ?_⟩
  rw [Env.answerAfter]
  split_ifs with hq
  · obtain ⟨-, hh, ho⟩ := key rs
    have hhist : (C.toPureEnv.oracleIn (H, c) rs).hist.map HistoryEntry.request =
        (histOf (Resp := Resp) rs).map HistoryEntry.request := by
      rw [hh, List.take_of_length_le hq.le, map_request_histOf]
    change ((C.respond c (C.toPureEnv.oracleIn (H, c) rs).hist req).run
      ((C.toPureEnv.oracleIn (H, c) rs).base.reprogram (C.toPureEnv.oracleIn (H, c) rs).ass)).response = _
    rw [ho, hC c _ _ req hhist]
  · rfl

/-- **Challengers with the same responses at canonical histories give the same pure game**: the
same answers and oracles in force after every list of requests. -/
theorem RespondsByRequests.toPureEnv_congr {C' : Challenger X Y Req Resp}
    (hC : C.RespondsByRequests) (hC' : C'.RespondsByRequests) (hQ : C.Q = C'.Q) {c : C.Coins}
    {c' : C'.Coins} (h : ∀ rs req, rs.length < C.Q →
      C.respond c (histOf rs) req = C'.respond c' (histOf rs) req) (H : X → Y) :
    (∀ rs req, C.toPureEnv.answerAfter (H, c) rs req = C'.toPureEnv.answerAfter (H, c') rs req) ∧
      ∀ rs, (OracleState.toOracle (C.toPureEnv.oracleIn (H, c) rs) : X → Y) =
        OracleState.toOracle (C'.toPureEnv.oracleIn (H, c') rs) := by
  refine ⟨fun rs req => ?_, fun rs => ?_⟩
  · rw [(hC.toPureEnv H c rs).2, (hC'.toPureEnv H c' rs).2, oracleByReq_congr hQ h, ← hQ]
    split_ifs with hq
    · rw [h _ _ hq]
    · rfl
  · rw [(hC.toPureEnv H c rs).1, (hC'.toPureEnv H c' rs).1, oracleByReq_congr hQ h]

end Challenger

/-! ### A plain challenger and its reprogramming counterpart -/

namespace Challenger

variable {X Y Y₁ Y₂ Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]

/-- **A plain challenger and its counterpart that reprograms at revealed points.** The plain
challenger `C₀` reprograms nothing; its coins are `(ω₀, c) ← ν ⊗ ζ^Q` read through `enc₀`, with
`c j` the fresh coins of request number `j`: its reply to request `j` reads only `ω₀` and the
coins of the requests up to `j` (`causal`). At request number `j`, after the requests `rs`, with
request `req` and oracle in force `O`, the points `pts ω₀ c rs req O` are a finite subset of `B`
(`pts_subset`) that read the coins as the replies do (`pts_causal`) and the oracle only outside
`B` and through the second component (`pts_reads`); every point is among them with probability at
most `ε` over the fresh coins of request `j` (`pts_le`). The counterpart `C₁` has the coins
`(Z, (ω₀, c))` with `Z : Fin Q → X → Y₁` uniform and independent, read through `enc₁`; at
request `j` it replies with the response of `C₀` at the oracle `O'` whose first component on the
points is `Z j`, and its assignments turn `O` into `O'` (`reprog`). Both read the history only
through its requests. -/
structure RevealedPair (sp : Y ≃+ Y₁ × Y₂) (B : Set X) (ε : ℝ) (C₀ C₁ : Challenger X Y Req Resp)
    where
  /-- The coins that every request may read. -/
  Ω₀ : Type
  [instFintypeΩ₀ : Fintype Ω₀]
  [instDecEqΩ₀ : DecidableEq Ω₀]
  /-- The fresh coins of one request. -/
  Cn : Type
  [instFintypeCn : Fintype Cn]
  [instDecEqCn : DecidableEq Cn]
  /-- The law of the shared coins. -/
  ν : PMF Ω₀
  /-- The law of the fresh coins of one request. -/
  ζ : PMF Cn
  /-- The coins of `C₀` from the shared and the fresh coins. -/
  enc₀ : Ω₀ × (Fin C₀.Q → Cn) → C₀.Coins
  coins₀ : C₀.coins = (prodLaw ν (PMF.pi fun _ => ζ)).map enc₀
  /-- `C₀` reprograms nothing. -/
  plain : ∀ c hist req H, ((C₀.respond c hist req).run H).assignments = []
  byRequests₀ : C₀.RespondsByRequests
  /-- The reply to request `j` reads only the shared coins and the fresh coins up to `j`. -/
  causal : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req, (∀ i : Fin C₀.Q, (i : ℕ) ≤ hist.length → c i = c' i) →
    C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req
  /-- The points reprogrammed at a request. -/
  pts : Ω₀ → (Fin C₀.Q → Cn) → List Req → Req → (X → Y) → Finset X
  pts_subset : ∀ ω₀ c rs req O, (pts ω₀ c rs req O : Set X) ⊆ B
  pts_causal : ∀ ω₀ (c c' : Fin C₀.Q → Cn) rs req O,
    (∀ i : Fin C₀.Q, (i : ℕ) ≤ rs.length → c i = c' i) → pts ω₀ c rs req O = pts ω₀ c' rs req O
  pts_reads : ∀ ω₀ c rs req (O O' : X → Y), (∀ x ∉ B, O x = O' x) →
    (∀ x, (sp (O x)).2 = (sp (O' x)).2) → pts ω₀ c rs req O = pts ω₀ c rs req O'
  pts_le : ∀ ω₀ c rs req O x (h : rs.length < C₀.Q),
    (ζ.toOuterMeasure {c' | x ∈ pts ω₀ (Function.update c ⟨rs.length, h⟩ c') rs req O}).toReal ≤ ε
  /-- The coins of `C₁` from the fresh values and the coins of `C₀`. -/
  enc₁ : (Fin C₀.Q → X → Y₁) × (Ω₀ × (Fin C₀.Q → Cn)) → C₁.Coins
  coins₁ : C₁.coins =
    (prodLaw (PMF.uniformOfFintype (Fin C₀.Q → X → Y₁)) (prodLaw ν (PMF.pi fun _ => ζ))).map enc₁
  byRequests₁ : C₁.RespondsByRequests
  /-- `C₁` replies as `C₀` at the reprogrammed oracle, and its assignments reprogram it. -/
  reprog : ∀ Z ω hist req H (h : hist.length < C₀.Q),
    ((C₁.respond (enc₁ (Z, ω)) hist req).run H).response =
        ((C₀.respond (enc₀ ω) hist req).run
          (reprogBase sp (pts ω.1 ω.2 (hist.map HistoryEntry.request) req H) (Z ⟨hist.length, h⟩) H)).response ∧
      H.reprogram ((C₁.respond (enc₁ (Z, ω)) hist req).run H).assignments =
        reprogBase sp (pts ω.1 ω.2 (hist.map HistoryEntry.request) req H) (Z ⟨hist.length, h⟩) H
  Q_eq : C₁.Q = C₀.Q

attribute [instance] RevealedPair.instFintypeΩ₀ RevealedPair.instDecEqΩ₀ RevealedPair.instFintypeCn
  RevealedPair.instDecEqCn

namespace RevealedPair

variable {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ} {C₀ C₁ : Challenger X Y Req Resp}
  (P : RevealedPair sp B ε C₀ C₁)

/-- **The coins of the hybrids**: the fresh values, the shared coins and the fresh coins. -/
abbrev HCoins := (Fin C₀.Q → X → Y₁) × (P.Ω₀ × (Fin C₀.Q → P.Cn))

/-- The law of the coins of the hybrids. -/
noncomputable def hLaw : PMF P.HCoins :=
  prodLaw (PMF.uniformOfFintype (Fin C₀.Q → X → Y₁)) (prodLaw P.ν (PMF.pi fun _ => P.ζ))

/-- **The hybrid challenger `e`**: `C₀` for the requests numbered below `e`, `C₁` from request `e`
on. -/
noncomputable def hyb [Nonempty Y₁] (e : ℕ) : Challenger X Y Req Resp where
  Coins := P.HCoins
  coins := P.hLaw
  Q := C₀.Q
  q := max C₀.q C₁.q
  respond ψ hist req :=
    if hist.length < e then C₀.respond (P.enc₀ ψ.2) hist req else C₁.respond (P.enc₁ ψ) hist req
  respond_queries ψ hist req H := by
    split_ifs
    · exact (C₀.respond_queries _ _ _ _).trans (le_max_left _ _)
    · exact (C₁.respond_queries _ _ _ _).trans (le_max_right _ _)

omit [Fintype Y] [Nonempty Y] in
/-- **The hybrid reads the history only through its requests.** -/
theorem byRequests_hyb [Nonempty Y₁] (e : ℕ) : (P.hyb e).RespondsByRequests := by
  intro ψ hist hist' req h
  have hl : hist.length = hist'.length := by
    rw [← List.length_map (f := HistoryEntry.request), h, List.length_map]
  simp only [hyb]
  rw [hl]
  split_ifs
  · exact P.byRequests₀ _ _ _ _ h
  · exact P.byRequests₁ _ _ _ _ h

end RevealedPair

end Challenger

namespace Distinguisher

variable {W X Y Y₁ Y₂ Req Resp : Type} [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y]
  [Nonempty Y] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  [Nonempty Y₁] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ}
  {C₀ C₁ : Challenger X Y Req Resp} (P : C₀.RevealedPair sp B ε C₁)

omit [DecidableEq X] [Nonempty Y] in
/-- **Environments with the same answers and oracles in force accept with the same
probability.** -/
theorem acceptWithAt_congr {Ω Ω' St St' : Type} {Q Q' : ℕ} [OracleState St X Y]
    [OracleState St' X Y] (E : Env Ω Req Resp X Y Q St) (E' : Env Ω' Req Resp X Y Q' St')
    {ω : Ω} {ω' : Ω'} (hans : ∀ rs req, E.answerAfter ω rs req = E'.answerAfter ω' rs req)
    (horc : ∀ rs, (OracleState.toOracle (E.oracleIn ω rs) : X → Y) =
      OracleState.toOracle (E'.oracleIn ω' rs))
    (Pev : DReg W n X Y Req Resp → LogReg Req m → (X → Y) → Prop) :
    D.acceptWithAt E Pev ω = D.acceptWithAt E' Pev ω' := by
  unfold acceptWithAt Env.oracle
  rw [D.run_eq_contOp E ω (Nat.zero_le _), D.run_eq_contOp E' ω' (Nat.zero_le _),
    D.contOp_congr E E' hans horc, D.stage_congr E E' hans horc]
  simp only [horc]

/-- **The hybrid `0` is `C₁`**: averaged over the coins, the same acceptance probability. -/
theorem sum_acceptWithAt_hyb_zero (Pev : DReg W n X Y Req Resp → LogReg Req m → (X → Y) → Prop)
    (H : X → Y) :
    ∑ c, (C₁.coins c).toReal * D.acceptWithAt C₁.toPureEnv Pev (H, c) =
      ∑ ψ, (P.hLaw ψ).toReal * D.acceptWithAt (P.hyb 0).toPureEnv Pev (H, ψ) := by
  rw [P.coins₁, PMF.sum_toReal_map_mul]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  congr 1
  obtain ⟨hans, horc⟩ := Challenger.RespondsByRequests.toPureEnv_congr P.byRequests₁
    (P.byRequests_hyb 0) P.Q_eq (c := P.enc₁ ψ) (c' := ψ)
    (fun rs req _ => by
        show _ = if (Challenger.histOf (Resp := Resp) rs).length < 0 then
          C₀.respond (P.enc₀ ψ.2) (Challenger.histOf rs) req
          else C₁.respond (P.enc₁ ψ) (Challenger.histOf rs) req
        simp) H
  exact D.acceptWithAt_congr _ _ hans horc Pev

/-- **The hybrid `Q` is `C₀`**: averaged over the coins, the same acceptance probability. -/
theorem sum_acceptWithAt_hyb_Q (Pev : DReg W n X Y Req Resp → LogReg Req m → (X → Y) → Prop)
    (H : X → Y) :
    ∑ c, (C₀.coins c).toReal * D.acceptWithAt C₀.toPureEnv Pev (H, c) =
      ∑ ψ, (P.hLaw ψ).toReal * D.acceptWithAt (P.hyb C₀.Q).toPureEnv Pev (H, ψ) := by
  rw [P.coins₀, PMF.sum_toReal_map_mul]
  symm
  rw [Fintype.sum_prod_type]
  have hu : ∑ z, (PMF.uniformOfFintype (Fin C₀.Q → X → Y₁) z).toReal = 1 := by
    have h1 := PMF.tsum_coe (PMF.uniformOfFintype (Fin C₀.Q → X → Y₁))
    rw [tsum_fintype] at h1
    rw [← ENNReal.toReal_sum (fun _ _ => PMF.apply_ne_top _ _), h1, ENNReal.toReal_one]
  have hψ : ∀ z ω, (P.hLaw (z, ω)).toReal * D.acceptWithAt (P.hyb C₀.Q).toPureEnv Pev (H, (z, ω)) =
      (PMF.uniformOfFintype (Fin C₀.Q → X → Y₁) z).toReal *
        ((prodLaw P.ν (PMF.pi fun _ => P.ζ) ω).toReal * D.acceptWithAt C₀.toPureEnv Pev (H, P.enc₀ ω)) := by
    intro z ω
    rw [Challenger.RevealedPair.hLaw, prodLaw_apply, ENNReal.toReal_mul, mul_assoc]
    congr 2
    obtain ⟨hans, horc⟩ := Challenger.RespondsByRequests.toPureEnv_congr P.byRequests₀
      (P.byRequests_hyb C₀.Q) rfl (c := P.enc₀ ω) (c' := (z, ω))
      (fun rs req hq => by
        show _ = if (Challenger.histOf (Resp := Resp) rs).length < C₀.Q then
          C₀.respond (P.enc₀ ω) (Challenger.histOf rs) req
          else C₁.respond (P.enc₁ (z, ω)) (Challenger.histOf rs) req
        simp [Challenger.histOf, hq]) H
    exact (D.acceptWithAt_congr _ _ hans horc Pev).symm
  simp_rw [hψ, ← Finset.mul_sum, ← Finset.sum_mul, hu, one_mul]

end Distinguisher

end GordieHowe.Quantum
