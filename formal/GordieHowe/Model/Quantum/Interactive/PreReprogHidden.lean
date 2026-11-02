-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.PreReprog
public import GordieHowe.Model.Quantum.Interactive.HiddenReadsPair

@[expose] public section

/-!
# The kept-only and the full reprogramming challenger as a hidden-reads pair

The reprogramming challenger `Challenger.preReprog C₀ sp pts` reprograms the base component at the
points of each request before answering; `Challenger.preReprogKeep … keep` answers the same but
keeps in force only the assignments at the kept points
(`GordieHowe/Model/Quantum/Interactive/PreReprog.lean`). Their oracles in force differ only at the
points not kept (`oracleByReq_preReprogKeep_eq`), and their responses differ only when a request
reads such a point of an earlier request (`response_preReprogKeep_eq_of_reads`). With the fresh base
values `Z` among the shared coins, the two form a `HiddenReadsPair`
(`GordieHowe/Model/Quantum/Interactive/HiddenReadsPair.lean`) when `C₀` is plain, reads the history
through its requests and each request's coins only at that request, the points and the kept points
do the same, and the kept points of a request are determined by its response (`hkept`).

- `prodLaw_map_assoc`: a product law with its second factor a mapped product is a mapped product.
- `respondsByRequests_preReprog`: the full reprogramming challenger reads the history through its
  requests.
- `Challenger.HiddenReadsPair.ofPreReprogKeep`: **the hidden-reads pair**, with the reads of a
  request the queries of the full reprogramming challenger's response at the kept-only
  challenger's oracle in force, at most `qp + K + C₀.q`.
-/

namespace GordieHowe

namespace Quantum

namespace Challenger

variable {X Y Y₁ Y₂ Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]

/-- **A product law with its second factor a mapped product** is the product of the first two
factors with the third, mapped. -/
theorem prodLaw_map_assoc {α β γ δ : Type*} (p : PMF α) (q : PMF β) (r : PMF γ)
    (f : β × γ → δ) :
    prodLaw p ((prodLaw q r).map f) =
      (prodLaw (prodLaw p q) r).map fun x => (x.1.1, f (x.1.2, x.2)) := by
  simp only [prodLaw, PMF.map_bind, PMF.bind_bind, PMF.map_comp, PMF.bind_map, Function.comp_apply]
  rfl

variable {C₀ : Challenger X Y Req Resp} {sp : Y ≃+ Y₁ × Y₂}
  {pts : C₀.Coins → List (HistoryEntry Req Resp) → Req → OracleProg X Y (Finset X)}
  {qp K : ℕ} {hqp : ∀ c hist req, (pts c hist req).QueriesLE qp}
  {hK : ∀ c hist req H, ((pts c hist req).run H).card ≤ K}

omit [Fintype Y] [Nonempty Y] in
/-- **The full reprogramming challenger reads the history only through its requests** when `C₀`
and the point program do. -/
theorem respondsByRequests_preReprog (byRequests₀ : C₀.RespondsByRequests)
    (hptsReq : ∀ c (hist hist' : List (HistoryEntry Req Resp)) req,
      hist.map HistoryEntry.request = hist'.map HistoryEntry.request →
      pts c hist req = pts c hist' req) :
    (C₀.preReprog sp pts qp K hqp hK).RespondsByRequests := by
  intro c hist hist' req hh
  have hlen : hist.length = hist'.length := by
    simpa using congrArg List.length hh
  simp only [preReprog, hptsReq c.2 hist hist' req hh, byRequests₀ c.2 hist hist' req hh, hlen]

omit [Fintype Y] [Nonempty Y] in
/-- **The kept-only reprogramming challenger reads request `|hist|`'s coins only** when `C₀`, the
points and the kept points do. -/
theorem respond_preReprogKeep_congr {Ω₀ Cn : Type} (enc₀ : Ω₀ × (Fin C₀.Q → Cn) → C₀.Coins)
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (own : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req (h : hist.length < C₀.Q),
      c ⟨hist.length, h⟩ = c' ⟨hist.length, h⟩ →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req ∧
        pts (enc₀ (ω₀, c)) hist req = pts (enc₀ (ω₀, c')) hist req ∧
        keep (enc₀ (ω₀, c)) hist req = keep (enc₀ (ω₀, c')) hist req)
    (ownQ : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req, C₀.Q ≤ hist.length →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req)
    (Z : Fin C₀.Q → X → Y₁) (ω₀ : Ω₀) (c c' : Fin C₀.Q → Cn)
    (hist : List (HistoryEntry Req Resp)) (req : Req)
    (hc : ∀ h : hist.length < C₀.Q, c ⟨hist.length, h⟩ = c' ⟨hist.length, h⟩) :
    (C₀.preReprogKeep sp pts qp K hqp hK keep).respond (Z, enc₀ (ω₀, c)) hist req =
        (C₀.preReprogKeep sp pts qp K hqp hK keep).respond (Z, enc₀ (ω₀, c')) hist req ∧
      (C₀.preReprog sp pts qp K hqp hK).respond (Z, enc₀ (ω₀, c)) hist req =
        (C₀.preReprog sp pts qp K hqp hK).respond (Z, enc₀ (ω₀, c')) hist req := by
  by_cases h : hist.length < C₀.Q
  · obtain ⟨h1, h2, h3⟩ := own ω₀ c c' hist req h (hc h)
    exact ⟨by simp only [preReprogKeep, h, ↓reduceDIte, h1, h2, h3],
      by simp only [preReprog, h, ↓reduceDIte, h1, h2]⟩
  · have h1 := ownQ ω₀ c c' hist req (Nat.le_of_not_lt h)
    exact ⟨by simp only [preReprogKeep, h, ↓reduceDIte, h1],
      by simp only [preReprog, h, ↓reduceDIte, h1]⟩

omit [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y] [AddGroup Y] in
/-- Updating the coins of request `j` keeps the coins of the other requests. -/
theorem update_eq_of_ne {Cn : Type} (c : Fin C₀.Q → Cn) (j : Fin C₀.Q) (a a' : Cn) {n : ℕ}
    (hn : n ≠ (j : ℕ)) (h : n < C₀.Q) :
    Function.update c j a ⟨n, h⟩ = Function.update c j a' ⟨n, h⟩ := by
  have hne : (⟨n, h⟩ : Fin C₀.Q) ≠ j := fun he => hn (congrArg Fin.val he)
  rw [Function.update_of_ne hne, Function.update_of_ne hne]

omit [Fintype Y] [Nonempty Y] in
/-- **A request other than `j` gets the same response and reads** after redrawing request `j`'s
coins, at equal oracles in force. -/
theorem respAt_trace_eq_of_ne {Ω₀ Cn : Type} (enc₀ : Ω₀ × (Fin C₀.Q → Cn) → C₀.Coins)
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (own : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req (h : hist.length < C₀.Q),
      c ⟨hist.length, h⟩ = c' ⟨hist.length, h⟩ →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req ∧
        pts (enc₀ (ω₀, c)) hist req = pts (enc₀ (ω₀, c')) hist req ∧
        keep (enc₀ (ω₀, c)) hist req = keep (enc₀ (ω₀, c')) hist req)
    (ownQ : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req, C₀.Q ≤ hist.length →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req)
    (Z : Fin C₀.Q → X → Y₁) (ω₀ : Ω₀) (c : Fin C₀.Q → Cn) (j : Fin C₀.Q) (a a' : Cn) (H : X → Y)
    (rs : List Req) (req : Req) (hjeq : rs.length ≠ (j : ℕ))
    (ho : (C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq
        (Z, enc₀ (ω₀, Function.update c j a)) H rs =
      (C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq
        (Z, enc₀ (ω₀, Function.update c j a')) H rs) :
    (C₀.preReprogKeep sp pts qp K hqp hK keep).respAt (Z, enc₀ (ω₀, Function.update c j a)) H
        rs req =
      (C₀.preReprogKeep sp pts qp K hqp hK keep).respAt (Z, enc₀ (ω₀, Function.update c j a'))
        H rs req ∧
    ((C₀.preReprog sp pts qp K hqp hK).respond (Z, enc₀ (ω₀, Function.update c j a)) (histOf rs)
        req).trace ((C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq
          (Z, enc₀ (ω₀, Function.update c j a)) H rs) =
      ((C₀.preReprog sp pts qp K hqp hK).respond (Z, enc₀ (ω₀, Function.update c j a'))
        (histOf rs) req).trace ((C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq
          (Z, enc₀ (ω₀, Function.update c j a')) H rs) := by
  have hc : ∀ h : (histOf (Resp := Resp) rs).length < C₀.Q,
      Function.update c j a ⟨(histOf (Resp := Resp) rs).length, h⟩ =
        Function.update c j a' ⟨(histOf (Resp := Resp) rs).length, h⟩ := fun h =>
    update_eq_of_ne c j a a' (by simpa [histOf] using hjeq) h
  obtain ⟨h1, h2⟩ := respond_preReprogKeep_congr (sp := sp) (qp := qp) (K := K) (hqp := hqp)
    (hK := hK) enc₀ keep own ownQ Z ω₀ _ _ (histOf rs) req hc
  unfold respAt
  rw [ho, h1, h2]
  exact ⟨rfl, rfl⟩

omit [Fintype Y] [Nonempty Y] in
/-- **Redrawing the coins of request `j` keeps the kept-only challenger's oracles in force** along
the requests `rs` when it keeps the responses to request `j`: the other requests read their own
coins, and request `j` keeps in force the assignments at its kept points, determined by its
response (`hkept`). -/
theorem oracleByReq_preReprogKeep_update {Ω₀ Cn : Type} (enc₀ : Ω₀ × (Fin C₀.Q → Cn) → C₀.Coins)
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (plain : ∀ c hist req H, ((C₀.respond c hist req).run H).assignments = [])
    (own : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req (h : hist.length < C₀.Q),
      c ⟨hist.length, h⟩ = c' ⟨hist.length, h⟩ →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req ∧
        pts (enc₀ (ω₀, c)) hist req = pts (enc₀ (ω₀, c')) hist req ∧
        keep (enc₀ (ω₀, c)) hist req = keep (enc₀ (ω₀, c')) hist req)
    (ownQ : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req, C₀.Q ≤ hist.length →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req)
    (hkept : ∀ ω₀ (c c' : Fin C₀.Q → Cn) (rs : List Req) req (z : X → Y₁) (O : X → Y)
      (h : rs.length < C₀.Q), (∀ i, i ≠ ⟨rs.length, h⟩ → c i = c' i) →
      ((C₀.respond (enc₀ (ω₀, c)) (histOf rs) req).run
          (reprogBase sp ((pts (enc₀ (ω₀, c)) (histOf rs) req).run O) z O)).response =
        ((C₀.respond (enc₀ (ω₀, c')) (histOf rs) req).run
          (reprogBase sp ((pts (enc₀ (ω₀, c')) (histOf rs) req).run O) z O)).response →
      (pts (enc₀ (ω₀, c)) (histOf rs) req).run O ∩
          keep (enc₀ (ω₀, c)) (histOf rs) req ((C₀.respond (enc₀ (ω₀, c)) (histOf rs) req).run
            (reprogBase sp ((pts (enc₀ (ω₀, c)) (histOf rs) req).run O) z O)).response =
        (pts (enc₀ (ω₀, c')) (histOf rs) req).run O ∩
          keep (enc₀ (ω₀, c')) (histOf rs) req ((C₀.respond (enc₀ (ω₀, c')) (histOf rs) req).run
            (reprogBase sp ((pts (enc₀ (ω₀, c')) (histOf rs) req).run O) z O)).response)
    (Z : Fin C₀.Q → X → Y₁) (ω₀ : Ω₀) (c : Fin C₀.Q → Cn) (j : Fin C₀.Q) (a a' : Cn) (H : X → Y)
    (rs : List Req)
    (hj : ∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length = (j : ℕ) →
      (C₀.preReprogKeep sp pts qp K hqp hK keep).respAt (Z, enc₀ (ω₀, Function.update c j a)) H
          rs₀ req =
        (C₀.preReprogKeep sp pts qp K hqp hK keep).respAt (Z, enc₀ (ω₀, Function.update c j a'))
          H rs₀ req) :
    ∀ rs₀, rs₀ <+: rs →
      (C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq (Z, enc₀ (ω₀, Function.update c j a))
          H rs₀ =
        (C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq
          (Z, enc₀ (ω₀, Function.update c j a')) H rs₀ := by
  intro rs₀ hpre
  induction rs₀ using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs₀ req ih =>
    have ho := ih ((List.prefix_append _ _).trans hpre)
    have ek := oracleByReq_append_singleton (C := C₀.preReprogKeep sp pts qp K hqp hK keep)
      (Z, enc₀ (ω₀, Function.update c j a)) H rs₀ req
    have ek' := oracleByReq_append_singleton (C := C₀.preReprogKeep sp pts qp K hqp hK keep)
      (Z, enc₀ (ω₀, Function.update c j a')) H rs₀ req
    rw [ek, ek', ho]
    have hQk : (C₀.preReprogKeep sp pts qp K hqp hK keep).Q = C₀.Q := rfl
    rw [hQk]
    by_cases hq : rs₀.length < C₀.Q
    · simp only [hq, ↓reduceIte]
      have hlen : (histOf (Resp := Resp) rs₀).length < C₀.Q := by simpa [histOf] using hq
      set O := (C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq
        (Z, enc₀ (ω₀, Function.update c j a')) H rs₀ with hO
      by_cases hjeq : rs₀.length = (j : ℕ)
      · have hjf : (⟨(histOf (Resp := Resp) rs₀).length, hlen⟩ : Fin C₀.Q) = j :=
          Fin.ext (by simpa [histOf] using hjeq)
        have hr := hj rs₀ req hpre hjeq
        unfold respAt at hr
        rw [ho, run_respond_preReprogKeep keep Z _ (histOf rs₀) req O hlen,
          run_respond_preReprogKeep keep Z _ (histOf rs₀) req O hlen] at hr
        have hk := hkept ω₀ (Function.update c j a) (Function.update c j a') rs₀ req
          (Z ⟨(histOf (Resp := Resp) rs₀).length, hlen⟩) O (by simpa [histOf] using hlen)
          (fun i hi => by
            have hij : i ≠ j := fun he =>
              hi (he.trans (Fin.ext (by simpa [histOf] using hjeq.symm)))
            rw [Function.update_of_ne hij, Function.update_of_ne hij]) hr
        rw [run_respond_preReprogKeep keep Z _ (histOf rs₀) req O hlen,
          run_respond_preReprogKeep keep Z _ (histOf rs₀) req O hlen]
        dsimp only
        rw [plain, plain, List.append_nil, List.append_nil]
        funext x
        rw [reprogram_filter_reprogAssigns, reprogram_filter_reprogAssigns]
        have hiff := congrArg (fun T : Finset X => x ∈ T) hk
        simp only [Finset.mem_inter, eq_iff_iff] at hiff
        by_cases hx : x ∈ (pts (enc₀ (ω₀, Function.update c j a)) (histOf rs₀) req).run O ∧
            x ∈ keep (enc₀ (ω₀, Function.update c j a)) (histOf rs₀) req
              ((C₀.respond (enc₀ (ω₀, Function.update c j a)) (histOf rs₀) req).run
                (reprogBase sp ((pts (enc₀ (ω₀, Function.update c j a)) (histOf rs₀) req).run O)
                  (Z ⟨(histOf (Resp := Resp) rs₀).length, hlen⟩) O)).response
        · rw [ite_eq_left_of_eq_true _ _ (eq_true hx),
            ite_eq_left_of_eq_true _ _ (eq_true (hiff.1 hx))]
        · rw [ite_eq_right_of_eq_false _ _ (eq_false hx),
            ite_eq_right_of_eq_false _ _ (eq_false fun h => hx (hiff.2 h))]
      · have hc : ∀ h : (histOf (Resp := Resp) rs₀).length < C₀.Q,
            Function.update c j a ⟨(histOf (Resp := Resp) rs₀).length, h⟩ =
              Function.update c j a' ⟨(histOf (Resp := Resp) rs₀).length, h⟩ := fun h =>
          update_eq_of_ne c j a a' (by simpa [histOf] using hjeq) h
        rw [(respond_preReprogKeep_congr enc₀ keep own ownQ Z ω₀ _ _ (histOf rs₀) req hc).1]
    · simp only [hq, ↓reduceIte]

variable (C₀ sp pts qp K hqp hK) in
/-- **The kept-only and the full reprogramming challenger form a hidden-reads pair** (module
docstring): shared coins the fresh base values `Z` and the shared coins `ω₀ ← ν` of `C₀`, fresh
coins those of `C₀` per request (`c j ← ζ`); hidden points `hiddenKeep`; reads the queries of the
full challenger's response at the kept-only challenger's oracle in force. -/
noncomputable def HiddenReadsPair.ofPreReprogKeep {B : Set X}
    {Ω₀ Cn : Type} [Fintype Ω₀] [DecidableEq Ω₀] [Fintype Cn] [DecidableEq Cn]
    (ν : PMF Ω₀) (ζ : PMF Cn) (enc₀ : Ω₀ × (Fin C₀.Q → Cn) → C₀.Coins)
    (coins₀ : C₀.coins = (prodLaw ν (PMF.pi fun _ => ζ)).map enc₀)
    (keep : C₀.Coins → List (HistoryEntry Req Resp) → Req → Option Resp → Finset X)
    (plain : ∀ c hist req H, ((C₀.respond c hist req).run H).assignments = [])
    (byRequests₀ : C₀.RespondsByRequests)
    (hptsReq : ∀ c (hist hist' : List (HistoryEntry Req Resp)) req,
      hist.map HistoryEntry.request = hist'.map HistoryEntry.request →
      pts c hist req = pts c hist' req)
    (hkeepReq : ∀ c (hist hist' : List (HistoryEntry Req Resp)) req,
      hist.map HistoryEntry.request = hist'.map HistoryEntry.request →
      keep c hist req = keep c hist' req)
    (own : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req (h : hist.length < C₀.Q),
      c ⟨hist.length, h⟩ = c' ⟨hist.length, h⟩ →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req ∧
        pts (enc₀ (ω₀, c)) hist req = pts (enc₀ (ω₀, c')) hist req ∧
        keep (enc₀ (ω₀, c)) hist req = keep (enc₀ (ω₀, c')) hist req)
    (ownQ : ∀ ω₀ (c c' : Fin C₀.Q → Cn) hist req, C₀.Q ≤ hist.length →
      C₀.respond (enc₀ (ω₀, c)) hist req = C₀.respond (enc₀ (ω₀, c')) hist req)
    (hsub : ∀ c hist req O, (((pts c hist req).run O : Finset X) : Set X) ⊆ B)
    (hreads : ∀ c hist req (O O' : X → Y), (∀ x ∉ B, O x = O' x) →
      (∀ x, (sp (O x)).2 = (sp (O' x)).2) → (pts c hist req).run O = (pts c hist req).run O')
    (hkept : ∀ ω₀ (c c' : Fin C₀.Q → Cn) (rs : List Req) req (z : X → Y₁) (O : X → Y)
      (h : rs.length < C₀.Q), (∀ i, i ≠ ⟨rs.length, h⟩ → c i = c' i) →
      ((C₀.respond (enc₀ (ω₀, c)) (histOf rs) req).run
          (reprogBase sp ((pts (enc₀ (ω₀, c)) (histOf rs) req).run O) z O)).response =
        ((C₀.respond (enc₀ (ω₀, c')) (histOf rs) req).run
          (reprogBase sp ((pts (enc₀ (ω₀, c')) (histOf rs) req).run O) z O)).response →
      (pts (enc₀ (ω₀, c)) (histOf rs) req).run O ∩
          keep (enc₀ (ω₀, c)) (histOf rs) req ((C₀.respond (enc₀ (ω₀, c)) (histOf rs) req).run
            (reprogBase sp ((pts (enc₀ (ω₀, c)) (histOf rs) req).run O) z O)).response =
        (pts (enc₀ (ω₀, c')) (histOf rs) req).run O ∩
          keep (enc₀ (ω₀, c')) (histOf rs) req ((C₀.respond (enc₀ (ω₀, c')) (histOf rs) req).run
            (reprogBase sp ((pts (enc₀ (ω₀, c')) (histOf rs) req).run O) z O)).response) :
    (C₀.preReprogKeep sp pts qp K hqp hK keep).HiddenReadsPair (C₀.preReprog sp pts qp K hqp hK)
      (qp + K + C₀.q) where
  Ω₀ := (Fin C₀.Q → X → Y₁) × Ω₀
  Cn := Cn
  ν := prodLaw (PMF.uniformOfFintype _) ν
  ζ := ζ
  enc p := (p.1.1, enc₀ (p.1.2, p.2))
  coins_eq := by
    change prodLaw (PMF.uniformOfFintype _) C₀.coins = _
    rw [coins₀, prodLaw_map_assoc]
    rfl
  enc' p := (p.1.1, enc₀ (p.1.2, p.2))
  coins_eq' := by
    change prodLaw (PMF.uniformOfFintype _) C₀.coins = _
    rw [coins₀, prodLaw_map_assoc]
    rfl
  Q_eq := rfl
  byRequests := respondsByRequests_preReprogKeep keep byRequests₀ hptsReq hkeepReq
  byRequests' := respondsByRequests_preReprog byRequests₀ hptsReq
  hidden H ω₀ c rs req :=
    (C₀.hiddenKeep sp pts qp K hqp hK keep (ω₀.1, enc₀ (ω₀.2, c)) H rs req : Set X)
  reads H ω₀ c rs req :=
    (((C₀.preReprog sp pts qp K hqp hK).respond (ω₀.1, enc₀ (ω₀.2, c)) (histOf rs) req).trace
      ((C₀.preReprogKeep sp pts qp K hqp hK keep).oracleByReq (ω₀.1, enc₀ (ω₀.2, c)) H rs)).toFinset
  reads_card H ω₀ c rs req :=
    (List.toFinset_card_le _).trans (((C₀.preReprog sp pts qp K hqp hK).respond_queries _ _ _ _))
  oracle H ω₀ c rs x hx :=
    oracleByReq_preReprogKeep_eq keep plain hsub hreads _ H rs x fun rs₀ req h hl =>
      fun hm => hx rs₀ req h hl (Finset.mem_coe.2 hm)
  answer H ω₀ c rs req _ hx :=
    response_preReprogKeep_eq_of_reads keep plain hsub hreads _ H rs req fun y hy rs₀ req' h hl =>
      fun hm => hx y (List.mem_toFinset.2 hy) rs₀ req' h hl (Finset.mem_coe.2 hm)
  agree j H ω₀ c a a' rs hj := by
    have ho := oracleByReq_preReprogKeep_update enc₀ keep plain own ownQ hkept ω₀.1 ω₀.2 c j a a' H
      rs hj
    refine ⟨ho, fun rs₀ req hpre _ => ?_⟩
    by_cases hjeq : rs₀.length = (j : ℕ)
    · exact hj rs₀ req hpre hjeq
    · exact (respAt_trace_eq_of_ne enc₀ keep own ownQ ω₀.1 ω₀.2 c j a a' H rs₀ req hjeq
        (ho rs₀ ((List.prefix_append _ _).trans hpre))).1
  reads_agree j H ω₀ c a a' rs req hjl hj := by
    have ho := oracleByReq_preReprogKeep_update enc₀ keep plain own ownQ hkept ω₀.1 ω₀.2 c j a a' H
      rs hj
    exact congrArg List.toFinset (respAt_trace_eq_of_ne enc₀ keep own ownQ ω₀.1 ω₀.2 c j a a' H rs
      req (Nat.ne_of_gt hjl) (ho rs (List.prefix_refl rs))).2

end Challenger

end Quantum

end GordieHowe
