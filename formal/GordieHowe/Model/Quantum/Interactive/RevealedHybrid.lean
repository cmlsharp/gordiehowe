-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.RevealedPair

@[expose] public section

/-!
# One hybrid step of reprogramming at revealed points

The hybrid `e` of a `RevealedPair` (`GordieHowe/Model/Quantum/Interactive/RevealedPair.lean`)
reprograms request `e` at its points; the hybrid `e + 1` does not. On split tapes
`((H, (Z, (ω₀, c))), (g, z))`, read through `hybTape` as the oracle `mixB H g` (the first
components on `B` taken from `g`) and the fresh values `Z` with `z` at `e`, the two hybrids
(`hybEnv`) satisfy `RevealedHyp` with the points `hybPts` (`revealedHyp_hyb`): before request `e`
both reply as `C₀` and keep the oracle, the hybrid `e + 1` never reads `z`, and from request `e`
on the hybrid `e` at `(g, z)` agrees with the hybrid `e + 1` at the tape with `g` and `z`
exchanged on the points (`hyb_post`), since reprogramming the mixed oracle on the points is
mixing in `g` set to `z` there (`reprogBase_mixB`).

The uniform oracle is the uniform mixed oracle (`sum_uniform_mixB`), and under the law of the
coins the fresh value and the fresh coins of request `e` are uniform and independent
(`sum_hLaw_update_Z`, `sum_hLaw_update_c`). So the bound of
`GordieHowe/Model/Quantum/O2H/RevealedAvg.lean` (`avg_abs_sum_acceptWithAt_sub_le`) at each
`(H, ψ)` gives

- `abs_sum_acceptWithAt_hyb_succ_le_mixB`: for a fixed base oracle `H`, summed over `g` and
  averaged over the coins, the hybrids `e` and `e + 1` differ by at most
  `|Y₁^X| (√(ε W) + ε W / 2)` with `W = n q + C₀.q e`;
- `abs_sum_acceptWithAt_hyb_succ_le`: averaged over the uniform oracle and the coins, they differ
  by at most `√(ε W) + ε W / 2`.

This is one hybrid step of GHHM21 (Grilo, Hövelmanns, Hülsing, Majenz, "Tight adaptive
reprogramming in the QROM", ASIACRYPT 2021) Theorem 6.
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

/-! ### Mixed oracles -/

section Split

variable {X Y Y₁ Y₂ : Type*} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
  (sp : Y ≃+ Y₁ × Y₂) (B : Set X) [DecidablePred (· ∈ B)]

/-- Reprogramming a mixed oracle on `S ⊆ B` to `z` mixes in `g` set to `z` on `S`. -/
theorem reprogBase_mixB [DecidableEq X] {S : Finset X} (hS : (S : Set X) ⊆ B) (H : X → Y) (g z : X → Y₁) :
    reprogBase sp S z (mixB sp B H g) = mixB sp B H (Junta.setOn S g z) := by
  funext x
  by_cases hx : x ∈ S
  · have hB : x ∈ B := hS hx
    simp [reprogBase, mixB, Junta.setOn, hx, hB]
  · by_cases hB : x ∈ B <;> simp [reprogBase, mixB, Junta.setOn, hx, hB]

/-- A mixed oracle is the base oracle off `B`. -/
theorem mixB_of_notMem (H : X → Y) (g : X → Y₁) {x : X} (hx : x ∉ B) : mixB sp B H g x = H x := by
  simp [mixB, hx]

/-- A mixed oracle has the second components of the base oracle. -/
theorem snd_sp_mixB (H : X → Y) (g : X → Y₁) (x : X) :
    (sp (mixB sp B H g x)).2 = (sp (H x)).2 := by
  by_cases hx : x ∈ B <;> simp [mixB, hx]

/-- A mixed oracle reads `g` pointwise. -/
theorem readsPointwise_mixB [Fintype X] [DecidableEq X] [Fintype Y₁] [Fintype Y] [DecidableEq Y] (H : X → Y) :
    Junta.ReadsPointwise fun g : X → Y₁ => mixB sp B H g := by
  intro a
  by_cases ha : a ∈ B
  · exact Or.inl ⟨a, fun g g' h => by simp [mixB, ha, h]⟩
  · exact Or.inr fun g g' => by simp [mixB, ha]

/-- **The exchange of `g` and the first components of `H` on `B`**: `(H, g)` goes to the mixed
oracle `mixB H g` and the first components of `H` on `B` (with `g` off `B`). -/
def mixSwap (p : (X → Y) × (X → Y₁)) : (X → Y) × (X → Y₁) :=
  (mixB sp B p.1 p.2, fun x => if x ∈ B then (sp (p.1 x)).1 else p.2 x)

/-- The exchange `mixSwap` is an involution. -/
theorem mixSwap_involutive : Function.Involutive (mixSwap sp B) := by
  rintro ⟨H, g⟩
  simp only [mixSwap, Prod.mk.injEq]
  constructor <;> funext x <;> by_cases hx : x ∈ B <;> simp [mixB, hx]

end Split

/-! ### Reweighting sums -/

/-- **Reweighting along an involution** `F` of `α × β` whose weights `w a * ρ b` it preserves:
averaging `f` over the first component of `F (a, b)` with `b ← ρ` leaves the `w`-sum of `f`. -/
theorem sum_mul_sum_involutive {α β : Type*} [Fintype α] [Fintype β] (w : α → ℝ) (ρ : β → ℝ)
    (F : α × β → α × β) (hF : Function.Involutive F)
    (hw : ∀ p, w p.1 * ρ p.2 = w (F p).1 * ρ (F p).2) (hρ : ∑ b, ρ b = 1) (f : α → ℝ) :
    ∑ a, w a * ∑ b, ρ b * f (F (a, b)).1 = ∑ a, w a * f a := by
  calc ∑ a, w a * ∑ b, ρ b * f (F (a, b)).1 = ∑ p : α × β, w p.1 * ρ p.2 * f (F p).1 := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ p : α × β, w (F p).1 * ρ (F p).2 * f (F p).1 :=
        Finset.sum_congr rfl fun p _ => by rw [hw]
    _ = ∑ p : α × β, w p.1 * ρ p.2 * f p.1 :=
        Equiv.sum_comp (Function.Involutive.toPerm F hF) (fun p => w p.1 * ρ p.2 * f p.1)
    _ = ∑ a, w a * f a := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => ?_
        have h : ∀ b, w a * ρ b * f a = w a * f a * ρ b := fun b => by ring
        simp only [h, ← Finset.mul_sum, hρ, mul_one]

/-- The product of a function over a family with one coordinate updated. -/
theorem prod_update_mul {ι β : Type*} [Fintype ι] [DecidableEq ι] (p : β → ℝ) (c : ι → β)
    (i : ι) (y : β) : (∏ j, p (Function.update c i y j)) * p (c i) = (∏ j, p (c j)) * p y := by
  have h1 : ∏ j, p (Function.update c i y j) = p y * ∏ j ∈ ({i}ᶜ : Finset ι), p (c j) := by
    rw [Fintype.prod_eq_mul_prod_compl i]
    simp only [Function.update_self]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by
      rw [Function.update_of_ne (by simpa using hj)]
  have h2 : ∏ j, p (c j) = p (c i) * ∏ j ∈ ({i}ᶜ : Finset ι), p (c j) :=
    Fintype.prod_eq_mul_prod_compl i _
  rw [h1, h2]
  ring

/-- A weighted average with nonnegative weights summing to one is bounded by a bound on the
absolute values. -/
theorem abs_sum_mul_le {κ : Type*} [Fintype κ] (w f : κ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (h1 : ∑ i, w i = 1) {b : ℝ} (hf : ∀ i, |f i| ≤ b) : |∑ i, w i * f i| ≤ b := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ i, |w i * f i| ≤ ∑ i, w i * b := Finset.sum_le_sum fun i _ => by
        rw [abs_mul, abs_of_nonneg (hw i)]
        exact mul_le_mul_of_nonneg_left (hf i) (hw i)
    _ = b := by rw [← Finset.sum_mul, h1, one_mul]

/-! ### Challengers that read the history through its requests -/

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

omit [Fintype X] [Fintype Y] [Nonempty Y] in
/-- **Two challengers with the same oracle in force after `L` and the same oracle updates from
request `L.length` on have the same oracle in force after every extension of `L`.** -/
theorem oracleByReq_append_congr {C C' : Challenger X Y Req Resp} (hQ : C.Q = C'.Q)
    {c : C.Coins} {c' : C'.Coins} {H H' : X → Y} (L : List Req)
    (h0 : C.oracleByReq c H L = C'.oracleByReq c' H' L)
    (hstep : ∀ rs req (O : X → Y), L.length ≤ rs.length → rs.length < C.Q →
      O.reprogram ((C.respond c (histOf rs) req).run O).assignments =
        O.reprogram ((C'.respond c' (histOf rs) req).run O).assignments)
    (rs : List Req) : C.oracleByReq c H (L ++ rs) = C'.oracleByReq c' H' (L ++ rs) := by
  induction rs using List.reverseRecOn with
  | nil => simpa using h0
  | append_singleton rs r ih =>
    rw [← List.append_assoc, oracleByReq_append_singleton (C := C),
      oracleByReq_append_singleton (C := C'), ih, ← hQ]
    split_ifs with h
    · exact hstep _ _ _ (by simp) h
    · rfl

/-- The canonical history has one entry per request. -/
theorem length_histOf (rs : List Req) : (histOf (Resp := Resp) rs).length = rs.length := by
  simp [histOf]

end Challenger

/-! ### The hybrids -/

namespace Challenger.RevealedPair

variable {X Y Y₁ Y₂ Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
  {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ} {C₀ C₁ : Challenger X Y Req Resp}
  (P : RevealedPair sp B ε C₀ C₁)

omit [Fintype Y] [Nonempty Y] in
/-- Before request `e'`, the hybrid `e'` replies as `C₀`. -/
theorem hyb_respond_of_lt {e' : ℕ} (ψ : P.HCoins) {rs : List Req} (h : rs.length < e')
    (req : Req) :
    (P.hyb e').respond ψ (histOf rs) req = C₀.respond (P.enc₀ ψ.2) (histOf rs) req := by
  simp only [hyb, length_histOf, ite_eq_left h]

omit [Fintype Y] [Nonempty Y] in
/-- From request `e'` on, the hybrid `e'` replies as `C₁`. -/
theorem hyb_respond_of_le {e' : ℕ} (ψ : P.HCoins) {rs : List Req} (h : e' ≤ rs.length)
    (req : Req) :
    (P.hyb e').respond ψ (histOf rs) req = C₁.respond (P.enc₁ ψ) (histOf rs) req := by
  simp only [hyb, length_histOf, ite_eq_right (not_lt.mpr h)]

omit [Fintype Y] [Nonempty Y] [DecidableEq Y₁] [Nonempty Y₁] in
/-- `reprog` at the canonical history. -/
theorem reprog_histOf (Z : Fin C₀.Q → X → Y₁) (ω : P.Ω₀ × (Fin C₀.Q → P.Cn)) (rs : List Req)
    (req : Req) (O : X → Y) (h : rs.length < C₀.Q) :
    ((C₁.respond (P.enc₁ (Z, ω)) (histOf rs) req).run O).response =
        ((C₀.respond (P.enc₀ ω) (histOf rs) req).run
          (reprogBase sp (P.pts ω.1 ω.2 rs req O) (Z ⟨rs.length, h⟩) O)).response ∧
      O.reprogram ((C₁.respond (P.enc₁ (Z, ω)) (histOf rs) req).run O).assignments =
        reprogBase sp (P.pts ω.1 ω.2 rs req O) (Z ⟨rs.length, h⟩) O := by
  have h' : (histOf (Resp := Resp) rs).length < C₀.Q := by rwa [length_histOf]
  have hf : (⟨(histOf (Resp := Resp) rs).length, h'⟩ : Fin C₀.Q) = ⟨rs.length, h⟩ :=
    Fin.ext (length_histOf rs)
  have := P.reprog Z ω (histOf rs) req O h'
  rwa [map_request_histOf, hf] at this

omit [Fintype Y] [Nonempty Y] in
/-- **A step of the hybrid `e'` from request `e'` on**: the reply of `C₀` at the oracle
reprogrammed on the points, which becomes the oracle in force. -/
theorem hyb_step_of_le {e' : ℕ} (Z : Fin C₀.Q → X → Y₁) (ω : P.Ω₀ × (Fin C₀.Q → P.Cn))
    {rs : List Req} (h : e' ≤ rs.length) (hQ : rs.length < C₀.Q) (req : Req) (O : X → Y) :
    (((P.hyb e').respond (Z, ω) (histOf rs) req).run O).response =
        ((C₀.respond (P.enc₀ ω) (histOf rs) req).run
          (reprogBase sp (P.pts ω.1 ω.2 rs req O) (Z ⟨rs.length, hQ⟩) O)).response ∧
      O.reprogram (((P.hyb e').respond (Z, ω) (histOf rs) req).run O).assignments =
        reprogBase sp (P.pts ω.1 ω.2 rs req O) (Z ⟨rs.length, hQ⟩) O := by
  rw [P.hyb_respond_of_le _ h]
  exact P.reprog_histOf Z ω rs req O hQ

omit [Fintype Y] [Nonempty Y] in
/-- **Two hybrid steps that agree**: both before their reprogramming request, or both after it
with the same fresh value at this request. -/
theorem hyb_step_congr {e₁ e₂ : ℕ} (Z₁ Z₂ : Fin C₀.Q → X → Y₁) (ω : P.Ω₀ × (Fin C₀.Q → P.Cn))
    {rs : List Req} (hQ : rs.length < C₀.Q) (req : Req) (O : X → Y)
    (h : (rs.length < e₁ ∧ rs.length < e₂) ∨
      (e₁ ≤ rs.length ∧ e₂ ≤ rs.length ∧ Z₁ ⟨rs.length, hQ⟩ = Z₂ ⟨rs.length, hQ⟩)) :
    (((P.hyb e₁).respond (Z₁, ω) (histOf rs) req).run O).response =
        (((P.hyb e₂).respond (Z₂, ω) (histOf rs) req).run O).response ∧
      O.reprogram (((P.hyb e₁).respond (Z₁, ω) (histOf rs) req).run O).assignments =
        O.reprogram (((P.hyb e₂).respond (Z₂, ω) (histOf rs) req).run O).assignments := by
  rcases h with ⟨h₁, h₂⟩ | ⟨h₁, h₂, hZ⟩
  · rw [P.hyb_respond_of_lt _ h₁, P.hyb_respond_of_lt _ h₂]
    exact ⟨rfl, rfl⟩
  · obtain ⟨a₁, b₁⟩ := P.hyb_step_of_le Z₁ ω h₁ hQ req O
    obtain ⟨a₂, b₂⟩ := P.hyb_step_of_le Z₂ ω h₂ hQ req O
    rw [a₁, a₂, b₁, b₂, hZ]
    exact ⟨rfl, rfl⟩

omit [Fintype Y] [Nonempty Y] in
/-- **Before request `e'`, the hybrid `e'` keeps the oracle** (`C₀` assigns nothing). -/
theorem hyb_oracleByReq_of_le {e' : ℕ} (ψ : P.HCoins) (O : X → Y) {rs : List Req}
    (h : rs.length ≤ e') : (P.hyb e').oracleByReq ψ O rs = O := by
  induction rs using List.reverseRecOn with
  | nil => rfl
  | append_singleton rs r ih =>
    rw [List.length_append, List.length_singleton] at h
    rw [oracleByReq_append_singleton (C := P.hyb e') ψ, ih (by omega),
      P.hyb_respond_of_lt ψ (by omega), P.plain]
    split_ifs <;> rfl

omit [Fintype Y] [Nonempty Y] in
/-- The oracle in force of a hybrid after one more request numbered below `Q`. -/
theorem hyb_oracleByReq_snoc (e' : ℕ) (ψ : P.HCoins) (O : X → Y) (rs : List Req) (req : Req)
    (hQ : rs.length < C₀.Q) :
    (P.hyb e').oracleByReq ψ O (rs ++ [req]) = ((P.hyb e').oracleByReq ψ O rs).reprogram
      (((P.hyb e').respond ψ (histOf rs) req).run ((P.hyb e').oracleByReq ψ O rs)).assignments := by
  rw [oracleByReq_append_singleton (C := P.hyb e') ψ, ite_eq_left (show rs.length < (P.hyb e').Q from hQ)]

/-- The oracle in force of a hybrid in the pure game. -/
theorem hyb_oracleIn (e' : ℕ) (O : X → Y) (ψ : P.HCoins) (rs : List Req) :
    (OracleState.toOracle ((P.hyb e').toPureEnv.oracleIn (O, ψ) rs) : X → Y) =
      (P.hyb e').oracleByReq ψ O rs :=
  ((P.byRequests_hyb e').toPureEnv O ψ rs).1

/-- The answers of a hybrid in the pure game. -/
theorem hyb_answerAfter (e' : ℕ) (O : X → Y) (ψ : P.HCoins) (rs : List Req) (req : Req) :
    (P.hyb e').toPureEnv.answerAfter (O, ψ) rs req = if rs.length < C₀.Q then
      (((P.hyb e').respond ψ (histOf rs) req).run ((P.hyb e').oracleByReq ψ O rs)).response
      else none :=
  ((P.byRequests_hyb e').toPureEnv O ψ rs).2 req

/-- **Two hybrids with the same oracle in force after `L` and agreeing steps from request
`L.length` on have the same oracles in force and answers after every extension of `L`.** -/
theorem hyb_agree_from {e₁ e₂ : ℕ} {ψ₁ ψ₂ : P.HCoins} {O₁ O₂ : X → Y} (L : List Req)
    (h0 : (P.hyb e₁).oracleByReq ψ₁ O₁ L = (P.hyb e₂).oracleByReq ψ₂ O₂ L)
    (hstep : ∀ rs req (O : X → Y), L.length ≤ rs.length → rs.length < C₀.Q →
      (((P.hyb e₁).respond ψ₁ (histOf rs) req).run O).response =
          (((P.hyb e₂).respond ψ₂ (histOf rs) req).run O).response ∧
        O.reprogram (((P.hyb e₁).respond ψ₁ (histOf rs) req).run O).assignments =
          O.reprogram (((P.hyb e₂).respond ψ₂ (histOf rs) req).run O).assignments)
    (rs : List Req) :
    (P.hyb e₁).oracleByReq ψ₁ O₁ (L ++ rs) = (P.hyb e₂).oracleByReq ψ₂ O₂ (L ++ rs) ∧
      ∀ req, (P.hyb e₁).toPureEnv.answerAfter (O₁, ψ₁) (L ++ rs) req =
        (P.hyb e₂).toPureEnv.answerAfter (O₂, ψ₂) (L ++ rs) req := by
  have ho := oracleByReq_append_congr (C := P.hyb e₁) (C' := P.hyb e₂) rfl L h0
    (fun rs req O h₁ h₂ => (hstep rs req O h₁ h₂).2) rs
  refine ⟨ho, fun req => ?_⟩
  rw [hyb_answerAfter, hyb_answerAfter, ho]
  split_ifs with hQ
  · exact (hstep _ _ _ (by simp) hQ).1
  · rfl

omit [Fintype Y] [Nonempty Y] [DecidableEq Y₁] [Nonempty Y₁] in
/-- The points do not read the mixed part of the oracle. -/
theorem pts_mixB [DecidablePred (· ∈ B)] (ω₀ : P.Ω₀) (c : Fin C₀.Q → P.Cn) (rs : List Req)
    (req : Req) (H : X → Y) (g : X → Y₁) :
    P.pts ω₀ c rs req (mixB sp B H g) = P.pts ω₀ c rs req H :=
  P.pts_reads _ _ _ _ _ _ (fun _ hx => mixB_of_notMem sp B H g hx) (fun x => snd_sp_mixB sp B H g x)

omit [Fintype Y] [Nonempty Y] [DecidableEq Y₁] [Nonempty Y₁] in
/-- **The oracle after the reprogramming request** `e` of a mixed oracle with the fresh value
`z` at `e`. -/
theorem reprogBase_event [DecidablePred (· ∈ B)] {e : ℕ} (he : e < C₀.Q)
    (Z : Fin C₀.Q → X → Y₁) (ω : P.Ω₀ × (Fin C₀.Q → P.Cn)) {rs : List Req} (h : rs.length = e)
    (hQ : rs.length < C₀.Q) (req : Req) (H : X → Y) (g z : X → Y₁) :
    reprogBase sp (P.pts ω.1 ω.2 rs req (mixB sp B H g))
        (Function.update Z ⟨e, he⟩ z ⟨rs.length, hQ⟩) (mixB sp B H g) =
      mixB sp B H (Junta.setOn (P.pts ω.1 ω.2 rs req H) g z) := by
  have hf : (⟨rs.length, hQ⟩ : Fin C₀.Q) = ⟨e, he⟩ := Fin.ext h
  rw [hf, Function.update_self, pts_mixB, reprogBase_mixB sp B (P.pts_subset _ _ _ _ _)]

omit [Fintype Y] [Nonempty Y] [DecidableEq Y₁] [Nonempty Y₁] in
/-- The law of the coins of the hybrids, as a real weight. -/
theorem hLaw_toReal (Z : Fin C₀.Q → X → Y₁) (ω₀ : P.Ω₀) (c : Fin C₀.Q → P.Cn) :
    (P.hLaw (Z, (ω₀, c))).toReal = (Fintype.card (Fin C₀.Q → X → Y₁) : ℝ)⁻¹ *
      ((P.ν ω₀).toReal * ∏ i, (P.ζ (c i)).toReal) := by
  rw [hLaw, prodLaw_apply, prodLaw_apply, PMF.uniformOfFintype_apply, PMF.pi_apply,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_prod]

omit [Fintype Y] [Nonempty Y] [DecidableEq Y₁] in
/-- **The fresh value of one request is uniform and independent** under the law of the coins. -/
theorem sum_hLaw_update_Z (i : Fin C₀.Q) (f : P.HCoins → ℝ) :
    ∑ ψ, (P.hLaw ψ).toReal * ∑ z : X → Y₁, (Fintype.card (X → Y₁) : ℝ)⁻¹ *
        f (Function.update ψ.1 i z, ψ.2) = ∑ ψ, (P.hLaw ψ).toReal * f ψ :=
  sum_mul_sum_involutive (fun ψ => (P.hLaw ψ).toReal) (fun _ => (Fintype.card (X → Y₁) : ℝ)⁻¹)
    (fun p => ((Function.update p.1.1 i p.2, p.1.2), p.1.1 i))
    (by rintro ⟨⟨Z, ω⟩, z⟩; simp)
    (by rintro ⟨⟨Z, ω₀, c⟩, z⟩; dsimp only; rw [hLaw_toReal, hLaw_toReal])
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]) f

omit [Fintype Y] [Nonempty Y] [DecidableEq Y₁] [Nonempty Y₁] in
/-- **The fresh coins of one request are independent** under the law of the coins. -/
theorem sum_hLaw_update_c (i : Fin C₀.Q) (f : P.HCoins → ℝ) :
    ∑ ψ, (P.hLaw ψ).toReal * ∑ c', (P.ζ c').toReal *
        f (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c')) = ∑ ψ, (P.hLaw ψ).toReal * f ψ :=
  sum_mul_sum_involutive (fun ψ => (P.hLaw ψ).toReal) (fun c' => (P.ζ c').toReal)
    (fun p => ((p.1.1, (p.1.2.1, Function.update p.1.2.2 i p.2)), p.1.2.2 i))
    (by rintro ⟨⟨Z, ω₀, c⟩, c'⟩; simp)
    (by
      rintro ⟨⟨Z, ω₀, c⟩, c'⟩
      dsimp only
      rw [hLaw_toReal, hLaw_toReal]
      have := prod_update_mul (fun y => (P.ζ y).toReal) c i c'
      linear_combination (-((Fintype.card (Fin C₀.Q → X → Y₁) : ℝ)⁻¹ * (P.ν ω₀).toReal)) * this)
    (PMF.sum_toReal P.ζ) f

/-! ### The two hybrids as environments on split tapes -/

variable [DecidablePred (· ∈ B)]

/-- **The tape map of hybrid step `e`**: the tape `((H, (Z, ω)), (g, z))` gives the oracle
`mixB H g` and the fresh values `Z` with `z` at `e`. -/
noncomputable def hybTape {e : ℕ} (he : e < C₀.Q)
    (p : ((X → Y) × P.HCoins) × ((X → Y₁) × (X → Y₁))) : (X → Y) × P.HCoins :=
  (mixB sp B p.1.1 p.2.1, (Function.update p.1.2.1 ⟨e, he⟩ p.2.2, p.1.2.2))

/-- The points of request `e` at `θ = (H, (Z, (ω₀, c)))`. -/
def hybPts (θ : (X → Y) × P.HCoins) (rs : List Req) (req : Req) : Finset X :=
  P.pts θ.2.2.1 θ.2.2.2 rs req θ.1

/-- **The hybrid `e'` on split tapes** (through `hybTape`). -/
noncomputable def hybEnv (e' : ℕ) {e : ℕ} (he : e < C₀.Q)
    (μ : PMF (((X → Y) × P.HCoins) × ((X → Y₁) × (X → Y₁)))) :
    Env (((X → Y) × P.HCoins) × ((X → Y₁) × (X → Y₁))) Req Resp X Y C₀.Q
      (ChallengerState X Y Req Resp) :=
  (P.hyb e').toPureEnv.comap μ (P.hybTape he)

variable {e : ℕ} (he : e < C₀.Q) (μ : PMF (((X → Y) × P.HCoins) × ((X → Y₁) × (X → Y₁))))

theorem hybEnv_oracleIn (e' : ℕ) (H : X → Y) (Z : Fin C₀.Q → X → Y₁)
    (ω : P.Ω₀ × (Fin C₀.Q → P.Cn)) (g z : X → Y₁) (rs : List Req) :
    (OracleState.toOracle ((P.hybEnv e' he μ).oracleIn ((H, (Z, ω)), (g, z)) rs) : X → Y) =
      (P.hyb e').oracleByReq (Function.update Z ⟨e, he⟩ z, ω) (mixB sp B H g) rs := by
  exact P.hyb_oracleIn e' _ _ rs

theorem hybEnv_answerAfter_eq (e' : ℕ) (H : X → Y) (Z : Fin C₀.Q → X → Y₁)
    (ω : P.Ω₀ × (Fin C₀.Q → P.Cn)) (g z : X → Y₁) (rs : List Req) (req : Req) :
    (P.hybEnv e' he μ).answerAfter ((H, (Z, ω)), (g, z)) rs req =
      (P.hyb e').toPureEnv.answerAfter (mixB sp B H g, (Function.update Z ⟨e, he⟩ z, ω)) rs req :=
  rfl

theorem hybEnv_answerAfter (e' : ℕ) (H : X → Y) (Z : Fin C₀.Q → X → Y₁)
    (ω : P.Ω₀ × (Fin C₀.Q → P.Cn)) (g z : X → Y₁) (rs : List Req) (req : Req) :
    (P.hybEnv e' he μ).answerAfter ((H, (Z, ω)), (g, z)) rs req = if rs.length < C₀.Q then
      (((P.hyb e').respond (Function.update Z ⟨e, he⟩ z, ω) (histOf rs) req).run
        ((P.hyb e').oracleByReq (Function.update Z ⟨e, he⟩ z, ω) (mixB sp B H g) rs)).response
      else none := by
  rw [hybEnv_answerAfter_eq]
  exact P.hyb_answerAfter e' _ _ rs req

/-- The hybrid `e + 1` does not read the fresh value at `e`: oracles in force. -/
theorem hybEnv_succ_free (H : X → Y) (Z : Fin C₀.Q → X → Y₁) (ω : P.Ω₀ × (Fin C₀.Q → P.Cn))
    (g z z' : X → Y₁) (rs : List Req) :
    (P.hyb (e + 1)).oracleByReq (Function.update Z ⟨e, he⟩ z, ω) (mixB sp B H g) rs =
        (P.hyb (e + 1)).oracleByReq (Function.update Z ⟨e, he⟩ z', ω) (mixB sp B H g) rs ∧
      ∀ req, (P.hyb (e + 1)).toPureEnv.answerAfter
          (mixB sp B H g, (Function.update Z ⟨e, he⟩ z, ω)) rs req =
        (P.hyb (e + 1)).toPureEnv.answerAfter
          (mixB sp B H g, (Function.update Z ⟨e, he⟩ z', ω)) rs req := by
  have := P.hyb_agree_from (e₁ := e + 1) (e₂ := e + 1)
    (ψ₁ := (Function.update Z ⟨e, he⟩ z, ω)) (ψ₂ := (Function.update Z ⟨e, he⟩ z', ω))
    (O₁ := mixB sp B H g) (O₂ := mixB sp B H g) [] rfl (fun rs req O _ hQ => by
      refine P.hyb_step_congr _ _ ω hQ req O ?_
      by_cases hk : rs.length < e + 1
      · exact Or.inl ⟨hk, hk⟩
      · have hne : (⟨rs.length, hQ⟩ : Fin C₀.Q) ≠ ⟨e, he⟩ := fun h => by
          have := congrArg Fin.val h
          simp only at this
          omega
        exact Or.inr ⟨by omega, by omega, by
          rw [Function.update_of_ne hne, Function.update_of_ne hne]⟩) rs
  simpa using this

/-- **After the reprogramming request** `e`, the hybrid `e` at `(g, z)` and the hybrid `e + 1` at
the exchanged tape have the same oracles in force and answers. -/
theorem hyb_post (H : X → Y) (Z : Fin C₀.Q → X → Y₁) (ω : P.Ω₀ × (Fin C₀.Q → P.Cn))
    (g z : X → Y₁) {rs : List Req} {req : Req} (h : rs.length = e) (rs' : List Req) :
    (P.hyb e).oracleByReq (Function.update Z ⟨e, he⟩ z, ω) (mixB sp B H g) (rs ++ [req] ++ rs') =
        (P.hyb (e + 1)).oracleByReq
          (Function.update Z ⟨e, he⟩ (Junta.setOn (P.pts ω.1 ω.2 rs req H) z g), ω)
          (mixB sp B H (Junta.setOn (P.pts ω.1 ω.2 rs req H) g z)) (rs ++ [req] ++ rs') ∧
      ∀ req', (P.hyb e).toPureEnv.answerAfter (mixB sp B H g, (Function.update Z ⟨e, he⟩ z, ω))
          (rs ++ [req] ++ rs') req' =
        (P.hyb (e + 1)).toPureEnv.answerAfter
          (mixB sp B H (Junta.setOn (P.pts ω.1 ω.2 rs req H) g z),
            (Function.update Z ⟨e, he⟩ (Junta.setOn (P.pts ω.1 ω.2 rs req H) z g), ω))
          (rs ++ [req] ++ rs') req' := by
  have hQ : rs.length < C₀.Q := by omega
  refine P.hyb_agree_from (rs ++ [req]) ?_ (fun rs₂ req₂ O hL hQ₂ => ?_) rs'
  · rw [P.hyb_oracleByReq_snoc e _ _ _ _ hQ, P.hyb_oracleByReq_snoc (e + 1) _ _ _ _ hQ,
      P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e by omega),
      P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega),
      (P.hyb_step_of_le _ ω (show e ≤ rs.length by omega) hQ req _).2,
      P.reprogBase_event he Z ω h hQ, P.hyb_respond_of_lt _ (show rs.length < e + 1 by omega),
      P.plain]
    rfl
  · simp only [List.length_append, List.length_singleton] at hL
    have hne : (⟨rs₂.length, hQ₂⟩ : Fin C₀.Q) ≠ ⟨e, he⟩ := fun h' => by
      have := congrArg Fin.val h'
      simp only at this
      omega
    refine P.hyb_step_congr _ _ ω hQ₂ req₂ O (Or.inr ⟨by omega, by omega, ?_⟩)
    rw [Function.update_of_ne hne, Function.update_of_ne hne]

/-- **Hybrid step `e` as a reprogramming at a revealed set** (`RevealedHyp`): the hybrid `e`
(`E₁`) and the hybrid `e + 1` (`E₀`) on split tapes. -/
theorem revealedHyp_hyb : RevealedHyp (P.hybEnv (e + 1) he μ) (P.hybEnv e he μ) e P.hybPts := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro ⟨H, Z, ω⟩ g z z' rs req h
    rw [hybEnv_answerAfter, hybEnv_answerAfter, ite_eq_left (show rs.length < C₀.Q by omega),
      ite_eq_left (show rs.length < C₀.Q by omega),
      P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e by omega),
      P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega),
      P.hyb_respond_of_lt _ h, P.hyb_respond_of_lt _ (show rs.length < e + 1 by omega)]
  · rintro ⟨H, Z, ω⟩ g z z' rs h
    rw [hybEnv_oracleIn, hybEnv_oracleIn, P.hyb_oracleByReq_of_le _ _ h,
      P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega)]
  · rintro ⟨H, Z, ω⟩ g z z' rs req
    exact (P.hybEnv_succ_free he H Z ω g z z' rs).2 req
  · rintro ⟨H, Z, ω⟩ g z z' rs
    rw [hybEnv_oracleIn, hybEnv_oracleIn]
    exact (P.hybEnv_succ_free he H Z ω g z z' rs).1
  · rintro ⟨H, Z, ω⟩ g z rs req h
    have hQ : rs.length < C₀.Q := by omega
    simp only [Junta.swapOn_apply]
    rw [hybEnv_answerAfter, hybEnv_answerAfter, ite_eq_left hQ, ite_eq_left hQ,
      P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e by omega),
      P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega),
      (P.hyb_step_of_le _ ω (show e ≤ rs.length by omega) hQ req _).1,
      P.reprogBase_event he Z ω h hQ, P.hyb_respond_of_lt _ (show rs.length < e + 1 by omega)]
    rfl
  · rintro ⟨H, Z, ω⟩ g z rs req rs' req' h
    simp only [Junta.swapOn_apply]
    rw [hybEnv_answerAfter_eq, hybEnv_answerAfter_eq,
      show rs ++ req :: rs' = (rs ++ [req]) ++ rs' by simp]
    exact (P.hyb_post he H Z ω g z h rs').2 req'
  · rintro ⟨H, Z, ω⟩ g z rs req rs' h
    simp only [Junta.swapOn_apply]
    rw [hybEnv_oracleIn, hybEnv_oracleIn, show rs ++ req :: rs' = (rs ++ [req]) ++ rs' by simp]
    exact (P.hyb_post he H Z ω g z h rs').1

end Challenger.RevealedPair

/-- **The uniform oracle is the uniform mixed oracle**: averaging over the first components on
`B` leaves the uniform average. -/
theorem sum_uniform_mixB {X Y Y₁ Y₂ : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
    [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [Nonempty Y₁] (sp : Y ≃+ Y₁ × Y₂)
    (B : Set X) [DecidablePred (· ∈ B)] (f : (X → Y) → ℝ) :
    ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * ∑ g : X → Y₁,
        (Fintype.card (X → Y₁) : ℝ)⁻¹ * f (mixB sp B H g) =
      ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * f H :=
  sum_mul_sum_involutive _ (fun _ => (Fintype.card (X → Y₁) : ℝ)⁻¹) (mixSwap sp B)
    (mixSwap_involutive sp B) (fun p => by simp [PMF.uniformOfFintype_apply])
    (by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)]) f

namespace Distinguisher

open Challenger Challenger.RevealedPair

variable {W X Y Y₁ Y₂ Req Resp : Type} [Fintype W] [Fintype X] [DecidableEq X] [Fintype Y]
  [Nonempty Y] [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] [Fintype Y₁] [DecidableEq Y₁]
  [Nonempty Y₁] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] {n m : ℕ}
  (D : Distinguisher W X Y Req Resp n m) {sp : Y ≃+ Y₁ × Y₂} {B : Set X} {ε : ℝ}
  {C₀ C₁ : Challenger X Y Req Resp} (P : C₀.RevealedPair sp B ε C₁)

open Classical in
/-- **One hybrid step at a fixed base oracle**: for the oracle `H` mixed with `g` on `B`, summed
over `g` and averaged over the coins, the hybrids `e` and `e + 1` differ by at most
`|Y₁^X| (√(ε W) + ε W / 2)` with `W = n q + C₀.q e`. -/
theorem abs_sum_acceptWithAt_hyb_succ_le_mixB [Nonempty X] [Nonempty Req] {q : ℕ}
    (bud : D.Budget q) {e : ℕ} (he : e < C₀.Q)
    (Pev : DReg W n X Y Req Resp → LogReg Req m → (X → Y) → Prop) (H : X → Y) :
    |∑ g : X → Y₁, ∑ ψ, (P.hLaw ψ).toReal *
        D.acceptWithAt (P.hyb e).toPureEnv Pev (mixB sp B H g, ψ) -
      ∑ g : X → Y₁, ∑ ψ, (P.hLaw ψ).toReal *
        D.acceptWithAt (P.hyb (e + 1)).toPureEnv Pev (mixB sp B H g, ψ)| ≤
      Fintype.card (X → Y₁) * (√(ε * (n * q + C₀.q * e)) + ε * (n * q + C₀.q * e) / 2) := by
  obtain ⟨ψ₀, -⟩ := P.hLaw.support_nonempty
  set μ : PMF (((X → Y) × P.HCoins) × ((X → Y₁) × (X → Y₁))) := PMF.pure ((H, ψ₀), (z₀, z₀))
  have hyp := P.revealedHyp_hyb he μ
  set N : ℝ := (Fintype.card (X → Y₁) : ℝ) with hNdef
  set K : ℝ := ε * (n * q + C₀.q * e) with hKdef
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  set i : Fin C₀.Q := ⟨e, he⟩ with hidef
  have hθ : ∀ ψ : P.HCoins, ∑ c', (P.ζ c').toReal *
      |∑ g, ∑ z, D.acceptWithAt (P.hybEnv e he μ) Pev
          ((H, (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c'))), (g, z)) -
        ∑ g, ∑ z, D.acceptWithAt (P.hybEnv (e + 1) he μ) Pev
          ((H, (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c'))), (g, z))| ≤
      N ^ 2 * (√K + K / 2) := by
    rintro ⟨Z, ω₀, c⟩
    refine D.avg_abs_sum_acceptWithAt_sub_le bud hyp (H, (Z, (ω₀, c)))
      (fun θ c' => (θ.1, (θ.2.1, (θ.2.2.1, Function.update θ.2.2.2 i c')))) P.ζ ?_ ?_ ?_ ?_ ?_ Pev
    · intro c₁ c₂ g rs req h
      dsimp only
      rw [hybEnv_answerAfter, hybEnv_answerAfter, ite_eq_left (show rs.length < C₀.Q by omega),
        ite_eq_left (show rs.length < C₀.Q by omega),
        P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega),
        P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega),
        P.hyb_respond_of_lt _ (show rs.length < e + 1 by omega),
        P.hyb_respond_of_lt _ (show rs.length < e + 1 by omega)]
      dsimp only
      rw [P.causal ω₀ _ (Function.update c i c₂)]
      intro i' hi
      rw [length_histOf] at hi
      have hne : i' ≠ i := fun h' => by
        rw [h', hidef] at hi
        simp only at hi
        omega
      rw [Function.update_of_ne hne, Function.update_of_ne hne]
    · intro c₁ c₂ g rs h
      dsimp only
      rw [hybEnv_oracleIn, hybEnv_oracleIn,
        P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega),
        P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega)]
    · intro c₁ rs h
      convert readsPointwise_mixB sp B H using 1
      funext g
      dsimp only
      rw [hybEnv_oracleIn, P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega)]
    · intro c₁ rs req a h
      have key : ∀ g, (P.hybEnv (e + 1) he μ).answerAfter
          ((H, (Z, (ω₀, Function.update c i c₁))), (g, z₀)) rs req =
          ((C₀.respond (P.enc₀ (ω₀, Function.update c i c₁)) (histOf rs) req).mapOutput
            Reply.response).run (mixB sp B H g) := fun g => by
        rw [hybEnv_answerAfter, ite_eq_left (show rs.length < C₀.Q by omega),
          P.hyb_oracleByReq_of_le _ _ (show rs.length ≤ e + 1 by omega),
          P.hyb_respond_of_lt _ (show rs.length < e + 1 by omega), OracleProg.run_mapOutput]
      dsimp only
      simp only [key]
      exact Junta.indicator_run_mem_degLE (readsPointwise_mixB sp B H) _
        (fun g => by rw [OracleProg.trace_mapOutput]; exact C₀.respond_queries _ _ _ _) a
    · intro rs req x h
      have hQ : rs.length < C₀.Q := by omega
      have := P.pts_le ω₀ c rs req H x hQ
      rw [show (⟨rs.length, hQ⟩ : Fin C₀.Q) = i from Fin.ext h] at this
      exact this
  -- The difference as a coin average.
  set Φ : (X → Y) × P.HCoins → ℝ := fun ω =>
    D.acceptWithAt (P.hyb e).toPureEnv Pev ω - D.acceptWithAt (P.hyb (e + 1)).toPureEnv Pev ω
    with hΦ
  set f : P.HCoins → ℝ := fun ψ => ∑ g : X → Y₁, Φ (mixB sp B H g, ψ) with hf
  set F : P.HCoins → ℝ := fun ψ => ∑ z : X → Y₁, N⁻¹ * f (Function.update ψ.1 i z, ψ.2) with hF
  have h1 : ∑ g : X → Y₁, ∑ ψ, (P.hLaw ψ).toReal *
        D.acceptWithAt (P.hyb e).toPureEnv Pev (mixB sp B H g, ψ) -
      ∑ g : X → Y₁, ∑ ψ, (P.hLaw ψ).toReal *
        D.acceptWithAt (P.hyb (e + 1)).toPureEnv Pev (mixB sp B H g, ψ) =
      ∑ ψ, (P.hLaw ψ).toReal * ∑ c', (P.ζ c').toReal *
        F (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c')) := by
    rw [P.sum_hLaw_update_c i F, hF]
    dsimp only
    rw [P.sum_hLaw_update_Z i f, hf, ← Finset.sum_sub_distrib]
    simp only [← Finset.sum_sub_distrib, ← mul_sub, hΦ]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    rfl
  rw [h1]
  refine abs_sum_mul_le _ _ (fun _ => ENNReal.toReal_nonneg) (PMF.sum_toReal P.hLaw) fun ψ => ?_
  have heq : ∀ c', F (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c')) = N⁻¹ *
      (∑ g, ∑ z, D.acceptWithAt (P.hybEnv e he μ) Pev
          ((H, (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c'))), (g, z)) -
        ∑ g, ∑ z, D.acceptWithAt (P.hybEnv (e + 1) he μ) Pev
          ((H, (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c'))), (g, z))) := fun c' => by
    simp only [hF, hf, hΦ]
    rw [← Finset.mul_sum, Finset.sum_comm, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_sub_distrib]
    rfl
  calc |∑ c', (P.ζ c').toReal * F (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c'))|
      ≤ ∑ c', |(P.ζ c').toReal * F (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c'))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ = N⁻¹ * ∑ c', (P.ζ c').toReal *
        |∑ g, ∑ z, D.acceptWithAt (P.hybEnv e he μ) Pev
            ((H, (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c'))), (g, z)) -
          ∑ g, ∑ z, D.acceptWithAt (P.hybEnv (e + 1) he μ) Pev
            ((H, (ψ.1, (ψ.2.1, Function.update ψ.2.2 i c'))), (g, z))| := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [heq, abs_mul, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg,
          abs_of_pos (inv_pos.mpr hN)]
        ring
    _ ≤ N⁻¹ * (N ^ 2 * (√K + K / 2)) := mul_le_mul_of_nonneg_left (hθ ψ) (inv_pos.mpr hN).le
    _ = N * (√K + K / 2) := by field_simp

open Classical in
/-- **One hybrid step**: the hybrids `e` and `e + 1` (which differ in whether request `e` is
reprogrammed), averaged over the uniform oracle and the coins, differ by at most
`√(ε W) + ε W / 2` with `W = n q + C₀.q e`, for a distinguisher with a budget of `q` query
slots. -/
theorem abs_sum_acceptWithAt_hyb_succ_le [Nonempty X] [Nonempty Req] {q : ℕ} (bud : D.Budget q)
    {e : ℕ} (he : e < C₀.Q) (Pev : DReg W n X Y Req Resp → LogReg Req m → (X → Y) → Prop) :
    |∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ∑ ψ, (P.hLaw ψ).toReal * D.acceptWithAt (P.hyb e).toPureEnv Pev (H, ψ) -
      ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ∑ ψ, (P.hLaw ψ).toReal * D.acceptWithAt (P.hyb (e + 1)).toPureEnv Pev (H, ψ)| ≤
      √(ε * (n * q + C₀.q * e)) + ε * (n * q + C₀.q * e) / 2 := by
  set N : ℝ := (Fintype.card (X → Y₁) : ℝ) with hNdef
  have hN : 0 < N := Nat.cast_pos.mpr Fintype.card_pos
  set T : (X → Y) → ℝ := fun H => ∑ ψ, (P.hLaw ψ).toReal *
    (D.acceptWithAt (P.hyb e).toPureEnv Pev (H, ψ) -
      D.acceptWithAt (P.hyb (e + 1)).toPureEnv Pev (H, ψ)) with hT
  have h1 : ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ∑ ψ, (P.hLaw ψ).toReal * D.acceptWithAt (P.hyb e).toPureEnv Pev (H, ψ) -
      ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal *
        ∑ ψ, (P.hLaw ψ).toReal * D.acceptWithAt (P.hyb (e + 1)).toPureEnv Pev (H, ψ) =
      ∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * ∑ g : X → Y₁, N⁻¹ * T (mixB sp B H g) := by
    rw [sum_uniform_mixB sp B T, hT, ← Finset.sum_sub_distrib]
    simp only [← mul_sub, ← Finset.sum_sub_distrib]
  rw [h1]
  refine abs_sum_mul_le _ _ (fun _ => ENNReal.toReal_nonneg)
    (PMF.sum_toReal (PMF.uniformOfFintype (X → Y))) fun H => ?_
  have h2 : ∑ g : X → Y₁, N⁻¹ * T (mixB sp B H g) = N⁻¹ *
      (∑ g : X → Y₁, ∑ ψ, (P.hLaw ψ).toReal *
          D.acceptWithAt (P.hyb e).toPureEnv Pev (mixB sp B H g, ψ) -
        ∑ g : X → Y₁, ∑ ψ, (P.hLaw ψ).toReal *
          D.acceptWithAt (P.hyb (e + 1)).toPureEnv Pev (mixB sp B H g, ψ)) := by
    rw [← Finset.mul_sum, hT, ← Finset.sum_sub_distrib]
    simp only [← mul_sub, ← Finset.sum_sub_distrib]
  rw [h2, abs_mul, abs_of_pos (inv_pos.mpr hN)]
  calc N⁻¹ * |_| ≤ N⁻¹ * (N * (√(ε * (n * q + C₀.q * e)) + ε * (n * q + C₀.q * e) / 2)) :=
        mul_le_mul_of_nonneg_left (D.abs_sum_acceptWithAt_hyb_succ_le_mixB P bud he Pev H)
          (inv_pos.mpr hN).le
    _ = _ := by field_simp

end Distinguisher

end GordieHowe.Quantum
