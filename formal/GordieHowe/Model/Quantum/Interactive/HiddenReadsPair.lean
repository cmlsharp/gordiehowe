-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.HiddenReads
public import GordieHowe.Model.Quantum.Interactive.RevealedPair

@[expose] public section

/-!
# Hidden points with the challenger's reads as queries, for two challengers

`Challenger.HiddenReadsPair C C' qC` relates two challengers that read the history through their
requests and draw their coins from shared coins `ω₀ ← ν` and fresh coins `c j ← ζ` per request:
their oracles in force differ only at hidden points of each request, and their responses differ
only when the response reads, at most `qC` points, meet a hidden point of an earlier request.
`Challenger.respAt` is the response of a challenger after a list of requests.

- `AdaptiveIAlg.advantage_outLaw_le_of_hiddenReadsPair`: for such a pair, the probabilities that
  an interactive adversary outputs `o`, averaged over the uniform oracle, differ by at most
  `2 √(q + Q') √((width q + qC Q) ∑ j, ε j)` with `q = budget + post`, `Q' = 0` if `qC = 0` and
  `Q` otherwise, and `ε j` bounding the probability over the fresh coins of request `j` that a
  guess from its response is a hidden point of it. The proof builds the pure environments of
  both challengers on the tapes `(H, (ω₀, c))` and applies
  `AdaptiveIAlg.advantage_outLaw_le_of_hiddenReads`.
- `Challenger.HiddenReadsPair.refl`: a challenger against itself, with no hidden points and no
  reads.

`Env.castQ` renames the request bound of an environment along an equality; it keeps the states
and answers (`Env.oracleIn_castQ`, `Env.answerAfter_castQ`).
-/

open Finset
open scoped BigOperators ENNReal

namespace GordieHowe.Quantum

namespace Challenger

variable {X Y Req Resp : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]

/-- **The response of a challenger to `req` after the requests `rs`**, at the coins `c` and the
base oracle `H`: its program at the canonical history, run at the oracle in force
(`oracleByReq`). -/
noncomputable def respAt (C : Challenger X Y Req Resp) (c : C.Coins) (H : X → Y) (rs : List Req)
    (req : Req) : Option Resp :=
  ((C.respond c (histOf rs) req).run (C.oracleByReq c H rs)).response

/-- **Two challengers whose oracles differ at hidden points of each request, whose responses
differ only through their reads at hidden points.** Both read the history through its requests
and draw their coins as `enc (ω₀, c)` and `enc' (ω₀, c)` with `(ω₀, c) ← ν ⊗ ζ^Q`, `c j` the fresh
coins of request number `j`. After the requests `rs`, at the base oracle `H`, their oracles in
force agree outside the hidden points `hidden H ω₀ c rs₀ req` of the requests of `rs`
(`oracle`); their responses to a request agree when its reads `reads H ω₀ c rs req`, at most `qC`
points, avoid the hidden points of the earlier requests (`answer`); and for `C` the coins of
request `j` reach the later responses, oracles in force (`agree`) and reads (`reads_agree`) only
through the response to request `j`. -/
structure HiddenReadsPair (C C' : Challenger X Y Req Resp) (qC : ℕ) where
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
  /-- The coins of `C`. -/
  enc : Ω₀ × (Fin C.Q → Cn) → C.Coins
  coins_eq : C.coins = (prodLaw ν (PMF.pi fun _ => ζ)).map enc
  /-- The coins of `C'`. -/
  enc' : Ω₀ × (Fin C.Q → Cn) → C'.Coins
  coins_eq' : C'.coins = (prodLaw ν (PMF.pi fun _ => ζ)).map enc'
  Q_eq : C'.Q = C.Q
  byRequests : C.RespondsByRequests
  byRequests' : C'.RespondsByRequests
  /-- The hidden points of request `req` after the requests `rs`. -/
  hidden : (X → Y) → Ω₀ → (Fin C.Q → Cn) → List Req → Req → Set X
  /-- The reads of the response to `req` after the requests `rs`. -/
  reads : (X → Y) → Ω₀ → (Fin C.Q → Cn) → List Req → Req → Finset X
  reads_card : ∀ H ω₀ c rs req, (reads H ω₀ c rs req).card ≤ qC
  oracle : ∀ H ω₀ c rs x, (∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length < C.Q →
      x ∉ hidden H ω₀ c rs₀ req) →
    C.oracleByReq (enc (ω₀, c)) H rs x = C'.oracleByReq (enc' (ω₀, c)) H rs x
  answer : ∀ H ω₀ c rs req, rs.length < C.Q →
    (∀ x ∈ reads H ω₀ c rs req, ∀ rs₀ req₀, rs₀ ++ [req₀] <+: rs → rs₀.length < C.Q →
      x ∉ hidden H ω₀ c rs₀ req₀) →
    C.respAt (enc (ω₀, c)) H rs req = C'.respAt (enc' (ω₀, c)) H rs req
  agree : ∀ (j : Fin C.Q) H ω₀ c a a' rs, (∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length = (j : ℕ) →
      C.respAt (enc (ω₀, Function.update c j a)) H rs₀ req =
        C.respAt (enc (ω₀, Function.update c j a')) H rs₀ req) →
    (∀ rs₀, rs₀ <+: rs → C.oracleByReq (enc (ω₀, Function.update c j a)) H rs₀ =
      C.oracleByReq (enc (ω₀, Function.update c j a')) H rs₀) ∧
    ∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length < C.Q →
      C.respAt (enc (ω₀, Function.update c j a)) H rs₀ req =
        C.respAt (enc (ω₀, Function.update c j a')) H rs₀ req
  reads_agree : ∀ (j : Fin C.Q) H ω₀ c a a' rs req, (j : ℕ) < rs.length →
    (∀ rs₀ req₀, rs₀ ++ [req₀] <+: rs → rs₀.length = (j : ℕ) →
      C.respAt (enc (ω₀, Function.update c j a)) H rs₀ req₀ =
        C.respAt (enc (ω₀, Function.update c j a')) H rs₀ req₀) →
    reads H ω₀ (Function.update c j a) rs req = reads H ω₀ (Function.update c j a') rs req

attribute [instance] HiddenReadsPair.instFintypeΩ₀ HiddenReadsPair.instDecEqΩ₀
  HiddenReadsPair.instFintypeCn HiddenReadsPair.instDecEqCn

end Challenger

namespace AdaptiveIAlg

/-- **An environment with its request bound renamed** along `Q = Q'`. -/
def _root_.GordieHowe.Quantum.Env.castQ {Ω Req A X' Y' : Type} {St : Type} {Q Q' : ℕ}
    (E : Env Ω Req A X' Y' Q St) (h : Q = Q') : Env Ω Req A X' Y' Q' St where
  μ := E.μ
  oracle₀ := E.oracle₀
  respond ω c := E.respond ω (Fin.cast h.symm c)

/-- Renaming the request bound keeps the states. -/
theorem _root_.GordieHowe.Quantum.Env.oracleIn_castQ {Ω Req A X' Y' : Type} {St : Type}
    {Q Q' : ℕ} (E : Env Ω Req A X' Y' Q St) (h : Q = Q') (ω : Ω) (rs : List Req) :
    (E.castQ h).oracleIn ω rs = E.oracleIn ω rs := by
  subst h
  rfl

/-- Renaming the request bound keeps the answers. -/
theorem _root_.GordieHowe.Quantum.Env.answerAfter_castQ {Ω Req A X' Y' : Type} {St : Type}
    {Q Q' : ℕ} (E : Env Ω Req A X' Y' Q St) (h : Q = Q') (ω : Ω) (rs : List Req) (req : Req) :
    (E.castQ h).answerAfter ω rs req = E.answerAfter ω rs req := by
  subst h
  rfl

variable {X Y Req Resp O : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [DecidableEq O] {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **Hidden points with the challenger's reads as queries, for two challengers, against an
interactive adversary**: for a `HiddenReadsPair` of challengers and `ε j` bounding the
probability, over the fresh coins of request `j`, that a guess computed from its response is a
hidden point of it, the probabilities that the adversary outputs `o`, averaged over the uniform
oracle, differ by at most `2 √(q + Q') √((width q + qC Q) ∑ j, ε j)` with `q = budget + post`
and `Q' = 0` if `qC = 0`, `Q` otherwise. -/
theorem advantage_outLaw_le_of_hiddenReadsPair [Nonempty Req] {C C' : Challenger X Y Req Resp}
    {qC : ℕ} (P : C.HiddenReadsPair C' qC) (ε : Fin C.Q → ℝ)
    (hfind : ∀ (j : Fin C.Q) H ω₀ c rs₀ req, rs₀.length = (j : ℕ) → ∀ g : Option Resp → X,
      (P.ζ.toOuterMeasure {a | g (C.respAt (P.enc (ω₀, Function.update c j a)) H rs₀ req) ∈
        P.hidden H ω₀ (Function.update c j a) rs₀ req}).toReal ≤ ε j)
    (o : O) :
    GordieHowe.advantage
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * ((A.compose C).outLaw H (some o)).toReal)
      (∑ H, (PMF.uniformOfFintype (X → Y) H).toReal * ((A.compose C').outLaw H (some o)).toReal) ≤
        2 * √((A.budget + A.post : ℕ) + if qC = 0 then 0 else C.Q) *
          √((A.width * (A.budget + A.post : ℕ) + qC * C.Q) * ∑ j, ε j) := by
  classical
  -- the tapes: the base oracle, the shared coins and the fresh coins
  let μ : PMF ((X → Y) × (P.Ω₀ × (Fin C.Q → P.Cn))) :=
    prodLaw (PMF.uniformOfFintype (X → Y)) (prodLaw P.ν (PMF.pi fun _ => P.ζ))
  let E := C.toPureEnv.comap μ (fun ω => (ω.1, P.enc ω.2))
  let E' := (C'.toPureEnv.castQ P.Q_eq).comap μ (fun ω => (ω.1, P.enc' ω.2))
  have hO : ∀ ω rs, (OracleState.toOracle (E.oracleIn ω rs) : X → Y) =
      C.oracleByReq (P.enc ω.2) ω.1 rs := fun ω rs => (P.byRequests.toPureEnv _ _ rs).1
  have hA : ∀ ω rs req, E.answerAfter ω rs req =
      if rs.length < C.Q then C.respAt (P.enc ω.2) ω.1 rs req else none :=
    fun ω rs req => (P.byRequests.toPureEnv _ _ rs).2 req
  have hO' : ∀ ω rs, (OracleState.toOracle (E'.oracleIn ω rs) : X → Y) =
      C'.oracleByReq (P.enc' ω.2) ω.1 rs := fun ω rs => by
    show (OracleState.toOracle ((C'.toPureEnv.castQ P.Q_eq).oracleIn _ rs) : X → Y) = _
    rw [Env.oracleIn_castQ]
    exact (P.byRequests'.toPureEnv _ _ rs).1
  have hA' : ∀ ω rs req, E'.answerAfter ω rs req =
      if rs.length < C.Q then C'.respAt (P.enc' ω.2) ω.1 rs req else none := fun ω rs req => by
    show (C'.toPureEnv.castQ P.Q_eq).answerAfter _ rs req = _
    rw [Env.answerAfter_castQ, (P.byRequests'.toPureEnv _ _ rs).2 req, P.Q_eq]
    rfl
  let res : Fin C.Q → (X → Y) × (P.Ω₀ × (Fin C.Q → P.Cn)) → P.Cn →
      (X → Y) × (P.Ω₀ × (Fin C.Q → P.Cn)) :=
    fun j ω a => (ω.1, (ω.2.1, Function.update ω.2.2 j a))
  -- the answers to the requests numbered `j` are the responses
  have hAj : ∀ (j : Fin C.Q) ω a rs₀ req, rs₀.length = (j : ℕ) → E.answerAfter (res j ω a) rs₀ req =
      C.respAt (P.enc (ω.2.1, Function.update ω.2.2 j a)) ω.1 rs₀ req := by
    intro j ω a rs₀ req h
    rw [hA]
    split_ifs with hq
    · rfl
    · exact absurd (h ▸ j.2) hq
  have hE : HiddenSideReads E E' P.ζ res (fun ω => P.hidden ω.1 ω.2.1 ω.2.2)
      (fun ω => P.reads ω.1 ω.2.1 ω.2.2) qC := {
    law := rfl,
    oracle := fun ω rs x hx => by
      rw [hO, hO']
      exact P.oracle _ _ _ _ _ hx,
    resample := fun j f => by
      show ∑ ω, (μ ω).toReal * f ω = ∑ ω, (μ ω).toReal * ∑ a, (P.ζ a).toReal * f (res j ω a)
      simp only [μ, Challenger.SaltFreshPair.sum_prodLaw]
      refine Finset.sum_congr rfl fun H _ => ?_
      congr 1
      refine Finset.sum_congr rfl fun ω₀ _ => ?_
      congr 1
      exact PMF.sum_toReal_pi_mul_eq_sum_update (fun _ => P.ζ) j (fun c => f (H, (ω₀, c)))
    agree j ω a a' rs h := by
      have h' : ∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length = (j : ℕ) →
          C.respAt (P.enc (ω.2.1, Function.update ω.2.2 j a)) ω.1 rs₀ req =
            C.respAt (P.enc (ω.2.1, Function.update ω.2.2 j a')) ω.1 rs₀ req :=
        fun rs₀ req hp hl => by rw [← hAj j ω a _ _ hl, ← hAj j ω a' _ _ hl]; exact h _ _ hp hl
      obtain ⟨h1, h2⟩ := P.agree j ω.1 ω.2.1 ω.2.2 a a' rs h'
      refine ⟨fun rs₀ hp => ?_, fun rs₀ req hp => ?_⟩
      · rw [hO, hO]
        exact h1 _ hp
      · rw [hA, hA]
        split_ifs with hq
        · exact h2 _ _ hp hq
        · rfl,
    reads_card := fun ω rs req => P.reads_card _ _ _ _ _,
    answer := fun ω rs req h => by
      rw [hA, hA']
      split_ifs with hq
      · exact P.answer _ _ _ _ _ hq h
      · rfl
    reads_agree j ω a a' rs req hj h := by
      refine P.reads_agree j ω.1 ω.2.1 ω.2.2 a a' rs req hj fun rs₀ req₀ hp hl => ?_
      rw [← hAj j ω a _ _ hl, ← hAj j ω a' _ _ hl]
      exact h _ _ hp hl }
  refine advantage_outLaw_le_of_hiddenReads A (μH := PMF.uniformOfFintype (X → Y)) hE ε
    (fun j ω rs₀ req hl g => ?_) o ?_ ?_
  · refine le_of_eq_of_le ?_ (hfind j ω.1 ω.2.1 ω.2.2 rs₀ req hl g)
    congr 2
    ext a
    rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hAj j ω a rs₀ req hl]
  · show _ = ∑ ω, (μ ω).toReal * (A.pureDil o).acceptProbAt E noPost ω
    simp only [E, Distinguisher.acceptProbAt_comap, μ, Challenger.SaltFreshPair.sum_prodLaw,
      P.coins_eq, PMF.sum_toReal_map_mul]
  · have hacc : ∀ ω, (A.pureDil o).acceptProbAt E' noPost ω =
        (A.pureDil o).acceptProbAt C'.toPureEnv noPost (ω.1, P.enc' ω.2) := fun ω => by
      have ha : ∀ rs req, E'.answerAfter ω rs req =
          C'.toPureEnv.answerAfter (ω.1, P.enc' ω.2) rs req :=
        fun rs req => Env.answerAfter_castQ C'.toPureEnv P.Q_eq _ _ _
      have ho : ∀ rs, E'.oracleIn ω rs = C'.toPureEnv.oracleIn (ω.1, P.enc' ω.2) rs :=
        fun rs => Env.oracleIn_castQ C'.toPureEnv P.Q_eq _ _
      exact (A.pureDil o).acceptProbAt_congr _ _ (fun lg k => by
        unfold Env.answer
        rw [show E'.answerAfter ω = C'.toPureEnv.answerAfter (ω.1, P.enc' ω.2) from
          funext fun rs => funext (ha rs)])
        (fun lg => by
        unfold Env.oracle
        rw [ho]) noPost
    show _ = ∑ ω, (μ ω).toReal * (A.pureDil o).acceptProbAt E' noPost ω
    simp only [hacc, μ, Challenger.SaltFreshPair.sum_prodLaw, P.coins_eq', PMF.sum_toReal_map_mul]


/-- **A trivial instance**: a challenger reading the history through its requests, against
itself, with no hidden points and no reads. -/
def _root_.GordieHowe.Quantum.Challenger.HiddenReadsPair.refl {C : Challenger X Y Req Resp}
    (hC : C.RespondsByRequests) {Ω₀ Cn : Type} [Fintype Ω₀] [DecidableEq Ω₀] [Fintype Cn]
    [DecidableEq Cn] (ν : PMF Ω₀) (ζ : PMF Cn) (enc : Ω₀ × (Fin C.Q → Cn) → C.Coins)
    (hcoins : C.coins = (prodLaw ν (PMF.pi fun _ => ζ)).map enc)
    (hag : ∀ (j : Fin C.Q) H ω₀ c a a' rs, (∀ rs₀ req, rs₀ ++ [req] <+: rs →
      rs₀.length = (j : ℕ) → C.respAt (enc (ω₀, Function.update c j a)) H rs₀ req =
        C.respAt (enc (ω₀, Function.update c j a')) H rs₀ req) →
      (∀ rs₀, rs₀ <+: rs → C.oracleByReq (enc (ω₀, Function.update c j a)) H rs₀ =
        C.oracleByReq (enc (ω₀, Function.update c j a')) H rs₀) ∧
      ∀ rs₀ req, rs₀ ++ [req] <+: rs → rs₀.length < C.Q →
        C.respAt (enc (ω₀, Function.update c j a)) H rs₀ req =
          C.respAt (enc (ω₀, Function.update c j a')) H rs₀ req) :
    C.HiddenReadsPair C 0 where
  Ω₀ := Ω₀
  Cn := Cn
  ν := ν
  ζ := ζ
  enc := enc
  coins_eq := hcoins
  enc' := enc
  coins_eq' := hcoins
  Q_eq := rfl
  byRequests := hC
  byRequests' := hC
  hidden _ _ _ _ _ := ∅
  reads _ _ _ _ _ := ∅
  reads_card _ _ _ _ _ := by simp
  oracle _ _ _ _ _ _ := rfl
  answer _ _ _ _ _ _ _ := rfl
  agree := hag
  reads_agree _ _ _ _ _ _ _ _ _ _ := rfl

end AdaptiveIAlg

end GordieHowe.Quantum
