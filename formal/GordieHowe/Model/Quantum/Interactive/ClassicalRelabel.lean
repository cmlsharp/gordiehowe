-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.ClassicalSim

@[expose] public section

/-!
# Relabelling the requests and responses of a challenger

A challenger on requests `Req'` and responses `Resp'` is read through equivalences
`eq : Req ≃ Req'` and `er : Resp ≃ Resp'` as a challenger on `Req` and `Resp`; against its
classical game `classicalAt H`, a deterministic strategy wins an event of its output with the
probability of the relabelled strategy against the classical game of the original challenger.

- `Quantum.HistoryEntry.relabel`: a history entry with its request and response relabelled.
- `Quantum.Challenger.relabel`: the challenger `C'` read through `eq` and `er`.
- `Interaction.histRelabel`: a classical history with its moves and responses relabelled.
- `Interaction.histRelabel_symm_histRelabel`, `Interaction.histRelabel_histRelabel_symm`: the
  relabellings by `eq, er` and by their inverses are inverse.
- `Interaction.histRelabel_append_singleton`: relabelling a history appends the relabelled
  last round.
- `Interaction.histReqs_histRelabel`: the requests of a relabelled history are the relabelled
  requests.
- `Interaction.DetStrategy.next_toStrategy`, `Interaction.DetStrategy.out_toStrategy`: the
  laws of a deterministic strategy are point masses.
- `Interaction.DetStrategy.relabel`: a deterministic strategy played through the relabelling.
- `Quantum.Challenger.oracleIn_relabel`: the pure-environment state of `C'.relabel eq er` after
  `rs` has the base oracle and assignments of `C'` after `rs.map eq`, and its history relabelled
  is that of `C'`.
- `Quantum.Challenger.visReply_relabel`: the visible reply of `C'.relabel eq er` is that of `C'`
  at the relabelled requests and move, with the response mapped back.
- `Quantum.Challenger.input_classicalAt`, `Quantum.Challenger.reply_classicalAt`: the input and
  replies of `classicalAt`.
- `Quantum.Challenger.cont_relabel`: the continuation of the relabelled strategy against `C'` is
  that of the strategy against `C'.relabel eq er` from the history mapped back, with the history
  relabelled.
- `Quantum.Challenger.winProb_relabel_preimage`: the win probability of the relabelled strategy
  against `C'` for an event is that of the strategy against `C'.relabel eq er` for its preimage.
- `Quantum.Challenger.winProb_classicalAt_relabel`: for events of the output only, the two win
  probabilities are equal.
-/

namespace GordieHowe

namespace Quantum

/-- A history entry with its request relabelled by `eq` and its response by `er`. -/
def HistoryEntry.relabel {Req Req' Resp Resp' : Type} (eq : Req ≃ Req') (er : Resp ≃ Resp')
    (e : HistoryEntry Req Resp) : HistoryEntry Req' Resp' :=
  ⟨eq e.request, e.response.map er⟩

/-- **The challenger `C'` read through `eq` and `er`**: the same coins and query bound; a request
`r` after the history `hist` is answered by `C'` on `eq r` after the relabelled history, with the
response mapped back by `er.symm` and the same assignments. -/
def Challenger.relabel {X Y Req Req' Resp Resp' : Type} (C' : Challenger X Y Req' Resp')
    (eq : Req ≃ Req') (er : Resp ≃ Resp') : Challenger X Y Req Resp where
  Coins := C'.Coins
  coins := C'.coins
  Q := C'.Q
  q := C'.q
  respond ω hist r := (C'.respond ω (hist.map (HistoryEntry.relabel eq er)) (eq r)).mapOutput
    fun o => ⟨o.response.map er.symm, o.assignments⟩
  respond_queries ω hist r H := by
    rw [OracleProg.trace_mapOutput]
    exact C'.respond_queries _ _ _ _

end Quantum

namespace Interaction

variable {Req Req' Resp Resp' Ix : Type}

/-- A classical history with its moves relabelled by `eq` and the responses of its replies by
`er`. -/
def histRelabel (eq : Req ≃ Req') (er : Resp ≃ Resp') :
    Hist (Option Req) (Option Resp × Ix) → Hist (Option Req') (Option Resp' × Ix) :=
  List.map fun p => (p.1.map eq, (p.2.1.map er, p.2.2))

/-- Relabelling by `eq, er` and then by their inverses gives back the history. -/
theorem histRelabel_symm_histRelabel (eq : Req ≃ Req') (er : Resp ≃ Resp')
    (h : Hist (Option Req) (Option Resp × Ix)) :
    histRelabel eq.symm er.symm (histRelabel eq er h) = h := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    simp only [histRelabel, List.map_cons] at ih ⊢
    rw [ih]
    simp [Option.map_map, Function.comp_def]

/-- Relabelling by the inverses and then by `eq, er` gives back the history. -/
theorem histRelabel_histRelabel_symm (eq : Req ≃ Req') (er : Resp ≃ Resp')
    (h : Hist (Option Req') (Option Resp' × Ix)) :
    histRelabel eq er (histRelabel eq.symm er.symm h) = h :=
  histRelabel_symm_histRelabel eq.symm er.symm h

/-- Relabelling a history ending in the round `x` appends the relabelled `x`. -/
theorem histRelabel_append_singleton (eq : Req ≃ Req') (er : Resp ≃ Resp')
    (h : Hist (Option Req) (Option Resp × Ix)) (x : Option Req × (Option Resp × Ix)) :
    histRelabel eq er (h ++ [x]) = histRelabel eq er h ++ [(x.1.map eq, (x.2.1.map er, x.2.2))] :=
  by simp [histRelabel]

/-- The requests of a relabelled history are its requests relabelled by `eq`. -/
theorem histReqs_histRelabel (eq : Req ≃ Req') (er : Resp ≃ Resp')
    (h : Hist (Option Req) (Option Resp × Ix)) :
    Quantum.Env.histReqs (histRelabel eq er h) = (Quantum.Env.histReqs h).map eq := by
  induction h with
  | nil => rfl
  | cons x h ih =>
    obtain ⟨m, r⟩ := x
    simp only [histRelabel, Quantum.Env.histReqs, List.map_cons] at ih ⊢
    cases m <;> simp [ih]

/-- The move law of a deterministic strategy is the point mass at its move. -/
theorem DetStrategy.next_toStrategy {I M R O : Type} (s : DetStrategy I M R O) (i : I)
    (h : Hist M R) : s.toStrategy.next i h = PMF.pure (s.next i h) :=
  rfl

/-- The output law of a deterministic strategy is the point mass at its output. -/
theorem DetStrategy.out_toStrategy {I M R O : Type} (s : DetStrategy I M R O) (i : I)
    (h : Hist M R) : s.toStrategy.out i h = PMF.pure (s.out i h) :=
  rfl

/-- **A deterministic strategy played through the relabelling**: it maps the history back by
`eq.symm` and `er.symm`, plays the move of `s` relabelled by `eq`, and outputs the output of `s`
on the history mapped back. -/
def DetStrategy.relabel {I O : Type} (s : DetStrategy I (Option Req) (Option Resp × Ix) O)
    (eq : Req ≃ Req') (er : Resp ≃ Resp') : DetStrategy I (Option Req') (Option Resp' × Ix) O where
  next i h := (s.next i (histRelabel eq.symm er.symm h)).map eq
  out i h := s.out i (histRelabel eq.symm er.symm h)

end Interaction

namespace Quantum

namespace Challenger

variable {X Y Req Req' Resp Resp' : Type} [Fintype X] [DecidableEq X] [Fintype Y] [Nonempty Y]
  (C' : Challenger X Y Req' Resp') (eq : Req ≃ Req') (er : Resp ≃ Resp')

/-- **The state of the relabelled challenger after `rs`**: the base oracle and assignments of `C'`
after `rs.map eq`, and the history of `C'` after `rs.map eq` once relabelled. -/
theorem oracleIn_relabel (ω : (X → Y) × C'.Coins) (rs : List Req) :
    ((C'.relabel eq er).toPureEnv.oracleIn ω rs).base = (C'.toPureEnv.oracleIn ω (rs.map eq)).base ∧
    ((C'.relabel eq er).toPureEnv.oracleIn ω rs).hist.map (HistoryEntry.relabel eq er) =
      (C'.toPureEnv.oracleIn ω (rs.map eq)).hist ∧
    ((C'.relabel eq er).toPureEnv.oracleIn ω rs).ass =
      (C'.toPureEnv.oracleIn ω (rs.map eq)).ass := by
  induction rs using List.reverseRecOn with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | append_singleton rs r ih =>
    rw [List.map_append, List.map_singleton,
      Env.oracleIn_append_singleton (C'.relabel eq er).toPureEnv ω rs r,
      Env.oracleIn_append_singleton C'.toPureEnv ω (rs.map eq) (eq r)]
    obtain ⟨h1, h2, h3⟩ := ih
    generalize (C'.relabel eq er).toPureEnv.oracleIn ω rs = st at h1 h2 h3
    generalize C'.toPureEnv.oracleIn ω (rs.map eq) = st' at h1 h2 h3
    have hQ : (C'.relabel eq er).Q = C'.Q := rfl
    simp only [Env.update, hQ, List.length_map]
    split_ifs with hlt
    · simp only [Challenger.toPureEnv, Challenger.relabel, OracleProg.run_mapOutput, h1, h2, h3,
        List.map_append, List.map_singleton, HistoryEntry.relabel, Option.map_map,
        Function.comp_def, Equiv.apply_symm_apply, Option.map_id']
      refine ⟨?_, ?_, ?_⟩ <;> simp
    · exact ⟨h1, h2, h3⟩

/-- **The visible reply of the relabelled challenger** after the requests `rs` to the move `e` is
the visible reply of `C'` after `rs.map eq` to `e.map eq`, with the response mapped by
`er.symm`. -/
theorem visReply_relabel (ω : (X → Y) × C'.Coins) (rs : List Req) (e : Option Req) :
    (C'.relabel eq er).toPureEnv.visReply ω rs e =
      Prod.map (Option.map er.symm) id (C'.toPureEnv.visReply ω (rs.map eq) (e.map eq)) := by
  have hor : ∀ l : List Req,
      (OracleState.toOracle ((C'.relabel eq er).toPureEnv.oracleIn ω l) : X → Y) =
      (OracleState.toOracle (C'.toPureEnv.oracleIn ω (l.map eq)) : X → Y) := by
    intro l
    obtain ⟨h1, -, h3⟩ := C'.oracleIn_relabel eq er ω l
    change ((C'.relabel eq er).toPureEnv.oracleIn ω l).base.reprogram
        ((C'.relabel eq er).toPureEnv.oracleIn ω l).ass =
      (C'.toPureEnv.oracleIn ω (l.map eq)).base.reprogram (C'.toPureEnv.oracleIn ω (l.map eq)).ass
    rw [h1, h3]
  cases e with
  | none => simp only [Env.visReply, Option.map_none, Prod.map, Option.map_none, id, hor]
  | some r =>
    simp only [Env.visReply, Option.map_some, Prod.map, id]
    rw [hor, List.map_append, List.map_singleton]
    refine Prod.ext ?_ rfl
    simp only [Env.answerAfter, List.length_map]
    have hQ : (C'.relabel eq er).Q = C'.Q := rfl
    obtain ⟨h1, h2, h3⟩ := C'.oracleIn_relabel eq er ω rs
    split_ifs with hlt hlt' hlt'
    · generalize hst : (C'.relabel eq er).toPureEnv.oracleIn ω rs = st at h1 h2 h3
      change (((C'.relabel eq er).respond ω.2 st.hist r).run (st.base.reprogram st.ass)).response =
        _
      simp only [Challenger.relabel, OracleProg.run_mapOutput]
      rw [h1, h2, h3]
      rfl
    · exact absurd hlt (hQ ▸ hlt')
    · exact absurd (hQ ▸ hlt') hlt
    · rfl

/-- The input of `C.classicalAt H` is the oracle `H` with no assignments. -/
theorem input_classicalAt {Rq Rs : Type} (C : Challenger X Y Rq Rs) (H : X → Y) (c : C.Coins) :
    (C.classicalAt H).input c = H.reprogram [] :=
  rfl

/-- The reply of `C.classicalAt H` is the point mass at the visible reply of the pure game. -/
theorem reply_classicalAt {Rq Rs : Type} (C : Challenger X Y Rq Rs) (H : X → Y) (c : C.Coins)
    (h : Interaction.Hist (Option Rq) (Option Rs × (X → Y))) (e : Option Rq) :
    (C.classicalAt H).reply c h e = PMF.pure (C.toPureEnv.visReply (H, c) (Env.histReqs h) e) :=
  rfl

/-- **The continuation of the relabelled strategy** against `C'` from the history `h'` is the
continuation of `s` against the relabelled challenger from `h'` mapped back, with the final history
relabelled. -/
theorem cont_relabel {O : Type}
    (s : Interaction.DetStrategy (X → Y) (Option Req) (Option Resp × (X → Y)) O) (H : X → Y)
    (c : C'.Coins) (k : ℕ) (h' : Interaction.Hist (Option Req') (Option Resp' × (X → Y))) :
    Interaction.cont (s.relabel eq er).toStrategy (C'.classicalAt H) c h' k =
      (Interaction.cont s.toStrategy ((C'.relabel eq er).classicalAt H) c
        (Interaction.histRelabel eq.symm er.symm h') k).map
          (Prod.map (Interaction.histRelabel eq er) id) := by
  induction k generalizing h' with
  | zero =>
    simp only [Interaction.cont]
    simp only [Interaction.DetStrategy.out_toStrategy, PMF.pure_map]
    simp only [Prod.map, Interaction.histRelabel_histRelabel_symm, id]
    rfl
  | succ k ih =>
    simp only [Interaction.cont]
    simp only [Interaction.DetStrategy.next_toStrategy, PMF.pure_bind, reply_classicalAt,
      input_classicalAt]
    rw [reply_classicalAt (C'.relabel eq er) H c, input_classicalAt (C'.relabel eq er) H c,
      PMF.pure_bind, ih]
    congr 2
    rw [Interaction.histRelabel_append_singleton]
    congr 2
    simp only [Interaction.DetStrategy.relabel]
    refine Prod.ext (by simp [Option.map_map, Function.comp_def]) ?_
    refine (?_ : _ = _).trans (visReply_relabel C' eq er (H, c) _ _).symm
    rw [Interaction.histReqs_histRelabel, List.map_map]
    simp [Function.comp_def, Prod.map]

/-- **The win probability of the relabelled strategy** against `C'` for the event `W` is that of
`s` against the relabelled challenger for the preimage of `W` under relabelling the history. -/
theorem winProb_relabel_preimage {O : Type}
    (s : Interaction.DetStrategy (X → Y) (Option Req) (Option Resp × (X → Y)) O) (H : X → Y)
    (m : ℕ) (W : Set (Interaction.Hist (Option Req') (Option Resp' × (X → Y)) × O)) :
    Interaction.winProb (s.relabel eq er).toStrategy (C'.classicalAt H) m W =
      Interaction.winProb s.toStrategy ((C'.relabel eq er).classicalAt H) m
        (Prod.map (Interaction.histRelabel eq er) id ⁻¹' W) := by
  simp only [Interaction.winProb, Interaction.exper]
  have : (C'.classicalAt H).coins.bind (fun c =>
      Interaction.cont (s.relabel eq er).toStrategy (C'.classicalAt H) c [] m) =
      (((C'.relabel eq er).classicalAt H).coins.bind fun c =>
        Interaction.cont s.toStrategy ((C'.relabel eq er).classicalAt H) c [] m).map
          (Prod.map (Interaction.histRelabel eq er) id) := by
    rw [PMF.map_bind]
    exact congrArg _ (funext fun c => C'.cont_relabel eq er s H c m [])
  rw [this, PMF.toOuterMeasure_map_apply]

/-- **Relabelling preserves win probabilities**: against the challenger `C'` read through `eq`
and `er`, a deterministic strategy wins an event of its output with the probability of the
relabelled strategy against `C'`. -/
theorem winProb_classicalAt_relabel {O : Type}
    (s : Interaction.DetStrategy (X → Y) (Option Req) (Option Resp × (X → Y)) O) (H : X → Y)
    (m : ℕ) (W : Set O) :
    Interaction.winProb s.toStrategy ((C'.relabel eq er).classicalAt H) m {p | p.2 ∈ W} =
      Interaction.winProb (s.relabel eq er).toStrategy (C'.classicalAt H) m {p | p.2 ∈ W} := by
  rw [winProb_relabel_preimage]
  rfl

end Challenger

end Quantum

end GordieHowe
