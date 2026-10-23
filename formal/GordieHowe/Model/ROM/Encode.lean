-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.ROM.InteractiveNIZKLastProofQuery
public import GordieHowe.Model.NARG.Encoding

@[expose] public section

/-!
# Classical adversaries against an encoded oracle

An encoding `enc : NARG.OracleEncoding A B X Y` of an oracle `A → B` into an oracle `X → Y`
(`GordieHowe/Model/NARG/Encoding.lean`) maps a classical adversary against `A → B` to one against
`X → Y` that encodes its queries and decodes the answers (`IAlg.decode`). Against a uniform oracle
`H : X → Y`, the decoded oracle `enc.decode H` is uniform (`OracleEncoding.map_uniform_decode`), so
the adversary's acceptance probability against the encoded prover and simulator is its acceptance
probability against the prover and simulator themselves (`acceptProb_decode_realEnv`,
`acceptProb_decode_simEnv`). Zero knowledge at the encoded oracle therefore gives zero knowledge at
the oracle `A → B` (`GordieHowe.NARG.ROM.zeroKnowledge_of_encode`).
-/

namespace GordieHowe

open GordieHowe.IOP GordieHowe.QROM
open scoped ENNReal

namespace NARG.OracleEncoding

variable {A B X Y : Type} (enc : OracleEncoding A B X Y)

/-- **The decoded oracle of a uniform oracle is uniform**: the answers at the encoded queries of a
uniform `H : X → Y` are uniform and independent (the encoding is injective), and decoding them is a
bijection. -/
theorem map_uniform_decode [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B] [Fintype X]
    [DecidableEq X] [Fintype Y] [Nonempty Y] :
    (PMF.uniformOfFintype (X → Y)).map enc.decode = PMF.uniformOfFintype (A → B) := by
  classical
  ext h
  have hp : ((PMF.uniformOfFintype (X → Y)).map enc.decode).toOuterMeasure {h} =
      (PMF.uniformOfFintype (A → B)).toOuterMeasure {h} := by
    rw [PMF.toOuterMeasure_map_apply]
    let φ : A ↪ X := ⟨enc.query, enc.query_injective⟩
    have h1 : (PMF.uniformOfFintype (X → Y)).toOuterMeasure (enc.decode ⁻¹' {h}) =
        Pr[H ← (X → Y) : enc.answer ∘ (H ∘ φ) = h] := rfl
    have h2 : (PMF.uniformOfFintype (A → B)).toOuterMeasure {h} = Pr[g ← (A → B) : g = h] := rfl
    rw [h1, h2, probUniform_comp_embedding φ (fun g => enc.answer ∘ g = h)]
    exact probUniform_equiv (Equiv.arrowCongr (Equiv.refl A) enc.answer) (fun g => g = h)
  simpa [PMF.toOuterMeasure_apply_singleton] using hp

end NARG.OracleEncoding

namespace ROM

variable {A B X Y Req Resp Resp' : Type} (enc : NARG.OracleEncoding A B X Y) (fr : Resp → Resp')

/-- A reply against the encoded oracle, read as a reply against `A → B`: the answer decoded and
the response read by `fr`. -/
def Reply.decode : Reply Y Resp → Reply B Resp'
  | .answer y => .answer (enc.answer y)
  | .response o => .response (fr o)

/-- An action against `A → B`, as an action against the encoded oracle: the query encoded. -/
def Action.encode : Action A Req → Action X Req
  | .query a => .query (enc.query a)
  | .request r => .request r

@[simp] theorem Action.isQuery_encode (a : Action A Req) : (Action.encode enc a).IsQuery ↔ a.IsQuery := by
  cases a <;> rfl

namespace IAlg

variable {Out Out' : Type} {m : ℕ} (g : Out → Out') (𝒜 : IAlg A B Req Resp' Out m)

/-- **The algorithm against the encoded oracle**: its actions with the queries encoded, on the
replies with the answers decoded and the responses read by `fr`, and its output mapped by `g`.

Running time: that of `𝒜`, with one encoding per query and one decoding per answer. This running
time is argued here, not proved in Lean. -/
def decode : IAlg X Y Req Resp Out' m where
  next hist := Action.encode enc (𝒜.next (hist.map (Reply.decode enc fr)))
  out hist := g (𝒜.out (hist.map (Reply.decode enc fr)))

/-- **Responders that agree through the encoding**: at every request and every oracle `O'`, the
responder `R'` gives a response that `fr` reads as the response of `R` at the decoded oracle, and an
oracle after the request whose decoding is the oracle `R` gives. -/
structure ResponderDecode (R' : Responder X Y Req Resp) (R : Responder A B Req Resp') : Prop where
  response : ∀ i r O', fr (R' i r O').1 = (R i r (enc.decode O')).1
  oracle : ∀ i r O', enc.decode (R' i r O').2 = (R i r (enc.decode O')).2

/-- **Responders that agree through the encoding along the run** from `O'` before step `n`: at
every request of the encoded algorithm's run, `R'` gives a response that `fr` reads as the response
of `R` at the decoded oracle in force, and an oracle after the request whose decoding is the oracle
`R` gives. -/
def DecodeAlong (R' : Responder X Y Req Resp) (R : Responder A B Req Resp') (O' : X → Y) (n : ℕ) :
    Prop :=
  ∀ k < n, ∀ r, (𝒜.decode enc fr g).next ((𝒜.decode enc fr g).run R' O' k).hist = .request r →
    fr (R' ((𝒜.decode enc fr g).run R' O' k).nreq r ((𝒜.decode enc fr g).run R' O' k).oracle).1 =
        (R ((𝒜.decode enc fr g).run R' O' k).nreq r
          (enc.decode ((𝒜.decode enc fr g).run R' O' k).oracle)).1 ∧
      enc.decode (R' ((𝒜.decode enc fr g).run R' O' k).nreq r
          ((𝒜.decode enc fr g).run R' O' k).oracle).2 =
        (R ((𝒜.decode enc fr g).run R' O' k).nreq r
          (enc.decode ((𝒜.decode enc fr g).run R' O' k).oracle)).2

/-- Responders that agree through the encoding agree along every run. -/
theorem ResponderDecode.decodeAlong {R' : Responder X Y Req Resp} {R : Responder A B Req Resp'}
    (hR : ResponderDecode enc fr R' R) (O' : X → Y) (n : ℕ) : 𝒜.DecodeAlong enc fr g R' R O' n :=
  fun _ _ _ _ => ⟨hR.response _ _ _, hR.oracle _ _ _⟩

/-- **The run against the encoded oracle is the run against the decoded oracle**: the replies
decoded, the oracle in force decoded and the number of requests agree at every step up to `n`, for
responders that agree through the encoding along the run. -/
theorem run_decode {R' : Responder X Y Req Resp} {R : Responder A B Req Resp'} {O' : X → Y}
    {n : ℕ} (hR : 𝒜.DecodeAlong enc fr g R' R O' n) : ∀ k ≤ n,
    ((𝒜.decode enc fr g).run R' O' k).hist.map (Reply.decode enc fr) = (𝒜.run R (enc.decode O') k).hist ∧
      enc.decode ((𝒜.decode enc fr g).run R' O' k).oracle = (𝒜.run R (enc.decode O') k).oracle ∧
      ((𝒜.decode enc fr g).run R' O' k).nreq = (𝒜.run R (enc.decode O') k).nreq
  | 0, _ => ⟨rfl, rfl, rfl⟩
  | k + 1, hk => by
    obtain ⟨hh, ho, hn⟩ := run_decode hR k (by omega)
    have hRk := hR k (by omega)
    rw [run_succ, run_succ]
    generalize hs' : (𝒜.decode enc fr g).run R' O' k = s' at hh ho hn hRk
    generalize hs : 𝒜.run R (enc.decode O') k = s at hh ho hn
    have hnext : (𝒜.decode enc fr g).next s'.hist = Action.encode enc (𝒜.next s.hist) := by
      show Action.encode enc (𝒜.next (s'.hist.map (Reply.decode enc fr))) = _
      rw [hh]
    unfold step
    rw [hnext]
    rw [hnext] at hRk
    cases hA : 𝒜.next s.hist with
    | query a =>
      refine ⟨?_, ho, hn⟩
      simp only [Action.encode, List.map_append, List.map_cons, List.map_nil, hh]
      rw [← ho]
      rfl
    | request r =>
      rw [hA] at hRk
      obtain ⟨h1, h2⟩ := hRk r rfl
      refine ⟨?_, ?_, ?_⟩
      · simp only [Action.encode, List.map_append, List.map_cons, List.map_nil, hh, Reply.decode]
        rw [h1, ho, hn]
      · simp only [Action.encode]
        rw [h2, ho, hn]
      · simp only [Action.encode, hn]

/-- The encoded algorithm takes the same actions, encoded. -/
theorem next_decode_run {R' : Responder X Y Req Resp} {R : Responder A B Req Resp'} {O' : X → Y}
    {n : ℕ} (hR : 𝒜.DecodeAlong enc fr g R' R O' n) {k : ℕ} (hk : k ≤ n) :
    (𝒜.decode enc fr g).next ((𝒜.decode enc fr g).run R' O' k).hist =
      Action.encode enc (𝒜.next (𝒜.run R (enc.decode O') k).hist) := by
  show Action.encode enc (𝒜.next (((𝒜.decode enc fr g).run R' O' k).hist.map (Reply.decode enc fr))) = _
  rw [(run_decode enc fr g 𝒜 hR k hk).1]

/-- The encoded algorithm makes the same number of queries before each step. -/
theorem queryCountBefore_decode {R' : Responder X Y Req Resp} {R : Responder A B Req Resp'}
    {O' : X → Y} {n : ℕ} (hR : 𝒜.DecodeAlong enc fr g R' R O' n) {k : ℕ} (hk : k ≤ n) :
    (𝒜.decode enc fr g).queryCountBefore R' O' k = 𝒜.queryCountBefore R (enc.decode O') k := by
  unfold queryCountBefore
  congr 1
  refine Finset.filter_congr fun i hi => ?_
  rw [next_decode_run enc fr g 𝒜 hR (by simp at hi; omega), Action.isQuery_encode]

/-- The output of the encoded algorithm is the mapped output against the decoded oracle. -/
theorem out_decode_run {R' : Responder X Y Req Resp} {R : Responder A B Req Resp'} {O' : X → Y}
    (hR : 𝒜.DecodeAlong enc fr g R' R O' m) :
    (𝒜.decode enc fr g).out ((𝒜.decode enc fr g).run R' O' m).hist =
      g (𝒜.out (𝒜.run R (enc.decode O') m).hist) := by
  show g (𝒜.out (((𝒜.decode enc fr g).run R' O' m).hist.map (Reply.decode enc fr))) = _
  rw [(run_decode enc fr g 𝒜 hR m le_rfl).1]

/-- The oracle in force after the run against the encoded oracle decodes to the oracle after the run
against the decoded oracle. -/
theorem oracle_decode_run {R' : Responder X Y Req Resp} {R : Responder A B Req Resp'} {O' : X → Y}
    (hR : 𝒜.DecodeAlong enc fr g R' R O' m) :
    enc.decode ((𝒜.decode enc fr g).run R' O' m).oracle = (𝒜.run R (enc.decode O') m).oracle :=
  (run_decode enc fr g 𝒜 hR m le_rfl).2.1

end IAlg

namespace IAlg

variable {A B Req Resp Out : Type} {m : ℕ} (𝒜 : IAlg A B Req Resp Out m) (R : Responder A B Req Resp)
  (O : A → B)

/-- The number of requests never decreases along a run. -/
theorem nreq_run_mono {k j : ℕ} (h : k ≤ j) : (𝒜.run R O k).nreq ≤ (𝒜.run R O j).nreq := by
  induction j, h using Nat.le_induction with
  | base => exact le_rfl
  | succ j _ ih =>
    refine ih.trans ?_
    rw [run_succ]
    unfold step
    split <;> simp

/-- **A request increases the number of requests**: after a request at step `k`, every later step
has more requests than step `k`. -/
theorem nreq_lt_of_request {k j : ℕ} (hkj : k < j) {r : Req}
    (hr : 𝒜.next (𝒜.run R O k).hist = .request r) : (𝒜.run R O k).nreq < (𝒜.run R O j).nreq := by
  have h1 : (𝒜.run R O (k + 1)).nreq = (𝒜.run R O k).nreq + 1 := by
    rw [run_succ]
    unfold step
    rw [hr]
  calc (𝒜.run R O k).nreq < (𝒜.run R O (k + 1)).nreq := by rw [h1]; omega
    _ ≤ (𝒜.run R O j).nreq := 𝒜.nreq_run_mono R O hkj

/-- **Two requests with the same number of earlier requests are at the same step.** -/
theorem eq_of_request_of_nreq_eq {k j : ℕ} {r r' : Req}
    (hr : 𝒜.next (𝒜.run R O k).hist = .request r) (hr' : 𝒜.next (𝒜.run R O j).hist = .request r')
    (h : (𝒜.run R O k).nreq = (𝒜.run R O j).nreq) : k = j := by
  rcases lt_trichotomy k j with hkj | rfl | hjk
  · exact absurd h (𝒜.nreq_lt_of_request R O hkj hr).ne
  · rfl
  · exact absurd h.symm (𝒜.nreq_lt_of_request R O hjk hr').ne

end IAlg

namespace IAlg

variable {Out Out' : Type} {m : ℕ} (g : Out → Out') (𝒜 : IAlg A B Req Resp' Out m)

open Classical in
/-- **A responder of the decoded oracle read off a run against the encoded oracle**: request number
`i` is answered as `R'` answers it in that run, its response read by `fr` and its oracle decoded. -/
noncomputable def alongResponder (R' : Responder X Y Req Resp) (O' : X → Y) :
    Responder A B Req Resp' := fun i r O =>
  if h : ∃ k r₀, k < m ∧ ((𝒜.decode enc fr g).run R' O' k).nreq = i ∧
      (𝒜.decode enc fr g).next ((𝒜.decode enc fr g).run R' O' k).hist = .request r₀ then
    (fr (R' i r ((𝒜.decode enc fr g).run R' O' h.choose).oracle).1,
      enc.decode (R' i r ((𝒜.decode enc fr g).run R' O' h.choose).oracle).2)
  else (fr (R' i r O').1, O)

/-- The responder read off the run agrees with `R'` along the run. -/
theorem decodeAlong_alongResponder (R' : Responder X Y Req Resp) (O' : X → Y) :
    𝒜.DecodeAlong enc fr g R' (𝒜.alongResponder enc fr g R' O') O' m := by
  intro k hk r hr
  have hex : ∃ k' r₀, k' < m ∧ ((𝒜.decode enc fr g).run R' O' k').nreq =
      ((𝒜.decode enc fr g).run R' O' k).nreq ∧
      (𝒜.decode enc fr g).next ((𝒜.decode enc fr g).run R' O' k').hist = .request r₀ :=
    ⟨k, r, hk, rfl, hr⟩
  have hk' : hex.choose = k := by
    obtain ⟨r₀, -, hn, hr₀⟩ := hex.choose_spec
    exact (𝒜.decode enc fr g).eq_of_request_of_nreq_eq R' O' hr₀ hr hn
  unfold alongResponder
  rw [dite_eq_left hex, hk']
  exact ⟨rfl, rfl⟩

/-- **The decoded algorithm keeps a budget of queries.** -/
theorem budget_decode {t : ℕ} (h : 𝒜.Budget t) : (𝒜.decode enc fr g).Budget t := fun R' O' =>
  (queryCountBefore_decode enc fr g 𝒜 (𝒜.decodeAlong_alongResponder enc fr g R' O') le_rfl).trans_le
    (h _ _)

/-- **The decoded algorithm keeps a budget of queries before each request.** -/
theorem requestBudget_decode {t : ℕ} (h : 𝒜.RequestBudget t) : (𝒜.decode enc fr g).RequestBudget t := by
  intro R' O' k hk r hr
  have hR := 𝒜.decodeAlong_alongResponder enc fr g R' O'
  rw [queryCountBefore_decode enc fr g 𝒜 hR hk.le]
  rw [next_decode_run enc fr g 𝒜 hR hk.le] at hr
  cases hn : 𝒜.next (𝒜.run (𝒜.alongResponder enc fr g R' O') (enc.decode O') k).hist with
  | query a => rw [hn] at hr; cases hr
  | request r₀ => exact h _ _ k hk r₀ hn

end IAlg

/-! ### Zero-knowledge adversaries -/

section ZeroKnowledge

variable {Stmt Wit Proof Proof' : Type} (fp : Proof → Proof')

/-- **The output of a zero-knowledge adversary read at the decoded oracle.** -/
def outDecode (f : (A → B) → Bool) : (X → Y) → Bool := fun O' => f (enc.decode O')

namespace QueryBoundedAdversary

variable {t : ℕ}
  (𝒜 : QueryBoundedAdversary A B (QROM.ProofQuery Stmt Wit) (Option Proof') ((A → B) → Bool) t)

/-- **The zero-knowledge adversary against the encoded oracle**: each algorithm decoded
(`IAlg.decode`), its proofs read by `fp`, its output read at the decoded final oracle. -/
def decode : QueryBoundedAdversary X Y (QROM.ProofQuery Stmt Wit) (Option Proof) ((X → Y) → Bool) t where
  steps := 𝒜.steps
  Coins := 𝒜.Coins
  coins := 𝒜.coins
  alg r := (𝒜.alg r).decode enc (Option.map fp) (outDecode enc)
  budget r := (𝒜.alg r).budget_decode enc _ _ (𝒜.budget r)

/-- The decoded adversary keeps a budget of queries before each proof query. -/
theorem queriesBeforeLastProofQuery_decode {T : ℕ} (h : 𝒜.QueriesBeforeLastProofQuery T) :
    (𝒜.decode enc fp).QueriesBeforeLastProofQuery T :=
  fun r => (𝒜.alg r).requestBudget_decode enc (Option.map fp) (outDecode enc) (h r)

/-- The decoded adversary's output does not read the final oracle when `𝒜`'s does not. -/
theorem outputOracleFree_decode (h : 𝒜.OutputOracleFree) : (𝒜.decode enc fp).OutputOracleFree :=
  fun r _ _ _ => h r _ _ _

/-- **The decoded adversary accepts as the adversary does**, against environments on uniform tapes
whose responders agree through the encoding at the decoded oracle. -/
theorem acceptProb_decode [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B] [Fintype X]
    [DecidableEq X] [Fintype Y] [Nonempty Y] {C : Type} [Fintype C] {Q : ℕ} (μc : PMF C)
    (E' : Quantum.Env ((X → Y) × (Fin Q → C)) (QROM.ProofQuery Stmt Wit) Proof X Y Q)
    (E : Quantum.Env ((A → B) × (Fin Q → C)) (QROM.ProofQuery Stmt Wit) Proof' A B Q)
    (hμ' : E'.μ = QROM.tapeDist Q μc) (hμ : E.μ = QROM.tapeDist Q μc)
    (h0' : ∀ ω, E'.oracle₀ ω = ω.1) (h0 : ∀ ω, E.oracle₀ ω = ω.1)
    (hR : ∀ ω', IAlg.ResponderDecode enc (Option.map fp) (toResponder (NIZK.envResponder E' ω'))
      (toResponder (NIZK.envResponder E (enc.decode ω'.1, ω'.2)))) :
    (𝒜.decode enc fp).acceptProb E' = 𝒜.acceptProb E := by
  unfold acceptProb
  congr 1
  refine tsum_congr fun r => congrArg _ ?_
  have hacc : ∀ ω', ((𝒜.decode enc fp).alg r).accepts (toResponder (NIZK.envResponder E' ω'))
      (E'.oracle₀ ω') = (𝒜.alg r).accepts (toResponder (NIZK.envResponder E (enc.decode ω'.1, ω'.2)))
        (E.oracle₀ (enc.decode ω'.1, ω'.2)) := by
    intro ω'
    have hA := (hR ω').decodeAlong enc (Option.map fp) (outDecode enc) (𝒜.alg r) (E'.oracle₀ ω')
      𝒜.steps
    rw [h0', h0]
    rw [h0'] at hA
    unfold IAlg.accepts
    dsimp only [decode]
    rw [IAlg.out_decode_run enc _ _ _ hA, ← IAlg.oracle_decode_run enc _ _ _ hA]
    rfl
  have hmap : (QROM.tapeDist Q μc : PMF ((X → Y) × (Fin Q → C))).map
      (fun ω => (enc.decode ω.1, ω.2)) = QROM.tapeDist Q μc := by
    unfold QROM.tapeDist
    rw [PMF.map_bind]
    simp only [PMF.map_comp, Function.comp_def]
    rw [← enc.map_uniform_decode, PMF.bind_map]
    rfl
  rw [hμ', hμ, ← hmap, PMF.toOuterMeasure_map_apply]
  congr 1
  ext ω'
  simp only [Set.mem_preimage, Set.mem_ofPred_eq]
  rw [hacc]

end QueryBoundedAdversary

variable [Fintype A] [DecidableEq A] [Fintype B] [Nonempty B] [Fintype X] [DecidableEq X]
  [Fintype Y] [Nonempty Y] {rel : Stmt → Wit → Prop} [DecidableRel rel] {Coins SimCoins : Type}
  [Fintype Coins] [Fintype SimCoins]

/-- **Provers that agree through the encoding**: on a pair in the relation, the proof of `P'`
against `O'`, read by `fp`, is the proof of `P` against the decoded oracle. -/
def ProverDecode (P' : NARG.ProverFn X Y Stmt Wit Proof Coins)
    (P : NARG.ProverFn A B Stmt Wit Proof' Coins) : Prop :=
  P'.coins = P.coins ∧ ∀ O' x w c, rel x w → fp (P'.prove O' x w c) = P.prove (enc.decode O') x w c

/-- **Simulators that agree through the encoding**: on a statement with a witness in the relation,
the proof of `S'` against `O'`, read by `fp`, is that of `S` against the decoded oracle, and the
oracle `S'` reprograms decodes to the oracle `S` reprograms. -/
def SimulatorDecode (S' : NARG.SimulatorFn X Y Stmt Proof SimCoins)
    (S : NARG.SimulatorFn A B Stmt Proof' SimCoins) : Prop :=
  ∀ O' x c, (∃ w, rel x w) → fp (S'.run O' x c).proof = (S.run (enc.decode O') x c).proof ∧
    enc.decode (O'.reprogram (S'.run O' x c).assignments) =
      (enc.decode O').reprogram (S.run (enc.decode O') x c).assignments

variable {enc fp} in
theorem responderDecode_realEnv {P' : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {P : NARG.ProverFn A B Stmt Wit Proof' Coins} (hP : ProverDecode enc fp (rel := rel) P' P) {Q : ℕ}
    (ω' : (X → Y) × (Fin Q → Coins)) :
    IAlg.ResponderDecode enc (Option.map fp) (toResponder (NIZK.envResponder (QROM.realEnv rel P' Q) ω'))
      (toResponder (NIZK.envResponder (QROM.realEnv rel P Q) (enc.decode ω'.1, ω'.2))) := by
  constructor <;> intro i req O' <;>
    simp only [toResponder, NIZK.envResponder, QROM.realEnv] <;> split_ifs with hi hr <;>
    first | rfl | simp [hP.2 _ _ _ _ hr]

variable {enc fp} in
theorem responderDecode_simEnv {S' : NARG.SimulatorFn X Y Stmt Proof SimCoins}
    {S : NARG.SimulatorFn A B Stmt Proof' SimCoins} (hS : SimulatorDecode enc fp (rel := rel) S' S)
    {Q : ℕ} (ω' : (X → Y) × (Fin Q → SimCoins)) :
    IAlg.ResponderDecode enc (Option.map fp)
      (toResponder (NIZK.envResponder (QROM.simEnv (Wit := Wit) rel S' Q) ω'))
      (toResponder (NIZK.envResponder (QROM.simEnv (Wit := Wit) rel S Q) (enc.decode ω'.1, ω'.2))) := by
  constructor <;> intro i req O' <;>
    simp only [toResponder, NIZK.envResponder, QROM.simEnv] <;> split_ifs with hi hr <;>
    first | rfl | simp [(hS _ _ _ ⟨_, hr⟩).1, (hS _ _ _ ⟨_, hr⟩).2]

variable {enc fp}

/-- **The advantage at the encoded oracle is the advantage at `A → B`.** -/
theorem QueryBoundedAdversary.advantage_decode {t : ℕ}
    (𝒜 : QueryBoundedAdversary A B (QROM.ProofQuery Stmt Wit) (Option Proof') ((A → B) → Bool) t)
    {P' : NARG.ProverFn X Y Stmt Wit Proof Coins} {P : NARG.ProverFn A B Stmt Wit Proof' Coins}
    {S' : NARG.SimulatorFn X Y Stmt Proof SimCoins} {S : NARG.SimulatorFn A B Stmt Proof' SimCoins}
    (hP : ProverDecode enc fp (rel := rel) P' P) (hS : SimulatorDecode enc fp (rel := rel) S' S)
    (Q : ℕ) : (𝒜.decode enc fp).advantage rel P' S' Q = 𝒜.advantage rel P S Q := by
  unfold QueryBoundedAdversary.advantage
  rw [𝒜.acceptProb_decode enc fp P.coins _ _ (by rw [← hP.1]; rfl) rfl (fun _ => rfl) (fun _ => rfl)
      (responderDecode_realEnv hP),
    𝒜.acceptProb_decode enc fp (NARG.SimulatorFn.coins S) _ _ rfl rfl (fun _ => rfl) (fun _ => rfl)
      (responderDecode_simEnv hS)]

/-- **Zero knowledge at an encoded oracle gives zero knowledge at the oracle `A → B`**, for a prover
and a simulator that agree through the encoding: every adversary against `A → B` is, decoded, an
adversary against the encoded oracle with the same advantage and the same query budget. -/
theorem ZeroKnowledge.of_decode {P' : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {P : NARG.ProverFn A B Stmt Wit Proof' Coins} {S' : NARG.SimulatorFn X Y Stmt Proof SimCoins}
    {S : NARG.SimulatorFn A B Stmt Proof' SimCoins} (hP : ProverDecode enc fp (rel := rel) P' P)
    (hS : SimulatorDecode enc fp (rel := rel) S' S) {ε : ℕ → ℕ → ℝ}
    (h : ZeroKnowledge rel P' S' ε) : ZeroKnowledge rel P S ε := fun t Q 𝒜 h𝒜 =>
  (𝒜.advantage_decode hP hS Q).symm.trans_le
    (h t Q (𝒜.decode enc fp) (𝒜.outputOracleFree_decode enc fp h𝒜))

/-- **Everlasting zero knowledge at an encoded oracle gives everlasting zero knowledge at the oracle
`A → B`** (as `ZeroKnowledge.of_decode`). -/
theorem EverlastingZeroKnowledge.of_decode {P' : NARG.ProverFn X Y Stmt Wit Proof Coins}
    {P : NARG.ProverFn A B Stmt Wit Proof' Coins} {S' : NARG.SimulatorFn X Y Stmt Proof SimCoins}
    {S : NARG.SimulatorFn A B Stmt Proof' SimCoins} (hP : ProverDecode enc fp (rel := rel) P' P)
    (hS : SimulatorDecode enc fp (rel := rel) S' S) {ε : ℕ → ℕ → ℝ}
    (h : EverlastingZeroKnowledge rel P' S' ε) : EverlastingZeroKnowledge rel P S ε :=
  fun T t Q 𝒜 h𝒜 => (𝒜.advantage_decode hP hS Q).symm.trans_le
    (h T t Q (𝒜.decode enc fp) (𝒜.queriesBeforeLastProofQuery_decode enc fp h𝒜))

end ZeroKnowledge

end ROM

end GordieHowe
