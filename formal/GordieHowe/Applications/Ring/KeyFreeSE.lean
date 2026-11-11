-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeMain
public import GordieHowe.Applications.Ring.RingInsider
public import GordieHowe.Applications.Ring.RingForgerZK

@[expose] public section

/-!
# The simulation-extraction step of the key-free unforgeability route

The simulation-extraction step of the key-free unforgeability route
(`GordieHowe/Applications/Ring/KeyFreeMain.lean`), with the claim's statement the adversary's
explicit statement: an adversary `A` with output `(o, x₀)` against the simulated main challenger
`kfMainSim` (the multi-user challenger without messages and the simulated proof challenger) is an
adversary of the spBCS simulation-extraction game (`SPBCS.winTestProb`), whose claim is `x₀` with
the proof `prf o`; a fresh accepted claim is extracted
(`weak_online_simulation_extractability_qrom`), and the extraction run is that of the table form
of `A` with the table of multi-user replies `keyReplyNone keys`.

The relay `seTwoKF` sends each request `r` as the tagged statement `(stmtOf r, r)`: a multi-user
request as its dummy proof query's statement, a proof query as its statement when its witness is
in the relation and as the dummy statement `dummyS` otherwise; the relay reads the witness and
answers a proof query outside the relation by `none`, as the proof challenger does, and a
public-key request by the public key itself; the corruptions are its only outer requests. The
simulator of the simulation-extraction game is inert on dummy statements (`inertOnDummy`), which
are outside the relation (`DummyStmts`).

- `stmtOf`, `seTwoKF`, `seTwoKF_route_injective`, `seTwoKF_outer_eq`, `inertOnDummy`,
  `DummyStmts`.
- `relays_kfMainSim_se`: `kfMainSim` relays the simulation-extraction challenger of the inert
  simulator by `seTwoKF` at the outer replies `keyReplyNone keys`.
- `relayList_seTwoKF`, `stmtOf_ne`: the relayed statements, and their freshness from the dummy
  statements' disjointness and the freshness of the proof queries in the relation.
- `outLaw_kfMainSim_se`: the adversary against `kfMainSim` is its absorption through `seTwoKF`
  against the simulation-extraction challenger. `outLaw_seTwoKF_absorbTab`: the absorption with
  the multi-user replies as a table (`AdaptiveIAlg.absorbTab`).
- `claimOfOutX`, `seAlgKF`, `WinsKF`, `okAtKF`: the claim of an output, the
  simulation-extraction adversary, the key-free win and the query-free test.
- `seAlgKFS`, `seAlgKF_toShape`: the shape of `seAlgKF`.
- `accepts_of_acceptedKF`, `winTestProb_mapOut'`.
- `sim_le_winTestProbKF`: the simulated key-free game, averaged over the oracle, is at most the
  simulation-extraction game of `seAlgKF` with the test `okAtKF`.
- `simAssignsAtKeys_inertOnDummy`, `seAdversaryKF`, `forgerWinsKF`, `extractFreshTestProb_le_KF`.
- `winTestProb_le_forgerWinsKF`: simulation extraction, the simulation-extraction game at most the
  forger's win in the extraction run plus `simExtractionError`.
- `simProb_extAdv_seAlgKF_eq`: the forger's win as an extraction run of the table form.
-/

namespace GordieHowe

open Quantum Signature QROM

namespace RingSignature.KeyFree

/-! ### The simulation-extraction relay and the simulator inert on dummy statements -/

section Relay

variable {X Y Xb Yb : Type} {N n : ℕ} {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.BSig]
  [DecidableEq TB.BSig] [Fintype TB.KeyCoins]
  [DecidableEq TB.KeyCoins]
  (B : BaseSigner Xb Yb N TB) {Stmt Wit Proof SC R : Type}
  (rel : Stmt → Wit → Prop) [DecidableRel rel]
  (enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit) (dummyS : Stmt)
  {X₀ : Type} (stmtX : Stmt → X₀)

/-- **The statement sent to the simulator for a request**: the dummy proof query's statement for
a multi-user request; for a proof query, its statement when its witness is in the relation and
the dummy statement `dummyS` otherwise. -/
def stmtOf : MURequest (SignOracle.none B.core) n ⊕ R → Stmt
  | .inl m => (enc (.inl m)).stmt
  | .inr q => if rel (enc (.inr q)).stmt (enc (.inr q)).wit then (enc (.inr q)).stmt else dummyS

/-- **The relay of the simulation-extraction step** at the public keys `pks`: request `r` is sent
to the simulator as the tagged statement `(stmtOf r, r)`; below `Q` requests, a public-key request
for user `i` is answered by `pks i` and a corruption has itself as the outer request, its reply the
outer reply; a proof query is answered by the simulator's reply when its witness is in the
relation and by `none` otherwise (the relay reads the witness and decides the relation itself, as
the proof challenger does). The corruptions are the only outer requests. -/
def seTwoKF (pks : Fin n → B.PK) (Q : ℕ) :
    TwoRelay (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)
      (Stmt × (MURequest (SignOracle.none B.core) n ⊕ R)) Proof (MURequest (SignOracle.none B.core) n)
      (MUResponse B.core) where
  route₁ _ r := (stmtOf B rel enc dummyS r, r)
  answer₁ c r a := match r with
    | .inl (.publicKey i) => if c < Q then some (.inl (.publicKey (pks i))) else none
    | .inl _ => none
    | .inr q => if rel (enc (.inr q)).stmt (enc (.inr q)).wit then a.map Sum.inr else none
  outer c r := match r with
    | .inl (.corrupt i) => if c < Q then some (.corrupt i) else none
    | _ => none
  answer₂ _ _ b := b.map Sum.inl

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- The relay of the simulation-extraction step sends distinct requests to distinct statements. -/
theorem seTwoKF_route_injective (pks : Fin n → B.PK) (Q c : ℕ) :
    Function.Injective ((seTwoKF (Proof := Proof) B rel enc dummyS pks Q).route₁ c) :=
  fun _ _ h => congrArg Prod.snd h

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The outer requests of the simulation-extraction relay are corruptions.** -/
theorem seTwoKF_outer_eq (pks : Fin n → B.PK) {Q c : ℕ} {r} {q : MURequest (SignOracle.none B.core) n}
    (h : (seTwoKF (Proof := Proof) B rel enc dummyS pks Q).outer c r = some q) :
    ∃ i, r = .inl (.corrupt i) ∧ q = .corrupt i := by
  rcases r with (i | ⟨i, sm⟩ | i) | r
  · simp [seTwoKF] at h
  · exact sm.elim
  · by_cases hc : c < Q
    · simp only [seTwoKF, hc, ↓reduceIte, Option.some.injEq] at h
      exact ⟨i, rfl, h.symm⟩
    · simp [seTwoKF, hc] at h
  · simp [seTwoKF] at h

/-- **The simulator answering `p₀` on dummy statements**: on a statement `s` with `isDummy s` it
returns `p₀` without queries or assignments; on every other statement it runs `S`.

Running time: that of `S`, plus one evaluation of `isDummy`. This running time is argued here, not
proved in Lean. -/
def inertOnDummy {X Y St : Type} (isDummy : St → Bool) (S : NARG.Simulator X Y St Proof SC)
    (p₀ : Proof) : NARG.Simulator X Y St Proof SC where
  prog s c := if isDummy s then .pure ⟨p₀, []⟩ else S.prog s c
  coins_nonempty := S.coins_nonempty
  q := S.q
  prog_queries s c H := by
    split_ifs
    · simp
    · exact S.prog_queries s c H

/-- **The hypotheses on the dummy statements**: `dummyS` and the statements of the dummy proof
queries of multi-user requests are dummy statements, and no dummy statement is in the relation. -/
structure DummyStmts (isDummy : X₀ → Bool) : Prop where
  /-- The dummy statement is a dummy statement. -/
  dummyS : isDummy (stmtX dummyS) = true
  /-- The dummy proof query of a multi-user request has a dummy statement. -/
  inl : ∀ m, isDummy (stmtX (enc (.inl m)).stmt) = true
  /-- No dummy statement is in the relation. -/
  not_rel : ∀ s, isDummy (stmtX s) = true → ∀ w, ¬ rel s w

variable [Fintype SC] [DecidableEq SC] {isDummy : X₀ → Bool}

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The simulated main challenger relays the simulation-extraction challenger** of the simulator
inert on dummy statements, by the relay `seTwoKF` at the public keys of `keys` and the outer
replies `keyReplyNone keys`: a public-key request is answered by the relay and a corruption by
`keyReplyNone`, as `keyReplyNone` answers both, while the simulator answers its dummy statement
inertly; a proof query in the relation is simulated on its statement with the coins of its global
count in both; a proof query outside the relation gets `none` from the proof challenger, and the
inert simulator's reply on `dummyS` is replaced by `none`. -/
theorem relays_kfMainSim_se (hd : DummyStmts B rel enc dummyS stmtX isDummy)
    (S : NARG.Simulator X Y X₀ Proof SC) (p₀ : Proof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (c₁ : (muNone (X := X) (Y := Y) B keys Q).Coins)
    (c₂ : Fin Q → SC) :
    ((seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q).atC
        fun _ => keyReplyNone B keys).RelaysChallenger
      (kfMainSim B rel (S.comap stmtX) enc keys Q) (c₁, c₂)
      (simExtChallenger ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q) c₂ where
  Q_eq := rfl
  run_eq hist hist' x G hreq hlen := by
    change hist.length < Q at hlen
    have hl' : hist'.length = hist.length := by
      simpa using congrArg List.length hreq
    have hQ' : hist'.length < Q := hl' ▸ hlen
    have hi : (⟨hist'.length, hQ'⟩ : Fin Q) = ⟨hist.length, hlen⟩ := Fin.ext hl'
    rcases x with m | q
    · have hl : (leftHist hist).length < Q :=
        lt_of_le_of_lt (List.length_filterMap_le _ _) hlen
      simp only [kfMainSim, Challenger.sumDummy, OracleProg.run_mapOutput,
        respond_muChallenger_none B keys Q _ _ _ _ hl, TwoRelay.atC, seTwoKF, hlen,
        ↓reduceIte, simExtChallenger, simExtRespond, hQ', ↓reduceDIte, NARG.Simulator.comap,
        inertOnDummy, stmtOf, Function.comp_apply, hd.inl]
      rcases m with i | ⟨i, sm⟩ | i
      · rfl
      · exact sm.elim
      · rfl
    · have hdl : (dummyHist enc hist).length = hist.length := by simp [dummyHist]
      by_cases hr : rel (enc (.inr q)).stmt (enc (.inr q)).wit
      · have hnd : isDummy (stmtX (enc (.inr q)).stmt) = false := by
          by_contra h
          exact hd.not_rel _ (by simpa using h) _ hr
        simp only [kfMainSim, Challenger.sumDummy, OracleProg.run_mapOutput, simChallenger,
          hdl, hlen, ↓reduceDIte, hr, ↓reduceIte, TwoRelay.atC, seTwoKF, simExtChallenger,
          simExtRespond, hQ', NARG.Simulator.comap, inertOnDummy, stmtOf, Function.comp_apply,
          hnd, hi,
          Bool.false_eq_true, OracleProg.run_bind, OracleProg.run_pure]
      · simp only [kfMainSim, Challenger.sumDummy, OracleProg.run_mapOutput, simChallenger,
          hdl, hlen, ↓reduceDIte, hr, ↓reduceIte, TwoRelay.atC, seTwoKF, simExtChallenger,
          simExtRespond, hQ', NARG.Simulator.comap, inertOnDummy, stmtOf, Function.comp_apply,
          hd.dummyS,
          OracleProg.run_bind, OracleProg.run_pure]
        rfl
  answer_none i x hi := by
    change Q ≤ i at hi
    rcases x with m | q
    · rcases m with i | ⟨i, sm⟩ | i
      · simp [TwoRelay.atC, seTwoKF, not_lt.2 hi]
      · exact sm.elim
      · simp [TwoRelay.atC, seTwoKF, not_lt.2 hi]
    · simp [TwoRelay.atC, seTwoKF]

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- The relayed requests of the simulation-extraction relay are the tagged statements. -/
theorem relayList_seTwoKF (pks : Fin n → B.PK) (Q : ℕ)
    (b : ℕ → MURequest (SignOracle.none B.core) n → Option (MUResponse B.core))
    (rs : List (MURequest (SignOracle.none B.core) n ⊕ R)) :
    ((seTwoKF (Proof := Proof) B rel enc dummyS pks Q).atC b).relayList rs =
      rs.map fun r => (stmtOf B rel enc dummyS r, r) := by
  exact List.ext_getElem (by simp) fun i _ _ => by
    simp [SideRelay.relayList, TwoRelay.atC, seTwoKF]

omit [Fintype TB.PK] [DecidableEq TB.PK] [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins] in
/-- **The statements sent for the first `Q` requests differ from a statement `x₀`** when every
dummy statement does (`hdisj`) and every proof query in the relation among them does (`hq`). -/
theorem stmtOf_ne {isDummy : X₀ → Bool}
    (hd : DummyStmts B rel enc dummyS stmtX isDummy) {x₀ : X₀}
    (hdisj : ∀ x, isDummy x = true → x ≠ x₀)
    {rs : List (MURequest (SignOracle.none B.core) n ⊕ R)}
    (hq : ∀ q, .inr q ∈ rs → rel (enc (.inr q)).stmt (enc (.inr q)).wit →
      stmtX (enc (.inr q)).stmt ≠ x₀) :
    ∀ r ∈ rs, stmtX (stmtOf B rel enc dummyS r) ≠ x₀ := by
  rintro (m | q) hr
  · exact hdisj _ (hd.inl m)
  · by_cases h : rel (enc (.inr q)).stmt (enc (.inr q)).wit
    · simpa only [stmtOf, h, ↓reduceIte] using hq q hr h
    · simpa only [stmtOf, h, ↓reduceIte] using hdisj _ hd.dummyS

section Absorb

variable [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y] [Nonempty X] [AddGroup Y]
  [Nonempty Y] [Fintype R] [DecidableEq R] [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Inhabited R] [Fintype Proof] [DecidableEq Proof] [DecidableEq Xb] [DecidableEq Yb] {O : Type}

/-- **The adversary against the simulated main challenger is the adversary absorbed through the
simulation-extraction relay against the simulation-extraction challenger** of the simulator inert
on dummy statements (`relays_kfMainSim_se`, `AdaptiveIAlg.outLaw_absorb`), on every event of the
adversary's registers, its logs, the relayed logs, the proof part's coins and the final oracle. -/
theorem outLaw_kfMainSim_se (hd : DummyStmts B rel enc dummyS stmtX isDummy)
    (S : NARG.Simulator X Y X₀ Proof SC) (p₀ : Proof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)} (A : AdaptiveIAlg shA O)
    (H : X → Y)
    (P : DReg A.toKindAlg.W A.width X Y (MURequest (SignOracle.none B.core) n ⊕ R)
        (MUResponse B.core ⊕ Proof) → LogReg (MURequest (SignOracle.none B.core) n ⊕ R) A.slots →
      LogReg (Stmt × (MURequest (SignOracle.none B.core) n ⊕ R)) A.slots → (Fin Q → SC) →
        (X → Y) → Prop) :
    ((A.toKindAlg.composeBothOut (kfMainSim B rel (S.comap stmtX) enc keys Q) id).outLaw
        H).toOuterMeasure
        {o | ∃ v ∈ o, P v.adv v.chal.logs
          (((seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q).atC
            fun _ => keyReplyNone B keys).logs
            v.chal.logs)
          v.chal.coins.2 (H.reprogram (A.toKindAlg.postAss _ v.chal))} =
      (((A.absorb ((seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q).atC
          fun _ => keyReplyNone B keys)).toKindAlg.composeBothOut
          (simExtChallenger ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, P (A.absorbedAdv ((seTwoKF (Proof := Proof) B rel enc dummyS
          (B.pk ∘ keys) Q).atC
            fun _ => keyReplyNone B keys) v.adv) v.adv.1.1.1.logs v.chal.logs v.chal.coins
          (H.reprogram ((A.absorb ((seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q).atC
            fun _ => keyReplyNone B keys)).toKindAlg.postAss
              (simExtChallenger ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q)
                v.chal))} := by
  rw [A.outLaw_absorb (C := kfMainSim B rel (S.comap stmtX) enc keys Q)
    (C' := simExtChallenger ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q)
    (muNone (X := X) (Y := Y) B keys Q).coins
    (fun _ => (seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q).atC
      fun _ => keyReplyNone B keys)
    (Equiv.refl ((muNone (X := X) (Y := Y) B keys Q).Coins ×
      (Fin Q → SC)))
    (fun s c' => Challenger.coins_sumDummy
      (C₂ := simChallenger (Wit := Wit) rel (S.comap stmtX) Q) (R := R) (enc := enc) s c')
    (fun H s c' => (relays_kfMainSim_se B rel enc dummyS stmtX hd S p₀ keys Q s c').relays H _)
    (fun _ c => seTwoKF_route_injective (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q c) H
    fun adv lg lg' c G => P adv lg lg' c.2 G]
  refine Eq.trans ?_ (one_mul _)
  rw [← PMF.sum_coe (muNone (X := X) (Y := Y) B keys Q).coins]
  rw [Finset.sum_mul]
  rfl

/-- **The absorbed adversary at the outer replies `keyReplyNone keys` has the law of the adversary
absorbed with them as a table of outer replies** (`AdaptiveIAlg.absorbTab`), against every
challenger and on every event of the composed registers named without the relay. -/
theorem outLaw_seTwoKF_absorbTab (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape X Y (MURequest (SignOracle.none B.core) n ⊕ R) (MUResponse B.core ⊕ Proof)} (A : AdaptiveIAlg shA O)
    (C' : Challenger X Y (Stmt × (MURequest (SignOracle.none B.core) n ⊕ R)) Proof) (H : X → Y)
    (P : A.AbsCW C' → Prop) :
    (((A.absorb ((seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q).atC
        fun _ => keyReplyNone B keys)).toKindAlg.composeBothOut
        C' id).outLaw H).toOuterMeasure {o | ∃ v ∈ o, P v} =
      (((A.absorbTab (seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q)
          (fun _ => keyReplyNone B keys)).toKindAlg.composeBothOut
          C' id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, P ((A.absorb (seTwoKF (Proof := Proof) B rel enc dummyS
          (B.pk ∘ keys) Q).base).forgetCWTo
          (fun _ => keyReplyNone B keys)
          (A.stepTab (seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q)) C'
          (A.absorb ((seTwoKF (Proof := Proof) B rel enc dummyS (B.pk ∘ keys) Q).atC
            fun _ => keyReplyNone B keys)).step v)} :=
  (AdaptiveIAlg.toOuterMeasure_outLaw_absorbTab' A (seTwoKF (Proof := Proof) B rel enc dummyS
    (B.pk ∘ keys) Q)
    (tab := fun _ => keyReplyNone B keys) (b := fun _ => keyReplyNone B keys)
    (fun lg j _ q _ _ => AdaptiveIAlg.tabAt_outerCount_const _ _ _ lg j q) C' H P).symm

end Absorb

end Relay

/-! ### The simulation-extraction adversary and the simulated game -/

section SPBCS

open GordieHowe.SPBCS IOP SPTerm RingSignature.Insider

variable {k kN kS L e N n t : ℕ} {Xb Yb : Type} [DecidableEq Xb] [DecidableEq Yb]
  {TB : BaseTypes} [Fintype TB.PK] [DecidableEq TB.PK]
  [Fintype TB.BSig] [DecidableEq TB.BSig]
  [Fintype TB.KeyCoins] [DecidableEq TB.KeyCoins]
  {B : BaseSigner Xb Yb N TB}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {b : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)]
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x} (hb : M.FormatBounds Qs b b)
  {Stmt Wit SC R Frg : Type} [Fintype Stmt] [DecidableEq Stmt] [Inhabited Stmt]
  [Fintype R] [DecidableEq R] [Inhabited R] [Fintype SC] [DecidableEq SC]
  {rel : Stmt → Wit → Prop} [DecidableRel rel]
  {enc : MURequest (SignOracle.none B.core) n ⊕ R → ProofQuery Stmt Wit} {dummyS : Stmt}
  {isDummy : X₀ → Bool} [Inhabited M.NIProof]

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B.core) n

/-- **The claim of an output** `(o, x₀)`: the adversary's explicit statement `x₀` with the proof
`prf o`, the default proof when `o` has none. -/
def claimOfOutX (prf : Frg → Option M.NIProof) (p : Frg × X₀) : Claim X₀ M.NIProof :=
  ⟨p.2, (prf p.1).getD default⟩

/-- **The adversary of the simulation-extraction step** at the key coins `keys`: the adversary
with its requests sent as tagged statements (`seTwoKF`), the multi-user requests answered from a
table of outer replies `keyReplyNone keys` (`AdaptiveIAlg.absorbTab`, a classical register written
once at initialization), its output read as a claim (`claimOfOutX`, the claim's statement the
adversary's explicit statement).

Running time: that of `AdaptiveIAlg.absorbTab` (its paragraph) at the relay `seTwoKF` and the table
`keyReplyNone keys`, plus one evaluation of `prf` on the output. This running time is argued here,
not proved in Lean. -/
abbrev seAlgKF (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀)) :=
  (A.absorbTab (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
    (fun _ => keyReplyNone B keys)).mapOut (claimOfOutX prf)

/-- **The shape of the simulation-extraction adversary** (`seAlgKF`) of an adversary of shape
`s`: the shape of the adversary absorbed with the table of the multi-user replies
(`AlgShape.absorbTabS`). -/
@[reducible] def seAlgKFS (s : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)) :
    AlgShape Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) :=
  s.absorbTabS MUR (MUResponse B.core)

theorem seAlgKF_toShape (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀)) :
    (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q A).toShape =
      seAlgKFS (Stmt := Stmt) A.toShape :=
  rfl

/-- **The win of the key-free route** at the output `p = (o, x₀)`, the logged requests `rs` and
the oracle `G` (read as bytes): `x₀` passes the check, the compiled verifier accepts the claim of
`x₀` with the proof of `o`, and the output is fresh (`freshX`) at the first `Q` requests. -/
def WinsKF (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool)
    (freshX : Frg × X₀ → List (MUR ⊕ R) → Prop) (Q : ℕ) (p : Frg × X₀) (rs : List (MUR ⊕ R))
    (G : Xq → Out k e) : Prop :=
  checkX p.2 p.1 = true ∧ (∃ π ∈ prf p.1, (M.qVerifier Qs b b).Accepted G ⟨p.2, π⟩) ∧
    freshX p (rs.take Q)

/-- **The test of the simulation-extraction step**: the output carries a proof, its statement
passes the check, and it is fresh at the first `Q` logged requests. -/
def okAtKF (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool)
    (freshX : Frg × X₀ → List (MUR ⊕ R) → Prop) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (w : (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) (Stmt := Stmt) prf keys Q A).W) :
    Prop :=
  (prf (A.out w.1.work).1).isSome ∧ checkX (A.out w.1.work).2 (A.out w.1.work).1 = true ∧
    freshX (A.out w.1.work) ((Quantum.requests w.1.logs).take Q)

omit [Inhabited M.NIProof] [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
include hb in
/-- **The compiled verifier at its query budget accepts only claims that the spBCS verifier
accepts** under the oracle read through `outEquiv` and `Query.toBits` (`chainOracle`), for format
bounds `b` (`RingSignature.Insider.accepts_of_accepted` without the ring context). -/
theorem accepts_of_acceptedKF {G : Xq → XOut k e} {c : Claim X₀ M.NIProof}
    (h : (M.qVerifier Qs b b).Accepted (outEquiv k e ∘ G) c) :
    M.Accepts (chainOracle G) c.stmt c.proof (Qs c.stmt) := by
  refine (NARG.Verifier.ofOracle_accepted_iff (fun h₁ h₂ c hag hv => ?_)).1 h
  refine M.accepts_of_agree Qs (fun _ _ _ hv => queries_length_le_of_formatBounds hb hv)
    (fun i => ?_) hv
  have := hag i
  rwa [QROM.Expansion.queries_map] at this

omit [Inhabited M.NIProof] in
open Classical in
/-- **The simulation-extraction game of an adversary with its output read through a map**,
through the composition of the adversary before the readout. -/
theorem winTestProb_mapOut' {X' O : Type} [Fintype X'] [DecidableEq X']
    {shA : AlgShape Xq (XOut k e) X' (M.Response b)} (A : AdaptiveIAlg shA O) (f : O → Claim X₀ M.NIProof)
    {SC' : Type} [Fintype SC'] [DecidableEq SC']
    (Psim : NARG.Simulator Xq (XOut k e) X' (M.Response b) SC') (Q : ℕ) (fx : X' → X₀)
    (ok : (A.mapOut f).W → Prop) :
    winTestProb Qs (A.mapOut f) Psim Q fx ok =
      ((A.toKindAlg.composeBothOut (simExtChallenger Psim Q) id).realLaw
          (outEquiv k e)).toOuterMeasure
        {p | ∃ v, p.out = some v ∧
          SPBCS.Wins (A.mapOut f).toTPKindAlg Psim Q Qs fx ((outEquiv k e).symm ∘ p.oracle) v ∧
          ok (SPBCS.advWorkspace (A.mapOut f).toTPKindAlg Psim Q v).1} :=
  rfl

include hb in
/-- **The simulated key-free game is at most the simulation-extraction game with the test
`okAtKF`** at the key coins `keys` (the key-free route's simulation-extraction step): the
adversary against the simulated main challenger is its absorption through `seTwoKF` against the
simulation-extraction challenger of the simulator inert on dummy statements
(`outLaw_kfMainSim_se`, `outLaw_seTwoKF_absorbTab`); a win is a fresh statement of the
simulation-extraction game (`stmtOf_ne`: dummy statements differ from a checked statement, and
`freshX` separates the proof queries in the relation), accepted under the final oracle, whose
statement is the adversary's explicit statement. -/
theorem sim_le_winTestProbKF (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool)
    (freshX : Frg × X₀ → List (MUR ⊕ R) → Prop) (stmtX : Stmt → X₀)
    (hd : DummyStmts B rel enc dummyS stmtX isDummy)
    (hdisj : ∀ x, isDummy x = true → ∀ p : Frg × X₀, checkX p.2 p.1 = true → x ≠ p.2)
    (hfresh : ∀ p rs, freshX p rs → ∀ q, .inr q ∈ rs → rel (enc (.inr q)).stmt (enc (.inr q)).wit →
      stmtX (enc (.inr q)).stmt ≠ p.2)
    (S : NARG.Simulator Xq (XOut k e) X₀ (M.Response b) SC) (p₀ : M.Response b)
    (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀)) :
    ∑' H, PMF.uniformOfFintype (Xq → XOut k e) H *
        ((A.toKindAlg.composeBothOut (kfMainSim B rel (S.comap stmtX) enc keys Q) id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, WinsKF (Qs := Qs) (b := b) prf checkX freshX Q (A.out v.adv.workspace.1)
          (Quantum.requests v.chal.logs) (outEquiv k e ∘ H.reprogram
            (A.toKindAlg.postAss (kfMainSim B rel (S.comap stmtX) enc keys Q) v.chal))} ≤
      winTestProb Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A)
        ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q (stmtX ∘ Prod.fst)
        (okAtKF (rel := rel) (enc := enc) (dummyS := dummyS) prf checkX freshX keys Q A) := by
  have hstep := fun H => outLaw_kfMainSim_se B rel enc dummyS stmtX hd S p₀ keys Q A H
    (fun adv lg mlg _ G =>
      WinsKF (Qs := Qs) (b := b) prf checkX freshX Q (A.out adv.workspace.1) (Quantum.requests lg)
        (outEquiv k e ∘ G) ∧
      ∀ x' ∈ (Quantum.requests mlg).take Q, stmtX x'.1 ≠ (A.out adv.workspace.1).2)
  refine (tsum_congr fun H => congrArg (_ * ·) (Eq.trans ?_ (hstep H))).trans_le ?_
  · congr 1
    ext o
    refine exists_congr fun v => and_congr_right fun _ => ⟨fun h => ⟨h, ?_⟩, And.left⟩
    rw [SideRelay.requests_logs, relayList_seTwoKF, ← List.map_take]
    intro x' hx'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hx'
    exact stmtOf_ne B rel enc dummyS stmtX hd (fun x hx => hdisj x hx _ h.1)
      (fun q hq hrq => hfresh _ _ h.2.2 q hq hrq) r hr
  refine le_of_eq_of_le (tsum_congr fun H => congrArg (_ * ·)
    (outLaw_seTwoKF_absorbTab B rel enc dummyS keys Q A _ H _)) ?_
  unfold seAlgKF
  erw [winTestProb_mapOut']
  refine le_of_le_of_eq ?_ (Alg.toOuterMeasure_realLaw_eq_tsum _ (outEquiv k e)
    fun v G => SPBCS.Wins (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
        A).toTPKindAlg ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q Qs
        (stmtX ∘ Prod.fst)
        ((outEquiv k e).symm ∘ G) v ∧
      okAtKF (rel := rel) (enc := enc) (dummyS := dummyS) prf checkX freshX keys Q A
        (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          A).toTPKindAlg ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q v).1).symm
  refine ENNReal.tsum_le_tsum fun H =>
    mul_le_mul_of_nonneg_left (MeasureTheory.measure_mono ?_) zero_le
  rintro o ⟨v, hv, hw, hf⟩
  refine ⟨v, hv, ?_⟩
  have hH : (outEquiv k e).symm ∘ (outEquiv k e) ∘ H = H := by
    funext x
    simp
  rw [hH]
  obtain ⟨hck, ⟨π, hπ, hacc⟩, hfr⟩ := hw
  refine ⟨⟨fun x' hx' => ?_, ?_⟩, Option.isSome_iff_exists.2 ⟨π, Option.mem_def.1 hπ⟩, hck, hfr⟩
  · have hq := KindAlg.map_request_history_stateAt (seAlgKF (rel := rel) (enc := enc)
      (dummyS := dummyS) prf keys Q A).toTPKindAlg
      (simExtChallenger ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q) v.chal
      (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A).toTPKindAlg.slots
    unfold SPBCS.queried at hx'
    rw [hq] at hx'
    exact hf x' hx'
  · have h := accepts_of_acceptedKF hb hacc
    change M.Accepts _ (claimOfOutX prf _).stmt (claimOfOutX prf _).proof _
    have hg : ∀ o : Option M.NIProof, o = some π → o.getD default = π :=
      fun o ho => by rw [ho, Option.getD_some]
    rw [← hg _ hπ] at h
    exact h

/-! ### Simulation extraction -/

omit [Inhabited M.NIProof] [∀ j i, Nonempty ((P j).Challenge i)]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- **The simulator inert on dummy statements assigns only at the keys of its chain inputs** when
the simulator does. -/
theorem simAssignsAtKeys_inertOnDummy {C : Type} (isDummy : X₀ → Bool)
    (Sim : NARG.Simulator Xq (XOut k e) X₀ (M.Response b) (SaltedCoins (FiatShamirSalt kS) C))
    (p₀ : M.Response b) (hA : M.SimAssignsAtKeys b Sim id) :
    M.SimAssignsAtKeys b (inertOnDummy isDummy Sim p₀) id := by
  intro r c G qa hqa
  simp only [inertOnDummy] at hqa ⊢
  split_ifs at hqa ⊢ with h
  · exact nomatch hqa
  · exact hA r c G qa hqa

/-- **The query-bounded adversary of the simulation-extraction step** at the key coins `keys`:
`seAlgKF` on each auxiliary value of the `t`-query adversary `A'`. -/
noncomputable def seAdversaryKF (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins)
    (Q : ℕ)
    (A' : QueryBoundedAdversary Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) (Frg × X₀)
      t) :
    M.QBSimExtractionAdversary b (Stmt × (MUR ⊕ R)) t where
  Aux := A'.Aux
  aux := A'.aux
  sh a := seAlgKFS (Stmt := Stmt) (A'.sh a)
  alg a := seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a)
  tracePreserving a := AdaptiveIAlg.mapOut_tracePreserving
    (AdaptiveIAlg.absorbTab_tracePreserving _ _ (A'.tracePreserving a) _) _
  withinBudget a := AdaptiveIAlg.mapOut_withinBudget
    (AdaptiveIAlg.absorbTab_withinBudget (A'.alg a)
      (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q) (b :=
        fun _ => keyReplyNone B keys)
      (fun lg j _ q _ _ => AdaptiveIAlg.tabAt_outerCount_const _ _ _ lg j q)
      (fun _ _ _ h => congrArg Prod.snd h) (A'.withinBudget a)) _
  queries_le a := A'.queries_le a

/-- The shape of `seAdversaryKF` at `a` is `seAlgKFS` of `A'`'s shape. -/
@[simp] theorem seAdversaryKF_sh (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (A' : QueryBoundedAdversary Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) (Frg × X₀)
      t) (a : A'.Aux) :
    (seAdversaryKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A').sh a =
      seAlgKFS (Stmt := Stmt) (A'.sh a) :=
  rfl

/-- **The forger's win in one extraction run** of the simulation-extraction step, on the measured
registers `c` and the database `D`: some witness the database extractor `Ext` returns for the
adversary's explicit statement `x₀`, read through `wit`, satisfies the goal `Goal` at the output
and the first `Q` logged requests. -/
def forgerWinsKF [DecidableEq X₀] {SC' WitK W : Type} [Fintype SC'] [DecidableEq SC']
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (Goal : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A) Psim Q)
    (D : DB Xq (Out k e)) : Prop :=
  ∃ w ∈ M.dbExtractBits Ext (A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
      (dummyS := dummyS) prf keys Q A).toTPKindAlg Psim Q c).1.1.work).2 D,
    Goal (A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A).toTPKindAlg Psim Q c).1.1.work)
      ((Quantum.requests (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc)
        (dummyS := dummyS) prf keys Q A).toTPKindAlg Psim Q c).1.1.logs).take Q)
      (wit (A.out (SPBCS.advWorkspace (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf
        keys Q A).toTPKindAlg Psim Q c).1.1.work).2 w)


omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The forger wins at a disjunction of goals exactly when it wins at one of them.** -/
theorem forgerWinsKF_or [DecidableEq X₀] {SC' WitK W : Type} [Fintype SC'] [DecidableEq SC']
    (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (G₁ G₂ : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (c : SPBCS.Reg (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A) Psim Q)
    (D : DB Xq (Out k e)) :
    forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit
        (fun p rs w => G₁ p rs w ∨ G₂ p rs w) c D ↔
      forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit G₁ c D ∨
        forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit G₂ c
          D := by
  unfold forgerWinsKF
  constructor
  · rintro ⟨w, hw, h | h⟩
    · exact Or.inl ⟨w, hw, h⟩
    · exact Or.inr ⟨w, hw, h⟩
  · rintro (⟨w, hw, h⟩ | ⟨w, hw, h⟩)
    · exact ⟨w, hw, Or.inl h⟩
    · exact ⟨w, hw, Or.inr h⟩

omit [Inhabited M.NIProof] in
/-- **A fresh extracted witness passing the test is a win of the forger**, when a witness of the
relation at a checked fresh output gives the goal (`hgoal`). -/
theorem extractFreshTestProb_le_KF [DecidableEq X₀] {SC' WitK W : Type} [Fintype SC']
    [DecidableEq SC'] [Inhabited M.NIProof] (prf : Frg → Option M.NIProof)
    (checkX : X₀ → Frg → Bool) (freshX : Frg × X₀ → List (MUR ⊕ R) → Prop)
    (keys : Fin n → B.KeyCoins) (Q kq : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (fx : Stmt × (MUR ⊕ R) → X₀) {relK : Set (X₀ × WitK)} (Ext : CausalExtractor P τ X₀ WitK)
    (wit : X₀ → WitK → W) (Goal : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (hgoal : ∀ p rs w, checkX p.2 p.1 = true → freshX p rs → (p.2, w) ∈ relK →
      Goal p rs (wit p.2 w)) :
    extractFreshTestProb Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A)
        Psim Q kq fx relK Ext
        (okAtKF (rel := rel) (enc := enc) (dummyS := dummyS) prf checkX freshX keys Q A) ≤
      simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A) Psim Q kq)
        (forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit
          Goal) := by
  refine simProb_mono _ _ fun c D ⟨hx, _, hok⟩ => ?_
  obtain ⟨w, hw, hrel⟩ := (extractsAt_dbExtractBits_iff M relK Ext).2 hx
  exact ⟨w, hw, hgoal _ _ _ hok.2.1 hok.2.2 hrel⟩

include hb in
/-- **Simulation extraction in the key-free route** (`weak_online_simulation_extractability_qrom`
with a query-free test, `SPBCS.WeakOnlineSimulationExtractable.unruhSimExtraction_of_queryFreeTest`,
and `extractFreshTestProb_le_KF`): averaged over the auxiliary input, the simulation-extraction
game of `seAlgKF` with the test `okAtKF` is at most the forger's win in the extraction run plus
`simExtractionError`, for a simulator `Sim` assigning only at the keys of its chain inputs, inert
on the dummy statements. -/
theorem winTestProb_le_forgerWinsKF [DecidableEq X₀] {C WitK W : Type} [Fintype C]
    [DecidableEq (SaltedCoins (FiatShamirSalt kS) C)] (prf : Frg → Option M.NIProof)
    (checkX : X₀ → Frg → Bool) (freshX : Frg × X₀ → List (MUR ⊕ R) → Prop)
    (stmtX : Stmt → X₀) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    (A' : QueryBoundedAdversary Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b) (Frg × X₀)
      t)
    (Sim : NARG.Simulator Xq (XOut k e) X₀ (M.Response b) (SaltedCoins (FiatShamirSalt kS) C))
    (p₀ : M.Response b) (hA : M.SimAssignsAtKeys b Sim id)
    {relK : Set (X₀ × WitK)} {Ext : CausalExtractor P τ X₀ WitK} {St : CausalStateFn P τ X₀}
    {ε : ChIdx P τ → NNReal} (hrbr : CausalRBRKnowledgeSound relK Vr Ext St ε)
    (wit : X₀ → WitK → W) (Goal : Frg × X₀ → List (MUR ⊕ R) → W → Prop)
    (hgoal : ∀ p rs w, checkX p.2 p.1 = true → freshX p rs → (p.2, w) ∈ relK →
      Goal p rs (wit p.2 w)) :
    ∑' a, A'.aux a * winTestProb Qs
        (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a))
        ((inertOnDummy isDummy Sim p₀).comap (stmtX ∘ Prod.fst)) Q (stmtX ∘ Prod.fst)
        (okAtKF (rel := rel) (enc := enc) (dummyS := dummyS) prf checkX freshX keys Q
          (A'.alg a)) ≤
      ∑' a, A'.aux a * simProb (outEquiv k e)
          (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a))
            ((inertOnDummy isDummy Sim p₀).comap (stmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
          (forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a)
            ((inertOnDummy isDummy Sim p₀).comap (stmtX ∘ Prod.fst)) Ext wit Goal) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε) Sim.q t Q := by
  have hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kqOf Mg nr b b :=
    fun _ _ _ hv => queries_length_le_of_formatBounds hb hv
  have hse := (weak_online_simulation_extractability_qrom (B := b) Qs hkq hrbr
    (inertOnDummy isDummy Sim p₀)
    (simAssignsAtKeys_inertOnDummy isDummy Sim p₀ hA)).unruhSimExtraction_of_queryFreeTest hkq
  exact (hse (Stmt × (MUR ⊕ R)) (stmtX ∘ Prod.fst) t Q
    (seAdversaryKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A')
    fun a => okAtKF (rel := rel) (enc := enc) (dummyS := dummyS) prf checkX freshX keys Q
      (A'.alg a)).trans
    (add_le_add (ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left
      (extractFreshTestProb_le_KF prf checkX freshX keys Q _ (A'.alg a) _ _ Ext wit Goal hgoal)
      zero_le) le_rfl)

omit [∀ j i, Nonempty ((P j).Challenge i)] in
/-- **The forger's win as an extraction run of the table form**: the extraction run of the
simulation-extraction adversary `seAlgKF` (`extAdv`) is the extraction run (`extRun`) of the
adversary at the table `keyReplyNone keys` through `seTwoKF`, with the expansion and the win read
through the reinsertion of the table (`insertTabM`) and the default with the table dropped, so
that only the table holds key coins. -/
theorem simProb_extAdv_seAlgKF_eq [DecidableEq X₀] {SC' WitK W : Type} [Fintype SC']
    [DecidableEq SC'] (prf : Frg → Option M.NIProof) (keys : Fin n → B.KeyCoins) (Q : ℕ)
    {shA : AlgShape Xq (XOut k e) (MUR ⊕ R) (MUResponse B.core ⊕ M.Response b)} (A : AdaptiveIAlg shA (Frg × X₀))
    (Psim : NARG.Simulator Xq (XOut k e) (Stmt × (MUR ⊕ R)) (M.Response b) SC')
    (Ext : CausalExtractor P τ X₀ WitK) (wit : X₀ → WitK → W)
    (Goal : Frg × X₀ → List (MUR ⊕ R) → W → Prop) (kq : ℕ) :
    simProb (outEquiv k e)
        (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A) Psim Q kq)
        (forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit
          Goal) =
      simProb (outEquiv k e) (extRun (outEquiv k e) A (simExtChallenger Psim Q)
          (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
          ⟨fun r => (simExtractionExpansion (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS)
            prf keys Q A).toTPKindAlg Psim Q Qs).next (Quantum.AdaptiveIAlg.insertTabM A
              (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel enc dummyS
                (B.pk ∘ keys) Q)
              (fun _ => keyReplyNone B keys) (claimOfOutX prf) r)⟩
          (kq + Q * Psim.q)
          (Quantum.AdaptiveIAlg.dropTabM A (simExtChallenger Psim Q)
            (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
              (fun _ => keyReplyNone B keys)
            (claimOfOutX prf)
            (((seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
              A).toTPKindAlg.composeBothOut
              (simExtChallenger Psim Q) id).defaultOut))
          (fun _ => keyReplyNone B keys))
        (fun r D => forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim
          Ext wit Goal (Quantum.AdaptiveIAlg.insertTabM A (simExtChallenger Psim Q)
            (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
              (fun _ => keyReplyNone B keys)
            (claimOfOutX prf) r) D) :=
  Quantum.AdaptiveIAlg.simProb_expandAdv_mapOut_cross
    (A.absorbTab (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
      (fun _ => keyReplyNone B keys)) (claimOfOutX prf) (simExtChallenger Psim Q)
    (simExtractionExpansion (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
      A).toTPKindAlg Psim Q Qs)
    (kq + Q * Psim.q)
    (((seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A).toTPKindAlg.composeBothOut
      (simExtChallenger Psim Q) id).defaultOut)
    (forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q A Psim Ext wit Goal)
    (dropTabCW A (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel enc dummyS
      (B.pk ∘ keys) Q)
      (fun _ => keyReplyNone B keys))
    (Quantum.AdaptiveIAlg.insertTabM A (simExtChallenger Psim Q)
      (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
        (fun _ => keyReplyNone B keys)
      (claimOfOutX prf))
    (extOut A (simExtChallenger Psim Q) (seTwoKF (Proof := M.Response b) B rel enc dummyS
      (B.pk ∘ keys) Q)
      (Quantum.AdaptiveIAlg.dropTabM A (simExtChallenger Psim Q)
        (seTwoKF (Proof := M.Response b) B rel enc dummyS (B.pk ∘ keys) Q)
          (fun _ => keyReplyNone B keys)
        (claimOfOutX prf)
        (((seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q
          A).toTPKindAlg.composeBothOut
          (simExtChallenger Psim Q) id).defaultOut))
      (fun _ => keyReplyNone B keys))
    (fun o => by cases o <;> rfl)
    (fun c => SPBCS.simExtractionExpansion_mapOut_next_congr Qs _ (claimOfOutX prf) Psim Q _ c
      rfl rfl)
    (fun _ _ => Iff.rfl)

end SPBCS

end RingSignature.KeyFree

end GordieHowe
