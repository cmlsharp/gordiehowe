-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.KeyFreeSE
public import GordieHowe.Applications.Ring.KeyFreeZK

@[expose] public section

/-!
# The key-free route's chain against the main challenger

The second half of the key-free unforgeability route at the level of an adversary `A'` against
the main challenger `kfMain` (`GordieHowe/Applications/Ring/KeyFreeMain.lean`) whose output
`(o, x₀)` carries the forgery `o` and its explicit statement `x₀`: the zero-knowledge hop
(`acceptKAt_kfMain_le`, `GordieHowe/Applications/Ring/KeyFreeZK.lean`), the simulated game as
the simulation-extraction game (`sim_le_winTestProbKF`) and simulation extraction
(`winTestProb_le_forgerWinsKF`, both `GordieHowe/Applications/Ring/KeyFreeSE.lean`), composed
for the classical test `kfWinTest` of a key-free win.

- `freshXKF`: no logged proof query with a statement that is not a dummy statement has the
  statement `x₀` (it reads statements only).
- `honestKF`: every key of the claim's ring belongs to a user whose corruption was not logged.
- `kfFresh`: `freshXKF`, `honestKF` and a caller-supplied side condition at an auxiliary value
  `ω`.
- `kfWinTest`, `kfWinTest_queriesLE`, `run_kfWinTest`: the test of a key-free win at `ω`, the
  compiled verifier's queries on the claim followed by the check and `kfFresh`; it accepts exactly
  on `WinsKF` with `kfFresh` at `ω`.
- `acceptKAt_kfMainSim_le_winTestProb`: at one auxiliary value, the test against the simulated
  main challenger is at most the simulation-extraction game of `seAlgKF`.
- `acceptKAt_kfMain_le_winTestProb`: at one auxiliary value, the test against `kfMain` is at most
  the simulation-extraction game of `seAlgKF` plus `zkError δ t Q`.
- `kfChainAt_le` (**the chain**): averaged over the auxiliary input, the test against `kfMain`
  is at most the forger's win in the extraction run plus `simExtractionError` and
  `zkError δ t Q`.
-/

namespace GordieHowe

open Quantum Signature
open scoped ENNReal

namespace RingSignature.KeyFree

open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm RingSignature.Insider

section SPBCS

variable {k kN kS L e N n t : ℕ} {Xb Yb : Type} [DecidableEq Xb] [DecidableEq Yb]
  {TS : Signature.SchemeTypes} {RMsg : Type} [Fintype TS.PK] [DecidableEq TS.PK]
  [Fintype TS.BSig] [DecidableEq TS.BSig]
  [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins]
  {B : BaseSigner Xb Yb N TS RMsg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {X₀ Wit₀ : Type} {M : SPBCS Mg P X₀ k kN kS L e} {Λ : SiteLayout Mg} {b : ℕ}
  {E : (j : ι) → (M.comp j).Encoder}
  {Vr : X₀ → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {R : Type} [Fintype R] [DecidableEq R] [Nonempty R] {honest : Wit₀ → R → CausalProver P τ X₀}
  {Stmt Wit Rq Frg : Type} {rel : Stmt → Wit → Prop}
  {enc : MURequest (SignOracle.none B.core) n ⊕ Rq → ProofQuery Stmt Wit} {stmtX : Stmt → X₀}

local notation "Xq" => Bits (queryBits k kN kS L)

local notation "MUR" => MURequest (SignOracle.none B.core) n

variable (enc stmtX) in
/-- **The freshness of the key-free route**: no logged proof query `q` in `rs` whose statement is
not a dummy statement (`isDummy`) has the statement `x₀` of the output `p = (o, x₀)`. It reads
only the statements of the logged requests, not their witnesses. -/
def freshXKF (isDummy : X₀ → Bool) (p : Frg × X₀) (rs : List (MUR ⊕ Rq)) : Prop :=
  ∀ q, .inr q ∈ rs → isDummy (stmtX (enc (.inr q)).stmt) = false → stmtX (enc (.inr q)).stmt ≠ p.2

/-- **The honest ring of the key-free route** (Bender, Katz, Morselli 2006, Def. 7, the ring of
the forgery made of honest keys; `Fresh.honest_ring`,
`GordieHowe/Model/RingSignature/Unforgeability.lean`): every key of the ring of the claim's
ring statement `fstX x₀` is the public key `pks i` of a user `i` whose corruption is not among
the logged requests `rs`. -/
def honestKF (pks : Fin n → B.PK) (fstX : X₀ → RingStmt B)
    (p : Frg × X₀) (rs : List (MUR ⊕ Rq)) : Prop :=
  ∀ pk ∈ (fstX p.2).ring.1, ∃ i, pks i = pk ∧ (.inl (.corrupt i) : MUR ⊕ Rq) ∉ rs

variable (enc stmtX) in
/-- **The win condition on the logged requests**: the freshness `freshXKF`, the honest ring
`honestKF` and the caller's side condition `side` at the auxiliary value `ω`. The side condition
should read only the statements and tags of the logged requests and `ω`; nothing here enforces
that. -/
def kfFresh {Ω : Type} (isDummy : X₀ → Bool) (pks : Fin n → B.PK) (fstX : X₀ → RingStmt B)
    (side : Ω → Frg × X₀ → List (MUR ⊕ Rq) → Prop) (ω : Ω) (p : Frg × X₀)
    (rs : List (MUR ⊕ Rq)) : Prop :=
  freshXKF enc stmtX isDummy p rs ∧ honestKF pks fstX p rs ∧ side ω p rs

variable (M b Qs enc stmtX) in
/-- **The test of a key-free win** at the auxiliary value `ω`, the output `p = (o, x₀)` and the
logged requests `rs`: with no proof in `o` it rejects; otherwise it runs the compiled verifier's
program on the claim `⟨x₀, π⟩` (its `kq` queries, answers read through `outEquiv`), then checks
`checkX x₀ o` and decides `kfFresh` (the freshness, the honest ring and the side condition) at
the first `Q` logged requests, classically.

Running time: the verifier's `kq` queries and decision (`NARG.Verifier.prog`), the check, and a
scan of the logged requests. This running time is argued here, not proved in Lean. -/
noncomputable def kfWinTest {Ω : Type} (isDummy : X₀ → Bool) (pks : Fin n → B.PK)
    (fstX : X₀ → RingStmt B) (side : Ω → Frg × X₀ → List (MUR ⊕ Rq) → Prop)
    (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool) (Q : ℕ) (ω : Ω)
    (p : Frg × X₀) (rs : List (MUR ⊕ Rq)) : OracleProg Xq (XOut k e) Bool :=
  open Classical in
  match prf p.1 with
  | none => .pure false
  | some π => (((M.qVerifier Qs b b).prog ⟨p.2, π⟩).mapQuery id (outEquiv k e)).bind fun v =>
      .pure (v && (checkX p.2 p.1 &&
        decide (kfFresh enc stmtX isDummy pks fstX side ω p (rs.take Q))))

omit [DecidableEq Xb] [DecidableEq Yb] [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- The test of a key-free win makes at most the verifier's `kq` queries. -/
theorem kfWinTest_queriesLE {Ω : Type} (isDummy : X₀ → Bool) (pks : Fin n → B.PK)
    (fstX : X₀ → RingStmt B) (side : Ω → Frg × X₀ → List (MUR ⊕ Rq) → Prop)
    (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool) (Q : ℕ) (ω : Ω)
    (p : Frg × X₀) (rs : List (MUR ⊕ Rq)) :
    (kfWinTest M b Qs enc stmtX isDummy pks fstX side prf checkX Q ω p rs).QueriesLE
      (M.qVerifier Qs b b).kq := by
  intro G
  unfold kfWinTest
  cases prf p.1 with
  | none => simp [OracleProg.trace]
  | some π =>
    simp only [OracleProg.trace_bind, OracleProg.trace_pure, List.append_nil,
      OracleProg.length_trace_mapQuery]
    exact NARG.Verifier.prog_queriesLE _ _ _

omit [DecidableEq Xb] [DecidableEq Yb] [Fintype TS.PK] [DecidableEq TS.PK] [Fintype TS.BSig]
  [DecidableEq TS.BSig] [Fintype TS.KeyCoins] [DecidableEq TS.KeyCoins] in
/-- **The test of a key-free win accepts exactly on a key-free win** (`WinsKF` with the
condition `kfFresh` at `ω`) at the oracle read through `outEquiv`. -/
theorem run_kfWinTest {Ω : Type} (isDummy : X₀ → Bool) (pks : Fin n → B.PK)
    (fstX : X₀ → RingStmt B) (side : Ω → Frg × X₀ → List (MUR ⊕ Rq) → Prop)
    (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool) (Q : ℕ) (ω : Ω)
    (p : Frg × X₀) (rs : List (MUR ⊕ Rq)) (G : Xq → XOut k e) :
    (kfWinTest M b Qs enc stmtX isDummy pks fstX side prf checkX Q ω p rs).run G = true ↔
      WinsKF (Qs := Qs) (b := b) prf checkX
        (kfFresh enc stmtX isDummy pks fstX side ω) Q p rs (outEquiv k e ∘ G) := by
  classical
  unfold kfWinTest WinsKF
  cases h : prf p.1 with
  | none => simp [OracleProg.run]
  | some π =>
    rw [OracleProg.run_bind, OracleProg.run_mapQuery]
    simp only [OracleProg.run, Bool.and_eq_true, decide_eq_true_eq, NARG.Verifier.run_prog,
      Option.mem_def, Option.some.injEq, exists_eq_left']
    tauto

/-! ### The chain -/

variable [DecidableEq X₀] [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype Stmt]
  [DecidableEq Stmt] [Inhabited Stmt] [Fintype Wit] [DecidableEq Wit]
  [Inhabited (ProofQuery Stmt Wit)] [Fintype Rq] [DecidableEq Rq] [Inhabited Rq] [DecidableRel rel]
  [Inhabited M.NIProof] {dummyS : Stmt} {isDummy : X₀ → Bool}
  (A' : QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
    (MURequest (SignOracle.none B.core) n ⊕ Rq) (MUResponse B.core ⊕ M.Response b) (Frg × X₀) t)

omit [DecidableEq X₀] [Fintype Wit] [DecidableEq Wit] [Inhabited (ProofQuery Stmt Wit)] in
include A' in
/-- **The simulated key-free game as the simulation-extraction game at one auxiliary value**
(`sim_le_winTestProbKF` with `run_kfWinTest`): the test of a key-free win at `ω` against the
simulated main challenger of the simulator `S` read at `stmtX` is at most the
simulation-extraction game of `seAlgKF` with the test `okAtKF` of `kfFresh` at `ω`, against the
simulator inert on dummy statements, under the dummy-statement hypotheses (`hd`) and dummy
statements that differ from every checked statement (`hdisj`). The freshness hypothesis of
`sim_le_winTestProbKF` holds by the definition of `freshXKF`, as no dummy statement is in the
relation. -/
theorem acceptKAt_kfMainSim_le_winTestProb (hb : M.FormatBounds Qs b b)
    (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool)
    (hd : DummyStmts B rel enc dummyS stmtX isDummy)
    (hdisj : ∀ x, isDummy x = true → ∀ p : Frg × X₀, checkX p.2 p.1 = true → x ≠ p.2)
    {Ω : Type} (pks : Fin n → B.PK) (fstX : X₀ → RingStmt B)
    (side : Ω → Frg × X₀ → List (MUR ⊕ Rq) → Prop) (ω : Ω)
    {SC : Type} [Fintype SC] [DecidableEq SC]
    (S : NARG.Simulator Xq (XOut k e) X₀ (M.Response b) SC) (p₀ : M.Response b)
    (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux) :
    acceptKAt A' (kfWinTest M b Qs enc stmtX isDummy pks fstX side prf checkX Q ω)
        (kfMainSim B rel (S.comap stmtX) enc keys Q) a ≤
      winTestProb Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a))
        ((inertOnDummy isDummy S p₀).comap (stmtX ∘ Prod.fst)) Q (stmtX ∘ Prod.fst)
        (okAtKF (rel := rel) (enc := enc) (dummyS := dummyS) prf checkX
          (kfFresh enc stmtX isDummy pks fstX side ω) keys Q (A'.alg a)) := by
  unfold acceptKAt
  simp_rw [run_kfWinTest]
  refine sim_le_winTestProbKF hb prf checkX _ stmtX hd hdisj (fun _ _ h q hq hr => h.1 q hq ?_) S
    p₀ keys Q (A'.alg a)
  cases hdq : isDummy (stmtX (enc (.inr q)).stmt)
  · rfl
  · exact absurd hr (hd.not_rel _ hdq _)

omit [DecidableEq X₀] in
/-- **The key-free game as the simulation-extraction game at one auxiliary value**
(`acceptKAt_kfMain_le`, then `acceptKAt_kfMainSim_le_winTestProb`): the test of a key-free win
at `ω` against `kfMain` with the compiled spBCS prover is at most the simulation-extraction game
of `seAlgKF` against the spBCS joint simulator inert on dummy statements, plus
`zkError δ t Q`. -/
theorem acceptKAt_kfMain_le_winTestProb (hb : M.FormatBounds Qs b b)
    {fw : Wit → Wit₀} {relH : Set (X₀ × Wit₀)} (hrel : ∀ x w, rel x w ↔ (stmtX x, fw w) ∈ relH)
    (henc : Function.Injective enc) (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool)
    (hd : DummyStmts B rel enc dummyS stmtX isDummy)
    (hdisj : ∀ x, isDummy x = true → ∀ p : Frg × X₀, checkX p.2 p.1 = true → x ≠ p.2)
    {Ω : Type} (pks : Fin n → B.PK) (fstX : X₀ → RingStmt B)
    (side : Ω → Frg × X₀ → List (MUR ⊕ Rq) → Prop) (ω : Ω)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub) (Sim : CausalJointSimulator VE.MV Pub)
    (T : M.Preimages) {δ : NNReal} (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    (p₀ : M.Response b) (keys : Fin n → B.KeyCoins) (Q : ℕ) (a : A'.Aux) :
    acceptKAt A' (kfWinTest M b Qs enc stmtX isDummy pks fstX side prf checkX Q ω)
        (kfMain B rel ((encProver M Λ E hb honest).comap stmtX fw) (PMF.uniformOfFintype _) enc keys Q) a ≤
      winTestProb Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a))
        ((inertOnDummy isDummy (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T) p₀).comap
          (stmtX ∘ Prod.fst)) Q (stmtX ∘ Prod.fst)
        (okAtKF (rel := rel) (enc := enc) (dummyS := dummyS) prf checkX
          (kfFresh enc stmtX isDummy pks fstX side ω) keys Q (A'.alg a)) +
        ENNReal.ofReal (M.zkError δ t Q) :=
  (acceptKAt_kfMain_le A' _ hrel henc (fun r => hd.not_rel _ (hd.inl r) _)
    (kfWinTest_queriesLE (M := M) (b := b) (Qs := Qs) (enc := enc) (stmtX := stmtX)
      isDummy pks fstX side prf checkX Q ω) VE pub Sim T hvzk keys Q a).trans
    (add_le_add (acceptKAt_kfMainSim_le_winTestProb A' hb prf checkX hd hdisj pks fstX side ω _
      p₀ keys Q a) le_rfl)

/-- **The key-free route's chain**: averaged over the auxiliary input, the adversary `A'` against
the main challenger `kfMain` with the compiled spBCS prover passes the test of a key-free win at
`ω` (`kfWinTest`) with at most the probability of the forger's win (`forgerWinsKF` at the goal
`Goal ω`) in the extraction run of `seAlgKF` against the spBCS joint simulator inert on dummy
statements, plus `simExtractionError` and `zkError δ t Q`. The hypotheses: the relation `rel` is
`relH` read through `stmtX` and `fw` (`hrel`); `enc` is injective (`henc`); the dummy statements
satisfy `DummyStmts` (`hd`) and differ from every checked statement (`hdisj`); the composite is
honest-verifier zero knowledge for `relH` (`hvzk`) and round-by-round knowledge sound for `relK`
(`hrbr`); digests have at least one byte (`hk`); a witness of `relK` at a checked output with
`kfFresh` at `ω` (the freshness, the honest ring and the side condition `side`) gives the goal
(`hgoal`). The side condition is the caller's; it should read only statements, tags and `ω`, and
nothing here enforces that. -/
theorem kfChainAt_le (hk : 0 < k) (hb : M.FormatBounds Qs b b)
    {fw : Wit → Wit₀} {relH : Set (X₀ × Wit₀)} (hrel : ∀ x w, rel x w ↔ (stmtX x, fw w) ∈ relH)
    (henc : Function.Injective enc) (prf : Frg → Option M.NIProof) (checkX : X₀ → Frg → Bool)
    (hd : DummyStmts B rel enc dummyS stmtX isDummy)
    (hdisj : ∀ x, isDummy x = true → ∀ p : Frg × X₀, checkX p.2 p.1 = true → x ≠ p.2)
    {Ω : Type} (pks : Fin n → B.PK) (fstX : X₀ → RingStmt B)
    (side : Ω → Frg × X₀ → List (MUR ⊕ Rq) → Prop) (ω : Ω)
    (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : X₀ → Pub) (Sim : CausalJointSimulator VE.MV Pub)
    (T : M.Preimages) {δ : NNReal} (hvzk : CausalHVZK VE.MV relH honest pub Sim δ)
    {WitK W : Type} {relK : Set (X₀ × WitK)} {Ext : CausalExtractor P τ X₀ WitK}
    {St : CausalStateFn P τ X₀} {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound relK Vr Ext St ε) (wit : X₀ → WitK → W)
    (Goal : Ω → Frg × X₀ → List (MUR ⊕ Rq) → W → Prop)
    (hgoal : ∀ p rs w, checkX p.2 p.1 = true → kfFresh enc stmtX isDummy pks fstX side ω p rs →
      (p.2, w) ∈ relK → Goal ω p rs (wit p.2 w))
    (p₀ : M.Response b) (keys : Fin n → B.KeyCoins) (Q : ℕ) :
    acceptK A' (kfWinTest M b Qs enc stmtX isDummy pks fstX side prf checkX Q ω)
        (kfMain B rel ((encProver M Λ E hb honest).comap stmtX fw) (PMF.uniformOfFintype _) enc keys Q) ≤
      ∑' a, A'.aux a * simProb (outEquiv k e)
          (extAdv Qs (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a))
            ((inertOnDummy isDummy (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T)
              p₀).comap (stmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
          (forgerWinsKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a)
            ((inertOnDummy isDummy (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T)
              p₀).comap (stmtX ∘ Prod.fst)) Ext wit (Goal ω)) +
        M.simExtractionError (kqOf Mg nr b b) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T).q t Q +
        ENNReal.ofReal (M.zkError δ t Q) := by
  unfold acceptK
  calc _ ≤ ∑' a, (A'.aux a * winTestProb Qs
          (seAlgKF (rel := rel) (enc := enc) (dummyS := dummyS) prf keys Q (A'.alg a))
          ((inertOnDummy isDummy (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T) p₀).comap
            (stmtX ∘ Prod.fst)) Q (stmtX ∘ Prod.fst)
          (okAtKF (rel := rel) (enc := enc) (dummyS := dummyS) prf checkX
            (kfFresh enc stmtX isDummy pks fstX side ω) keys Q (A'.alg a)) +
          A'.aux a * ENNReal.ofReal (M.zkError δ t Q)) :=
        ENNReal.tsum_le_tsum fun a => by
          rw [← mul_add]
          exact mul_le_mul_of_nonneg_left (acceptKAt_kfMain_le_winTestProb A' hb hrel henc prf
            checkX hd hdisj pks fstX side ω VE pub Sim T hvzk p₀ keys Q a) zero_le
    _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := add_le_add (winTestProb_le_forgerWinsKF hb prf checkX _ stmtX keys Q A'
        (M.niJointSimulatorProg Λ VE.toViewRead b pub Sim T) p₀
        (simAssignsAtKeys_niJointSimulatorProg hk Λ VE b pub Sim T) hrbr wit (Goal ω) hgoal)
        le_rfl

end SPBCS

end RingSignature.KeyFree

end GordieHowe
