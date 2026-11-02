-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1CaseU
public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeBase
public import GordieHowe.Applications.Ring.MLDSAW1OracleFacts

@[expose] public section

/-!
# The key-free chain at the ML-DSA ring publishing `w₁`

The key-free chain (`RingSignature.KeyFree.kfChainFull_le`,
`GordieHowe/Applications/Ring/KeyFreeChainFull.lean`, then
`RingSignature.KeyFree.kfChainAt_le`, `GordieHowe/Applications/Ring/KeyFreeChainAt.lean`) at the
fresh-mask base signer of the ML-DSA ring publishing `w₁`, at fixed users' key coins and side
coins, for the proof system `w1HPS` at a check `chk` accepting only nonempty rings, read at the
fresh statements. The adversary is followed by the program statement of its forgery
(`QueryBoundedAdversary.thenProgOut`, `w1ForgeStmtProg`), and the relay absorbed at each base
component `ω` is the key-free relay in side-read mode (`kfRelaySide`).

- `w1ForgeEv`: the forgery event (a forgery, `Forges`, with no message-representative collision
  at the base oracle, `w1CollRing`).
- `instInhabitedW1Stmt`, `instInhabitedProofQueryW1Stmt`: the main statements and their proof
  queries are inhabited.
- `w1SideRelay`: the key-free relay in side-read mode at the ML-DSA ring publishing `w₁`.
- `allOut_w1StmtProg`: the statement program's outputs read back the ring statement and list one
  hash per member.
- `w1ForgeEv_hE`: the forgery event gives the event hypotheses of the chain.
- `kfGame_le_w1Chain` (**the key-free chain at the ML-DSA ring publishing `w₁`**).
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree
open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] {sp : OracleSplit Y Y₁ (XOut kh e)}
  {prims : Primitives p}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) Y p prims Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] [Nonempty RMsg] [Nonempty (FIPSSignature p prims)]
  {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt prims RMsg N)
    kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {E : (j : ι) → (Mc.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Mc.IOPQueries Vr x} {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (freshBase prims O Mo βmin tol enc k D bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ} [NeZero n]
  {chk : RingSignature.RingStmt (freshBase prims O Mo βmin tol enc k D bmsg) → Bool}

local notation "Xq" => Bits (queryBits kh kN kS L)
local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "X₀f" => W1ExpStmt prims RMsg N
local notation "PSh" => w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk
local notation "PSf" => (PSh)
local notation "Sf" => freshScheme prims O Mo βmin tol enc k D bmsg PSh adm
local notation "Frg" => KeyRing (PubKey p prims) N × RMsg × (BucketVec p × Mc.Response b)

attribute [local instance] admDecF

variable (O sp) in
/-- **The forgery event against the key-free game** at the users' key coins `keys` and the base
oracle `H`, for the output `o`, the answered requests `rs` and the final oracle `G`: `o` is a
forgery (`Forges`) at `G` and the history of `rs`, and no ring signing request collides with a
member's message representative at the base component of `H` (`w1CollRing`). -/
def w1ForgeEv (keys : Fin n → (Bf).KeyCoins) (H : Xq → Y)
    (x : Frg × List (RingSignature.Insider.Req Bf PSf adm n) × (Xq → Y)) : Prop :=
  Forges (S := Sf) (O := SideOracle.none Sf) keys x.2.2 x.1 (Challenger.histOf x.2.1) ∧
    ¬ w1CollRing (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i)) (base sp H) x.1.1
      x.1.2.1 x.2.1

/-- The main statements are inhabited, by the dummy statement `w1DummyS`. -/
noncomputable instance instInhabitedW1Stmt {TPS : PSTypes} {PS : ProofSystem Xq Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS} :
    Inhabited (W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q) :=
  ⟨w1DummyS PS adm n Q⟩

/-- The proof queries of the main statements are inhabited, by the dummy statement `w1DummyS`
and the dummy witness `w1W0`. -/
noncomputable instance instInhabitedProofQueryW1Stmt {TPS : PSTypes} {PS : ProofSystem Xq Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS} :
    Inhabited (ProofQuery (W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q)
      (RingSignature.Insider.RelayWit Bf)) :=
  ⟨⟨w1DummyS PS adm n Q, w1W0 prims O Mo βmin tol enc k D bmsg⟩⟩

variable (sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk) in
/-- **The key-free relay in side-read mode at the ML-DSA ring publishing `w₁`**
(`kfRelaySide`) at the users' key coins `keys`, the side coins `sc` and the base component `ω`:
the signer `w1KFSign` factoring as `w1KFFactors`, the statement program `w1KFStmt`, the proof
requests `w1ToR` and `w1DummyR`, and the idle request `w1Idle`. -/
noncomputable abbrev w1SideRelay (h : W1OracleFacts O Mo sp) (keys : Fin n → (Bf).KeyCoins)
    (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) (ω : Xq → Y₁) :=
  kfRelaySide sp Bf (fun i => (Bf).pk (keys i))
    (w1KFFactors (T := T) prims O sp βmin tol enc k D bmsg h.hO)
    (w1KFStmt prims O Mo βmin tol enc k D bmsg sp)
    (w1ToR (PS := PSh) (adm := adm) (Q := Q)) w1DummyR sc ω w1Idle

omit [Fintype Y] [DecidableEq Y] [Nonempty Y] [NeZero (bucketCount p)] [Nonempty (MaskBox p)]
  [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Nonempty RMsg]
  [Nonempty (FIPSSignature p prims)] [NeZero n] in
/-- **The statement program's outputs** read back its input and carry hash lists of the ring's
length, on every path. -/
theorem allOut_w1StmtProg (x : RingSignature.RingStmtOf (PubKey p prims) RMsg (BucketVec p) N) :
    (w1StmtProg sp prims O bmsg x).AllOut fun x₀ =>
      x₀.1 = x ∧ x₀.2.length = x.ring.1.length :=
  OracleProg.AllOut.mapOutput _ ((allOut_hashesProg_length sp O _ _ _).mono fun _ h => ⟨rfl, h⟩)

omit [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [Nonempty RMsg]
  [Nonempty (FIPSSignature p prims)] [NeZero n] in
/-- **The forgery event gives the event hypotheses of the key-free chain**: for a check `chk`
accepting only nonempty rings, a forgery `o` with no collision (`w1ForgeEv`) whose program
statement `x₀` is the statement program's output at the final oracle `G` has a proof accepted
against the second component of `G` at `x₀`, passes `w1CheckX`, was never signed on its ring and
message, has an honest ring, and meets the ring-level side condition `w1SideRing`. -/
theorem w1ForgeEv_hE (hchk : ∀ x, chk x = true → x.ring.1 ≠ []) (keys : Fin n → (Bf).KeyCoins)
    (H : Xq → Y) (o : Frg) (x₀ : X₀f) (rs : List (RingSignature.Insider.Req Bf PSf adm n))
    (G : Xq → Y) (hEv : w1ForgeEv sp O keys H (o, rs, G))
    (hx : x₀ = (w1ForgeStmtProg sp prims O bmsg Mc o).run G) :
    (∃ π ∈ w1PrfOf o, (Mc.qVerifier Qs b b).Accepted (outEquiv kh e ∘ prf sp G) ⟨x₀, π⟩) ∧
      w1CheckX x₀ o = true ∧ (∀ s, UnforgeRequest.sign s x₀.1.ring x₀.1.msg ∉ rs) ∧
      (∀ pk ∈ x₀.1.ring.1, ∃ i, (Bf).pk (keys i) = pk ∧ UnforgeRequest.corrupt i ∉ rs) ∧
      w1SideRing (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i)) G (base sp H)
        (o, x₀) rs := by
  obtain ⟨R, m, y, π⟩ := o
  obtain ⟨hF, hcoll⟩ := hEv
  have hx' : x₀ = (w1StmtProg sp prims O bmsg ⟨R, m, y⟩).run (base sp G) :=
    hx.trans (OracleProg.run_mapQuery _ _ _ _)
  have hx1 : x₀.1 = ⟨R, m, y⟩ := hx' ▸ ((allOut_w1StmtProg _).run _).1
  have hiff := verify_spbcsSplitProofSystem_eq_true_iff sp Mc Λ E hb honest
      (w1StmtProg sp prims O bmsg) (2 * N)
      (w1StmtProg_queries sp prims O bmsg) chk (fun _ w => some w) G ⟨R, m, y⟩ π
  obtain ⟨hc, c, hcm, hacc⟩ := hiff.1 hF.verify_eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · cases π with
    | none => simp [spbcsSplitClaim] at hcm
    | some q =>
      simp only [spbcsSplitClaim, Option.map_some, Option.mem_def, Option.some.injEq] at hcm
      subst hcm
      exact ⟨q.1, rfl, hx' ▸ hacc⟩
  · simp only [w1CheckX, hx1, decide_true, Bool.true_and, decide_eq_true_eq]
    exact hchk _ hc
  · intro s hs
    rw [hx1] at hs
    exact hF.fresh.not_signQueried ⟨⟨_, none⟩, List.mem_map_of_mem hs, s, rfl⟩
  · intro pk hpk
    rw [hx1] at hpk
    obtain ⟨i, hi, hn⟩ := hF.fresh.honest_ring pk hpk
    exact ⟨i, hi, fun hm => hn ⟨⟨_, none⟩, List.mem_map_of_mem hm, rfl⟩⟩
  · refine w1SideRing_of sp _ G (base sp H) _ rs ⟨R, m, y⟩ ?_ hx
    rw [hx1]
    exact hcoll

/-- **A pointwise bound scaled by a constant**: `f a ≤ w` for every `a` gives `f a · c ≤ w · c`. A
named proof, so the width bounds passed to `thenProgOut` are one term in statements and definitions
(a definition would otherwise abstract an inline proof into its own auxiliary lemma). -/
theorem _root_.GordieHowe.forall_mul_le_mul_right {α : Type*} {f : α → ℕ} {w : ℕ} (c : ℕ)
    (h : ∀ a, f a ≤ w) : ∀ a, f a * c ≤ w * c :=
  fun a => Nat.mul_le_mul_right c (h a)

open Classical in
/-- **The key-free chain at the ML-DSA ring publishing `w₁`**, at the users' key coins `keys` and
the side coins `sc`. For the proof system `w1HPS` at a check `chk` accepting only nonempty rings
(`hchk`), read at the fresh statements, and an adversary `𝒜` of the key-free game (`kfGame` of the
key-free relay of `w1KFSign` over `kfMainFull` with the compiled spBCS prover read through
`w1StmtX`), the forgery event `w1ForgeEv` has, with the oracle `H` uniform, at most the average
over a uniform base component `ω` of the forger's win (`forgerWinsKF` at the goal `w1Goal`) in the
extraction run of `seAlgKF` for `𝒜` followed by the program statement of its forgery
(`w1ForgeStmtProg`, `2N` queries in batches of `𝒜`'s width, at most `w`), with the relay
`w1SideRelay` at `ω` absorbed, plus `simExtractionError` and `zkError` at
`t + w · 2N + Q + Q` queries.

Hypotheses: digests have at least one byte (`hk`); the oracle facts of the ring (`h`); the
composite is honest-verifier zero knowledge for `w1ExpRel` (`hvzk`) and round-by-round knowledge
sound for `w1ExpRel` (`hrbr`). -/
theorem kfGame_le_w1Chain [Inhabited Mc.NIProof]
    [DecidableRel (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)]
    (hk : 0 < kh) (hchk : ∀ x, chk x = true → x.ring.1 ≠ []) (h : W1OracleFacts O Mo sp)
    (keys : Fin n → (Bf).KeyCoins) (sc : Fin Q → KFCoins (p := p) (T := T) k D Y₁) {t w : ℕ}
    (𝒜 : QueryBoundedAdversary Xq Y (RingSignature.Insider.Req Bf PSf adm n)
      (RingSignature.Insider.Resp Bf PSf adm) Frg t) (hw : ∀ a, (𝒜.alg a).width ≤ w)
    (VE : Mc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Mc.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel prims enc bmsg adm) honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel prims enc bmsg adm) Vr Ext St ε)
    (p₀ : Mc.Response b) :
    ∑' H, PMF.uniformOfFintype (Xq → Y) H *
        (𝒜.assignLaw (kfGame (kfMainFull sp Bf (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
          ((RingSignature.Insider.encProver Mc Λ E hb honest).comap w1StmtX
            (RingSignature.Insider.RelayWit.toWit (B := Bf)))
          (w1Enc fun i => (Bf).pk (keys i)) keys Q)
          (kfRelay (PS := PSf) Bf (fun i => (Bf).pk (keys i))
            (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (w1StmtP sp)
            (w1ToR (PS := PSh) (adm := adm) (Q := Q)) (w1DummyR (PS := PSh) (adm := adm) (Q := Q))
            sc (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg)
            (w1StmtP_queries sp) w1Idle) Q) H).toOuterMeasure
          {x | ∃ q ∈ x, w1ForgeEv sp O keys H q} ≤
      ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
        (∑' a, ((((𝒜.thenProgOut (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                (forall_mul_le_mul_right _ hw)).absorbAssign (PMF.pure ())
              (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk h
                keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
              Prod.fst).aux a *
          simProb (outEquiv kh e)
            (extAdv Qs (seAlgKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
              (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
              w1PrfOf keys Q
                (((((𝒜.thenProgOut (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                  (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                  (forall_mul_le_mul_right _ hw)).absorbAssign (PMF.pure ())
                (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk
                  h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
                Prod.fst).alg a))
              ((inertOnDummy w1IsDummy (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp)
                p₀).comap (w1StmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
            (forgerWinsKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
              (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
              w1PrfOf keys Q
                (((((𝒜.thenProgOut (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                  (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                  (forall_mul_le_mul_right _ hw)).absorbAssign (PMF.pure ())
                (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk
                  h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
                Prod.fst).alg a)
              ((inertOnDummy w1IsDummy (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp)
                p₀).comap (w1StmtX ∘ Prod.fst)) Ext (fun _ w => w)
              (w1Goal prims O Mo βmin tol enc k D bmsg adm sp (fun i => (Bf).pk (keys i)) ω)) +
          Mc.simExtractionError (kqOf Mg nr b b) (maxError ε)
            (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
            (t + w * (2 * N) + Q * 1 + Q * 1) Q +
          ENNReal.ofReal (Mc.zkError δ (t + w * (2 * N) + Q * 1 + Q * 1) Q)) := by
  let EvK : (Xq → Y) → (Frg × X₀f) × List (RingSignature.Insider.Req Bf PSf adm n) × (Xq → Y) →
      Prop := fun H q => w1ForgeEv sp O keys H (q.1.1, q.2.1, q.2.2) ∧
        q.1.2 = (w1ForgeStmtProg sp prims O bmsg Mc q.1.1).run q.2.2
  have hSt := allOut_w1StmtProg (sp := sp) (O := O) (bmsg := bmsg)
  have hag : ∀ H, (kfRelay Bf (fun i => (Bf).pk (keys i)) (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg)
      (w1StmtP sp) (w1ToR (PS := PSh) (adm := adm) (Q := Q))
      (w1DummyR (PS := PSh) (adm := adm) (Q := Q)) sc
      (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (w1StmtP_queries sp)
      w1Idle).AgreeAt H
      (w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk h keys sc
        (base sp H)) := fun H =>
    agreeAt_kfRelaySide _ _ (fun x G => run_w1StmtP_eq_w1StmtPω sp x G) _ H
  have hA : ∀ ω (q : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q),
      MultiRelay.AsksIn (MUResponse Bf ⊕ Mc.Response b)
        (((w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk h keys sc
          ω).relayOf Q).prog q)
        (FromSigned Bf (w1Enc (fun i => (Bf).pk (keys i))) w1StmtX Prod.fst w1IsDummy q.req) := fun ω q =>
    AssignRelay.asksIn_relayOf _ Q (P := fun _ r => FromSigned Bf (w1Enc (fun i => (Bf).pk (keys i))) w1StmtX Prod.fst
      w1IsDummy r)
      (fun T c r => asksIn_kfProgK Bf (fun i => (Bf).pk (keys i)) _ _ sc (w1Enc (fun i => (Bf).pk (keys i))) w1StmtX Prod.fst _ _ _
        (w1KFEncoding sp keys).hdumS
        (fun x => ((hSt x).mono fun _ hx => hx.1).translate _ _)
        (fun x => ((hSt x).mono fun x₀ hx r σ =>
          w1StmtX_enc_toR (fun i => (Bf).pk (keys i)) (hx.2.trans_le x.ring.2) r σ).translate _ _) T c r) q
  have hAc : ∀ ω (q : AssignRelay.TaggedReq Xq Y (RingSignature.Insider.Req Bf PSf adm n) Q),
      MultiRelay.AsksIn (MUResponse Bf ⊕ Mc.Response b)
        (((w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk h keys sc
          ω).relayOf Q).prog q)
        fun r' => ∀ i, r' = .inl (.corrupt i) → q.req = .corrupt i := fun ω q =>
    AssignRelay.asksIn_relayOf _ Q (P := fun _ (r : RingSignature.Insider.Req Bf PSf adm n)
        (r' : MURequest (SignOracle.none Bf) n ⊕
          W1Rq prims O Mo βmin tol enc k D bmsg PSh adm n Q) =>
        ∀ i, r' = .inl (.corrupt i) → r = .corrupt i)
      (fun T c r => asksIn_kfProgK_corrupt Bf (fun i => (Bf).pk (keys i)) _ _ sc _ _ _ T c r) q
  have hside : ∀ H Tb (hPl : List (AssignRelay.TaggedReq Xq Y
        (RingSignature.Insider.Req Bf PSf adm n) Q)) hist' (f : Frg × X₀f),
      w1SideRing (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i)) (reprogT Tb H) (base sp H) f
        (hPl.map AssignRelay.TaggedReq.req) →
      (w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk h keys sc
        (base sp H)).Explains Q H Tb hPl hist' →
      w1Side (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i)) (base sp H) f (hist'.map HistoryEntry.request) :=
    fun H Tb hPl hist' f hR hex => w1Side_of_sideRing sp h.hO h.hdisj h.hch _ (fun i => (Bf).pk (keys i)) sc w1Idle rfl H
      Tb hPl hist' f hR hex
  have hE : ∀ H (f : Frg × X₀f) rs G, EvK H (f, rs, G) → _ := fun H f rs G hf =>
    w1ForgeEv_hE (Λ := Λ) (E := E) (hb := hb) (honest := honest) hchk keys H f.1 f.2 rs G hf.1
      hf.2
  refine (ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left
    (QueryBoundedAdversary.assignLaw_le_thenProgOut 𝒜 _ (2 * N) (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
      (forall_mul_le_mul_right _ hw) _ H _ (EvK H)
      fun o rs G hE => ⟨hE, rfl⟩) zero_le).trans ?_
  refine (kfChainFull_le sp Bf (fun i => (Bf).pk (keys i)) (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg)
    (w1StmtP sp) (w1ToR (PS := PSh) (adm := adm) (Q := Q))
    (w1DummyR (PS := PSh) (adm := adm) (Q := Q)) sc
    (w1KFSign_queries (RMsg := RMsg) prims O sp βmin tol enc k D bmsg) (w1StmtP_queries sp)
    w1Idle (w1Enc (fun i => (Bf).pk (keys i))) (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q) w1StmtX Prod.fst
    ((RingSignature.Insider.encProver Mc Λ E hb honest).comap w1StmtX
      (RingSignature.Insider.RelayWit.toWit (B := Bf))) keys
    (𝒜.thenProgOut (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N) (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
      (forall_mul_le_mul_right _ hw))
    (fun pk Rg c msg s H o ho => prf_reprogram_w1KFSign sp pk Rg c msg s H o ho)
    (w1KFEncoding sp keys)
    (fun ω => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk h keys sc ω)
    1 1 (fun _ => le_rfl) (fun _ => le_rfl) hag hA hAc EvK
    (fun p h => ∃ π ∈ w1PrfOf p.1, (Mc.qVerifier Qs b b).Accepted (outEquiv kh e ∘ h) ⟨p.2, π⟩)
    (fun p => w1CheckX p.2 p.1 = true) (w1SideRing (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i)))
    (w1Side (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i))) hE hside).trans ?_
  refine ENNReal.tsum_le_tsum fun ω => mul_le_mul_of_nonneg_left (le_of_eq_of_le ?_
    ((kfChainAt_le (B := Bf) (enc := w1Enc (fun i => (Bf).pk (keys i))) (Λ := Λ) (A' := (((𝒜.thenProgOut
      (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N) (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
      (forall_mul_le_mul_right _ hw)).absorbAssign
      (PMF.pure ())
      (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk h keys sc
        ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut Prod.fst) hk hb (w1Rel_iff (Q := Q)) (w1Enc_injective _) w1PrfOf w1CheckX (w1DummyStmts _)
      (fun x hx q hq => w1Disj x hx q hq) (fun i => (Bf).pk (keys i)) Prod.fst (w1Side (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i)))
      ω VE pub Sim Tp hvzk hrbr (fun _ w => w)
      (w1Goal prims O Mo βmin tol enc k D bmsg adm sp (fun i => (Bf).pk (keys i)))
      (fun p rs w _ hfr hw => w1Goal_of sp (fun i => (Bf).pk (keys i)) ω p rs w hfr.2.1 hfr.2.2 hw) p₀ keys Q).trans_eq
        ?_)) zero_le
  rotate_left
  · with_reducible rfl
  unfold acceptK acceptKAt
  -- TODO(unbundle-M4): the goal reads the absorbed adversary at `Mc.Response b` (from
  -- `kfChainAt_le`) and at `PSf.Proof` (from `kfChainFull_le`); generalizing it first keeps the
  -- defeq between the two readings on a free variable
  generalize QueryBoundedAdversary.restrictAt sp ω ((𝒜.thenProgOut
      (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N) (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
      (forall_mul_le_mul_right _ hw)).absorbAssign
      (PMF.pure ())
      (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk h keys sc
        ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q) = A₀
  rw [← GordieHowe.tsum_mul_tsum_mul_comm]
  refine tsum_congr fun g => congrArg _ ?_
  exact Quantum.QueryBoundedAdversary.transcriptLaw_eq_tsum_test A₀
    (C := kfMain Bf (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
      ((RingSignature.Insider.encProver Mc Λ E hb honest).comap w1StmtX
        (RingSignature.Insider.RelayWit.toWit (B := Bf))) (w1Enc (fun i => (Bf).pk (keys i))) keys Q)
    (kfMain_noAssign Bf _ _ (w1Enc (fun i => (Bf).pk (keys i))) keys Q) g
    (fun o rs => (∃ π ∈ w1PrfOf o.1, (Mc.qVerifier Qs b b).Accepted (outEquiv kh e ∘ g)
        ⟨o.2, π⟩) ∧ w1CheckX o.2 o.1 = true ∧
      kfFresh (w1Enc (fun i => (Bf).pk (keys i))) w1StmtX w1IsDummy (fun i => (Bf).pk (keys i)) Prod.fst
        (w1Side (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i))) ω o rs)
    (kfWinTest Mc b Qs (w1Enc (fun i => (Bf).pk (keys i))) w1StmtX w1IsDummy (fun i => (Bf).pk (keys i)) Prod.fst
      (w1Side (PS := PSh) (adm := adm) O sp (fun i => (Bf).pk (keys i))) w1PrfOf w1CheckX Q ω)
    fun o rs => by
      rw [run_kfWinTest]
      exact ⟨fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩, fun ⟨h1, h2, h3⟩ => ⟨h2, h1, h3⟩⟩

end GordieHowe.Ring.MLDSAW1
