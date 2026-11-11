-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeChainW1
public import GordieHowe.Applications.Ring.MLDSAW1ConvertedChain
public import GordieHowe.Applications.Ring.W1ConcreteOracles
public import GordieHowe.Model.RingSignature.CollisionGame

@[expose] public section

/-!
# The backbone of the key-free unforgeability chain at the ML-DSA ring publishing `w₁`

BKM06 Definition 7 against the hedged scheme of the proof system `w1HPS` at a check `chk`
accepting only nonempty rings, bounded by the hops to the key-free relay challenger
(`insiderForgeProb_le_w1C2`, `GordieHowe/Applications/Ring/MLDSAW1ConvertedChain.lean`), a
collision of message representatives at the base oracle (`runLawIn_le_add_collision`,
`GordieHowe/Model/RingSignature/CollisionGame.lean`), and the average over the key coins and the
side coins of the key-free chain (`kfGame_le_w1Chain`,
`GordieHowe/Applications/Ring/MLDSAW1KeyFreeChainW1.lean`), through `runLawIn_w1C2_eq`.

- `w1ChainAdv`: the relabelled adversary at the users' public keys.
- `W1OracleFacts.probUniform_muAns_mem_le`: message representatives of a uniform value are
  uniform.
- `runLawIn_w1C2_le_add_w1ForgeEv`: the forgery event without a collision, plus the collision term.
- `GordieHowe.ENNReal.le_ofReal_add_of_toReal_le`, `GordieHowe.ENNReal.tsum_mul_sum_le`: two
  bounds in `ℝ≥0∞`.
- `runLawIn_w1ForgeEv_le`: the forgery event without a collision, through the key-free chain.
- `insiderForgeProb_le_w1C2_w1HPS`: the hops at `w1HPS`.
- `insiderForgeProb_le_w1KFChain` (**the backbone**).
-/

open scoped ENNReal

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature RingSignature.KeyFree
open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP GordieHowe.MLDSA.Regularity

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {I J Y₁ : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  [AddGroup Y₁] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] {sp : OracleSplit (BitStr I J) Y₁
    (XOut kh e)}
  {prims : Primitives p}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) (BitStr I J) p prims Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) (BitStr I J) p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] [Nonempty RMsg] [Nonempty
    (FIPSSignature p prims)]
  {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {Mc : SPBCS Mg P (W1ExpStmt prims RMsg N)
    kh kN kS L e}
  {Λ : SiteLayout Mg} {b : ℕ} [∀ j i, Fintype ((Mc.comp j).MessageWrite i)]
  {E : (j : ι) → (Mc.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool}
  {Qs : ∀ x, Mc.IOPQueries Vr x} {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R]
  [DecidableEq R] [Nonempty R]
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

local notation "Sh" => hedgedScheme prims O Mo βmin tol enc k D bmsg PSh adm

attribute [local instance] admDecF

variable (prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk) in
/-- **The adversary of the chain at the users' public keys `pks`**: the adversary `A` against the
hedged scheme relabelled to the fresh scheme (`w1FreshAdv`) at `pks`, read as an adversary of the
insider requests and responses of the fresh base signer. The chain runs it at the public keys of
the users' key coins. -/
noncomputable abbrev w1ChainAdv {t : ℕ}
    (A : InsiderAdversary (Sh) n (OracleView.queriesOnly Xq (BitStr I J)) t)
    (pks : Fin n → (Bf).PK) : QueryBoundedAdversary Xq (BitStr I J)
      (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm) Frg t :=
  w1FreshAdv prims O Mo βmin tol enc k D bmsg PSh adm A (pks, ())


omit [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁] [NeZero (bucketCount p)] nttOps
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg]
  [Nonempty (FIPSSignature p prims)] in
/-- **Message representatives of a uniform value are uniform** (`UniformSplit.map_muAns`): a set
`S` of representatives has probability `|S| / |Bytes 64|`. -/
theorem W1OracleFacts.probUniform_muAns_mem_le (h : W1OracleFacts O Mo sp)
    (S : Finset (MLDSA.Bytes 64)) :
    Pr[y ← BitStr I J : O.muAns y ∈ S] ≤ S.card / (Fintype.card (MLDSA.Bytes 64) : ℝ≥0∞) := by
  refine le_of_eq ?_
  unfold probUniform
  rw [show {y : BitStr I J | O.muAns y ∈ S} = O.muAns ⁻¹' (S : Set (MLDSA.Bytes 64)) from rfl,
    ← PMF.toOuterMeasure_map_apply, h.uniformSplit.map_muAns,
    PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [Finset.coe_sort_coe, Fintype.card_coe]

omit [Nonempty Y₁] in
open Classical in
/-- **The forgery event without a message-representative collision**: against the key-free relay
challenger `w1C2`, the forgery event has at most the probability of the forgery event without a
collision of the message representatives at the base oracle (`w1ForgeEv`), plus the collision
term of `runLawIn_le_add_collision` at the `N + Q` named points `w1MuPts`, for decodings reading
only the first component and message representatives with `|S| / c` mass on every set `S`. -/
theorem runLawIn_w1C2_le_add_w1ForgeEv
    [DecidableRel (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)] (h : W1OracleFacts O Mo sp)
    {c : ℝ≥0∞} (hf : ∀ S : Finset (MLDSA.Bytes 64), Pr[y ← BitStr I J : O.muAns y ∈ S] ≤ S.card / c)
    {t : ℕ} (A' : (Fin n → (Bf).KeyCoins) → QueryBoundedAdversary Xq (BitStr I J)
      (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm) Frg t) :
    (runLawIn (fun keys _ => A' keys)
        (fun keys => w1C2 prims O Mo βmin tol enc k D bmsg PSh adm sp
          (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
          (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk) (PMF.uniformOfFintype _)
          (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR w1DummyR (w1StmtP_queries sp) w1Idle
          keys Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)} ≤
      (runLawIn (fun keys _ => A' keys)
        (fun keys => w1C2 prims O Mo βmin tol enc k D bmsg PSh adm sp
          (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
          (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk) (PMF.uniformOfFintype _)
          (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR w1DummyR (w1StmtP_queries sp) w1Idle
          keys Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, w1ForgeEv sp O x.1 x.2.1 q} +
      (12 * ((t + Q * (w1KFq N reps k T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk).q) + (N + Q) : ℕ) :
            ℝ≥0∞) ^ 2 *
          ((t + Q * (w1KFq N reps k T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk).q) + (N + Q) - 1 : ℕ) :
            ℝ≥0∞) / c +
          2 * (N + Q : ℕ) / Fintype.card (BitStr I J)) := by
  have hl := toOuterMeasure_runLawIn_inter_length A' (fun keys => w1C2 prims O Mo βmin tol enc k D
    bmsg PSh adm sp
      (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
      (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk) (PMF.uniformOfFintype _)
      (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR w1DummyR (w1StmtP_queries sp) w1Idle
      keys Q) (Q := Q) (fun _ => rfl)
    {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)}
  rw [hl]
  have hc := runLawIn_le_add_collision O.muAns hf A' (fun keys => w1C2 prims O Mo βmin tol enc k D
    bmsg PSh adm sp
      (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
      (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk) (PMF.uniformOfFintype _)
      (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR w1DummyR (w1StmtP_queries sp) w1Idle
      keys Q)
    (Q := Q) (qC := w1KFq N reps k T + 2 * N +
      max 0 (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk).q) (fun _ => rfl)
    (fun _ => le_rfl) (Set.range O.muPt) (N + Q) (fun keys o => w1MuPts (PS := PSh) (adm := adm) O
      (fun i => (Bf).pk (keys i)) o.1.1 o.1.2.1 (o.2.take Q))
    (fun keys o => (length_w1MuPts_le _ _ _ _).trans
      (Nat.add_le_add_left (List.length_take_le _ _) _))
    ({x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)} ∩
      {x | ∀ q ∈ x.2.2, q.2.1.length ≤ Q})
  refine hc.trans (add_le_add (MeasureTheory.measure_mono ?_) le_rfl)
  rintro ⟨keys, H, x⟩ ⟨⟨⟨q, hq, hF⟩, hlen⟩, hcol⟩
  refine ⟨q, hq, hF, fun hc => hcol q hq ?_⟩
  rw [List.take_of_length_le (hlen q hq)]
  exact collides_of_w1CollRing sp h.hO _ H _ _ _ hc

omit nttOps in
/-- **A real bound through a probability, in `ℝ≥0∞`**: if `P.toReal ≤ r.toReal + a + b + c + d`
for a finite `P` and `r ≤ X`, then `P ≤ ofReal (a + b + c + d) + X`. -/
theorem _root_.GordieHowe.ENNReal.le_ofReal_add_of_toReal_le {P r X : ℝ≥0∞} {a b c d : ℝ}
    (hP : P ≠ ⊤) (h1 : P.toReal ≤ r.toReal + a + b + c + d) (h2 : r ≤ X) :
    P ≤ ENNReal.ofReal (a + b + c + d) + X := by
  rw [← ENNReal.ofReal_toReal hP]
  refine (ENNReal.ofReal_le_ofReal (h1.trans_eq
    (show _ = r.toReal + (a + b + c + d) by ring))).trans ((ENNReal.ofReal_add_le).trans ?_)
  exact (add_comm _ _).le.trans (add_le_add le_rfl (ENNReal.ofReal_toReal_le.trans h2))

omit nttOps in
/-- **An average of a finite average, swapped and bounded**: for weights `a` and `b`, when
`Σ' x, a x * X x s ≤ Y s` for every `s`, `Σ' x, a x * Σ s, b s * X x s ≤ Σ' s, b s * Y s`. -/
theorem _root_.GordieHowe.ENNReal.tsum_mul_sum_le {α β : Type} [Fintype β] (a : α → ℝ≥0∞)
    (b : β → ℝ≥0∞) (X : α → β → ℝ≥0∞) (Y : β → ℝ≥0∞) (h : ∀ s, ∑' x, a x * X x s ≤ Y s) :
    ∑' x, a x * ∑ s, b s * X x s ≤ ∑' s, b s * Y s := by
  calc ∑' x, a x * ∑ s, b s * X x s = ∑' s, b s * ∑' x, a x * X x s := by
        simp_rw [Finset.mul_sum, ← tsum_fintype (L := SummationFilter.unconditional _)]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun s => ?_
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun x => mul_left_comm _ _ _
    _ ≤ ∑' s, b s * Y s := ENNReal.tsum_le_tsum fun s => mul_le_mul_of_nonneg_left (h s) zero_le

open Classical in
/-- **The forgery event without a collision, through the key-free chain**: against the key-free
relay challenger `w1C2`, the event `w1ForgeEv` has at most the average over the users' key coins
and the side coins of the bound of `kfGame_le_w1Chain`. -/
theorem runLawIn_w1ForgeEv_le [Inhabited Mc.NIProof]
    [DecidableRel (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)]
    (hk : 0 < kh) (hchk : ∀ x, chk x = true → x.ring.1 ≠ []) (h : W1OracleFacts O Mo sp)
    {t w : ℕ} (A' : (Fin n → (Bf).KeyCoins) → QueryBoundedAdversary Xq (BitStr I J)
      (RingSignature.Insider.Req Bf PSf adm n) (RingSignature.Insider.Resp Bf PSf adm) Frg t)
    (hw' : ∀ keys a, ((A' keys).alg a).width ≤ w)
    (VE : Mc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Mc.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel prims enc bmsg adm) honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel prims enc bmsg adm) Vr Ext St ε)
    (p₀ : Mc.Response b) :
    (runLawIn (fun keys _ => A' keys)
        (fun keys => w1C2 prims O Mo βmin tol enc k D bmsg PSh adm sp
          (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
          (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk) (PMF.uniformOfFintype _)
          (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR w1DummyR (w1StmtP_queries sp) w1Idle
          keys Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, w1ForgeEv sp O x.1 x.2.1 q} ≤
        ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
          ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
            ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
              (∑' a, ((((QueryBoundedAdversary.thenProgOut (A' keys) (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                      (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                      (forall_mul_le_mul_right _ (hw' keys))).absorbAssign (PMF.pure ())
                    (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm
                      chk h
                      keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
                    Prod.fst).aux a *
                simProb (outEquiv kh e)
                  (extAdv Qs (seAlgKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (A' keys) (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                        (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                        (forall_mul_le_mul_right _ (hw' keys))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest
                        adm chk
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a))
                    ((inertOnDummy w1IsDummy (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
                  (forgerWinsKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (A' keys) (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                        (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                        (forall_mul_le_mul_right _ (hw' keys))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest
                        adm chk
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a)
                    ((inertOnDummy w1IsDummy (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Ext (fun _ w => w)
                    (w1Goal prims O Mo βmin tol enc k D bmsg adm sp (fun i => (Bf).pk (keys i))
                      ω)) +
                Mc.simExtractionError (kqOf Mg nr b b) (maxError ε)
                  (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
                  (t + w * (2 * N) + Q * 1 + Q * 1) Q +
                ENNReal.ofReal (Mc.zkError δ (t + w * (2 * N) + Q * 1 + Q * 1) Q)) := by
  have he := runLawIn_w1C2_eq (RMsg := RMsg) (PS := PSh) sp
    (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
    ((RingSignature.Insider.encProver Mc Λ E hb honest).comap w1StmtX
      (RingSignature.Insider.RelayWit.toWit (B := Bf))) (PMF.uniformOfFintype _)
    (fun keys => w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR w1DummyR
    (w1StmtP_queries sp) w1Idle Q A' (fun keys H q => w1ForgeEv sp O keys H q)
  refine le_of_eq_of_le he ?_
  refine ENNReal.tsum_le_tsum fun keys => mul_le_mul_of_nonneg_left ?_ zero_le
  exact _root_.GordieHowe.ENNReal.tsum_mul_sum_le _ _ _ _ fun sc =>
    kfGame_le_w1Chain hk hchk h keys sc (A' keys) (hw' keys) VE pub Sim Tp hvzk hrbr p₀

open Classical in
/-- **The hops to the key-free relay challenger** (`insiderForgeProb_le_w1C2` at `w1HPS`, the
encoding `w1Enc`, the statement program `w1StmtP` and the main prover `w1MainProver`). -/
theorem insiderForgeProb_le_w1C2_w1HPS [Inhabited Mc.NIProof]
    [DecidableRel (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)]
    (h : W1OracleFacts O Mo sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range Mo.pt)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs1 : ∀ seed, polyVecBounded (keyGen prims seed).2.s1 p.eta)
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {Vp : RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg) →
      (PSh).Proof → OracleProg Xq (BitStr I J) Bool} {qv : ℕ} (hV : (PSh).VerifiesBy Vp qv)
    {t w : ℕ} (A : InsiderAdversary (Sh) n (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk A pks).alg a).width ≤
        w)
 :
    (insiderForgeProb A Q).toReal ≤
      ((runLawIn (fun keys _ => (w1ChainAdv prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm
        chk A (fun i => (Bf).pk (keys i))))
        (fun keys => w1C2 prims O Mo βmin tol enc k D bmsg PSh adm sp
          (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
          (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk) (PMF.uniformOfFintype _)
          (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR w1DummyR (w1StmtP_queries sp) w1Idle
          keys Q)).toOuterMeasure
        {x | ∃ q ∈ x.2.2, Forges x.1 q.2.2 q.1 (Challenger.histOf q.2.1)}).toReal +
      ((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 : ℝ)⁻¹)) +
      Q * (√((k * T : ℝ) * (n * commitPointAt prims) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q)) +
        (k * T : ℝ) * (n * commitPointAt prims) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q) / 2) +
      2 * √(t + w * qv + Q : ℝ) *
        √((t + w * qv + (1 + k * T + max (Sf).q (SideOracle.none Sf).q) * Q : ℝ) *
          (Q * (2 * k * T * (n * commitPointAt prims)))) +
      Q * (((k * T).choose 2 : ℝ) * (n * commitPointAt prims)) := by
  have h1 := insiderForgeProb_le_w1C2 (PS := PSh) sp h (h.w1HPS_hPSm hQm) (h.w1HPS_hPSv hQm)
    h.w1HPS_proverReadsPub h_laws hv henc hs1 hs2 hV
    (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
    (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk) (PMF.uniformOfFintype _) rfl
    (fun keys => w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR w1DummyR
    (w1StmtP_queries sp) w1Idle (fun keys => w1ProverRelays keys)
    (fun keys => w1KeptInRel (Q := Q) sp h.hO keys) A (fun keys => hw fun i => (Bf).pk (keys i)) Q
  exact h1

open Classical in
/-- **The backbone of the key-free unforgeability chain at the ML-DSA ring publishing `w₁`**: for
an adversary `A` of BKM06 Definition 7 against the hedged scheme of `w1HPS` at a check `chk`
accepting only nonempty rings (`hchk`), the forgery probability is at most the hop terms of
`insiderForgeProb_le_w1C2`, plus the collision term of the message representatives at the
`N + Q` named points (`runLawIn_le_add_collision` with `c = |Bytes 64|`), plus the average over
the users' key coins and the side coins of the bound of `kfGame_le_w1Chain` for the relabelled
adversary `w1ChainAdv`.

Hypotheses: digests have at least one byte (`hk`); the oracle facts of the ring (`h`); the mask
oracle avoids the encoded spBCS queries (`hQm`); the signing and verification laws
(`h_laws`, `hv`); `enc` is the bucket encoding (`henc`); key generation gives short secrets
(`hs1`, `hs2`); the verifier of `w1HPS` is a program (`hV`); the relabelled adversary's width is
at most `w` (`hw`); the composite is honest-verifier zero knowledge (`hvzk`) and round-by-round
knowledge sound (`hrbr`) for `w1ExpRel`. -/
theorem insiderForgeProb_le_w1KFChain [Inhabited Mc.NIProof]
    [DecidableRel (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)]
    (hk : 0 < kh) (hchk : ∀ x, chk x = true → x.ring.1 ≠ []) (h : W1OracleFacts O Mo sp)
    (hQm : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range Mo.pt)
    (h_laws : SigningLaws prims) (hv : VerifyLaws prims)
    (henc : ∀ w : RqVec p.k, enc (prims.highBitsVec w) = bucketsOf (rqVecCoeffs w))
    (hs1 : ∀ seed, polyVecBounded (keyGen prims seed).2.s1 p.eta)
    (hs2 : ∀ seed, polyVecBounded (keyGen prims seed).2.s2 p.eta)
    {Vp : RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg) →
      (PSh).Proof → OracleProg Xq (BitStr I J) Bool} {qv : ℕ} (hV : (PSh).VerifiesBy Vp qv)
    {t w : ℕ} (A : InsiderAdversary (Sh) n (OracleView.queriesOnly Xq (BitStr I J)) t)
    (hw : ∀ (pks : Fin n → (Bf).PK) a,
      ((w1ChainAdv prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk A pks).alg a).width ≤
        w)
    (VE : Mc.ViewEncoder E Qs) {Pub : Type} (pub : X₀f → Pub)
    (Sim : CausalJointSimulator VE.MV Pub) (Tp : Mc.Preimages) {δ : NNReal}
    (hvzk : CausalHVZK VE.MV (w1ExpRel prims enc bmsg adm) honest pub Sim δ)
    {Ext : CausalExtractor P τ X₀f (RingSignature.RingWitOf (FIPSSignature p prims))} {St : CausalStateFn P τ X₀f}
    {ε : ChIdx P τ → NNReal}
    (hrbr : CausalRBRKnowledgeSound (w1ExpRel prims enc bmsg adm) Vr Ext St ε)
    (p₀ : Mc.Response b) :
    insiderForgeProb A Q ≤
      ENNReal.ofReal (((Q * k).choose 2 * (2 ^ 256 : ℝ)⁻¹ + 2 * t * √((Q * k : ℕ) * (2 ^ 256 :
        ℝ)⁻¹)) +
      Q * (√((k * T : ℝ) * (n * commitPointAt prims) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q)) +
        (k * T : ℝ) * (n * commitPointAt prims) *
            (t + max (Sf).q (SideOracle.none Sf).q * Q) / 2) +
      2 * √(t + w * qv + Q : ℝ) *
        √((t + w * qv + (1 + k * T + max (Sf).q (SideOracle.none Sf).q) * Q : ℝ) *
          (Q * (2 * k * T * (n * commitPointAt prims)))) +
      Q * (((k * T).choose 2 : ℝ) * (n * commitPointAt prims))) +
      ((12 * ((t + Q * (w1KFq N reps k T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk).q) + (N + Q) : ℕ) :
            ℝ≥0∞) ^ 2 *
          ((t + Q * (w1KFq N reps k T + 2 * N +
            max 0 (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk).q) + (N + Q) - 1 : ℕ) :
            ℝ≥0∞) / Fintype.card (MLDSA.Bytes 64) +
          2 * (N + Q : ℕ) / Fintype.card (BitStr I J)) +
        ∑' keys, PMF.uniformOfFintype (Fin n → (Bf).KeyCoins) keys *
          ∑' sc, PMF.uniformOfFintype (Fin Q → KFCoins (p := p) (T := T) k D Y₁) sc *
            ∑' ω, PMF.uniformOfFintype (Xq → Y₁) ω *
              (∑' a, ((((QueryBoundedAdversary.thenProgOut (w1ChainAdv prims O Mo βmin tol enc k D
                bmsg Mc Λ E hb honest adm chk A (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                      (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                      (forall_mul_le_mul_right _ (hw (fun i => (Bf).pk (keys i))))).absorbAssign (PMF.pure ())
                    (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm
                      chk h
                      keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp ω).mapOut
                    Prod.fst).aux a *
                simProb (outEquiv kh e)
                  (extAdv Qs (seAlgKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv prims O Mo βmin tol enc k
                        D bmsg Mc Λ E hb honest adm chk A (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                        (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                        (forall_mul_le_mul_right _ (hw (fun i => (Bf).pk (keys i))))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest
                        adm chk
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a))
                    ((inertOnDummy w1IsDummy (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Q (kqOf Mg nr b b))
                  (forgerWinsKF (rel := w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
                    (enc := w1Enc fun i => (Bf).pk (keys i)) (dummyS := w1DummyS PSh adm n Q)
                    w1PrfOf keys Q
                      (((((QueryBoundedAdversary.thenProgOut (w1ChainAdv prims O Mo βmin tol enc k
                        D bmsg Mc Λ E hb honest adm chk A (fun i => (Bf).pk (keys i)))
                      (w1ForgeStmtProg sp prims O bmsg Mc) (2 * N)
                        (w1ForgeStmtProg_queries sp prims O bmsg Mc) (w * (2 * N))
                        (forall_mul_le_mul_right _ (hw (fun i => (Bf).pk (keys i))))).absorbAssign (PMF.pure ())
                      (fun _ => w1SideRelay sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest
                        adm chk
                        h keys sc ω) 1 (fun _ => le_rfl) 1 (fun _ => le_rfl) Q).restrictAt sp
                          ω).mapOut
                      Prod.fst).alg a)
                    ((inertOnDummy w1IsDummy (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp)
                      p₀).comap (w1StmtX ∘ Prod.fst)) Ext (fun _ w => w)
                    (w1Goal prims O Mo βmin tol enc k D bmsg adm sp (fun i => (Bf).pk (keys i))
                      ω)) +
                Mc.simExtractionError (kqOf Mg nr b b) (maxError ε)
                  (Mc.niJointSimulatorProg Λ VE.toViewRead b pub Sim Tp).q
                  (t + w * (2 * N) + Q * 1 + Q * 1) Q +
                ENNReal.ofReal (Mc.zkError δ (t + w * (2 * N) + Q * 1 + Q * 1) Q))) := by
  have h1 := insiderForgeProb_le_w1C2_w1HPS (Q := Q) h hQm h_laws hv henc hs1 hs2 hV A hw
  have h2 := (runLawIn_w1C2_le_add_w1ForgeEv (Q := Q)
      (c := (Fintype.card (MLDSA.Bytes 64) : ℝ≥0∞)) h (W1OracleFacts.probUniform_muAns_mem_le h)
        (fun keys =>
      (w1ChainAdv prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk A (fun i => (Bf).pk (keys i))))).trans
    (add_le_add (runLawIn_w1ForgeEv_le (Q := Q) hk hchk h (fun keys =>
      (w1ChainAdv prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest adm chk A (fun i => (Bf).pk (keys i)))) (fun keys => hw fun i => (Bf).pk (keys i)) VE
      pub Sim Tp hvzk hrbr p₀) le_rfl)
  exact _root_.GordieHowe.ENNReal.le_ofReal_add_of_toReal_le (ne_top_of_le_ne_top
    ENNReal.one_ne_top (PMF.toOuterMeasure_apply_le_one _ _)) h1 (h2.trans_eq (add_comm _ _))

end GordieHowe.Ring.MLDSAW1
