-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.Insider
public import GordieHowe.Applications.Ring.BKMSignRelay
public import GordieHowe.Model.Quantum.Interactive.SplitResample
public import GordieHowe.Foundations.ToMathlib.PMFFiber

@[expose] public section

/-!
# Unforgeability with respect to insider corruption from strong unforgeability

BKM06 Definition 7 (Bender, Katz, Morselli, TCC 2006, LNCS p. 67; ePrint 2005/304, p. 7) for the
ring signature compiled by spBCS at every base-message map `bind`, converted signatures
(`bind R m = m`) included, for a base scheme whose public value may depend on the signer's key
(ML-DSA's `w₁`): no `SigScheme.PubOfCoins` is assumed. The reduction answers each ring-signing
request with a real base signature `σ` from the signing oracle, publishes `pub σ`, and replaces
only the proof by the zero-knowledge simulator; the base game is multi-user strong
unforgeability with adaptive corruption (`SignRelayForger.success`; Diemert, Gellert, Jager, Lyu,
PKC 2021, ePrint 2021/235, Definition 2, pp. 7–8, the strong form of Bader et al., TCC 2015,
Definition 2), since the forgery's message may have been signed for another ring. An extracted
signature that the oracle returned is charged to the conditional min-entropy of a signature given
its public value (`SigScheme.SigGivenPubLe`): the adversary saw it only through its public value
and a simulated proof.

The steps, at each value of the auxiliary input and of the oracle:

1. Real ring signatures to checked ones (`outLaw_bkm_le_checked`, `Q · εc`), then the checked
   game is the side-coin average of the zero-knowledge distinguisher with the public values of
   the witnesses' signatures (`outLaw_bkm_eq_sum_real_sig`, `zkRelaySig`), whose real-to-simulated
   step costs `zkError` (`acceptProb_real_le_sig`).
2. The simulated distinguishers average to the checked simulated challenger with real public
   values (`sum_sim_eq_outLaw_simSig`), which costs `Q · εc` to uncheck (`outLaw_simCheckedSig_le`).
3. The per-request signing coins become signing tables (`outLaw_simSig_eq_table`, the reply laws
   agree: a request reads one uniform table entry).
4. Absorbed through the signing relay at the tables (`atKeys_bkmSignRelay`), the adversary is an
   adversary of the simulation-extraction game (`seAdversarySig`); a fresh forgery on a nonempty
   ring is a fresh statement (`hopSE_simTable_le`), weak simulation-sound extractability bounds
   its acceptance by the extraction probability plus `simExtractionError`.
5. An extracted witness decodes to a valid candidate under an uncorrupted member's key. Read off
   the forger's run in a view independent of the relay (`viewLaw`), either the candidate the
   forger picks is a strong forgery (`strongForgerSuccess`) or the forger's valid candidate is a
   signature the oracle returned at a request `j < Q` (`Collides`); the run depends on the tables
   only through the public values of their entries (`viewLaw_eq_of_pubTable_eq`), so that event
   has probability at most `γ` for each `j` (`PMF.sum_mul_toOuterMeasure_comp_le`,
   `PMF.uniformOfFintype_table_guess_le`).

The headline is `BKMAdversary.insiderWinProb_le_of_strongUnforgeability`.
-/

namespace GordieHowe.Ring

open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm
open scoped ENNReal NNReal

/-! ### The public values of the signing tables -/

section Tables

variable {Sch : SigScheme} {n N : ℕ} {RMsg : Type} [Nonempty RMsg]

/-- **The public values of the signatures at the entries of the signing tables `tabs`**: at
request `j` and entry `(i, m)`, the public value of user `i`'s signature on `m` with the entry's
coins. -/
noncomputable def pubTable (keys : Fin n → Sch.KeyCoins) {Q : ℕ} (tabs : Fin Q → SignTable Sch n) :
    Fin Q → Fin n × Sch.Msg → Sch.Pub :=
  fun j e => Sch.pub (Sch.signWith (Sch.sk (keys e.1)) e.2 (tabs j e))

/-- **The public values of a request read from public values per table entry `v`**: for a
ring-signing request `(s, R, m)`, the value at the entry `(s, bind R m)`. -/
noncomputable def pubsOfTable (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ}
    (v : Fin Q → Fin n × Sch.Msg → Sch.Pub) (r : BKMRequest Sch n N RMsg) : Fin Q → Sch.Pub :=
  fun j => match r with
    | .ringSign s R m => v j (s, bind R.1 m)
    | _ => Sch.pub (dummySig bind)

omit [Nonempty RMsg] in
/-- **The public values of the requests at the tables are read from the tables' public values.** -/
theorem sigPubs_rdTable [Nonempty RMsg] (keys : Fin n → Sch.KeyCoins)
    (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ} (tabs : Fin Q → SignTable Sch n) :
    sigPubs (N := N) keys bind (rdTable Sch n) tabs = pubsOfTable bind (pubTable keys tabs) := by
  funext r j
  cases r <;> rfl

omit [Nonempty RMsg] in
/-- **At equal public values of the tables, the signing relay is the same.** -/
theorem atKeys_bkmSignRelay_eq_of_pubTable_eq [Nonempty RMsg] {Resp : Type}
    (adm : List Sch.PK → Prop) (bind : List Sch.PK → RMsg → Sch.Msg) {Q : ℕ}
    (keys : Fin n → Sch.KeyCoins) {tabs tabs' : Fin Q → SignTable Sch n}
    (h : pubTable keys tabs = pubTable keys tabs') :
    (bkmSignRelay Sch n N RMsg Resp adm bind Q).atKeys keys tabs =
      (bkmSignRelay Sch n N RMsg Resp adm bind Q).atKeys keys tabs' := by
  rw [atKeys_bkmSignRelay, atKeys_bkmSignRelay, sigPubs_rdTable, sigPubs_rdTable, h]

end Tables

/-! ### Signing coins as signing tables -/

section Resample

variable {Sch : SigScheme} {n N : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]
  [Nonempty RMsg] {m k e : ℕ} {Resp SC : Type} [Fintype SC] [DecidableEq SC]
  (bind : List Sch.PK → RMsg → Sch.Msg) (adm : List Sch.PK → Prop)

open Classical in
/-- **The reply of the simulated challenger at a base signature `σ`**: `simReplySig` with the
public value of `σ`, without a test. -/
noncomputable def simReplyAt (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC)
    (Q : ℕ) (κ : Fin n → Sch.KeyCoins) (i : ℕ) (r : BKMRequest Sch n N RMsg) (σ : Sch.Sig)
    (sc : SC) : OracleProg (Bits m) (XOut k e) (Reply (Bits m) (XOut k e) (RingResponse Sch Resp)) :=
  if signerIn (fun i => Sch.pk (κ i)) adm r then
    (S.prog (stmtAt (fun i => Sch.pk (κ i)) adm (fun _ : Fin Q => Sch.pub σ) i r) sc).bind fun o =>
      .pure ⟨sideAnswer (fun i => Sch.pk (κ i)) κ adm (fun _ : Fin Q => Sch.pub σ) i r
        (some o.proof), o.assignments⟩
  else .pure ⟨sideAnswer (fun i => Sch.pk (κ i)) κ adm (fun _ : Fin Q => Sch.pub σ) i r none, []⟩

omit [Fintype RMsg] [DecidableEq RMsg] [Fintype SC] [DecidableEq SC] in
/-- The unchecked reply reads the coins only through the request's base signature. -/
theorem simReplySig_eq_simReplyAt
    (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC) {C : Type}
    (rd : C → Fin n → Sch.Msg → Sch.SignCoins) (Q : ℕ) (κ : Fin n → Sch.KeyCoins) (d : C × SC)
    (i : ℕ) (r : BKMRequest Sch n N RMsg) :
    simReplySig S adm bind rd Q (fun _ _ _ => True) κ d i r =
      simReplyAt adm S Q κ i r (sigOf κ bind rd d.1 r) d.2 := by
  unfold simReplySig simReplyAt
  split_ifs <;> first | rfl | (exfalso; tauto)

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The law of a request's base signature is the same at per-request coins and at a uniform
table**: the table's entry is uniform (`PMF.uniformOfFintype_map_eval`). -/
theorem map_sigOf_rdCoins_eq_rdTable (κ : Fin n → Sch.KeyCoins) (r : BKMRequest Sch n N RMsg) :
    (PMF.uniformOfFintype Sch.SignCoins).map (fun c => sigOf κ bind (rdCoins Sch n) c r) =
      (PMF.uniformOfFintype (SignTable Sch n)).map (fun t => sigOf κ bind (rdTable Sch n) t r) := by
  cases r with
  | publicKey i => exact (PMF.map_const _ _).trans (PMF.map_const _ _).symm
  | corrupt i => exact (PMF.map_const _ _).trans (PMF.map_const _ _).symm
  | ringSign s R m =>
    simp only [sigOf, rdCoins, rdTable]
    rw [show (fun t : SignTable Sch n => Sch.signWith (Sch.sk (κ s)) (bind R.1 m) (t (s, bind R.1 m)))
        = (fun c => Sch.signWith (Sch.sk (κ s)) (bind R.1 m) c) ∘ (fun t => t (s, bind R.1 m))
        from rfl, ← PMF.map_comp, PMF.uniformOfFintype_map_eval]

omit [Fintype RMsg] [DecidableEq RMsg] in
/-- **The reply laws of the unchecked simulated challenger agree at per-request coins and at
signing tables.** -/
theorem map_reply_simSplitSig_rdCoins_eq_rdTable
    (S : NARG.Simulator (Bits m) (XOut k e) (RingStmt Sch RMsg N) Resp SC) (Q : ℕ)
    (κ : Fin n → Sch.KeyCoins) (i : ℕ) (r : BKMRequest Sch n N RMsg) :
    (simSplitSig S adm bind (rdCoins Sch n) Q fun _ _ _ => True).draw.map
        (fun d => (simSplitSig S adm bind (rdCoins Sch n) Q fun _ _ _ => True).reply κ d i r) =
      (simSplitSig S adm bind (rdTable Sch n) Q fun _ _ _ => True).draw.map
        (fun d => (simSplitSig S adm bind (rdTable Sch n) Q fun _ _ _ => True).reply κ d i r) := by
  have h : ∀ {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
      (rd : C → Fin n → Sch.Msg → Sch.SignCoins),
      (simSplitSig S adm bind rd Q fun _ _ _ => True).draw.map
          (fun d => (simSplitSig S adm bind rd Q fun _ _ _ => True).reply κ d i r) =
        ((PMF.uniformOfFintype C).map fun c => sigOf κ bind rd c r).bind fun σ =>
          S.coins.map (simReplyAt adm S Q κ i r σ) := by
    intro C _ _ _ rd
    simp only [simSplitSig, simReplySig_eq_simReplyAt, PMF.map_bind, PMF.bind_map, PMF.map_comp,
      Function.comp_def]
  rw [h, h, map_sigOf_rdCoins_eq_rdTable]

end Resample

/-! ### Averages of outer measures -/

section Average

/-- **An outer measure that averages**: whenever a finite weighted sum of indicators of sets
`S t` is at most `b` at every point, the weighted sum of the sets' measures is at most `b`. The
images of Born weights of total weight at most one average (`isAvg_map_bornWeight`). -/
def OuterMeasureIsAvg {Ω : Type*} (ν : MeasureTheory.OuterMeasure Ω) : Prop :=
  ∀ {T : Type} [Fintype T] (c : T → ℝ≥0∞) (S : T → Set Ω) (b : ℝ≥0∞),
    (∀ o, ∑ t, c t * (S t).indicator 1 o ≤ b) → ∑ t, c t * ν (S t) ≤ b

/-- **The image of the Born weight of a state of norm at most one averages.** -/
theorem isAvg_map_bornWeight {ι Ω : Type*} [Fintype ι] (v : Quantum.QState ι)
    (hv : Quantum.bornWeight v Set.univ ≤ 1) (f : ι → Ω) :
    OuterMeasureIsAvg (MeasureTheory.OuterMeasure.map f (Quantum.bornWeight v)) := by
  intro T _ c S b h
  simp only [MeasureTheory.OuterMeasure.map_apply, Quantum.bornWeight_apply_eq_sum]
  have hw : ∑ i, (Set.univ : Set ι).indicator (fun i => ‖v i‖ₑ ^ 2) i ≤ 1 := by
    rwa [Quantum.bornWeight_apply_eq_sum] at hv
  simp only [Set.indicator_univ] at hw
  calc ∑ t, c t * ∑ i, (f ⁻¹' S t).indicator (fun i => ‖v i‖ₑ ^ 2) i
      = ∑ i, ‖v i‖ₑ ^ 2 * ∑ t, c t * (S t).indicator 1 (f i) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun t _ => ?_
        by_cases hi : f i ∈ S t
        · simp [hi, mul_comm]
        · simp [hi]
    _ ≤ ∑ i, ‖v i‖ₑ ^ 2 * b := Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (h _) zero_le
    _ = (∑ i, ‖v i‖ₑ ^ 2) * b := by rw [Finset.sum_mul]
    _ ≤ 1 * b := by gcongr
    _ = b := one_mul b

/-- **A run that depends on the coins only through `F` hits a coin-dependent target with
probability at most `γ`**, for outer measures that average, when every fibre of `F` gives the
target conditional probability at most `γ`. -/
theorem sum_mul_le_of_isAvg {T V Ω : Type} [Fintype T] (μ : PMF T) (F : T → V)
    (ρ : V → MeasureTheory.OuterMeasure Ω) (hρ : ∀ v, OuterMeasureIsAvg (ρ v)) (P : T → Set Ω)
    {γ : ℝ≥0∞}
    (h : ∀ t₀ o, μ.toOuterMeasure {t | F t = F t₀ ∧ o ∈ P t} ≤
      γ * μ.toOuterMeasure {t | F t = F t₀}) :
    ∑ t, μ t * ρ (F t) (P t) ≤ γ := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image F)
    (g := F) (fun t _ => Finset.mem_image_of_mem F (Finset.mem_univ t))]
  have hfib : ∀ v ∈ Finset.univ.image F,
      ∑ t ∈ Finset.univ.filter (fun t => F t = v), μ t * ρ (F t) (P t) ≤
        γ * μ.toOuterMeasure {t | F t = v} := by
    intro v hv
    obtain ⟨t₀, -, rfl⟩ := Finset.mem_image.1 hv
    have hs : ∑ t ∈ Finset.univ.filter (fun t => F t = F t₀), μ t * ρ (F t) (P t) =
        ∑ t, (if F t = F t₀ then μ t else 0) * ρ (F t₀) (P t) := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun t _ => ?_
      split_ifs with ht
      · rw [ht]
      · rw [zero_mul]
    rw [hs]
    refine hρ (F t₀) _ P _ fun o => le_of_eq_of_le ?_ (h t₀ o)
    rw [PMF.toOuterMeasure_apply_fintype]
    refine Finset.sum_congr rfl fun t _ => ?_
    by_cases h1 : F t = F t₀ <;> by_cases h2 : o ∈ P t <;>
      simp [h1, h2]
  calc ∑ v ∈ Finset.univ.image F, ∑ t ∈ Finset.univ.filter (fun t => F t = v), μ t * ρ (F t) (P t)
      ≤ ∑ v ∈ Finset.univ.image F, γ * μ.toOuterMeasure {t | F t = v} := Finset.sum_le_sum hfib
    _ = γ * ∑ v ∈ Finset.univ.image F, ∑ t ∈ Finset.univ.filter (fun t => F t = v), μ t := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun v _ => ?_
        rw [PMF.toOuterMeasure_apply_fintype, Finset.sum_filter]
        refine congrArg (γ * ·) (Finset.sum_congr rfl fun t _ => ?_)
        by_cases ht : F t = v <;> simp [ht]
    _ = γ * ∑ t, μ t := by
        rw [Finset.sum_fiberwise_of_maps_to (fun t _ => Finset.mem_image_of_mem F (Finset.mem_univ t))]
    _ = γ := by rw [← tsum_fintype (L := SummationFilter.unconditional T), PMF.tsum_coe, mul_one]

/-- **The image of the outcome of `Sim*(A)` averages** (`simLaw_univ`: total weight one). -/
theorem isAvg_map_simLaw {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
    {m : ℕ} {B' : Type} (e' : BitStr I J ≃ B') {t' : ℕ} {O Ω : Type}
    (A' : Quantum.QueryAlg (Bits m) (BitStr I J) t' O) (f : O × DB (Bits m) B' → Ω) :
    OuterMeasureIsAvg (MeasureTheory.OuterMeasure.map f (simLaw e' A')) := by
  have h1 := simLaw_univ e' A'
  rw [simLaw, MeasureTheory.OuterMeasure.map_apply, Set.preimage_univ] at h1
  rw [simLaw, MeasureTheory.OuterMeasure.map_map]
  exact @isAvg_map_bornWeight (SimRegister A'.W I J m t') Ω inferInstance (simState e' A') h1.le
    (f ∘ fun b : SimRegister A'.W I J m t' => (A'.out b.1.1, slotsDB e' b.2))

end Average

/-! ### The reduction -/

section SPBCS

variable {Sch : SigScheme} {n : ℕ} {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg] {N : ℕ}
  {k e : ℕ} {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {kN kS L : ℕ}
  {M : SPBCS Mg P (RingStmt Sch RMsg N) k kN kS L e} (Λ : SiteLayout Mg) {B : ℕ}
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : RingStmt Sch RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs B B) {R : Type} [Fintype R] [Nonempty R]
  (honest : RingWit Sch → R → CausalProver P τ (RingStmt Sch RMsg N))
  (VE : M.ViewEncoder E Qs) {Pub : Type} (pub : RingStmt Sch RMsg N → Pub)
  (Sim : CausalJointSimulator VE.MV Pub) (T : M.Preimages)
  (bind : List Sch.PK → RMsg → Sch.Msg) (adm : List Sch.PK → Prop)
  {t Q : ℕ} (A : BKMAdversary (M.qVerifier Qs B B) (M.Response B) n t Q)

namespace BKMAdversary

variable [Nonempty RMsg] [NeZero n] [Nonempty Sch.Sig]

/-- **The distinguisher of zero knowledge with the public values of real signatures** at the
auxiliary input `a` and the side coins `s`: the adversary with its side requests absorbed
(`zkRelaySig`), followed by `forgeryTest`.

Running time: that of the adversary, plus the relay of each request (at most one base signature
and its public value) and `forgeryTest`. This running time is argued here, not proved in Lean. -/
noncomputable def distinguisherSig (a : A.Aux) (s : SideCoins Sch n Q) :
    QueryBoundedAdversary (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt Sch n N RMsg) (RelayWit Sch N)) (M.Response B) Bool
      ((A.alg a).width * ((A.alg a).budget + (A.alg a).post) +
        (A.alg a).width * (M.qVerifier Qs B B).kq) where
  Aux := Unit
  aux := PMF.pure ()
  sh _ := (A.sh a).absorbS.thenProgS (M.qVerifier Qs B B).kq
  alg _ := ((A.alg a).absorb (zkRelaySig (N := N) (Resp := M.Response B) adm bind s)).thenProg
    (A.forgeryTest a s) (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)
  tracePreserving _ := AdaptiveIAlg.thenProg_tracePreserving
    ((A.alg a).absorb (zkRelaySig (N := N) (Resp := M.Response B) adm bind s)) (A.forgeryTest a s)
    (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)
    (AdaptiveIAlg.absorb_tracePreserving (A.alg a) (zkRelaySig adm bind s) (A.tracePreserving a))
  withinBudget _ := AdaptiveIAlg.withinBudget_thenProg
    ((A.alg a).absorb (zkRelaySig (N := N) (Resp := M.Response B) adm bind s)) (A.forgeryTest a s)
    (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)
    (AdaptiveIAlg.absorb_withinBudget (A.alg a) (zkRelaySig adm bind s)
      (zkRelaySig_route_injective adm bind s) (A.withinBudget a))
  queries_le _ := (AdaptiveIAlg.thenProg_queries
    ((A.alg a).absorb (zkRelaySig (N := N) (Resp := M.Response B) adm bind s)) (A.forgeryTest a s)
    (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)).le

variable (Sch n Q) in
/-- **The side coins of the simulation-extraction step**: the users' key-generation coins and a
signing table per request. -/
abbrev TableCoins : Type := (Fin n → Sch.KeyCoins) × (Fin Q → SignTable Sch n)

omit [Fintype RMsg] [DecidableEq RMsg] [∀ j i, Nonempty ((P j).Challenge i)]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] [NeZero n] [Nonempty Sch.Sig] in
/-- The signing relay at the users' coins and the tables routes each request number
injectively. -/
theorem atKeys_bkmSignRelay_route_injective (s : TableCoins Sch n Q) (c : ℕ) :
    Function.Injective (((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).atKeys s.1
      s.2).route c) := by
  rw [atKeys_bkmSignRelay]
  exact seRelayPub_route_injective _ _ _ _ c

/-- **The adversary of the simulation-extraction game with real public values** at the side
coins `s = (keys, tabs)`: the adversary with its requests absorbed through the signing relay at the
users' coins `keys` and the signing tables `tabs` (`bkmSignRelay`, which is `seRelayPub` with the
public values of the signers' signatures at the tables, `atKeys_bkmSignRelay`).

Running time: that of the adversary, plus the relay of each request (at most two base calls and a
lookup of the signer's key in the ring). This running time is argued here, not proved in Lean. -/
noncomputable def seAdversarySig (s : TableCoins Sch n Q) :
    M.QBSimExtractionAdversary B (RelayStmt Sch n N RMsg) t where
  Aux := A.Aux
  aux := A.aux
  sh a := (A.sh a).absorbS
  alg a := (A.alg a).absorb ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).atKeys s.1 s.2)
  tracePreserving a := AdaptiveIAlg.absorb_tracePreserving _ _ (A.tracePreserving a)
  withinBudget a := AdaptiveIAlg.absorb_withinBudget _ _
    (atKeys_bkmSignRelay_route_injective bind adm s) (A.withinBudget a)
  queries_le a := A.queries_le a

/-- The shape of `seAdversarySig` at `a` is `A`'s shape absorbed (`AlgShape.absorbS`). -/
@[simp] theorem seAdversarySig_sh (s : TableCoins Sch n Q) (a : A.Aux) :
    (A.seAdversarySig bind adm s).sh a = (A.sh a).absorbS :=
  rfl

/-- **The forger of the multi-user strong-unforgeability game built from the adversary of
BKM06** (`SignRelayForger`): the adversary's requests relayed through the base oracles
(`bkmSignRelay`: public keys and corruptions forwarded; a member's ring-signing request asks one
base signature and sends its public value), the ring signatures simulated by `seSimulator` (which
programs the oracle), the database extractor `dbExtractBits Ext` and the decoding `decodeRing`.

Running time: that of the extraction run of the absorbed adversary (`extAdv`: the adversary, one
simulator run per ring-signing request, the verifier's queries on its claim, the oracle simulated
by a compressed oracle), plus at most two base calls per request and the extractor's and the
decoding's running times (their docstrings). This running time is argued here, not proved in
Lean. -/
noncomputable def signForger (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)) :
    SignRelayForger Sch n M B (BKMRequest Sch n N RMsg) (RingResponse Sch (M.Response B))
      (RelayStmt Sch n N RMsg)
      (SaltedCoins (FiatShamirSalt kS) (M.JointSimCoins VE.toViewRead Sim T)) where
  Aux := A.Aux
  aux := A.aux
  sh := A.sh
  alg := A.alg
  relay := bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q
  sim := (seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst
  extractor := M.dbExtractBits Ext
  decode := decodeRing bind

/-- **The success probability of the forger of the multi-user strong-unforgeability game** built
from the adversary of BKM06 (`signForger`, `SignRelayForger.success`): the forger reads the keys
only through the base oracles (public keys, signatures, and the key-generation coins of the users
the adversary corrupts). -/
noncomputable def strongForgerSuccess
    (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)) : ℝ≥0∞ :=
  (A.signForger Λ VE pub Sim T bind adm Ext).success Qs Q (kqOf Mg nr B B)

/-! #### Real to simulated ring signatures -/

open Classical in
/-- **The checked game of BKM06 is the side-coin average of the distinguisher with real public
values against the real challenger**, at each value of the auxiliary input and each oracle. -/
theorem outLaw_bkm_eq_sum_real_sig (a : A.Aux) (H : Bits (queryBits k kN kS L) → XOut k e) :
    (((A.alg a).toKindAlg.composeBothOut
        ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind
          adm).challenger Q) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} =
      ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
        (((A.distinguisherSig bind adm a s).alg ()).compose
          (realChallenger (relayRel bind adm)
            ((((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).comap Prod.fst
              RelayWit.toWit) Q)).outLaw H (some true) := by
  have hnil := KindAlg.postAss_eq_nil (A.alg a).toKindAlg
    ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind
      adm).challenger Q) (hopRS_outWith_challenger_assignments _ Q)
  have h := (A.alg a).outLaw_absorb (σ := PMF.uniformOfFintype (SideCoins Sch n Q))
    (F' := zkRelaySig (N := N) (Resp := M.Response B) adm bind)
    (C := (checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind
      adm).challenger Q)
    (e := drawEquiv (checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode
      queryEncoding) bind adm) Q)
    (C' := realChallenger (relayRel bind adm)
      ((((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).comap Prod.fst
        RelayWit.toWit) Q)
    (fun s c => drawLaw_drawEquiv_symm
      (checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind adm)
        Q s c)
    (fun H s c => (relays_bkm_real_sig
      (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind adm Q s c).relays
        H _)
    (zkRelaySig_route_injective adm bind) H
    (fun adv lg _ c G => A.WinAt a c.1 adv.workspace.1 lg G)
  have hr : ∀ G : Bits (queryBits k kN kS L) → XOut k e,
      G.reprogram ([] : List (Assignment (Bits (queryBits k kN kS L)) (XOut k e))) = G :=
    fun _ => rfl
  simp only [hnil, hr] at h
  refine h.trans (Finset.sum_congr rfl fun s _ => ?_)
  congr 1
  change _ = ((((A.alg a).absorb (zkRelaySig (N := N) (Resp := M.Response B) adm bind s)).thenProg
    (A.forgeryTest a s) (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)).compose _).outLaw H
      (some true)
  rw [AdaptiveIAlg.outLaw_thenProg]
  congr 2
  ext o
  simp only [hopRS_run_forgeryTest]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩

open Classical in
/-- **The side-coin average of the distinguisher with real public values against the simulated
challenger is the game of BKM06 with checked simulated ring signatures with real public values**
(`simSplitSig` at `rdCoins` with the test `drawOkSig`), at each value of the auxiliary input and
each oracle. -/
theorem sum_sim_eq_outLaw_simSig (a : A.Aux) (H : Bits (queryBits k kN kS L) → XOut k e) :
    ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
        (((A.distinguisherSig bind adm a s).alg ()).compose
          (simChallenger (relayRel bind adm)
            ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q)).outLaw H
          (some true) =
      (((A.alg a).toKindAlg.composeBothOut
          (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
            (rdCoins Sch n) Q (drawOkSig Sch N RMsg bind (rdCoins Sch n))).toChallenger id).outLaw
          H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} := by
  have h := (A.alg a).outLaw_absorb (σ := PMF.uniformOfFintype (SideCoins Sch n Q))
    (F' := zkRelaySig (N := N) (Resp := M.Response B) adm bind)
    (C := (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
      (rdCoins Sch n) Q (drawOkSig Sch N RMsg bind (rdCoins Sch n))).toChallenger)
    (C' := simChallenger (relayRel bind adm)
      ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q)
    (e := splitEquiv Q _)
    (fun s c => simCoinsLaw_splitEquiv_symm Q _ s c)
    (fun H s c => (relays_sim_zk_sig bind adm
      (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) Q s c).relays H _)
    (zkRelaySig_route_injective adm bind) H
    (fun adv lg _ c G => A.WinAt a c.1 adv.workspace.1 lg G)
  refine (Eq.trans (Finset.sum_congr rfl fun s _ => ?_) h.symm)
  congr 1
  change ((((A.alg a).absorb (zkRelaySig (N := N) (Resp := M.Response B) adm bind s)).thenProg
    (A.forgeryTest a s) (M.qVerifier Qs B B).kq (A.forgeryTest_queriesLE a s)).compose _).outLaw H
      (some true) = _
  rw [AdaptiveIAlg.outLaw_thenProg]
  congr 2
  ext o
  simp only [hopRS_run_forgeryTest]
  constructor
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩
  · rintro ⟨v, rfl, hv⟩
    exact ⟨v, rfl, hv⟩

/-- **The acceptance probability of a distinguisher with real public values with one auxiliary
value** is the oracle average of its output law at `true`. -/
theorem acceptProb_distinguisherSig (a : A.Aux) (s : SideCoins Sch n Q)
    (C : Challenger (Bits (queryBits k kN kS L)) (XOut k e)
      (ProofQuery (RelayStmt Sch n N RMsg) (RelayWit Sch N)) (M.Response B)) :
    (A.distinguisherSig bind adm a s).acceptProb C =
      ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.distinguisherSig bind adm a s).alg ()).compose C).outLaw H (some true) := by
  simp only [QueryBoundedAdversary.acceptProb, distinguisherSig]
  rw [tsum_eq_single () fun u hu => absurd (Subsingleton.elim u ()) hu]
  erw [PMF.pure_apply_self, one_mul]
  rw [Alg.realLaw, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun H => ?_
  congr 1
  rw [PMF.toOuterMeasure_map_apply]
  have : (fun o => (⟨o, Equiv.refl _ ∘ H⟩ :
      Outcome (Option Bool) (Bits (queryBits k kN kS L)) (XOut k e))) ⁻¹'
      {p | p.out = some true} = {some true} := by
    ext o
    simp
  rw [this, PMF.toOuterMeasure_apply_singleton]

open Classical in
/-- **Zero knowledge at one auxiliary value and one value of the side coins**, for the
distinguisher with real public values (`SPBCS.everlastingZeroKnowledge_qrom`). -/
theorem acceptProb_real_le_sig {δ : ℝ≥0}
    (hvzk : CausalHVZK VE.MV (ringRel adm bind) honest pub Sim δ) (a : A.Aux)
    (s : SideCoins Sch n Q) :
    (A.distinguisherSig bind adm a s).acceptProb (realChallenger (relayRel bind adm)
        ((((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).comap Prod.fst
          RelayWit.toWit) Q) ≤
      (A.distinguisherSig bind adm a s).acceptProb (simChallenger (relayRel bind adm)
        ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q) +
        ENNReal.ofReal (M.zkError δ t Q) := by
  have hzk := M.everlastingZeroKnowledge_qrom Λ honest E VE hb T
    (Prod.fst : RelayStmt Sch n N RMsg → RingStmt Sch RMsg N) (RelayWit.toWit (Sch := Sch) (N := N))
    hvzk
  unfold NARG.QROM.EverlastingZeroKnowledge at hzk
  rw [NARG.Prover.mapOutput_comap, NARG.Prover.encode_comap, NARG.Simulator.encode_comap,
    M.encode_niSimulator Λ E VE hb] at hzk
  have hD : (A.distinguisherSig bind adm a s).QueriesBeforeLastProofQuery t := fun _ =>
    ⟨(A.alg a).budget, (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)).trans (A.queries_le a),
      AdaptiveIAlg.requestsAfterAtMost_thenProg ((A.alg a).absorb (zkRelaySig adm bind s))
        (A.forgeryTest a s) _ (A.forgeryTest_queriesLE a s)⟩
  have hle : ∀ C, (A.distinguisherSig bind adm a s).acceptProb C ≤ 1 := fun C => by
    rw [A.acceptProb_distinguisherSig]
    calc _ ≤ ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H * 1 :=
          ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left (PMF.coe_le_one _ _) zero_le
      _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  have key : ∀ x y : ℝ≥0∞, x ≤ 1 → y ≤ 1 →
      GordieHowe.advantage x.toReal y.toReal ≤ M.zkError δ t Q →
      x ≤ y + ENNReal.ofReal (M.zkError δ t Q) := fun x y hx hy h => by
    have h' : |x.toReal - y.toReal| ≤ M.zkError δ t Q := h
    have hz : 0 ≤ M.zkError δ t Q := (abs_nonneg _).trans h'
    have hr : x.toReal ≤ y.toReal + M.zkError δ t Q := by
      linarith [le_abs_self (x.toReal - y.toReal)]
    rw [← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hx),
      ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top hy),
      ← ENNReal.ofReal_add ENNReal.toReal_nonneg hz]
    exact ENNReal.ofReal_le_ofReal hr
  have h := hzk t Q _ (A.distinguisherSig bind adm a s) hD
  convert key _ _ (hle _) (hle _) h using 4

omit [NeZero n] [Nonempty Sch.Sig] in
/-- **Replacing the checked simulated signer with real public values by the unchecked one costs at
most `Q · εc`** for a scheme with correctness error `εc` (`hcorr`). -/
theorem outLaw_simCheckedSig_le {εc : ℝ≥0∞} (hcorr : Sch.CorrectWithin εc) (a : A.Aux)
    (H : Bits (queryBits k kN kS L) → XOut k e) :
    (((A.alg a).toKindAlg.composeBothOut
        (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
          (rdCoins Sch n) Q (drawOkSig Sch N RMsg bind (rdCoins Sch n))).toChallenger id).outLaw
        H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} ≤
      (((A.alg a).toKindAlg.composeBothOut
          (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
            (rdCoins Sch n) Q fun _ _ _ => True).toChallenger id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
            (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} + Q * εc := by
  have hε := fun κ i r => draw_simSplitSig_ne_le (n := n) bind adm hcorr
    (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) Q κ i r
  have h := (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
      (rdCoins Sch n) Q (drawOkSig Sch N RMsg bind (rdCoins Sch n))).toOuterMeasure_outLaw_le_add
    (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
      (rdCoins Sch n) Q fun _ _ _ => True).reply
    (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
      (rdCoins Sch n) Q fun _ _ _ => True).reply_queries
    (fun κ i r _ => hε κ i r) (A.alg a).toKindAlg H
    (fun adv lg κ G => A.WinAt a κ adv.workspace.1 lg G)
  rw [← simSplitSig_withReply] at h
  exact h

omit [NeZero n] [Nonempty Sch.Sig] in
/-- **The simulated game with real public values is the same at per-request signing coins and at
signing tables** (`SplitChallenger.toOuterMeasure_outLaw_eq_of_map_reply_eq`). -/
theorem outLaw_simSig_eq_table (a : A.Aux) (H : Bits (queryBits k kN kS L) → XOut k e) :
    (((A.alg a).toKindAlg.composeBothOut
        (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
          (rdCoins Sch n) Q fun _ _ _ => True).toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} =
      (((A.alg a).toKindAlg.composeBothOut
          (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
            (rdTable Sch n) Q fun _ _ _ => True).toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} :=
  SplitChallenger.toOuterMeasure_outLaw_eq_of_map_reply_eq
    (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind (rdCoins Sch n) Q
      fun _ _ _ => True)
    (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind (rdTable Sch n) Q
      fun _ _ _ => True) rfl rfl
    (fun κ i r _ => map_reply_simSplitSig_rdCoins_eq_rdTable bind adm _ Q κ i r)
    (A.alg a).toKindAlg H (fun adv lg κ G => A.WinAt a κ adv.workspace.1 lg G)

/-! #### The simulation-extraction step -/

/-- **The freshness test of the simulation-extraction game at the users' coins `keys`**: every key
of the claim's ring is the key of a user without a corruption request among the first `Q` logged
requests. -/
def okAtKeys (keys : Fin n → Sch.KeyCoins) (a : A.Aux)
    (w : (A.alg a).AbsW (Resp' := M.Response B)) : Prop :=
  ∀ pk ∈ ((A.alg a).out w.work).stmt.ring.1, ∃ i, Sch.pk (keys i) = pk ∧
    BKMRequest.corrupt i ∉ (requests w.logs).take Q

omit [Fintype RMsg] [DecidableEq RMsg] [NeZero n] [Nonempty Sch.Sig] in
/-- **The relayed statements of the first `Q` requests differ from a fresh statement with a
nonempty ring**, for the relay of statements with request-dependent public values (as
`hopSE_fresh`). -/
theorem hopSE_fresh_pub {Resp : Type} (pkOf : Fin n → Sch.PK) (kcOf : Fin n → Sch.KeyCoins)
    {Q' : ℕ} (pubsOf : BKMRequest Sch n N RMsg → Fin Q' → Sch.Pub)
    {keys : Fin n → Sch.KeyCoins} {x : RingStmt Sch RMsg N}
    {rs : List (BKMRequest Sch n N RMsg)} (hf : InsiderFreshAt keys x (rs.take Q'))
    (hx : x.ring.1 ≠ []) :
    ∀ x' ∈ ((seRelayPub (Resp := Resp) pkOf kcOf adm pubsOf).relayList rs).take Q', x'.1 ≠ x := by
  intro x' hx' heq
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hx'
  simp only [List.length_take, SideRelay.length_relayList] at hj
  have hjQ : j < Q' := by omega
  have hjl : j < rs.length := by omega
  simp only [List.getElem_take, SideRelay.relayList, List.getElem_mapIdx, seRelayPub] at heq
  have hmem : rs[j] ∈ rs.take Q' :=
    List.mem_iff_getElem.2 ⟨j, by simp only [List.length_take]; omega, by simp⟩
  by_cases hs : j < Q' ∧ signerIn pkOf adm rs[j]
  · generalize rs[j] = r at heq hmem hs
    cases r with
    | publicKey i => exact hs.2.elim
    | corrupt i => exact hs.2.elim
    | ringSign s R m =>
      rw [stmtAt, dite_eq_left_of_eq_true (eq_true hs)] at heq
      subst heq
      exact hf.no_ringSign s R m hmem ⟨rfl, rfl⟩
  · exact hx (heq ▸ (stmtAt_ring_eq_nil_iff pkOf adm (pubsOf rs[j]) j rs[j]).2 hs)

omit [Nonempty Sch.Sig] in
include hb in
/-- **The game of BKM06 with simulated ring signatures with real public values at signing tables
is at most the side-coin average of the simulation-extraction game with the freshness test**: a
fresh forgery on a nonempty ring is a fresh statement of the simulation-extraction game of
`seAdversarySig`, accepted under the final oracle. -/
theorem hopSE_simTable_le (a : A.Aux) :
    ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
            (rdTable Sch n) Q fun _ _ _ => True).toChallenger id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
          (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} ≤
      ∑ s, PMF.uniformOfFintype (TableCoins Sch n Q) s *
        winTestProb Qs ((A.seAdversarySig bind adm s).alg a)
          ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAtKeys s.1 a) := by
  classical
  have hstep := fun H => AdaptiveIAlg.outLaw_absorb (A := A.alg a)
    (C := (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
      (rdTable Sch n) Q fun _ _ _ => True).toChallenger)
    (C' := simExtChallenger ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q)
    (PMF.uniformOfFintype (TableCoins Sch n Q))
    (fun s => (bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).atKeys s.1 s.2)
    (splitEquivOf Q (SignTable Sch n) _)
    (fun s c' => coinLaw_simSplitSig_splitEquivOf_symm
      (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind (rdTable Sch n) Q _ s c')
    (fun H s c' => by
      rw [atKeys_bkmSignRelay]
      exact (relays_sim_se_sig bind adm _ (rdTable Sch n) none Q s c').relays H _)
    (fun s c => atKeys_bkmSignRelay_route_injective bind adm s c) H
    (fun adv lg mlg c G => A.WinAt a c.1 adv.workspace.1 lg G ∧
      ∀ x' ∈ (requests mlg).take Q, x'.1 ≠ ((A.alg a).out adv.workspace.1).stmt)
  refine (tsum_congr fun H => congrArg (_ * ·) (Eq.trans ?_ (hstep H))).trans_le ?_
  · congr 1
    ext o
    refine exists_congr fun v => and_congr_right fun _ => ⟨fun h => ⟨h, ?_⟩, And.left⟩
    rw [SideRelay.requests_logs, atKeys_bkmSignRelay]
    exact hopSE_fresh_pub adm _ _ _ h.2.1 h.2.2
  rw [tsum_mul_sum_comm]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ zero_le
  unfold winTestProb
  refine le_of_le_of_eq ?_ (Alg.toOuterMeasure_realLaw_eq_tsum _ (outEquiv k e)
    fun v G => Wins ((A.seAdversarySig bind adm s).alg a).toTPKindAlg
      ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Qs Prod.fst
      ((outEquiv k e).symm ∘ G) v ∧
      A.okAtKeys s.1 a (advWorkspace ((A.seAdversarySig bind adm s).alg a).toTPKindAlg
        ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q v).1).symm
  refine ENNReal.tsum_le_tsum fun H => mul_le_mul_of_nonneg_left (MeasureTheory.measure_mono ?_)
    zero_le
  rintro o ⟨v, hv, hw, hf⟩
  refine ⟨v, hv, ?_⟩
  have hH : (outEquiv k e).symm ∘ (outEquiv k e) ∘ H = H := by
    funext x
    simp
  rw [hH]
  refine ⟨⟨fun x' hx' => ?_, hopSE_accepts hb hw.1⟩, fun pk hpk => hw.2.1.honest_ring pk hpk⟩
  have hq := KindAlg.map_request_history_stateAt ((A.seAdversarySig bind adm s).alg a).toTPKindAlg
    (simExtChallenger ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q) v.chal
    ((A.seAdversarySig bind adm s).alg a).toTPKindAlg.slots
  unfold SPBCS.queried at hx'
  rw [hq] at hx'
  exact hf x' hx'

/-- **A valid extracted candidate** at the side coins `s`, the auxiliary value `a`, the run's
registers `c` and the database `D`: some witness the database extractor returns for the claim's
statement decodes to a candidate that verifies under the key of a member not corrupted by the
first `Q` logged requests. -/
def ValidAt (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch))
    (s : TableCoins Sch n Q) (a : A.Aux)
    (c : SPBCS.Reg ((A.seAdversarySig bind adm s).alg a)
      ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q)
    (D : DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  ∃ w ∈ M.dbExtractBits Ext
      (advOut ((A.seAdversarySig bind adm s).alg a).toTPKindAlg _ Q c).stmt D,
    ∃ f ∈ decodeRing bind (advOut ((A.seAdversarySig bind adm s).alg a).toTPKindAlg _ Q c).stmt w,
      BaseForgery s.1 (fun i => BKMRequest.corrupt i ∈
          (requests (advWorkspace ((A.seAdversarySig bind adm s).alg a).toTPKindAlg _ Q c).1.logs).take Q)
        (fun _ _ => False) f

omit [Nonempty Sch.Sig] in
/-- **A fresh extracted witness that passes the test decodes to a valid candidate.** -/
theorem extractFreshTestProb_le_sig {Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)}
    (s : TableCoins Sch n Q) (a : A.Aux) :
    extractFreshTestProb Qs ((A.seAdversarySig bind adm s).alg a)
        ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B) Prod.fst
        (ringRel adm bind) Ext (A.okAtKeys s.1 a) ≤
      simProb (outEquiv k e)
        (extAdv Qs ((A.seAdversarySig bind adm s).alg a)
          ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B))
        (A.ValidAt Λ VE pub Sim T bind adm Ext s a) := by
  refine simProb_mono _ _ fun c D ⟨hx, _, hok⟩ => ?_
  obtain ⟨w, hw, hrel⟩ := (extractsAt_dbExtractBits_iff M (ringRel adm bind) Ext).2 hx
  have hR := hrel.2
  refine ⟨w, hw, _, (by simp only [decodeRing, hR.idx_lt, ↓reduceDIte]; rfl), hR.verify_eq, ?_⟩
  obtain ⟨i, hi, hc⟩ := hok _ hR.mem_ring
  exact ⟨i, hi, hc, not_false⟩

/-! #### The forger's run in a view independent of the relay -/

/-- **The law of the forger's run in a view independent of the relay**: the extraction run of the
adversary absorbed through the relay `X`, read as the first `Q` requests made, the claim's
statement and the measured database. -/
noncomputable def viewLaw (a : A.Aux)
    (X : SideRelay (BKMRequest Sch n N RMsg) (RingResponse Sch (M.Response B))
      (RelayStmt Sch n N RMsg) (M.Response B)) :
    MeasureTheory.OuterMeasure
      (List (BKMRequest Sch n N RMsg) × RingStmt Sch RMsg N × DB (Bits (queryBits k kN kS L)) (Out k e)) :=
  MeasureTheory.OuterMeasure.map (fun p =>
      ((requests (advWorkspace ((A.alg a).absorb X).toTPKindAlg
        ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q p.1.out).1.logs).take Q,
      (advOut ((A.alg a).absorb X).toTPKindAlg
        ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q p.1.out).stmt, p.2))
    (simLaw (outEquiv k e) (extAdv Qs ((A.alg a).absorb X)
      ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B)))

omit [Nonempty Sch.Sig] in
/-- **The view law averages**: it is the image of the Born weights of the simulated run, of total
weight one (`simLaw_univ`). -/
theorem isAvg_viewLaw (a : A.Aux)
    (X : SideRelay (BKMRequest Sch n N RMsg) (RingResponse Sch (M.Response B))
      (RelayStmt Sch n N RMsg) (M.Response B)) :
    OuterMeasureIsAvg (A.viewLaw Λ VE pub Sim T a X) := by
  exact isAvg_map_simLaw _ _ _

/-- **The candidates of a view**: the decodings of the witnesses the database extractor returns
for the statement from the database. -/
def candsOf (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch))
    (x : List (BKMRequest Sch n N RMsg) × RingStmt Sch RMsg N ×
      DB (Bits (queryBits k kN kS L)) (Out k e)) : Set (Sch.PK × Sch.Msg × Sch.Sig) :=
  {f | ∃ w ∈ M.dbExtractBits Ext x.2.1 x.2.2, f ∈ decodeRing bind x.2.1 w}

/-- **A valid candidate in a view** at the users' coins `keys`: a candidate that verifies under the
key of a member whose corruption the view's requests do not include. -/
def ValidView (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch))
    (keys : Fin n → Sch.KeyCoins)
    (x : List (BKMRequest Sch n N RMsg) × RingStmt Sch RMsg N ×
      DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  ∃ f ∈ candsOf (M := M) bind Ext x, BaseForgery keys (fun i => BKMRequest.corrupt i ∈ x.1)
    (fun _ _ => False) f

/-- **The strong forger wins in a view** at the users' coins `keys` and the signing tables `tabs`:
the candidate it picks is a strong forgery for the corruptions of the view's requests and the
signatures the signing relay returned on them. -/
def StrongView (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch))
    (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n)
    (x : List (BKMRequest Sch n N RMsg) × RingStmt Sch RMsg N ×
      DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  ∃ f, pickStrong keys (fun i => BKMRequest.corrupt i ∈ x.1)
      ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).Returned keys tabs x.1)
      (candsOf (M := M) bind Ext x) = some f ∧
    StrongForgery keys (fun i => BKMRequest.corrupt i ∈ x.1)
      ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).Returned keys tabs x.1) f

/-- **The valid candidate of a view is the signature returned at request `j`**: the candidate the
forger picks among the valid ones (`pickForgery`) carries the signature of user `i` on
`bind R m` at the entry `(i, bind R m)` of table `j`, request `j` being the ring-signing request
`(i, R, m)`. -/
def CollidesAt (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch))
    (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) (j : Fin Q)
    (x : List (BKMRequest Sch n N RMsg) × RingStmt Sch RMsg N ×
      DB (Bits (queryBits k kN kS L)) (Out k e)) : Prop :=
  ∃ f, pickForgery (BaseForgery keys (fun i => BKMRequest.corrupt i ∈ x.1) (fun _ _ => False))
      (candsOf (M := M) bind Ext x) = some f ∧
    ∃ i R m, x.1[(j : ℕ)]? = some (.ringSign i R m) ∧
      f.2.2 = Sch.signWith (Sch.sk (keys i)) (bind R.1 m) (tabs j (i, bind R.1 m))

omit [Fintype RMsg] [∀ j i, Nonempty ((P j).Challenge i)]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] [NeZero n] [Nonempty Sch.Sig] in
/-- **A valid candidate gives a strong forgery or a collision**: either the forger's pick is a
strong forgery, or the picked valid candidate's signature was returned by the signing oracle at
some request below `Q`. -/
theorem validView_imp (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch))
    (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n)
    {x : List (BKMRequest Sch n N RMsg) × RingStmt Sch RMsg N ×
      DB (Bits (queryBits k kN kS L)) (Out k e)}
    (h : ValidView (M := M) bind Ext keys x) :
    StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x ∨ ∃ j, CollidesAt (M := M) bind Ext keys tabs j x := by
  classical
  obtain ⟨f, hpick, hf⟩ := exists_mem_iff_pickForgery.1 h
  have hfmem : f ∈ candsOf (M := M) bind Ext x := by
    unfold pickForgery at hpick
    split_ifs at hpick with hex
    obtain rfl := Option.some_inj.1 hpick
    exact (Classical.choose_spec hex).1
  by_cases hs : StrongForgery keys (fun i => BKMRequest.corrupt i ∈ x.1)
      ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).Returned keys tabs x.1) f
  · exact Or.inl (exists_mem_iff_pickForgery.1 ⟨f, hfmem, hs⟩)
  · right
    obtain ⟨i, hi, hc, -⟩ := hf.exists_user
    have hret : (bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).Returned keys tabs x.1 i
        f.2.2 := by
      by_contra hr
      exact hs ⟨hf.verify_eq, i, hi, hc, hr⟩
    obtain ⟨⟨r, c⟩, hp, hpQ, R, m, hpr, hσ⟩ := exists_of_returned_bkmSignRelay adm bind hret
    refine ⟨⟨c, hpQ⟩, f, hpick, i, R, m, ?_, hσ⟩
    have hget := List.mem_zipIdx_iff_getElem?.1 hp
    simp only at hpr hget
    rw [← hpr]
    exact hget

omit [Nonempty Sch.Sig] in
/-- **The view law of the signing relay depends on the tables only through their public values**
(`atKeys_bkmSignRelay`, `sigPubs_rdTable`). -/
theorem viewLaw_atKeys_eq (a : A.Aux) (keys : Fin n → Sch.KeyCoins)
    (tabs : Fin Q → SignTable Sch n) :
    A.viewLaw Λ VE pub Sim T a ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).atKeys keys tabs) =
      A.viewLaw Λ VE pub Sim T a (seRelayPub (fun i => Sch.pk (keys i)) keys adm
        (pubsOfTable bind (pubTable keys tabs))) := by
  rw [atKeys_bkmSignRelay, sigPubs_rdTable]

omit [Nonempty Sch.Sig] in
/-- **The collision at request `j` has probability at most `γ` over the signing tables** for a
scheme whose signatures are guessed from their public values with probability at most `γ`
(`hγ`): the run depends on the tables only through the public values of their entries
(`viewLaw_atKeys_eq`), and the colliding signature is an entry's signature given its public value
(`PMF.uniformOfFintype_table_guess_le`, `sum_mul_le_of_isAvg`). -/
theorem sum_viewLaw_collidesAt_le {γ : ℝ≥0∞} (hγ : Sch.SigGivenPubLe γ)
    (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)) (a : A.Aux)
    (keys : Fin n → Sch.KeyCoins) (j : Fin Q) :
    ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs *
        A.viewLaw Λ VE pub Sim T a
          ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).atKeys keys tabs)
          {x | CollidesAt (M := M) bind Ext keys tabs j x} ≤ γ := by
  classical
  simp_rw [A.viewLaw_atKeys_eq Λ VE pub Sim T bind adm a keys]
  refine sum_mul_le_of_isAvg _ (pubTable keys) (fun v => A.viewLaw Λ VE pub Sim T a
      (seRelayPub (fun i => Sch.pk (keys i)) keys adm (pubsOfTable bind v)))
    (fun v => A.isAvg_viewLaw Λ VE pub Sim T a _) (fun tabs => {x | CollidesAt (M := M) bind Ext keys tabs j x})
    fun t₀ x => ?_
  by_cases hx : ∃ f, pickForgery (BaseForgery keys (fun i => BKMRequest.corrupt i ∈ x.1)
      (fun _ _ => False)) (candsOf (M := M) bind Ext x) = some f ∧
      ∃ i R m, x.1[(j : ℕ)]? = some (.ringSign i R m)
  · obtain ⟨f, hf, i, R, m, hj⟩ := hx
    refine le_trans (MeasureTheory.measure_mono (show _ ⊆ {t : Fin Q → SignTable Sch n |
        pubTable keys t = pubTable keys t₀ ∧
          Sch.signWith (Sch.sk (keys i)) (bind R.1 m) (t j (i, bind R.1 m)) = f.2.2}
      from fun t ht => ⟨ht.1, ?_⟩)) ?_
    · obtain ⟨f', hf', i', R', m', hj', hσ⟩ := ht.2
      rw [hf] at hf'
      obtain rfl := Option.some_inj.1 hf'
      rw [hj] at hj'
      simp only [Option.some_inj, BKMRequest.ringSign.injEq] at hj'
      obtain ⟨rfl, rfl, rfl⟩ := hj'
      exact hσ.symm
    · exact PMF.uniformOfFintype_table_guess_le
        (fun (e : Fin n × Sch.Msg) (c : Sch.SignCoins) =>
          Sch.pub (Sch.signWith (Sch.sk (keys e.1)) e.2 c))
        (fun (e : Fin n × Sch.Msg) (c : Sch.SignCoins) => Sch.signWith (Sch.sk (keys e.1)) e.2 c)
        (fun e y z => hγ (keys e.1) e.2 y z) (pubTable keys t₀) j (i, bind R.1 m) f.2.2
  · refine le_trans (MeasureTheory.measure_mono (show _ ⊆ (∅ : Set (Fin Q → SignTable Sch n))
      from fun t ht => hx ?_)) ?_
    · obtain ⟨f, hf, i, R, m, hj, -⟩ := ht.2
      exact ⟨f, hf, i, R, m, hj⟩
    · rw [MeasureTheory.measure_empty]
      exact zero_le


/-! #### The base forgery -/

omit [Nonempty Sch.Sig] in
/-- **The extraction probability of a valid candidate is that of the view law.** -/
theorem simProb_validAt_eq (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch))
    (s : TableCoins Sch n Q) (a : A.Aux) :
    simProb (outEquiv k e)
        (extAdv Qs ((A.seAdversarySig bind adm s).alg a)
          ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B))
        (A.ValidAt Λ VE pub Sim T bind adm Ext s a) =
      A.viewLaw Λ VE pub Sim T a
        ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).atKeys s.1 s.2)
        {x | ValidView (M := M) bind Ext s.1 x} := by
  simp only [seAdversarySig]
  rw [viewLaw, MeasureTheory.OuterMeasure.map_apply]
  unfold simProb
  congr 1
  ext p
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, ValidAt, ValidView, candsOf, seAdversarySig]
  constructor
  · rintro ⟨w, hw, f, hf, h⟩
    exact ⟨f, ⟨w, hw, hf⟩, h⟩
  · rintro ⟨f, ⟨w, hw, hf⟩, h⟩
    exact ⟨w, hw, f, hf, h⟩

omit [Nonempty Sch.Sig] in
/-- **The success of the strong forger at one value of the keys, the tables and the auxiliary
input is that of the view law**: its corrupted users are those whose corruption the requests
made include (`corrupt_mem_calls_bkmSignRelay`). -/
theorem simProb_strong_eq (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch))
    (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) (a : A.Aux) :
    simProb (outEquiv k e)
        ((A.signForger Λ VE pub Sim T bind adm Ext).run Qs Q (kqOf Mg nr B B) keys tabs a)
        (fun c D => ∃ f, (A.signForger Λ VE pub Sim T bind adm Ext).output Q keys tabs a c D =
            some f ∧
          StrongForgery keys ((A.signForger Λ VE pub Sim T bind adm Ext).Corrupted Q keys tabs a c)
            ((A.signForger Λ VE pub Sim T bind adm Ext).relay.Returned keys tabs
              ((A.signForger Λ VE pub Sim T bind adm Ext).made Q keys tabs a c)) f) =
      A.viewLaw Λ VE pub Sim T a
        ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).atKeys keys tabs)
        {x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} := by
  rw [viewLaw, MeasureTheory.OuterMeasure.map_apply]
  unfold simProb
  congr 1
  ext p
  have hc : (A.signForger Λ VE pub Sim T bind adm Ext).Corrupted Q keys tabs a p.1.out =
      fun i => BKMRequest.corrupt i ∈
        (A.signForger Λ VE pub Sim T bind adm Ext).made Q keys tabs a p.1.out :=
    funext fun i => propext (corrupt_mem_calls_bkmSignRelay (Resp := M.Response B) adm bind keys
      tabs _ i)
  simp only [Set.mem_ofPred_eq, SignRelayForger.output, hc]
  rfl

omit [Nonempty Sch.Sig] in
/-- **The extraction probability of a valid candidate, averaged over the side coins, is at most
the strong forger's success plus `Q · γ`** for a scheme whose signatures are guessed from their
public values with probability at most `γ` (`hγ`): a valid candidate is a strong forgery or a
collision at one of the `Q` requests (`validView_imp`), each of probability at most `γ`
(`sum_viewLaw_collidesAt_le`). -/
theorem sum_validAt_le {γ : ℝ≥0∞} (hγ : Sch.SigGivenPubLe γ)
    (Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)) :
    ∑ s, PMF.uniformOfFintype (TableCoins Sch n Q) s * ∑' a, A.aux a *
        simProb (outEquiv k e)
          (extAdv Qs ((A.seAdversarySig bind adm s).alg a)
            ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B))
          (A.ValidAt Λ VE pub Sim T bind adm Ext s a) ≤
      A.strongForgerSuccess Λ VE pub Sim T bind adm Ext + Q * γ := by
  classical
  set ν := fun (a : A.Aux) (keys : Fin n → Sch.KeyCoins) (tabs : Fin Q → SignTable Sch n) =>
    A.viewLaw Λ VE pub Sim T a ((bkmSignRelay Sch n N RMsg (M.Response B) adm bind Q).atKeys keys tabs)
    with hν
  have hpt : ∀ a keys tabs, ν a keys tabs {x | ValidView (M := M) bind Ext keys x} ≤
      ν a keys tabs {x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} +
        ∑ j : Fin Q, ν a keys tabs {x | CollidesAt (M := M) bind Ext keys tabs j x} := by
    intro a keys tabs
    calc ν a keys tabs {x | ValidView (M := M) bind Ext keys x}
        ≤ ν a keys tabs ({x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} ∪
            ⋃ j : Fin Q, {x | CollidesAt (M := M) bind Ext keys tabs j x}) :=
          MeasureTheory.measure_mono fun x hx =>
            (validView_imp bind adm Ext keys tabs hx).elim Or.inl
              fun ⟨j, hj⟩ => Or.inr (Set.mem_iUnion.2 ⟨j, hj⟩)
      _ ≤ _ := (MeasureTheory.measure_union_le _ _).trans
          (add_le_add le_rfl (MeasureTheory.measure_iUnion_fintype_le _ _))
  have key : ∀ keys : Fin n → Sch.KeyCoins,
      ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs * ∑' a, A.aux a *
          ν a keys tabs {x | ValidView (M := M) bind Ext keys x} ≤
        ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs * ∑' a, A.aux a *
          ν a keys tabs {x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} +
          Q * γ := by
    intro keys
    calc _ ≤ ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs * ∑' a, A.aux a *
          (ν a keys tabs {x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} +
            ∑ j : Fin Q, ν a keys tabs {x | CollidesAt (M := M) bind Ext keys tabs j x}) :=
          Finset.sum_le_sum fun tabs _ => mul_le_mul_of_nonneg_left
            (ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left (hpt a keys tabs) zero_le)
            zero_le
      _ = ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs * ∑' a, A.aux a *
            ν a keys tabs {x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} +
          ∑' a, A.aux a * ∑ j : Fin Q, ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs *
            ν a keys tabs {x | CollidesAt (M := M) bind Ext keys tabs j x} := by
          simp_rw [mul_add, ENNReal.tsum_add, mul_add, Finset.sum_add_distrib]
          congr 1
          rw [← tsum_mul_sum_comm]
          refine tsum_congr fun a => congrArg (A.aux a * ·) ?_
          simp_rw [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs * ∑' a, A.aux a *
            ν a keys tabs {x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} +
          ∑' a, A.aux a * ∑ _j : Fin Q, γ :=
          add_le_add le_rfl (ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun j _ => A.sum_viewLaw_collidesAt_le Λ VE pub Sim T bind adm hγ
              Ext a keys j) zero_le)
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  rw [Fintype.sum_prod_type]
  calc ∑ keys, ∑ tabs, PMF.uniformOfFintype (TableCoins Sch n Q) (keys, tabs) * ∑' a, A.aux a *
        simProb (outEquiv k e)
          (extAdv Qs ((A.seAdversarySig bind adm (keys, tabs)).alg a)
            ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B))
          (A.ValidAt Λ VE pub Sim T bind adm Ext (keys, tabs) a)
      = ∑ keys, PMF.uniformOfFintype (Fin n → Sch.KeyCoins) keys *
          ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs * ∑' a, A.aux a *
            ν a keys tabs {x | ValidView (M := M) bind Ext keys x} := by
        refine Finset.sum_congr rfl fun keys _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun tabs _ => ?_
        rw [uniformOfFintype_prod_apply, mul_assoc]
        simp_rw [A.simProb_validAt_eq Λ VE pub Sim T bind adm Ext]
        rfl
    _ ≤ ∑ keys, PMF.uniformOfFintype (Fin n → Sch.KeyCoins) keys *
          (∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs * ∑' a, A.aux a *
            ν a keys tabs {x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} +
            Q * γ) :=
        Finset.sum_le_sum fun keys _ => mul_le_mul_of_nonneg_left (key keys) zero_le
    _ = _ := by
        have hk1 : ∑ keys, PMF.uniformOfFintype (Fin n → Sch.KeyCoins) keys = 1 := by
          have h1 := (PMF.uniformOfFintype (Fin n → Sch.KeyCoins)).tsum_coe
          rwa [tsum_fintype] at h1
        have hS : ∑ keys, PMF.uniformOfFintype (Fin n → Sch.KeyCoins) keys *
            ∑ tabs, PMF.uniformOfFintype (Fin Q → SignTable Sch n) tabs * ∑' a, A.aux a *
              ν a keys tabs {x | StrongView (M := M) (B := B) (Q := Q) bind adm Ext keys tabs x} =
            A.strongForgerSuccess Λ VE pub Sim T bind adm Ext := by
          unfold strongForgerSuccess SignRelayForger.success
          refine Finset.sum_congr rfl fun keys _ => congrArg (_ * ·) (Finset.sum_congr rfl
            fun tabs _ => congrArg (_ * ·) (tsum_congr fun a => congrArg (_ * ·) ?_))
          exact (A.simProb_strong_eq Λ VE pub Sim T bind adm Ext keys tabs a).symm
        rw [← hS]
        simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hk1, one_mul]

/-! #### The headline -/

/-- **Unforgeability with respect to insider corruption (BKM06 Definition 7) of the ring signature
compiled by spBCS, at every base-message map, from strong unforgeability** (TCC 2006, LNCS p. 67;
ePrint 2005/304, p. 7: adversarially chosen rings, adaptive corruption, ring-signing queries, no
ordinary signing oracle), converted signatures (`bind R m = m`) included, for a base scheme whose
public value may depend on the signer's key. For a base scheme with correctness error `εc`
(`hcorr`) whose signatures are guessed from their public values with probability at most `γ`
(`hγ`, `SigScheme.SigGivenPubLe`), the spBCS compilation `M` of a ring composite that is
honest-verifier zero knowledge with error `δ` at the joint simulator `Sim` (`hvzk`) and
round-by-round knowledge sound in the series–parallel order at the extractor `Ext` with errors `ε`
(`hrbr`), with the proof format bounded by `B` (`hb`) and digests of at least one byte (`hk`): the
probability that an adversary of BKM06 with at most `Q` requests and `t` queries of its own wins
(`insiderWinProb`, the ring signatures produced by the compiled honest prover `niProver` at the
site layout `Λ`, run through `queryEncoding`) is at most the success probability of the explicit
forger of the multi-user strong-unforgeability game with adaptive corruption
(`strongForgerSuccess`: the forger reaches the keys only through public keys, signatures and
corruptions of the base oracles, asks one signature per ring-signing request, and outputs one
candidate), plus `Q · γ` (an extracted signature that the oracle returned), the zero-knowledge
error `zkError δ t Q`, the simulation-extraction error at the simulator's `q` queries, the
knowledge error at `t + Q · q_P + kq` queries (the forgeries on the empty ring), and `2 Q εc` (the
drawn signatures that fail to verify, once in the real game and once in the simulated one). Here
`kq = kqOf Mg nr B B` bounds the verifier's queries and `q_P` those of one honest prover run. -/
theorem insiderWinProb_le_of_strongUnforgeability (hk : 0 < k) {εc : ℝ≥0∞}
    (hcorr : Sch.CorrectWithin εc) {γ : ℝ≥0∞} (hγ : Sch.SigGivenPubLe γ) {δ : ℝ≥0}
    (hvzk : CausalHVZK VE.MV (ringRel adm bind) honest pub Sim δ)
    {Ext : CausalExtractor P τ (RingStmt Sch RMsg N) (RingWit Sch)}
    {St : CausalStateFn P τ (RingStmt Sch RMsg N)} {ε : ChIdx P τ → ℝ≥0}
    (hrbr : CausalRBRKnowledgeSound (ringRel adm bind) Vr Ext St ε) :
    A.insiderWinProb (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind adm ≤
      A.strongForgerSuccess Λ VE pub Sim T bind adm Ext + Q * γ +
        ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr B B) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q +
        knowledgeError k e (kqOf Mg nr B B)
          (t + Q * (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding).q +
            kqOf Mg nr B B) M.senc.digestsPerInput Mg.nJ (maxError ε) +
        2 * Q * εc := by
  classical
  have hkq : ∀ x h π, M.Accepts h x π (Qs x) → (M.queries x π h (Qs x)).length ≤ kqOf Mg nr B B :=
    fun _ _ _ hv => queries_length_le_of_formatBounds hb hv
  have h0 := A.emptyRing_le_knowledgeError (((M.niProver Λ honest E hb).mapOutput some).encode
    queryEncoding) bind adm (fun _ => rfl)
    (M.knowledgeBound (ringRel adm bind) Ext St hrbr Qs _ hkq)
  have hse := (weak_online_simulation_extractability_qrom (B := B) Qs hkq hrbr
    (seSimulator (B := B) Λ VE pub Sim T)
    (simAssignsAtKeys_seSimulator Λ VE pub Sim T hk)).unruhSimExtraction_of_queryFreeTest
  have hs : ∀ s : TableCoins Sch n Q, ∑' a, A.aux a *
      winTestProb Qs ((A.seAdversarySig bind adm s).alg a)
        ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAtKeys s.1 a) ≤
      ∑' a, A.aux a * simProb (outEquiv k e)
        (extAdv Qs ((A.seAdversarySig bind adm s).alg a)
          ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B))
        (A.ValidAt Λ VE pub Sim T bind adm Ext s a) +
        M.simExtractionError (kqOf Mg nr B B) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q := fun s =>
    (hse (RelayStmt Sch n N RMsg) Prod.fst t Q (A.seAdversarySig bind adm s)
      fun a => A.okAtKeys s.1 a).trans
      (add_le_add (ENNReal.tsum_le_tsum fun a =>
        mul_le_mul_of_nonneg_left (A.extractFreshTestProb_le_sig Λ VE pub Sim T bind adm s a)
          zero_le) le_rfl)
  have hσ : ∑ s : TableCoins Sch n Q, PMF.uniformOfFintype (TableCoins Sch n Q) s = 1 := by
    have h1 := (PMF.uniformOfFintype (TableCoins Sch n Q)).tsum_coe
    rwa [tsum_fintype] at h1
  have hσ' : ∑ s : SideCoins Sch n Q, PMF.uniformOfFintype (SideCoins Sch n Q) s = 1 := by
    have h1 := (PMF.uniformOfFintype (SideCoins Sch n Q)).tsum_coe
    rwa [tsum_fintype] at h1
  have ha : ∀ a, ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
      (((A.alg a).toKindAlg.composeBothOut
        (challenger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind adm
          (Q := Q)) id).outLaw H).toOuterMeasure
        {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} ≤
      ∑ s, PMF.uniformOfFintype (TableCoins Sch n Q) s *
        winTestProb Qs ((A.seAdversarySig bind adm s).alg a)
          ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAtKeys s.1 a) +
        ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc := by
    intro a
    have hsim : ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
            (rdCoins Sch n) Q (drawOkSig Sch N RMsg bind (rdCoins Sch n))).toChallenger id).outLaw
            H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
            (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} ≤
        ∑ s, PMF.uniformOfFintype (TableCoins Sch n Q) s *
          winTestProb Qs ((A.seAdversarySig bind adm s).alg a)
            ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAtKeys s.1 a) +
          Q * εc := by
      refine (tsum_pmf_mul_le_add _ _ _ _ fun H => A.outLaw_simCheckedSig_le Λ VE pub Sim T bind
        adm hcorr a H).trans (add_le_add ?_ le_rfl)
      simp_rw [A.outLaw_simSig_eq_table Λ VE pub Sim T bind adm a]
      exact A.hopSE_simTable_le Λ hb VE pub Sim T bind adm a
    have hreal : ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          ((checkedBkmLayer (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind
            adm).challenger Q) id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} ≤
        ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
          (((A.alg a).toKindAlg.composeBothOut
            (simSplitSig (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T) adm bind
              (rdCoins Sch n) Q (drawOkSig Sch N RMsg bind (rdCoins Sch n))).toChallenger id).outLaw
              H).toOuterMeasure
            {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs
              (H.reprogram ((A.alg a).toKindAlg.postAss _ v.chal))} +
          ENNReal.ofReal (M.zkError δ t Q) := by
      simp_rw [A.outLaw_bkm_eq_sum_real_sig Λ hb honest bind adm a]
      rw [tsum_mul_sum_comm]
      simp_rw [← A.acceptProb_distinguisherSig bind adm]
      calc _ ≤ ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
            ((A.distinguisherSig bind adm a s).acceptProb (simChallenger (relayRel bind adm)
              ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q) +
              ENNReal.ofReal (M.zkError δ t Q)) :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
              (A.acceptProb_real_le_sig Λ hb honest VE pub Sim T bind adm hvzk a s) zero_le
        _ = ∑ s, PMF.uniformOfFintype (SideCoins Sch n Q) s *
              (A.distinguisherSig bind adm a s).acceptProb (simChallenger (relayRel bind adm)
                ((M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).comap Prod.fst) Q) +
              ENNReal.ofReal (M.zkError δ t Q) := by
            simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hσ', one_mul]
        _ = _ := by
            congr 1
            simp_rw [A.acceptProb_distinguisherSig bind adm]
            rw [← tsum_mul_sum_comm]
            simp_rw [A.sum_sim_eq_outLaw_simSig Λ VE pub Sim T bind adm a]
    calc _ ≤ _ := tsum_pmf_mul_le_add _ _ _ _ fun H => A.outLaw_bkm_le_checked Λ hb honest bind adm
            hcorr a H
      _ ≤ _ := add_le_add (hreal.trans (add_le_add hsim le_rfl)) le_rfl
      _ = _ := by ring
  refine (A.insiderWinProb_le_add _ bind adm).trans ?_
  have hmain : ∑' a, A.aux a * ∑' H, PMF.uniformOfFintype (Bits (queryBits k kN kS L) → XOut k e) H *
        (((A.alg a).toKindAlg.composeBothOut
          (challenger (((M.niProver Λ honest E hb).mapOutput some).encode queryEncoding) bind adm
            (Q := Q)) id).outLaw H).toOuterMeasure
          {o | ∃ v ∈ o, A.WinAt a v.chal.coins.1 v.adv.workspace.1 v.chal.logs H} ≤
      A.strongForgerSuccess Λ VE pub Sim T bind adm Ext + Q * γ + ENNReal.ofReal (M.zkError δ t Q) +
        M.simExtractionError (kqOf Mg nr B B) (maxError ε)
          (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q + 2 * Q * εc := by
    calc _ ≤ ∑' a, A.aux a * (∑ s, PMF.uniformOfFintype (TableCoins Sch n Q) s *
          winTestProb Qs ((A.seAdversarySig bind adm s).alg a)
            ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAtKeys s.1 a) +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc)) :=
          ENNReal.tsum_le_tsum fun a => mul_le_mul_of_nonneg_left ((ha a).trans_eq (add_assoc _ _ _))
            zero_le
      _ = ∑ s, PMF.uniformOfFintype (TableCoins Sch n Q) s * ∑' a, A.aux a *
            winTestProb Qs ((A.seAdversarySig bind adm s).alg a)
              ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q Prod.fst (A.okAtKeys s.1 a) +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc) := by
          rw [tsum_pmf_mul_add, tsum_mul_sum_comm]
      _ ≤ ∑ s, PMF.uniformOfFintype (TableCoins Sch n Q) s * (∑' a, A.aux a * simProb (outEquiv k e)
            (extAdv Qs ((A.seAdversarySig bind adm s).alg a)
              ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B))
            (A.ValidAt Λ VE pub Sim T bind adm Ext s a) +
            M.simExtractionError (kqOf Mg nr B B) (maxError ε)
              (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q) +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc) :=
          add_le_add (Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hs s) zero_le) le_rfl
      _ = ∑ s, PMF.uniformOfFintype (TableCoins Sch n Q) s * ∑' a, A.aux a * simProb (outEquiv k e)
            (extAdv Qs ((A.seAdversarySig bind adm s).alg a)
              ((seSimulator (B := B) Λ VE pub Sim T).comap Prod.fst) Q (kqOf Mg nr B B))
            (A.ValidAt Λ VE pub Sim T bind adm Ext s a) +
          M.simExtractionError (kqOf Mg nr B B) (maxError ε)
            (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc) := by
          simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hσ, one_mul]
      _ ≤ A.strongForgerSuccess Λ VE pub Sim T bind adm Ext + Q * γ +
          M.simExtractionError (kqOf Mg nr B B) (maxError ε)
            (M.niJointSimulatorProg Λ VE.toViewRead B pub Sim T).q t Q +
          (ENNReal.ofReal (M.zkError δ t Q) + 2 * Q * εc) :=
          add_le_add (add_le_add (A.sum_validAt_le Λ VE pub Sim T bind adm hγ Ext) le_rfl)
            le_rfl
      _ = _ := by ring
  calc _ ≤ _ := add_le_add hmain h0
    _ = _ := add_right_comm _ _ _

end BKMAdversary

end SPBCS

end GordieHowe.Ring
