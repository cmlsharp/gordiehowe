-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeGuess
public import GordieHowe.Applications.Ring.MLDSAW1Unforgeability
public import GordieHowe.Applications.Ring.RingForgerSplit
public import GordieHowe.Applications.Ring.KeyFreeSignFactors

@[expose] public section

/-!
# Key-free signers that factor through the base component and a public part

A key-free signer `ksign` (the signer of the key-free relay,
`GordieHowe/Applications/Ring/KeyFreeRelay.lean`) whose run at an oracle `H` is read from the base
component `base sp H` and one value of the second component: the public part and the signature
`out` at the base component and the side coins, then the published value `pub`, and the assignment
`asg` from the public part and the second component of `H` at the kept point `xk`
(`KFSignFactors`). At a fixed base component the side coins enter the run only through `out`; the
signature is the secret part, guessed from the public part with the bound of
`GordieHowe/Applications/Ring/MLDSAW1KeyFreeGuess.lean`.

- `KFSignFactors` (`GordieHowe/Applications/Ring/KeyFreeSignFactors.lean`): the factorization.
- `w1KFPre`, `w1KFPreq`, `w1KFPre_queries`, `run_w1KFPre`: the key-free signer `w1KFSign` without
  its final read at the kept point, returning the kept data; at most `w1KFq - 1` queries.
- `w1KFOutB`, `run_w1KFOutB`, `w1KFOutB_queries`: `w1KFPre` read at the base component (each
  answer `y₁` read as `sp.symm (y₁, 0)`); it runs as `w1KFOut` with the kept point `w1KFKept`, the
  published value `w₁` and the assignment of the value with base component `v`.
- `w1KFOut`, `w1KFKept`, `w1KFFactors`: the key-free signer of the ML-DSA ring publishing `w₁`
  factors, with public part `(w1Of pk σ, v)` for a kept output `(w₁, σ, v)` of `kfLoop`, for
  decodings reading only the base component, with its program over the base component
  `w1KFOutB`; the relay `kfRelaySide` then makes one oracle read and `w1KFPreq + 2N` side reads
  per request.
- `sum_iSup_prob_w1KFOut_le`: the signature is hard to guess from that public part, with the
  bound `k · T · |BucketVec| / |MaskBox|` of `sum_iSup_prob_kfLoop_le`.
-/

open scoped ENNReal


namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum RingSignature.KeyFree

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  (prims : Primitives p) [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁]
  [AddGroup Y₂] (O : W1Oracles X Y p prims Msg N reps) (sp : Y ≃+ Y₁ × Y₂) (βmin : ℚ≥0)
  (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p) (k D : ℕ) {RMsg : Type}
  (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg) [Fintype Msg] [DecidableEq Msg]
  [Fintype RMsg] [DecidableEq RMsg]

open Classical in
/-- **The public part and the signature of the key-free signer at a base component** `ω`: the
key-free loop at the members' commitment hashes read at `ω`, a kept output `(w₁, σ, v)` giving the
public part `(w1Of pk σ, v)` and the signature `σ`; `none` unless the ring passes the public check
and its members' message representatives are distinct at `ω`, and `pk` is in the ring. -/
noncomputable def w1KFOut (ω : X → Y₁) (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N)
    (_c : ℕ) (m : RMsg) (sc : KFCoins (p := p) (T := T) k D Y₁) :
    Option ((BucketVec p × Y₁) × FIPSSignature p prims) :=
  if RingCheck prims βmin tol (O.gOrc (join sp ω 0)) R ∧
      MuDistinct prims (O.muOrc (join sp ω 0)) R (bmsg R m) then
    if hi : R.1.idxOf pk < R.1.length then
      (kfLoop prims O sp βmin pk R ⟨_, hi⟩
        (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc (join sp ω 0))) sc).map fun s =>
        ((w1Of prims enc pk s.2.1, s.2.2), s.2.1)
    else none
  else none

/-- **The kept point of a public part** `(w₁, v)` at a base component `ω`: the commitment-hash
point at the signer's message representative read at `ω` and `w₁`. -/
def w1KFKept (ω : X → Y₁) (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (m : RMsg)
    (q : BucketVec p × Y₁) : X :=
  O.chPt (O.muAt sp (ω (O.muPt (pubTr prims pk, bmsg R m))), q.1)

/-- **The key-free signer before its kept read**: `w1KFSign` without its final read at the kept
point; on a kept output `(w₁, σ, v)`, the public part `(w₁, v)`, the signature `σ`, the kept point
`x = H(µ, w₁)`, the published value `w₁` and the assignment at `x` of the value with base
component `v`. -/
noncomputable def w1KFPre (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (_c : ℕ)
    (m : RMsg) (sc : KFCoins (p := p) (T := T) k D Y₁) :
    OracleProg X Y (Option (((BucketVec p × Y₁) × FIPSSignature p prims) ×
      (X × BucketVec p × (Y₂ → List (Assignment X Y))))) :=
  (ringCheckProg prims O βmin tol R).bind fun ok =>
    (muDistinctProg prims O R (bmsg R m)).bind fun ok' =>
      if ok ∧ ok' then
        if hi : R.1.idxOf pk < R.1.length then
          (OracleProg.queryAll (R.1.map fun x => O.muPt (pubTr prims x, bmsg R m))).bind fun ans =>
            .query (O.muPt (pubTr prims pk, bmsg R m)) fun yMu =>
              (OracleProg.tabulate (fun _ => default)
                  (Finset.univ.toList : List ((Fin k × Fin T) × Fin R.1.length)) fun ctj =>
                .query (O.chPt ((ans.map O.muAns).getD ctj.2 default,
                  kfW1s prims O sp k pk sc.1 ctj.1)) fun y => .pure (O.chAns y)).bind fun cs =>
                .pure ((kfLoop prims O sp βmin pk R ⟨_, hi⟩
                    (kfHashes (kfW1s prims O sp k pk sc.1) cs) sc).map fun s =>
                  (((w1Of prims enc pk s.2.1, s.2.2), s.2.1),
                    O.chPt (O.muAns yMu, w1Of prims enc pk s.2.1), w1Of prims enc pk s.2.1,
                    fun y₂ => [⟨O.chPt (O.muAns yMu, w1Of prims enc pk s.2.1),
                      sp.symm (s.2.2, y₂)⟩]))
        else .pure none
      else .pure none

/-- The query bound of `w1KFPre`: `w1KFq` without the kept read. -/
abbrev w1KFPreq (N reps k T : ℕ) : ℕ := N * reps + (N + (N + (1 + k * T * N)))

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg] in
/-- **The key-free signer before its kept read makes at most `w1KFPreq` queries.** -/
theorem w1KFPre_queries (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ)
    (m : RMsg) (sc : KFCoins (p := p) (T := T) k D Y₁) :
    (w1KFPre prims O sp βmin tol enc k D bmsg pk R c m sc).QueriesLE (w1KFPreq N reps k T) := by
  refine (ringCheckProg_queries prims O βmin tol R).bind fun ok =>
    (muDistinctProg_queries prims O R (bmsg R m)).bind fun ok' => ?_
  split_ifs with h hi
  · refine ((OracleProg.QueriesLE.queryAll _).mono (by simpa using R.2)).bind fun ans => ?_
    refine (OracleProg.QueriesLE.query (q := k * T * N) _ fun yMu => ?_).mono (by omega)
    have h₂ := OracleProg.QueriesLE.tabulate (fun _ => (default : CommitHashBytes p))
      (Finset.univ.toList : List ((Fin k × Fin T) × Fin R.1.length)) (q := 1)
      (P := fun ctj => .query (O.chPt ((ans.map O.muAns).getD ctj.2 default,
        kfW1s prims O sp k pk sc.1 ctj.1)) fun y => .pure (O.chAns y))
      fun ctj h => by simp [OracleProg.trace_query, OracleProg.trace_pure]
    refine ((h₂.mono (q' := k * T * N) ?_).bind (q₂ := 0) fun cs =>
      OracleProg.QueriesLE.pure _ _).mono (by omega)
    simp only [Finset.length_toList, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      mul_one]
    exact Nat.mul_le_mul_left _ R.2
  · exact OracleProg.QueriesLE.pure _ _
  · exact OracleProg.QueriesLE.pure _ _

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg] in
open Classical in
/-- **The key-free signer before its kept read at the oracle `H`** (`run_w1KFSign` without the
kept read). -/
theorem run_w1KFPre (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ) (m : RMsg)
    (sc : KFCoins (p := p) (T := T) k D Y₁) (H : X → Y) :
    (w1KFPre prims O sp βmin tol enc k D bmsg pk R c m sc).run H =
      if RingCheck prims βmin tol (O.gOrc H) R ∧ MuDistinct prims (O.muOrc H) R (bmsg R m) then
        if hi : R.1.idxOf pk < R.1.length then
          (kfLoop prims O sp βmin pk R ⟨_, hi⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) sc).map fun s =>
            (((w1Of prims enc pk s.2.1, s.2.2), s.2.1),
              O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bmsg R m))), w1Of prims enc pk s.2.1),
              w1Of prims enc pk s.2.1,
              fun y₂ => [⟨O.chPt (O.muAns (H (O.muPt (pubTr prims pk, bmsg R m))),
                w1Of prims enc pk s.2.1), sp.symm (s.2.2, y₂)⟩])
        else none
      else none := by
  have hg := run_ringCheckProg prims O βmin tol R H
  have hm := run_muDistinctProg prims O R (bmsg R m) H
  simp only [w1KFPre, OracleProg.run_bind]
  rcases hg' : (ringCheckProg prims O βmin tol R).run H <;>
    rcases hm' : (muDistinctProg prims O R (bmsg R m)).run H
  · have : ¬ RingCheck prims βmin tol (O.gOrc H) R := fun h => by simp_all
    simp [this]
  · have : ¬ RingCheck prims βmin tol (O.gOrc H) R := fun h => by simp_all
    simp [this]
  · have : ¬ MuDistinct prims (O.muOrc H) R (bmsg R m) := fun h => by simp_all
    simp [this]
  · have h1 : RingCheck prims βmin tol (O.gOrc H) R := hg.1 hg'
    have h2 : MuDistinct prims (O.muOrc H) R (bmsg R m) := hm.1 hm'
    simp only [and_self, ↓reduceIte, h1, h2]
    split_ifs with hi
    · simp only [OracleProg.run_bind, OracleProg.run_queryAll, OracleProg.run_query,
        OracleProg.run_tabulate, OracleProg.run_pure, Finset.mem_toList, Finset.mem_univ,
        ite_true]
      have hloop : kfLoop prims O sp βmin pk R ⟨_, hi⟩ (kfHashes (kfW1s prims O sp k pk sc.1)
          fun ctj => O.chAns (H (O.chPt ((((R.1.map fun x => O.muPt (pubTr prims x, bmsg R m)).map
            H).map O.muAns).getD ctj.2 default, kfW1s prims O sp k pk sc.1 ctj.1)))) sc =
          kfLoop prims O sp βmin pk R ⟨_, hi⟩
            (PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H)) sc :=
        kfLoop_congr prims O sp βmin pk R _ sc fun ct j =>
          kfHashes_apply k (kfW1s prims O sp k pk sc.1) _
            (fun j w => PMF.ringOf (ringPts prims R.1 (bmsg R m)) (O.hOrc H) (j, w))
            (fun ct j => chOrc_getD_eq prims O R (bmsg R m) H (j, _)) ct j
      rw [hloop]
    · rfl

/-- **The public part, the signature and the kept data of the key-free signer over the base
component**: `w1KFPre` with each answer `y₁` read as `sp.symm (y₁, 0)`. Irreducible, also to
the kernel (`w1KFOutB_def` unfolds it), so that relays at two side coins compare without running
the signer. -/
noncomputable irreducible_def w1KFOutB (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ)
    (m : RMsg) (sc : KFCoins (p := p) (T := T) k D Y₁) :
    OracleProg X Y₁ (Option (((BucketVec p × Y₁) × FIPSSignature p prims) ×
      (X × BucketVec p × (Y₂ → List (Assignment X Y))))) :=
  OracleProg.translate id (fun _ y₁ => sp.symm (y₁, 0))
    (w1KFPre prims O sp βmin tol enc k D bmsg pk R c m sc)

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg] in
/-- **The base-component program runs as `w1KFOut`** with the kept point `w1KFKept`, the
published value and the assignment of `w1KFFactors`. -/
theorem run_w1KFOutB (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ) (m : RMsg)
    (sc : KFCoins (p := p) (T := T) k D Y₁) (ω : X → Y₁) :
    (w1KFOutB prims O sp βmin tol enc k D bmsg pk R c m sc).run ω =
      (w1KFOut (T := T) prims O sp βmin tol enc k D bmsg ω pk R c m sc).map fun q =>
        (q, w1KFKept prims O sp bmsg ω pk R m q.1, q.1.1,
          fun y₂ => [⟨w1KFKept prims O sp bmsg ω pk R m q.1, sp.symm (q.1.2, y₂)⟩]) := by
  rw [w1KFOutB, OracleProg.run_translate]
  change (w1KFPre prims O sp βmin tol enc k D bmsg pk R c m sc).run (join sp ω 0) = _
  rw [run_w1KFPre]
  unfold w1KFOut
  split_ifs
  · simp only [Option.map_map]
    rfl
  · rfl
  · rfl

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg] in
/-- **The base-component program makes at most `w1KFPreq` queries.** -/
theorem w1KFOutB_queries (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ)
    (m : RMsg) (sc : KFCoins (p := p) (T := T) k D Y₁) :
    (w1KFOutB prims O sp βmin tol enc k D bmsg pk R c m sc).QueriesLE (w1KFPreq N reps k T) :=
  fun ω => by
    rw [w1KFOutB, OracleProg.trace_translate, List.length_map]
    exact w1KFPre_queries prims O sp βmin tol enc k D bmsg pk R c m sc _

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg] in
/-- **The key-free signer of the ML-DSA ring publishing `w₁` factors** through the base component
and the public part `(w1Of pk σ, v)`, for decodings reading only the base component (`hO`): its
run at `H` is `w1KFOut` at `base sp H`, the published value `w₁`, the signature, and the assignment
at the kept point `w1KFKept` of the value with base component `v` and the second component of
`H` there. -/
noncomputable def w1KFFactors (hO : O.ReadsFst sp) :
    KFSignFactors sp (BucketVec p × Y₁)
      (w1KFSign (T := T) prims O sp βmin tol enc k D bmsg) where
  out := w1KFOut (T := T) prims O sp βmin tol enc k D bmsg
  xk := w1KFKept prims O sp bmsg
  pub _ _ _ _ q := q.1
  asg ω pk R m q y₂ := [⟨w1KFKept prims O sp bmsg ω pk R m q, sp.symm (q.2, y₂)⟩]
  run_eq pk R c m s H := by
    have hb : base sp H = base sp (join sp (base sp H) 0) := (base_join sp _ _).symm
    rw [run_w1KFSign]
    unfold w1KFOut
    rw [← W1Oracles.gOrc_eq_of_base hO hb, ← W1Oracles.muOrc_eq_of_base hO hb,
      ← W1Oracles.hOrc_eq_of_base hO hb]
    split_ifs
    · simp only [Option.map_map]
      refine congrArg (Option.map · _) (funext fun s => ?_)
      simp only [Function.comp_apply, w1KFKept, hO.muAns_eq_muAt]
      rfl
    · rfl
    · rfl
  outB := w1KFOutB prims O sp βmin tol enc k D bmsg
  qOut := w1KFPreq N reps k T
  run_outB pk R c m s ω := run_w1KFOutB prims O sp βmin tol enc k D bmsg pk R c m s ω
  outB_queries := w1KFOutB_queries prims O sp βmin tol enc k D bmsg

omit [Fintype prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg]
  [DecidableEq Msg] [Fintype RMsg] [DecidableEq RMsg] in
open Classical in
/-- **The key-free signature is hard to guess from its public part `(w1Of pk σ, v)`** (the public
part of `w1KFFactors`; `sum_iSup_prob_kfLoop_le` for the public part `(w₁, v)`): at every base
component, summed over the public parts, the largest probability of a signature is at most
`k · T · |BucketVec| / |MaskBox|`. -/
theorem sum_iSup_prob_w1KFOut_le [NeZero D] [Fintype Y₁] [DecidableEq Y₁] [Nonempty Y₁]
    (ω : X → Y₁)
    (pk : PubKey p prims) (R : KeyRing (PubKey p prims) N) (c : ℕ) (m : RMsg) :
    ∑ y : BucketVec p × Y₁, ⨆ σ : FIPSSignature p prims,
        (PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)).toOuterMeasure
          {sc | w1KFOut (T := T) prims O sp βmin tol enc k D bmsg ω pk R c m sc = some (y, σ)} ≤
      k * T * Fintype.card (BucketVec p) / Fintype.card (MaskBox p) := by
  set μ := PMF.uniformOfFintype (KFCoins (p := p) (T := T) k D Y₁)
  have hone : ∀ (z : RqVec p.l) (v : Y₁),
      (PMF.uniformOfFintype (MaskBox p × Y₁)).toOuterMeasure {x | x.1.1 = z ∧ x.2 = v} ≤
        ((Fintype.card (MaskBox p) : ℝ≥0∞) * Fintype.card Y₁)⁻¹ := by
    intro z v
    by_cases h : ∃ x : MaskBox p × Y₁, x.1.1 = z ∧ x.2 = v
    · obtain ⟨x, hx1, hx2⟩ := h
      have hsub : {x' : MaskBox p × Y₁ | x'.1.1 = z ∧ x'.2 = v} ⊆ {x} := fun x' hx' =>
        Prod.ext (Subtype.ext (hx'.1.trans hx1.symm)) (hx'.2.trans hx2.symm)
      refine (MeasureTheory.measure_mono hsub).trans_eq ?_
      rw [PMF.toOuterMeasure_apply_singleton, PMF.uniformOfFintype_apply, Fintype.card_prod,
        Nat.cast_mul]
    · have hemp : {x' : MaskBox p × Y₁ | x'.1.1 = z ∧ x'.2 = v} = ∅ :=
        Set.eq_empty_iff_forall_notMem.2 fun x' hx' => h ⟨x', hx'⟩
      rw [hemp, MeasureTheory.measure_empty]
      exact zero_le
  have hpt : ∀ y : BucketVec p × Y₁, ∀ σ : FIPSSignature p prims,
      μ.toOuterMeasure {sc | w1KFOut (T := T) prims O sp βmin tol enc k D bmsg ω pk R c m sc =
        some (y, σ)} ≤ k * T * ((Fintype.card (MaskBox p) : ℝ≥0∞) * Fintype.card Y₁)⁻¹ := by
    intro y σ
    calc μ.toOuterMeasure {sc | w1KFOut (T := T) prims O sp βmin tol enc k D bmsg ω pk R c m sc =
          some (y, σ)}
        ≤ μ.toOuterMeasure (⋃ ct ∈ (Finset.univ : Finset (Fin k × Fin T)),
            {sc | sc.1 ct.1 ct.2 ∈ {x : MaskBox p × Y₁ | x.1.1 = σ.z ∧ x.2 = y.2}}) := by
          refine MeasureTheory.measure_mono fun sc hsc => ?_
          simp only [Set.mem_ofPred_eq, w1KFOut] at hsc
          split_ifs at hsc with h1 h2
          · obtain ⟨s, hs, heq⟩ := Option.map_eq_some_iff.1 hsc
            obtain ⟨c', t, e1, e2⟩ := exists_coins_of_kfLoop_eq_some pk R _ _ sc hs
            have hσ : s.2.1 = σ := congrArg Prod.snd heq
            have hv : s.2.2 = y.2 := congrArg (fun q => q.1.2) heq
            exact Set.mem_biUnion (Finset.mem_univ (c', t)) ⟨e1.trans (by rw [hσ]), e2.trans hv⟩
      _ ≤ ∑ ct ∈ (Finset.univ : Finset (Fin k × Fin T)),
            μ.toOuterMeasure
              {sc | sc.1 ct.1 ct.2 ∈ {x : MaskBox p × Y₁ | x.1.1 = σ.z ∧ x.2 = y.2}} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ _ct ∈ (Finset.univ : Finset (Fin k × Fin T)),
            ((Fintype.card (MaskBox p) : ℝ≥0∞) * Fintype.card Y₁)⁻¹ := by
          refine Finset.sum_le_sum fun ct _ => ?_
          rw [prob_kfCoins_apply_mem]
          exact hone _ _
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_mul]
  calc ∑ y : BucketVec p × Y₁, ⨆ σ : FIPSSignature p prims,
        μ.toOuterMeasure {sc | w1KFOut (T := T) prims O sp βmin tol enc k D bmsg ω pk R c m sc =
          some (y, σ)}
      ≤ ∑ _y : BucketVec p × Y₁,
          k * T * ((Fintype.card (MaskBox p) : ℝ≥0∞) * Fintype.card Y₁)⁻¹ :=
        Finset.sum_le_sum fun y _ => iSup_le fun σ => hpt y σ
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_prod, nsmul_eq_mul]
        have hY : (Fintype.card Y₁ : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
        have hY' : (Fintype.card Y₁ : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
        rw [ENNReal.mul_inv (Or.inr hY') (Or.inr hY), div_eq_mul_inv]
        push_cast
        calc (Fintype.card (BucketVec p) : ℝ≥0∞) * Fintype.card Y₁ *
              (k * T * ((Fintype.card (MaskBox p) : ℝ≥0∞)⁻¹ * (Fintype.card Y₁ : ℝ≥0∞)⁻¹))
            = k * T * Fintype.card (BucketVec p) * (Fintype.card (MaskBox p) : ℝ≥0∞)⁻¹ *
                ((Fintype.card Y₁ : ℝ≥0∞) * (Fintype.card Y₁ : ℝ≥0∞)⁻¹) := by ring
          _ = _ := by rw [ENNReal.mul_inv_cancel hY hY', mul_one]

end GordieHowe.Ring.MLDSAW1
