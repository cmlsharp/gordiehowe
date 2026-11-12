-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.W1Placement
public import GordieHowe.Applications.Ring.W1OracleRange
public import GordieHowe.Applications.Ring.W1ProofReads
public import GordieHowe.Applications.Ring.MLDSAW1OracleFacts

@[expose] public section

/-!
# The concrete oracles of the ML-DSA ring publishing `w₁`

The oracles of the ring publishing `w₁` at one instance: the points of `W1Placement.lean` in the
oracle domain `Bits (queryBits k kN kS L)`, and values in `w1Y I₁ k e` decoded from the base
signer's component of the split `w1Sp`.

- `w1O₁`, `w1O`: the message-representative, commitment-hash and check oracles; the points are
  `w1MuPt`, `w1ChPt`, `w1GPt`, the values the bytes at the positions `ιm` (message
  representatives) and `ιc` (commitment hashes and check values). `w1O` reads them through
  `w1Sp` (`W1Oracles.viaBase`).
- `w1M₁`, `w1M`: the mask oracle at the points `w1MaskPt` with a mask decoding `d₁`, read through
  `w1Sp` (`MaskOracle.viaBase`).
- `w1OraclesPlaced`: the concrete oracles satisfy the oracle facts `W1OracleFacts` when `d₁` is
  a uniform decoding. `toBits_notMem_range_w1M`: the encoded spBCS queries are not mask points.
- `W1OracleFacts.w1HPS_hPSm`, `W1OracleFacts.w1HPS_hPSv`, `W1OracleFacts.w1HPS_proverReadsPub`
  (and the same for `w1PS`): the hypotheses `hPSm`, `hPSv`, `hPS` of `insiderForgeProb_le_w1C2`
  for the hedged proof system `w1HPS`, for mask oracles off the encoded spBCS queries.
- `w1OraclesPlaced_exists44`, `w1OraclesPlaced_exists65`, `w1OraclesPlaced_exists87`: at the three
  parameter sets, for `L` at least the four point domains' cardinalities and `I₁` with enough
  bytes for the mask, a mask decoding for which the concrete oracles satisfy `W1OracleFacts`.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.W1Range _root_.PMF
open GordieHowe.QROM (Bits BitStr Query queryBits XOut)
open scoped ENNReal GordieHowe.IOP

/-! ### The concrete oracles -/

section Concrete

variable {k kN kS L : ℕ} {p : Params} {prims : Primitives p} {Msg : Type} {N reps T : ℕ}
  [Fintype Msg] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  {I₁ : Type} [Fintype I₁] [DecidableEq I₁]

/-- **The base signer's oracles on the base component**: the points of `W1Placement.lean`, the
message representatives the bytes at `ιm`, the commitment hashes and check values the bytes at
`ιc`. -/
noncomputable def w1O₁ (F : W1Fit k kN kS L p prims Msg N reps T) (ιm : Fin 64 ↪ I₁)
    (ιc : Fin (p.lambda / 4) ↪ I₁) :
    W1Oracles (Bits (queryBits k kN kS L)) (BitStr I₁ (Fin 8)) p prims Msg N reps where
  muPt := w1MuPt F
  muAns := bytesOf ιm
  chPt := w1ChPt F
  chAns := bytesOf ιc
  gPt := w1GPt F
  gAns := bytesOf ιc

/-- **The base signer's oracles of the ring publishing `w₁`**: `w1O₁` read through `w1Sp`. -/
noncomputable def w1O (e : ℕ) (F : W1Fit k kN kS L p prims Msg N reps T) (ιm : Fin 64 ↪ I₁)
    (ιc : Fin (p.lambda / 4) ↪ I₁) :
    W1Oracles (Bits (queryBits k kN kS L)) (w1Y I₁ k e) p prims Msg N reps :=
  W1Oracles.viaBase (w1Sp I₁ k e) (w1O₁ F ιm ιc)

/-- **The mask oracle on the base component**: the points `w1MaskPt`, the masks decoded by `d₁`. -/
noncomputable def w1M₁ (F : W1Fit k kN kS L p prims Msg N reps T)
    (d₁ : BitStr I₁ (Fin 8) → MaskBox p) :
    MaskOracle (Bits (queryBits k kN kS L)) (BitStr I₁ (Fin 8)) p T Msg where
  pt := w1MaskPt F
  ans := d₁

/-- **The mask oracle of the ring publishing `w₁`**: `w1M₁` read through `w1Sp`. -/
noncomputable def w1M (e : ℕ) (F : W1Fit k kN kS L p prims Msg N reps T)
    (d₁ : BitStr I₁ (Fin 8) → MaskBox p) :
    MaskOracle (Bits (queryBits k kN kS L)) (w1Y I₁ k e) p T Msg :=
  MaskOracle.viaBase (w1Sp I₁ k e) (w1M₁ F d₁)

end Concrete

/-! ### The oracle facts -/

section ConcretePlaced

variable {k kN kS L e : ℕ} {p : Params} {prims : Primitives p} {Msg : Type} {N reps T : ℕ}
  [Fintype Msg] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  {I₁ : Type} [Fintype I₁] [DecidableEq I₁] [Nonempty (MaskBox p)]

/-- **The concrete oracles satisfy the oracle facts** (`W1OracleFacts`) when the mask decoding
`d₁` is uniform. -/
theorem w1OraclesPlaced (F : W1Fit k kN kS L p prims Msg N reps T) (ιm : Fin 64 ↪ I₁)
    (ιc : Fin (p.lambda / 4) ↪ I₁) {d₁ : BitStr I₁ (Fin 8) → MaskBox p}
    (hd : (uniformOfFintype (BitStr I₁ (Fin 8))).map d₁ = uniformOfFintype (MaskBox p)) :
    W1OracleFacts (w1O e F ιm ιc) (w1M e F d₁) (w1Sp I₁ k e) where
  uniformSplit :=
    { muPt_injective := w1MuPt_injective F
      chPt_injective := w1ChPt_injective F
      gPt_injective := w1GPt_injective F
      muPt_ne_chPt := w1MuPt_ne_w1ChPt F
      muPt_ne_gPt := w1MuPt_ne_w1GPt F
      chPt_ne_gPt := w1ChPt_ne_w1GPt F
      map_muAns := map_uniform_w1Bytes ιm
      map_chAns := map_uniform_w1Bytes ιc
      map_gAns := map_uniform_w1Bytes ιc }
  hMinj := w1MaskPt_injective F
  hdisjM := by
    rintro x (⟨a, rfl⟩ | ⟨a, rfl⟩ | ⟨a, rfl⟩) ⟨b, hb⟩
    · exact w1MuPt_ne_w1MaskPt F a b hb.symm
    · exact w1ChPt_ne_w1MaskPt F a b hb.symm
    · exact w1GPt_ne_w1MaskPt F a b hb.symm
  hO := W1Oracles.readsFst_viaBase _ _
  hM := MaskOracle.readsFst_viaBase _ _
  hMask := map_uniform_comp (f := fun y => (w1Sp I₁ k e y).1) (W1Range.map_uniform_fst_split _) hd

omit [Fintype I₁] [DecidableEq I₁] [Nonempty (MaskBox p)] in
/-- **The encoded spBCS queries are not points of the concrete mask oracle.** -/
theorem toBits_notMem_range_w1M (F : W1Fit k kN kS L p prims Msg N reps T)
    (d₁ : BitStr I₁ (Fin 8) → MaskBox p) (q : Query k kN kS L) :
    Query.toBits q ∉ Set.range (w1M e F d₁).pt := by
  rintro ⟨b, hb⟩
  exact w1MaskPt_notMem_range_toBits F b ⟨q, hb.symm⟩

omit [Fintype I₁] [DecidableEq I₁] [Nonempty (MaskBox p)] in
/-- **The concrete mask oracle satisfies `W1MaskQueryFacts`** (`toBits_notMem_range_w1M`). -/
theorem w1M_maskQueryFacts (F : W1Fit k kN kS L p prims Msg N reps T)
    (d₁ : BitStr I₁ (Fin 8) → MaskBox p) : W1MaskQueryFacts k kN kS L (w1M e F d₁) :=
  ⟨toBits_notMem_range_w1M F d₁⟩

end ConcretePlaced

/-! ### The proof-system facts -/

section Hedged

open GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

variable {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}
  {kh kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
  [Nonempty Y] {sp : OracleSplit Y Y₁ (XOut kh e)} {prims : Primitives p}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint]
  [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  {O : W1Oracles (Bits (queryBits kh kN kS L)) Y p prims Msg N reps}
  {Mo : MaskOracle (Bits (queryBits kh kN kS L)) Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
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
  {Y₂ : Type} [AddGroup Y₂] {sp' : Y ≃+ Y₁ × Y₂}
  {chk : RingSignature.RingStmt (freshBase prims O Mo βmin tol enc k D bmsg) → Bool}

omit [∀ j i, Fintype ((Mc.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The hedged prover reads no mask point** (`hPSm` of `insiderForgeProb_le_w1C2`), for any
check. -/
theorem W1OracleFacts.w1HPS_hPSm (h : W1OracleFacts O Mo sp')
    (hQ : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range Mo.pt) :
    ∀ x w c H H', Quantum.AgreeOffRange Mo.pt H H' →
      ((w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk).prove x w c).run H =
        ((w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk).prove x w c).run H' :=
  w1HPS_run_prove_eq_of_agreeOffRange h.hdisjM hQ

omit [∀ j i, Fintype ((Mc.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The hedged verifier reads no mask point** (`hPSv` of `insiderForgeProb_le_w1C2`), for any
check. -/
theorem W1OracleFacts.w1HPS_hPSv (h : W1OracleFacts O Mo sp')
    (hQ : ∀ q : Query kh kN kS L, Query.toBits q ∉ Set.range Mo.pt) :
    ∀ x π H H', Quantum.AgreeOffRange Mo.pt H H' →
      (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk).verify H x π =
        (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk).verify H' x π :=
  w1HPS_verify_eq_of_agreeOffRange h.hdisjM hQ

omit [∀ j i, Fintype ((Mc.comp j).MessageWrite i)] [DecidableEq R] [DecidableEq Y] in
/-- **`ProverReadsPub` for the hedged proof system** (`hPS` of `insiderForgeProb_le_w1C2`), for
any check. -/
theorem W1OracleFacts.w1HPS_proverReadsPub (h : W1OracleFacts O Mo sp') :
    ProverReadsPub O (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk) sp :=
  proverReadsPub_w1HPS h.hdisj

end Hedged

section Fresh

open GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [Nonempty Y]
  {sp : OracleSplit Y Y₁ (XOut k e)} {p : Params} {prims : Primitives p} {Msg : Type} {N reps : ℕ}
  [nttOps : NTTRingOps] [Nonempty (MaskBox p)] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg]
  [DecidableEq Msg] {O : W1Oracles (Bits (queryBits k kN kS L)) Y p prims Msg N reps}
  {βmin : ℚ≥0} {tol : ℕ} {enc : Vector prims.High p.k → BucketVec p}
  {CLp : Type} [Fintype CLp] [DecidableEq CLp] [Nonempty CLp] {Lp : W1Loop (Bits (queryBits k kN kS L)) Y p prims Msg N CLp} {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  {M : SPBCS Mg P (W1ExpStmt prims RMsg N) k kN kS L e} {Λ : SiteLayout Mg}
  {b : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)] {E : (j : ι) → (M.comp j).Encoder}
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  {hb : M.FormatBounds Qs b b} {R : Type} [Fintype R] [DecidableEq R] [Nonempty R]
  {honest : RingSignature.RingWit (w1BaseSigner prims O βmin tol enc Lp bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {T : ℕ} {Mo : MaskOracle (Bits (queryBits k kN kS L)) Y p T Msg}
  {Y₂ : Type} [AddGroup Y₂] {sp' : Y ≃+ Y₁ × Y₂}

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [DecidableEq R] in
/-- **The prover of `w1PS` reads no mask point.** -/
theorem W1OracleFacts.w1PS_hPSm (h : W1OracleFacts O Mo sp')
    (hQ : ∀ q : Query k kN kS L, Query.toBits q ∉ Set.range Mo.pt) :
    ∀ x w c H H', Quantum.AgreeOffRange Mo.pt H H' →
      ((w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).prove x w c).run H =
        ((w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).prove x w c).run H' :=
  w1PS_run_prove_eq_of_agreeOffRange h.hdisjM hQ

omit [∀ j i, Fintype ((M.comp j).MessageWrite i)] [Fintype R] [DecidableEq R] [Nonempty R] in
/-- **The verifier of `w1PS` reads no mask point.** -/
theorem W1OracleFacts.w1PS_hPSv (h : W1OracleFacts O Mo sp')
    (hQ : ∀ q : Query k kN kS L, Query.toBits q ∉ Set.range Mo.pt) :
    ∀ x π H H', Quantum.AgreeOffRange Mo.pt H H' →
      (w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).verify H x π =
        (w1PS sp prims O βmin tol enc Lp bmsg M Λ E hb honest).verify H' x π :=
  w1PS_verify_eq_of_agreeOffRange h.hdisjM hQ

end Fresh

/-! ### Satisfiability at the three parameter sets -/

section Exists

variable {k kN kS L e : ℕ} {Msg : Type} {N reps T : ℕ} [Fintype Msg]

/-- **The oracle facts at ML-DSA-44**: for `L` at least the four point domains' cardinalities and
`18432 ≤ 8 |I₁|`, there is a mask decoding for which the concrete oracles satisfy them. -/
theorem w1OraclesPlaced_exists44 {prims : Primitives _root_.MLDSA.mldsa44}
    [Fintype prims.Power2High] [DecidableEq prims.Power2High] {I₁ : Type} [Fintype I₁]
    [DecidableEq I₁]
    (hL : max (max (Fintype.card (Bytes 64 × Msg))
      (Fintype.card (Bytes 64 × BucketVec _root_.MLDSA.mldsa44)))
      (max (Fintype.card (KeyRing (PubKey _ prims) N × Fin N × Fin reps))
        (Fintype.card (Bytes 32 × MaskPt T Msg))) ≤ L)
    (hI : 18432 ≤ 8 * Fintype.card I₁) (ιm : Fin 64 ↪ I₁)
    (ιc : Fin (_root_.MLDSA.mldsa44.lambda / 4) ↪ I₁) :
    ∃ d₁ : BitStr I₁ (Fin 8) → MaskBox _root_.MLDSA.mldsa44,
      W1OracleFacts (w1O e (w1Fit_of_le (k := k) (kN := kN) (kS := kS) hL) ιm ιc)
        (w1M e (w1Fit_of_le hL) d₁) (w1Sp I₁ k e) :=
  let ⟨_, hd⟩ := exists_maskDecode44 hI
  ⟨_, w1OraclesPlaced _ ιm ιc hd⟩

/-- **The split, masks and mask points of the placed oracles at ML-DSA-44**
(`w1OraclesPlaced_exists44`): `W1SplitMask` and `W1MaskPoints` hold for some mask decoding. -/
theorem w1SplitMask_maskPoints_exists44 {prims : Primitives _root_.MLDSA.mldsa44}
    [Fintype prims.Power2High] [DecidableEq prims.Power2High] {I₁ : Type} [Fintype I₁]
    [DecidableEq I₁]
    (hL : max (max (Fintype.card (Bytes 64 × Msg))
      (Fintype.card (Bytes 64 × BucketVec _root_.MLDSA.mldsa44)))
      (max (Fintype.card (KeyRing (PubKey _ prims) N × Fin N × Fin reps))
        (Fintype.card (Bytes 32 × MaskPt T Msg))) ≤ L)
    (hI : 18432 ≤ 8 * Fintype.card I₁) (ιm : Fin 64 ↪ I₁)
    (ιc : Fin (_root_.MLDSA.mldsa44.lambda / 4) ↪ I₁) :
    ∃ d₁ : BitStr I₁ (Fin 8) → MaskBox _root_.MLDSA.mldsa44,
      W1SplitMask (w1O e (w1Fit_of_le (k := k) (kN := kN) (kS := kS) hL) ιm ιc)
          (w1M e (w1Fit_of_le hL) d₁) ∧
        W1MaskPoints (w1O e (w1Fit_of_le (k := k) (kN := kN) (kS := kS) hL) ιm ιc)
          (w1M e (w1Fit_of_le hL) d₁) :=
  let ⟨d₁, h⟩ := w1OraclesPlaced_exists44 (e := e) hL hI ιm ιc
  ⟨d₁, h.toW1SplitMask, h.toW1MaskPoints⟩

/-- **The oracle facts at ML-DSA-65**: for `L` at least the four point domains' cardinalities and
`25600 ≤ 8 |I₁|`, there is a mask decoding for which the concrete oracles satisfy them. -/
theorem w1OraclesPlaced_exists65 {prims : Primitives _root_.MLDSA.mldsa65}
    [Fintype prims.Power2High] [DecidableEq prims.Power2High] {I₁ : Type} [Fintype I₁]
    [DecidableEq I₁]
    (hL : max (max (Fintype.card (Bytes 64 × Msg))
      (Fintype.card (Bytes 64 × BucketVec _root_.MLDSA.mldsa65)))
      (max (Fintype.card (KeyRing (PubKey _ prims) N × Fin N × Fin reps))
        (Fintype.card (Bytes 32 × MaskPt T Msg))) ≤ L)
    (hI : 25600 ≤ 8 * Fintype.card I₁) (ιm : Fin 64 ↪ I₁)
    (ιc : Fin (_root_.MLDSA.mldsa65.lambda / 4) ↪ I₁) :
    ∃ d₁ : BitStr I₁ (Fin 8) → MaskBox _root_.MLDSA.mldsa65,
      W1OracleFacts (w1O e (w1Fit_of_le (k := k) (kN := kN) (kS := kS) hL) ιm ιc)
        (w1M e (w1Fit_of_le hL) d₁) (w1Sp I₁ k e) :=
  let ⟨_, hd⟩ := exists_maskDecode65 hI
  ⟨_, w1OraclesPlaced _ ιm ιc hd⟩

/-- **The oracle facts at ML-DSA-87**: for `L` at least the four point domains' cardinalities and
`35840 ≤ 8 |I₁|`, there is a mask decoding for which the concrete oracles satisfy them. -/
theorem w1OraclesPlaced_exists87 {prims : Primitives _root_.MLDSA.mldsa87}
    [Fintype prims.Power2High] [DecidableEq prims.Power2High] {I₁ : Type} [Fintype I₁]
    [DecidableEq I₁]
    (hL : max (max (Fintype.card (Bytes 64 × Msg))
      (Fintype.card (Bytes 64 × BucketVec _root_.MLDSA.mldsa87)))
      (max (Fintype.card (KeyRing (PubKey _ prims) N × Fin N × Fin reps))
        (Fintype.card (Bytes 32 × MaskPt T Msg))) ≤ L)
    (hI : 35840 ≤ 8 * Fintype.card I₁) (ιm : Fin 64 ↪ I₁)
    (ιc : Fin (_root_.MLDSA.mldsa87.lambda / 4) ↪ I₁) :
    ∃ d₁ : BitStr I₁ (Fin 8) → MaskBox _root_.MLDSA.mldsa87,
      W1OracleFacts (w1O e (w1Fit_of_le (k := k) (kN := kN) (kS := kS) hL) ιm ιc)
        (w1M e (w1Fit_of_le hL) d₁) (w1Sp I₁ k e) :=
  let ⟨_, hd⟩ := exists_maskDecode87 hI
  ⟨_, w1OraclesPlaced _ ιm ιc hd⟩

/-- **`w1OraclesPlaced_exists44` at `I₁ = Fin 4480`**: the byte embeddings are the first
indices, so the placed oracles exist whenever `L` meets the fit bound. -/
theorem w1OraclesPlaced_exists44_fin {prims : Primitives _root_.MLDSA.mldsa44}
    [Fintype prims.Power2High] [DecidableEq prims.Power2High]
    (hL : max (max (Fintype.card (Bytes 64 × Msg))
      (Fintype.card (Bytes 64 × BucketVec _root_.MLDSA.mldsa44)))
      (max (Fintype.card (KeyRing (PubKey _ prims) N × Fin N × Fin reps))
        (Fintype.card (Bytes 32 × MaskPt T Msg))) ≤ L) :
    ∃ d₁ : BitStr (Fin 4480) (Fin 8) → MaskBox _root_.MLDSA.mldsa44,
      W1OracleFacts
        (w1O e (w1Fit_of_le (k := k) (kN := kN) (kS := kS) hL) (Fin.castLEEmb (by omega))
          (Fin.castLEEmb (by decide)))
        (w1M e (w1Fit_of_le hL) d₁) (w1Sp (Fin 4480) k e) :=
  w1OraclesPlaced_exists44 hL (by simp) _ _

/-- **`w1OraclesPlaced_exists65` at `I₁ = Fin 4480`**: the byte embeddings are the first
indices, so the placed oracles exist whenever `L` meets the fit bound. -/
theorem w1OraclesPlaced_exists65_fin {prims : Primitives _root_.MLDSA.mldsa65}
    [Fintype prims.Power2High] [DecidableEq prims.Power2High]
    (hL : max (max (Fintype.card (Bytes 64 × Msg))
      (Fintype.card (Bytes 64 × BucketVec _root_.MLDSA.mldsa65)))
      (max (Fintype.card (KeyRing (PubKey _ prims) N × Fin N × Fin reps))
        (Fintype.card (Bytes 32 × MaskPt T Msg))) ≤ L) :
    ∃ d₁ : BitStr (Fin 4480) (Fin 8) → MaskBox _root_.MLDSA.mldsa65,
      W1OracleFacts
        (w1O e (w1Fit_of_le (k := k) (kN := kN) (kS := kS) hL) (Fin.castLEEmb (by omega))
          (Fin.castLEEmb (by decide)))
        (w1M e (w1Fit_of_le hL) d₁) (w1Sp (Fin 4480) k e) :=
  w1OraclesPlaced_exists65 hL (by simp) _ _

/-- **`w1OraclesPlaced_exists87` at `I₁ = Fin 4480`**: the byte embeddings are the first
indices, so the placed oracles exist whenever `L` meets the fit bound. -/
theorem w1OraclesPlaced_exists87_fin {prims : Primitives _root_.MLDSA.mldsa87}
    [Fintype prims.Power2High] [DecidableEq prims.Power2High]
    (hL : max (max (Fintype.card (Bytes 64 × Msg))
      (Fintype.card (Bytes 64 × BucketVec _root_.MLDSA.mldsa87)))
      (max (Fintype.card (KeyRing (PubKey _ prims) N × Fin N × Fin reps))
        (Fintype.card (Bytes 32 × MaskPt T Msg))) ≤ L) :
    ∃ d₁ : BitStr (Fin 4480) (Fin 8) → MaskBox _root_.MLDSA.mldsa87,
      W1OracleFacts
        (w1O e (w1Fit_of_le (k := k) (kN := kN) (kS := kS) hL) (Fin.castLEEmb (by omega))
          (Fin.castLEEmb (by decide)))
        (w1M e (w1Fit_of_le hL) d₁) (w1Sp (Fin 4480) k e) :=
  w1OraclesPlaced_exists87 hL (by simp) _ _

end Exists

end GordieHowe.Ring.MLDSAW1
