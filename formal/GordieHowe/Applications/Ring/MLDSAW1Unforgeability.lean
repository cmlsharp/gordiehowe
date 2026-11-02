-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.SPBCSSplit
public import GordieHowe.Applications.Ring.RingUnforgeability

@[expose] public section

/-!
# Unforgeability of the ML-DSA ring signature publishing `w₁`: the statement it proves

The ring relation of the ML-DSA ring publishing `w₁` (`RingRel` of `w1BaseSigner`) reads the oracle:
a member's signature verifies against the commitment hash `c̃ = H(H_µ(tr_i, m), w₁)`. The verifier
computes the members' commitment hashes `c̃_j` from the published `w₁` outside the circuit
(`GordieHowe/Applications/Ring/PublicW1/README.md`), so the circuit proves a fixed relation of the
statement with the hashes (`w1ExpRel`). With the oracle split additively into the base signer's
component and the proof system's (`GordieHowe/Applications/Ring/MLDSAW1Split.lean`), the hashes are
read from the base component by a classical program (`w1StmtProg`), the program statement of
`GordieHowe/Applications/Ring/SPBCSSplit.lean`.

- `W1Oracles.muAt`, `W1Oracles.chAt`: the message representatives and commitment hashes decoded
  from a value of the base component; `W1Oracles.ReadsFst.muAns_eq_muAt`,
  `W1Oracles.ReadsFst.chAns_eq_chAt`: for decodings reading only the first component, the value
  of the oracle decodes as its base component. `hOrc_eq_chAt`: so does the commitment hash
  `H(H_µ(tr, m), w₁)`.
- `hashesProg sp O m w₁ l`: the commitment hashes `c̃_j = H(H_µ(tr_j, m), w₁)` of the keys of `l`,
  two queries per key of the base component; `run_hashesProg`, `hashesProg_queries`.
- `W1ExpStmt`, `w1StmtProg`: the program statement, a ring statement with the hashes of its
  members (at most `2N` queries, `w1StmtProg_queries`); `run_w1StmtProg`: its value at a base
  component.
- `w1ExpRel adm`: the fixed relation: the ring is supported, the position is in the ring, the
  signature verifies (FIPS 204 Algorithm 8 with the recomputed commitment required to equal `w₁`)
  against the hash at the position, and its recomputed commitment is the statement's `w₁`.
- `ringVerify_congr`: verification reads the commitment hash at one point.
- `ringRel_of_mem_w1ExpRel`: a witness of the fixed relation for the program statement at the base
  component `base sp H` is a witness of the ring relation at `H`, for decodings reading only the
  first component.
- `bverify_of_mem_w1ExpRel`: a witness whose member's listed hash is the oracle's verifies there.
- `mem_w1ExpRel_of_ringRel`: conversely, a witness of the ring relation at `H` is one of the fixed
  relation for the program statement at `base sp H`; the honest witnesses are in the relation.
- `w1PS`: the proof system of the ring, the spBCS compilation of an IOP for the fixed relation of
  the program statements read at ring statements through `w1StmtProg` (`spbcsSplitProofSystem`);
  `ringRel_of_w1PS`: a witness of the fixed relation for its compiled program statement at a base
  component is one of the ring relation at every oracle with that base component.
- `bindsRing_w1BaseSigner_pair`: the base message `(R, m)` binds the ring (`BindsRing` is
  satisfiable).
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open scoped ENNReal

variable {X Y Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂] (sp : OracleSplit Y Y₁ Y₂)
  {p : Params} {prims : Primitives p} {Msg : Type} {N reps : ℕ}

/-! ### Decoding the base component -/

/-- **The message representative decoded from a value of the base component**: the decoding of the
oracle value with that first component and second component `0`. -/
def W1Oracles.muAt (O : W1Oracles X Y p prims Msg N reps) (y₁ : Y₁) : Bytes 64 :=
  O.muAns (sp.symm (y₁, 0))

/-- **The commitment hash decoded from a value of the base component.** -/
def W1Oracles.chAt (O : W1Oracles X Y p prims Msg N reps) (y₁ : Y₁) : CommitHashBytes p :=
  O.chAns (sp.symm (y₁, 0))

variable {sp}

/-- For decodings reading only the first component, a message representative decodes as the base
component of its value. -/
theorem W1Oracles.ReadsFst.muAns_eq_muAt {O : W1Oracles X Y p prims Msg N reps} (hO : O.ReadsFst sp)
    (y : Y) : O.muAns y = O.muAt sp (sp y).1 :=
  hO.muAns_eq _ _ (by simp)

/-- For decodings reading only the first component, a commitment hash decodes as the base
component of its value. -/
theorem W1Oracles.ReadsFst.chAns_eq_chAt {O : W1Oracles X Y p prims Msg N reps} (hO : O.ReadsFst sp)
    (y : Y) : O.chAns y = O.chAt sp (sp y).1 :=
  hO.chAns_eq _ _ (by simp)

/-- **The commitment hash of the oracle is the decoded hash of its base component**, for decodings
reading only the first component. -/
theorem hOrc_eq_chAt {O : W1Oracles X Y p prims Msg N reps} (hO : O.ReadsFst sp) (H : X → Y)
    (tr : Bytes 64) (m : Msg) (w1 : BucketVec p) :
    O.hOrc H ((tr, m), w1) =
      O.chAt sp (base sp H (O.chPt (O.muAt sp (base sp H (O.muPt (tr, m))), w1))) := by
  simp only [W1Oracles.hOrc, schemeOrc, W1Oracles.muOrc, W1Oracles.chOrc, hO.muAns_eq_muAt,
    hO.chAns_eq_chAt, base]

variable (sp)

/-! ### The program statement -/

section Stmt

variable (prims) (O : W1Oracles X Y p prims Msg N reps)

/-- **The members' commitment hashes from the base component**: for each key `pk` of `l`, the
message representative `µ = H_µ(tr, m)` at `(pubTr pk, m)`, then the commitment hash `H(µ, w₁)`, two
queries per key. -/
def hashesProg (m : Msg) (w1 : BucketVec p) :
    List (PubKey p prims) → OracleProg X Y₁ (List (CommitHashBytes p))
  | [] => .pure []
  | pk :: l => .query (O.muPt (pubTr prims pk, m)) fun a =>
      .query (O.chPt (O.muAt sp a, w1)) fun c =>
        (hashesProg m w1 l).mapOutput (O.chAt sp c :: ·)

/-- **The hashes the program reads** at a base component `ω`. -/
theorem run_hashesProg (m : Msg) (w1 : BucketVec p) (ω : X → Y₁) :
    ∀ l : List (PubKey p prims), (hashesProg sp prims O m w1 l).run ω =
      l.map fun pk => O.chAt sp (ω (O.chPt (O.muAt sp (ω (O.muPt (pubTr prims pk, m))), w1)))
  | [] => rfl
  | pk :: l => by
    simp only [hashesProg, OracleProg.run_query, OracleProg.run_mapOutput, List.map_cons,
      run_hashesProg m w1 ω l]

/-- The program makes two queries per key. -/
theorem hashesProg_queries (m : Msg) (w1 : BucketVec p) :
    ∀ l : List (PubKey p prims), (hashesProg sp prims O m w1 l).QueriesLE (2 * l.length)
  | [] => OracleProg.QueriesLE.pure _ _
  | pk :: l => by
    have h := OracleProg.QueriesLE.query (O.muPt (pubTr prims pk, m)) fun a =>
      OracleProg.QueriesLE.query (O.chPt (O.muAt sp a, w1)) fun c =>
        (hashesProg_queries m w1 l).mapOutput (O.chAt sp c :: ·)
    refine h.mono ?_
    simp only [List.length_cons]
    omega

variable [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg]
  [DecidableEq Msg] (βmin : ℚ≥0) (tol : ℕ)
  (enc : Vector prims.High p.k → BucketVec p) {CL : Type} [Fintype CL] [DecidableEq CL] [Nonempty CL] (L : W1Loop X Y p prims Msg N CL) {RMsg : Type}
  [Fintype RMsg] [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)

/-- **The program statement**: a ring statement (a ring of published keys, a ring message in
`RMsg`, a public value `w₁`) with the commitment hashes of its members. A function of exactly the
types it reads: the hedged and the fresh base signer have the same program statements. -/
abbrev W1ExpStmt {q : Params} (pr : Primitives q) (RMsg : Type) (n : ℕ) : Type :=
  RingSignature.RingStmtOf (PubKey q pr) RMsg (BucketVec q) n × List (CommitHashBytes q)

/-- **The program statement of a ring statement** `(R, m, w₁)`: the statement with the members'
commitment hashes `H(H_µ(tr_j, bmsg R m), w₁)` read from the base component. -/
def w1StmtProg (x : RingSignature.RingStmtOf (PubKey p prims) RMsg (BucketVec p) N) :
    OracleProg X Y₁ (W1ExpStmt prims RMsg N) :=
  (hashesProg sp prims O (bmsg x.ring x.msg) x.pub x.ring.1).mapOutput fun cs => (x, cs)

omit [NeZero (bucketCount p)] in
/-- The program statement is read by at most `2N` queries. -/
theorem w1StmtProg_queries (x : RingSignature.RingStmtOf (PubKey p prims) RMsg (BucketVec p) N) :
    (w1StmtProg sp prims O bmsg x).QueriesLE (2 * N) :=
  ((hashesProg_queries sp prims O _ _ x.ring.1).mapOutput _).mono
    (Nat.mul_le_mul_left 2 x.ring.2)

/-! ### The fixed relation -/

/-- **The fixed relation of the program statement** on the supported rings `adm`: the ring is
supported, the position `i` is in the ring, the signature verifies under the key at `i` on
`bmsg R m` at the recomputed commitment against the commitment hash at position `i` of the
statement's hashes, and its recomputed commitment is the statement's `w₁`. -/
def w1ExpRel (adm : KeyRing (PubKey p prims) N → Prop) :
    Set (W1ExpStmt prims RMsg N × RingSignature.RingWitOf (FIPSSignature p prims)) :=
  {q | adm q.1.1.ring ∧ ∃ hi : q.2.idx < q.1.1.ring.1.length, ∃ c, q.1.2[q.2.idx]? = some c ∧
    ringVerify prims (fun _ => c) enc (pubPk prims (q.1.1.ring.1[q.2.idx]'hi))
      (bmsg q.1.1.ring q.1.1.msg) (w1Of prims enc (q.1.1.ring.1[q.2.idx]'hi) q.2.sig) q.2.sig =
        true ∧
    w1Of prims enc (q.1.1.ring.1[q.2.idx]'hi) q.2.sig = q.1.1.pub}

omit [NeZero (bucketCount p)] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] in
/-- **Verification reads the commitment hash at one point**: two hash functions agreeing at
`((tr, m), w₁)`, with `tr` the hash of the key, give the same verdict. -/
theorem ringVerify_congr {H H' : (Bytes 64 × Msg) × BucketVec p → CommitHashBytes p}
    {pk : PublicKey p prims} {m : Msg} {w1 : BucketVec p} {σ : FIPSSignature p prims}
    (h : H ((prims.hashPublicKey pk.rho pk.t1, m), w1) =
      H' ((prims.hashPublicKey pk.rho pk.t1, m), w1)) :
    ringVerify prims H enc pk m w1 σ = ringVerify prims H' enc pk m w1 σ := by
  simp only [ringVerify, h]

variable {sp O βmin tol enc L bmsg}

omit [NeZero (bucketCount p)] in
/-- **The program statement at a base component**: the statement with its members' hashes read
from it. -/
theorem run_w1StmtProg (ω : X → Y₁)
    (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc L bmsg)) :
    (w1StmtProg sp prims O bmsg x).run ω = (x, x.ring.1.map fun pk =>
      O.chAt sp (ω (O.chPt (O.muAt sp (ω (O.muPt (pubTr prims pk, bmsg x.ring x.msg))),
        x.pub)))) := by
  rw [w1StmtProg, OracleProg.run_mapOutput]
  exact congrArg (Prod.mk x) (run_hashesProg sp prims O _ _ ω (x.ring.1 : List (PubKey p prims)))

omit [NeZero (bucketCount p)] in
/-- **The fixed relation gives the ring relation**: a witness of `w1ExpRel` for the program
statement of `x` at the base component `base sp H` is a witness of the ring relation at `H`, for
decodings reading only the first component. -/
theorem ringRel_of_mem_w1ExpRel (hO : O.ReadsFst sp) {adm : KeyRing (PubKey p prims) N → Prop}
    (H : X → Y) (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc L bmsg))
    (w : RingSignature.RingWitOf (FIPSSignature p prims))
    (hw : ((w1StmtProg sp prims O bmsg x).run (base sp H), w) ∈
      w1ExpRel prims enc bmsg adm) :
    RingSignature.RingRel (w1BaseSigner prims O βmin tol enc L bmsg) adm H x w := by
  rw [run_w1StmtProg] at hw
  obtain ⟨ha, hi, c, hc, hv, hp⟩ := hw
  change w.idx < x.ring.1.length at hi
  have hc' :=
    (List.getElem?_map (l := (x.ring.1 : List (PubKey p prims))) (i := w.idx)).symm.trans hc
  rw [List.getElem?_eq_getElem hi] at hc'
  have hc'' := Option.some.inj hc'
  refine ⟨ha, hi, ?_, hp⟩
  change ringVerify prims (O.hOrc H) enc (pubPk prims (x.ring.1[w.idx]'hi)) (bmsg x.ring x.msg)
    (w1Of prims enc (x.ring.1[w.idx]'hi) w.sig) w.sig = true
  rw [← hv]
  refine ringVerify_congr prims enc ?_
  rw [hOrc_eq_chAt hO, hp]
  exact hc''

omit [NeZero (bucketCount p)] in
/-- **The fixed relation gives base verification where the listed hash is the oracle's**: for a
witness of `w1ExpRel` whose member's listed commitment hash is the one read from `base sp H`, the
base signature verifies at `H`, for decodings reading only the first component. Only the
witness's member's hash is needed. -/
theorem bverify_of_mem_w1ExpRel (hO : O.ReadsFst sp) {adm : KeyRing (PubKey p prims) N → Prop}
    (H : X → Y) (q : W1ExpStmt prims RMsg N ×
      RingSignature.RingWitOf (FIPSSignature p prims))
    (hq : q ∈ w1ExpRel prims enc bmsg adm)
    (hc : ∀ hi : q.2.idx < q.1.1.ring.1.length, q.1.2[q.2.idx]? =
      some (O.chAt sp (base sp H (O.chPt (O.muAt sp (base sp H (O.muPt (pubTr prims
        (q.1.1.ring.1[q.2.idx]'hi), bmsg q.1.1.ring q.1.1.msg))), q.1.1.pub))))) :
    ∃ hi : q.2.idx < q.1.1.ring.1.length,
      (w1BaseSigner prims O βmin tol enc L bmsg).bverify H (q.1.1.ring.1[q.2.idx]'hi)
        (bmsg q.1.1.ring q.1.1.msg) q.2.sig = true := by
  obtain ⟨-, hi, c, hc0, hv, hp⟩ := hq
  refine ⟨hi, ?_⟩
  have hcc := Option.some.inj (hc0.symm.trans (hc hi))
  change ringVerify prims (O.hOrc H) enc (pubPk prims (q.1.1.ring.1[q.2.idx]'hi))
    (bmsg q.1.1.ring q.1.1.msg) (w1Of prims enc (q.1.1.ring.1[q.2.idx]'hi) q.2.sig) q.2.sig = true
  rw [← hv]
  refine ringVerify_congr prims enc ?_
  rw [hOrc_eq_chAt hO, hp]
  exact hcc.symm

omit [NeZero (bucketCount p)] in
/-- **The ring relation gives the fixed relation**: a witness of the ring relation at `H` is a
witness of `w1ExpRel` for the program statement at `base sp H`, for decodings reading only the
first component. -/
theorem mem_w1ExpRel_of_ringRel (hO : O.ReadsFst sp) {adm : KeyRing (PubKey p prims) N → Prop}
    (H : X → Y) (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc L bmsg))
    (w : RingSignature.RingWitOf (FIPSSignature p prims))
    (hw : RingSignature.RingRel (w1BaseSigner prims O βmin tol enc L bmsg) adm H x w) :
    ((w1StmtProg sp prims O bmsg x).run (base sp H), w) ∈
      w1ExpRel prims enc bmsg adm := by
  obtain ⟨ha, hi, hv, hp⟩ := hw
  change ringVerify prims (O.hOrc H) enc (pubPk prims (x.ring.1[w.idx]'hi)) (bmsg x.ring x.msg)
      (w1Of prims enc (x.ring.1[w.idx]'hi) w.sig) w.sig = true at hv
  change w1Of prims enc (x.ring.1[w.idx]'hi) w.sig = x.pub at hp
  rw [run_w1StmtProg]
  refine ⟨ha, hi, O.chAt sp (base sp H (O.chPt (O.muAt sp (base sp H
    (O.muPt (pubTr prims (x.ring.1[w.idx]'hi), bmsg x.ring x.msg))), x.pub))), ?_, ?_, hp⟩
  · exact (List.getElem?_map (l := (x.ring.1 : List (PubKey p prims))) (i := w.idx)).trans
      (by rw [List.getElem?_eq_getElem hi]; rfl)
  · rw [← hv]
    refine (ringVerify_congr prims enc ?_).symm
    rw [hOrc_eq_chAt hO, hp]
    rfl

end Stmt

end GordieHowe.Ring.MLDSAW1

/-! ### The proof system of the ring and the ring-binding base message -/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
open scoped ENNReal

section PS

variable {k kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁]
  (sp : OracleSplit Y Y₁ (XOut k e)) {p : Params} (prims : Primitives p) {Msg : Type} {N reps : ℕ}
  [NeZero (bucketCount p)] [nttOps : NTTRingOps] [Fintype prims.Power2High]
  [DecidableEq prims.Power2High] [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg]
  [DecidableEq Msg] (O : W1Oracles (Bits (queryBits k kN kS L)) Y p prims Msg N reps)
  (βmin : ℚ≥0) (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p)
  {CLp : Type} [Fintype CLp] [DecidableEq CLp] [Nonempty CLp] (Lp : W1Loop (Bits (queryBits k kN kS L)) Y p prims Msg N CLp) {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] (bmsg : KeyRing (PubKey p prims) N → RMsg → Msg)
  {ι : Type} {τ : SPTerm ι} {Mg : Merges τ} {nr : ι → ℕ}
  {P : (j : ι) → ProtocolSpec (nr j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)]
  (M : SPBCS Mg P (W1ExpStmt prims RMsg N) k kN kS L e) (Λ : SiteLayout Mg)
  {b : ℕ} [∀ j i, Fintype ((M.comp j).MessageWrite i)] (E : (j : ι) → (M.comp j).Encoder)
  {Vr : W1ExpStmt prims RMsg N → FullTr P τ → Bool} {Qs : ∀ x, M.IOPQueries Vr x}
  (hb : M.FormatBounds Qs b b) {R : Type} [Fintype R] [Nonempty R]
  (honest : RingSignature.RingWit (w1BaseSigner prims O βmin tol enc Lp bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N))

/-- **The proof system of the ML-DSA ring publishing `w₁`**: the spBCS compilation `M` of an IOP
for the fixed relation of the program statements, read at ring statements through the members'
commitment hashes from the base component (`spbcsSplitProofSystem` at `w1StmtProg`), the ring
witness as the honest input, every ring statement checked. -/
noncomputable abbrev w1PS :
    ProofSystem (Bits (queryBits k kN kS L)) Y (RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc Lp bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims))
      (spbcsPST M b R) :=
  spbcsSplitProofSystem sp M Λ E hb honest (w1StmtProg sp prims O bmsg) (2 * N)
    (w1StmtProg_queries sp prims O bmsg) (fun _ => true) fun _ w => some w

variable {sp prims O βmin tol enc Lp bmsg M Λ E hb honest}

omit [NeZero (bucketCount p)] in
/-- **A witness of the fixed relation for the compiled program statement is one of the ring
relation at every oracle with that base component**, for decodings reading only the first
component: the relation hypothesis of the split knowledge-soundness bound for `w1PS`. -/
theorem ringRel_of_w1PS (hO : O.ReadsFst sp) {adm : KeyRing (PubKey p prims) N → Prop}
    (ω : Bits (queryBits k kN kS L) → Y₁)
    (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc Lp bmsg))
    (w : RingSignature.RingWitOf (FIPSSignature p prims))
    (hw : ((compiledBySplit_spbcsSplitProofSystem sp M Λ E hb honest
        (w1StmtProg sp prims O bmsg) (2 * N)
        (w1StmtProg_queries sp prims O bmsg) (fun _ => true)
        fun _ w => some w).stmtAt ω x, w) ∈ w1ExpRel prims enc bmsg adm)
    (H : Bits (queryBits k kN kS L) → Y) (hH : base sp H = ω) :
    RingSignature.RingRel (w1BaseSigner prims O βmin tol enc Lp bmsg) adm H x w := by
  subst hH
  exact ringRel_of_mem_w1ExpRel prims hO H x w hw

end PS

section Binds

variable {X Y : Type} {p : Params} (prims : Primitives p) {N reps : ℕ} [NeZero (bucketCount p)]
  [nttOps : NTTRingOps] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] {RMsg : Type} [Fintype RMsg] [DecidableEq RMsg]

omit [NeZero (bucketCount p)] in
/-- **The base message `(R, m)` binds the ring** (`BaseSigner.BindsRing`): the base signer of the
ring publishing `w₁` with the ring and the message as its base message (`Prod.mk`). `BindsRing`
is satisfiable for the ring publishing `w₁`. -/
theorem bindsRing_w1BaseSigner_pair
    (O : W1Oracles X Y p prims (KeyRing (PubKey p prims) N × RMsg) N reps) (βmin : ℚ≥0)
    (tol : ℕ) (enc : Vector prims.High p.k → BucketVec p)
    {CLp : Type} [Fintype CLp] [DecidableEq CLp] [Nonempty CLp] (Lp : W1Loop X Y p prims (KeyRing (PubKey p prims) N × RMsg) N CLp) :
    (w1BaseSigner prims O βmin tol enc Lp Prod.mk).BindsRing :=
  fun _ _ _ _ h => Prod.mk.inj h

end Binds

end GordieHowe.Ring.MLDSAW1
