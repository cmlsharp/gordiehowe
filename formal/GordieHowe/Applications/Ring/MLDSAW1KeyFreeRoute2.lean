-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1KeyFreeBridge
public import GordieHowe.Applications.Ring.MLDSAW1Forge
public import GordieHowe.Applications.Ring.KeyFreeChain

@[expose] public section

/-!
# Route 2's key-free chain at the ML-DSA ring publishing `w₁`: the objects and the hypotheses

The objects at which the key-free chain (`RingSignature.KeyFree.kfChain_le`,
`GordieHowe/Applications/Ring/KeyFreeChain.lean`) is to be applied for the fresh-mask base signer of
the ML-DSA ring publishing `w₁`, with the key-free signer `w1KFSign`
(`GordieHowe/Applications/Ring/MLDSAW1KeyFreeStep.lean`), and the discharge of the chain's
hypotheses and of the route-2 hypotheses `ProverRelays` and `KeptInRel` on them.

The spBCS statement is the program statement `W1ExpStmt` (a ring statement with its members'
commitment hashes, `GordieHowe/Applications/Ring/MLDSAW1Unforgeability.lean`). The statements of
the main challenger carry it with its hash list bounded by `N` and a tag, so that they form a
finite type; the statement program's lists have the ring's length, so the bound loses nothing at
its outputs.

- `W1BStmt`, `w1Bnd`, `W1Tag`, `W1Stmt`, `w1StmtX`, `W1Rq`: the bounded program statements, the
  tags (a multi-user request, a signed request or a dummy request), the statements and their
  program statements, and the relay's proof requests.
- `w1Rel`: the relation, `w1ExpRel` read through `w1StmtX` and `RelayWit.toWit`.
- `w1DummyX`, `w1W0`, `w1Idx`, `w1Enc`, `w1ToR`, `w1DummyR`, `w1Idle`, `w1DummyS`, `w1IsDummy`,
  `w1CheckX`, `w1StmtP`: the encoding of the requests (a signed request's witness at the signer's
  position `idxOf`), the relay's maps, and the checks.
- `w1Enc_injective`, `w1Rel_iff`, `not_mem_w1ExpRel_nil`, `w1DummyStmts`, `w1Disj`, `w1DumS`,
  `w1IdleS`, `w1IdleC`, `allOut_hashesProg_length`, `w1Fst`, `w1ToROut`: the chain's hypotheses; the
  signer's assignments keep the second component by `prf_reprogram_w1KFSign`
  (`GordieHowe/Applications/Ring/MLDSAW1KeyFreeBridge.lean`).
- `run_w1StmtP`, `w1StmtP_queries`, `w1StmtX_enc_toR`, `val_w1Idx_sign`, `toWit_w1Enc_toR`,
  `w1KeptInRel`: the statement program's queries; kept signatures are in the relation.
- `w1HPS`, `comap_w1HPS`, `w1PrfOf`, `w1MainProver`, `w1ProverRelays`: the hedged proof system
  read back from the spBCS proof system of the fresh base signer at any check of the ring
  statements (`w1PS` at the check `fun _ => true`), the proof of a forgery, and
  `ProverRelays` for the main prover `encProver` read through `w1StmtX` and the second component;
  `w1MainProver_coins`: the main prover's coins are uniform (the hypothesis `hPc` of the
  bridge, `transcriptLawIn_w1C1_le_w1C2`).
- `instDecEqW1BStmt`, `instDecEqW1Tag`, `instDecEqW1Stmt`, `instDecEqW1Rq`: decidable equality of
  the new types (their finiteness is inferred).
- `w1KFEncoding`: the main-request encoding is well formed (`KFEncoding`).
- `W1Route2Hyps`, `w1Route2Hyps`: the hypotheses bundled, and their proof.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open GordieHowe.Quantum GordieHowe.Signature
open scoped ENNReal

variable {X Y : Type} {p : Params} {T : ℕ} {Msg : Type} {N reps : ℕ}

section Objects

variable {prims : Primitives p} [NeZero (bucketCount p)] [nttOps : NTTRingOps]
  [Fintype prims.Power2High] [DecidableEq prims.Power2High] [Fintype prims.Hint]
  [DecidableEq prims.Hint] [Nonempty (MaskBox p)] [Fintype Msg] [DecidableEq Msg]
  [Fintype Y] [DecidableEq Y] [Nonempty Y]
  {O : W1Oracles X Y p prims Msg N reps} {Mo : MaskOracle X Y p T Msg} {βmin : ℚ≥0} {tol : ℕ}
  {enc : Vector prims.High p.k → BucketVec p} {k D : ℕ} [NeZero D] {RMsg : Type} [Fintype RMsg]
  [DecidableEq RMsg] {bmsg : KeyRing (PubKey p prims) N → RMsg → Msg}
  {TPS : PSTypes} {PS : ProofSystem X Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims)) TPS}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D
local notation "PSf" => PS
local notation "X₀f" => W1ExpStmt prims RMsg N

attribute [local instance] admDecF

/-- **The bounded program statements**: a ring statement (published keys, ring messages in `RMsg`)
with a list of at most `n` commitment hashes (a finite type). A function of exactly the types it
reads. -/
abbrev W1BStmt {q : Params} (pr : Primitives q) (RMsg : Type) (n : ℕ) : Type :=
  RingSignature.RingStmtOf (PubKey q pr) RMsg (BucketVec q) n ×
    {l : List (CommitHashBytes q) // l.length ≤ n}

/-- **A program statement bounded**: its hash list truncated to `N` entries. -/
def w1Bnd (x₀ : X₀f) : W1BStmt prims RMsg N :=
  (x₀.1, ⟨x₀.2.take N, by simp⟩)

variable (prims O Mo βmin tol enc k D bmsg PS adm n Q) in
/-- **The tags of the main statements**: a multi-user request, or a signed request (`inl`) or a
dummy request (`inr`) of the insider game with its request number capped at `Q` (`w1Num`). -/
abbrev W1Tag : Type :=
  MURequest (SignOracle.none Bf) n ⊕
    ((RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)) ⊕
      (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)))

variable (prims O Mo βmin tol enc k D bmsg PS adm n Q) in
/-- **The statements of the main challenger**: a bounded program statement with a tag. -/
abbrev W1Stmt : Type :=
  W1BStmt prims RMsg N × W1Tag prims O Mo βmin tol enc k D bmsg PS adm n Q

/-- **The program statement of a main statement.** -/
def w1StmtX (s : W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q) : X₀f :=
  (s.1.1, s.1.2.val)

variable (prims O Mo βmin tol enc k D bmsg PS adm n Q) in
/-- **The proof requests of the relay**: a bounded program statement with the signing request,
its capped request number (`w1Num`) and the base signature, or a dummy request with its capped
request number. -/
abbrev W1Rq : Type :=
  (W1BStmt prims RMsg N × (RingSignature.Insider.Req Bf PSf adm n ×
    Fin (Q + 1)) × FIPSSignature p prims) ⊕ (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))

variable (Q) in
/-- **A request number capped at `Q`**: `min c Q`, below `Q + 1`. -/
def w1Num (c : ℕ) : Fin (Q + 1) :=
  ⟨min c Q, Nat.lt_succ_of_le (min_le_right _ _)⟩

/-- **A request number at most `Q` is kept by `w1Num`.** -/
theorem val_w1Num {c : ℕ} (h : c ≤ Q) : (w1Num Q c).val = c :=
  min_eq_left h

/-- **Distinct request numbers at most `Q` have distinct capped numbers.** -/
theorem w1Num_injOn {c c' : ℕ} (h : c ≤ Q) (h' : c' ≤ Q) (he : w1Num Q c = w1Num Q c') :
    c = c' := by
  rw [← val_w1Num h, ← val_w1Num h', he]

/-- The bounded program statements have decidable equality. -/
noncomputable instance instDecEqW1BStmt :
    DecidableEq (W1BStmt prims RMsg N) :=
  @instDecidableEqProd _ _
    (inferInstance : DecidableEq (RingSignature.RingStmtOf (PubKey p prims) RMsg (BucketVec p) N))
    (inferInstance : DecidableEq {l : List (CommitHashBytes p) // l.length ≤ N})

/-- The tags have decidable equality. -/
noncomputable instance instDecEqW1Tag [DecidableEq X] :
    DecidableEq (W1Tag prims O Mo βmin tol enc k D bmsg PS adm n Q) :=
  @instDecidableEqSum _ _ (inferInstance : DecidableEq (MURequest (SignOracle.none Bf) n))
    (@instDecidableEqSum _ _
      (inferInstance : DecidableEq (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)))
      (inferInstance : DecidableEq (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1))))

/-- The main statements have decidable equality. -/
noncomputable instance instDecEqW1Stmt [DecidableEq X] :
    DecidableEq (W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q) :=
  @instDecidableEqProd _ _ instDecEqW1BStmt instDecEqW1Tag

/-- The relay's proof requests have decidable equality. -/
noncomputable instance instDecEqW1Rq [DecidableEq X] :
    DecidableEq (W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q) :=
  @instDecidableEqSum _ _
    (@instDecidableEqProd _ _ instDecEqW1BStmt
      (@instDecidableEqProd _ _
        (inferInstance : DecidableEq (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)))
        (inferInstance : DecidableEq (FIPSSignature p prims))))
    (inferInstance : DecidableEq (RingSignature.Insider.Req Bf PSf adm n × Fin (Q + 1)))

variable (prims O Mo βmin tol enc k D bmsg PS adm n Q) in
/-- **The relation of the main challenger**: the fixed relation `w1ExpRel` read through the
program statement and the ring witness of a relayed witness. -/
def w1Rel (s : W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q)
    (w : RingSignature.Insider.RelayWit Bf) : Prop :=
  (w1StmtX s, RingSignature.Insider.RelayWit.toWit (B := Bf) w) ∈
    w1ExpRel prims enc bmsg adm

/-- **`w1Rel` is `w1ExpRel` read through the program statement and the ring witness.** -/
theorem w1Rel_iff (s : W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q)
    (w : RingSignature.Insider.RelayWit Bf) :
    w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q s w ↔
      (w1StmtX s, RingSignature.Insider.RelayWit.toWit (B := Bf) w) ∈
        w1ExpRel prims enc bmsg adm :=
  Iff.rfl

variable [Nonempty RMsg] [Nonempty (FIPSSignature p prims)]

variable (prims O Mo βmin tol enc k D bmsg) in
/-- **The dummy program statement**: the empty ring with no hashes. -/
noncomputable def w1DummyX : W1BStmt prims RMsg N :=
  (⟨⟨[], Nat.zero_le _⟩, Classical.arbitrary RMsg, Classical.arbitrary (BucketVec p)⟩,
    ⟨[], Nat.zero_le _⟩)

variable (prims O Mo βmin tol enc k D bmsg) in
/-- **The dummy witness.** -/
noncomputable def w1W0 : RingSignature.Insider.RelayWit Bf :=
  (0, Classical.arbitrary (FIPSSignature p prims))

/-- **The signer's position of a request**: for a signing request `(s, R, m)`, the position
`R.idxOf (pks s)` of the signer's key (below `N + 1`: at most the ring's length); `0` otherwise. -/
def w1Idx (pks : Fin n → PubKey p prims) : RingSignature.Insider.Req Bf PSf adm n → Fin (N + 1)
  | .sign s R _ => ⟨min (R.1.idxOf (pks s)) N, Nat.lt_succ_of_le (min_le_right _ _)⟩
  | _ => 0

/-- **The encoding of the requests as proof queries**: a multi-user request `m` as the dummy
statement tagged `m`; a proof request `(x₀, r, σ)` as `x₀` tagged with `r` (a request and its
capped number), with the signer's position `w1Idx` and `σ`; a dummy request as the dummy
statement tagged with it. -/
noncomputable def w1Enc (pks : Fin n → PubKey p prims) :
    MURequest (SignOracle.none Bf) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q →
      QROM.ProofQuery (W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q)
        (RingSignature.Insider.RelayWit Bf)
  | .inl m => ⟨(w1DummyX prims, .inl m),
      w1W0 prims O Mo βmin tol enc k D bmsg⟩
  | .inr (.inl q) => ⟨(q.1, .inr (.inl q.2.1)), (w1Idx pks q.2.1.1, q.2.2)⟩
  | .inr (.inr r) => ⟨(w1DummyX prims, .inr (.inr r)),
      w1W0 prims O Mo βmin tol enc k D bmsg⟩

/-- **The encoding of the requests is injective.** -/
theorem w1Enc_injective (pks : Fin n → PubKey p prims) :
    Function.Injective (w1Enc (PS := PS) (adm := adm) (Q := Q) pks) := by
  rintro (m | ⟨x, r, σ⟩ | r) (m' | ⟨x', r', σ'⟩ | r') h <;>
    simp only [w1Enc, QROM.ProofQuery.mk.injEq, Prod.mk.injEq, reduceCtorEq, Sum.inl.injEq,
      Sum.inr.injEq, false_and, and_false] at h
  · rw [h.1.2]
  · obtain ⟨⟨rfl, rfl⟩, -, rfl⟩ := h
    rfl
  · rw [h.1.2]

/-- **The proof request of a signed request** `r.1` at the program statement `x₀`; the request
number `r.2` is recorded capped at `Q` (`w1Num`). -/
def w1ToR (x₀ : X₀f) (r : RingSignature.Insider.Req Bf PSf adm n × ℕ)
    (σ : FIPSSignature p prims) : W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q :=
  .inl (w1Bnd x₀, (r.1, w1Num Q r.2), σ)

/-- **The dummy proof request** of the request `r.1`; the request number `r.2` is recorded capped
at `Q` (`w1Num`). -/
def w1DummyR (r : RingSignature.Insider.Req Bf PSf adm n × ℕ) :
    W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q :=
  .inr (r.1, w1Num Q r.2)

/-- **The idle main request**: the public key of user `0`. -/
def w1Idle [NeZero n] :
    MURequest (SignOracle.none Bf) n ⊕ W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q :=
  .inl (.publicKey 0)

variable (PS adm n Q) in
/-- **The dummy statement**: the dummy program statement tagged with the idle request. -/
noncomputable def w1DummyS [NeZero n] : W1Stmt prims O Mo βmin tol enc k D bmsg PS adm n Q :=
  (w1DummyX prims, .inl (.publicKey 0))

/-- **The dummy program statements**: those with the empty ring. -/
def w1IsDummy (x₀ : X₀f) : Bool :=
  decide (x₀.1.ring.1 = [])

open Classical in
/-- **The check of a forgery** `o = (R, m, (y, π))` with the program statement `x₀`: the ring
statement of `x₀` is `(R, m, y)`, and the ring is nonempty. -/
noncomputable def w1CheckX {Pf : Type} (x₀ : X₀f)
    (o : KeyRing (PubKey p prims) N × RMsg × (BucketVec p × Pf)) :
    Bool :=
  decide (x₀.1 = ⟨o.1, o.2.1, o.2.2.1⟩) && decide (o.1.1 ≠ [])

omit hadm [Nonempty RMsg] [Nonempty (FIPSSignature p prims)] in
/-- **No witness of the fixed relation has the empty ring.** -/
theorem not_mem_w1ExpRel_nil {x₀ : X₀f} (h : x₀.1.ring.1 = [])
    (w : RingSignature.RingWitOf (FIPSSignature p prims)) : (x₀, w) ∉ w1ExpRel prims enc bmsg adm := by
  rintro ⟨-, hi, -⟩
  change w.idx < x₀.1.ring.1.length at hi
  simp [h] at hi

/-- **The dummy statements** (`DummyStmts`): the dummy statement and the statements of the
multi-user requests have the empty ring, which has no witness. -/
theorem w1DummyStmts [NeZero n] (pks : Fin n → PubKey p prims)
    [DecidableRel (w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q)] :
    RingSignature.KeyFree.DummyStmts Bf (w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q)
      (w1Enc pks) (w1DummyS PS adm n Q) w1StmtX w1IsDummy where
  dummyS := by simp [w1IsDummy, w1StmtX, w1DummyS, w1DummyX]
  inl _ := by simp [w1IsDummy, w1StmtX, w1Enc, w1DummyX]
  not_rel s hs w := not_mem_w1ExpRel_nil (by simpa [w1IsDummy] using hs) _

omit [Nonempty RMsg] [Nonempty (FIPSSignature p prims)] in
/-- **A checked statement is not a dummy statement**: its ring is the forgery's, nonempty. -/
theorem w1Disj {Pf : Type} (x : X₀f) (hx : w1IsDummy x = true)
    (q : (KeyRing (PubKey p prims) N × RMsg × (BucketVec p × Pf)) × X₀f)
    (hq : w1CheckX q.2 q.1 = true) : x ≠ q.2 := by
  rintro rfl
  simp only [w1CheckX, Bool.and_eq_true, decide_eq_true_eq] at hq
  simp only [w1IsDummy, decide_eq_true_eq] at hx
  rw [hq.1] at hx
  exact hq.2 hx

/-- **The dummy requests have dummy statements**: the empty ring. -/
theorem w1DumS (pks : Fin n → PubKey p prims)
    (r : RingSignature.Insider.Req Bf PSf adm n × ℕ) :
    w1IsDummy (w1StmtX (w1Enc (PS := PS) (Q := Q) pks (.inr (w1DummyR r))).stmt) = true := by
  simp [w1IsDummy, w1StmtX, w1Enc, w1DummyR, w1DummyX]

/-- **The idle request is not a proof request**, so its proof requests have dummy statements
vacuously. -/
theorem w1IdleS [NeZero n] (pks : Fin n → PubKey p prims)
    (q : W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q) (hq : w1Idle = .inr q) :
    w1IsDummy (w1StmtX (w1Enc pks (.inr q)).stmt) = true :=
  absurd hq (by simp [w1Idle])

/-- **The idle request is not a corruption.** -/
theorem w1IdleC [NeZero n] (i : Fin n) :
    (w1Idle : MURequest (SignOracle.none Bf) n ⊕
      W1Rq prims O Mo βmin tol enc k D bmsg PS adm n Q) ≠ .inl (.corrupt i) := by
  simp [w1Idle]

omit [NeZero (bucketCount p)] [Fintype prims.Power2High] [DecidableEq prims.Power2High]
  [Fintype prims.Hint] [DecidableEq prims.Hint] [Fintype Msg] [DecidableEq Msg] nttOps
  [Nonempty (MaskBox p)] [Fintype Y] [DecidableEq Y] [Nonempty Y]
  [Nonempty (FIPSSignature p prims)] in
/-- **The hashes of a list of keys** have the list's length on every path. -/
theorem allOut_hashesProg_length {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]
    (sp : OracleSplit Y Y₁ Y₂) (O : W1Oracles X Y p prims Msg N reps) (m : Msg)
    (w1 : BucketVec p) :
    ∀ l : List (PubKey p prims),
      (hashesProg sp prims O m w1 l).AllOut fun cs => cs.length = l.length
  | [] => rfl
  | pk :: l => fun _ _ => OracleProg.AllOut.mapOutput _
      ((allOut_hashesProg_length sp O m w1 l).mono fun _ h => by simp [h])

variable {Y₁ Y₂ : Type} [AddGroup Y] [AddGroup Y₁] [AddGroup Y₂]

/-- **The statement program of the relay**: the program statement `w1StmtProg` of a ring
statement, its queries answered by the base component of the oracle. -/
noncomputable def w1StmtP (sp : OracleSplit Y Y₁ Y₂) (x : RingSignature.RingStmt Bf) :
    OracleProg X Y X₀f :=
  (w1StmtProg sp prims O bmsg x).mapQuery id fun y => (sp y).1

omit [Nonempty RMsg] [Nonempty (FIPSSignature p prims)] in
/-- **The statement program at an oracle** is the program statement at its base component. -/
theorem run_w1StmtP (sp : OracleSplit Y Y₁ Y₂) (x : RingSignature.RingStmt Bf) (H : X → Y) :
    (w1StmtP sp x).run H = (w1StmtProg sp prims O bmsg x).run (base sp H) :=
  OracleProg.run_mapQuery _ _ _ _

omit [Nonempty RMsg] [Nonempty (FIPSSignature p prims)] in
/-- **The statement program makes at most `2N` queries.** -/
theorem w1StmtP_queries (sp : OracleSplit Y Y₁ Y₂) (x : RingSignature.RingStmt Bf) :
    (w1StmtP sp x).QueriesLE (2 * N) := fun H => by
  rw [w1StmtP, OracleProg.length_trace_mapQuery]
  exact w1StmtProg_queries sp prims O bmsg _ _

omit [Nonempty RMsg] [Nonempty (FIPSSignature p prims)] in
/-- **The statement program's outputs** read back its input and carry hash lists of the ring's
length, on every path. -/
theorem allOut_w1StmtP (sp : OracleSplit Y Y₁ Y₂) (x : RingSignature.RingStmt Bf) :
    (w1StmtP sp x).AllOut fun x₀ => x₀.1 = x ∧ x₀.2.length = x.ring.1.length :=
  OracleProg.AllOut.mapQuery _ _ (OracleProg.AllOut.mapOutput _
    ((allOut_hashesProg_length sp O _ _ _).mono fun _ h => ⟨rfl, h⟩))

omit [Nonempty RMsg] [Nonempty (FIPSSignature p prims)] in
/-- **The statement program's outputs read back its input** (`hfst`). -/
theorem w1Fst (sp : OracleSplit Y Y₁ Y₂) (x : RingSignature.RingStmt Bf) :
    (w1StmtP sp x).AllOut fun x₀ => x₀.1 = x :=
  (allOut_w1StmtP sp x).mono fun _ h => h.1

omit [AddGroup Y] in
/-- **A proof request carries a program statement with at most `N` hashes.** -/
theorem w1StmtX_enc_toR (pks : Fin n → PubKey p prims) {x₀ : X₀f} (h : x₀.2.length ≤ N)
    (r : RingSignature.Insider.Req Bf PSf adm n × ℕ) (σ : FIPSSignature p prims) :
    w1StmtX (w1Enc (Q := Q) pks (.inr (w1ToR x₀ r σ))).stmt = x₀ := by
  change (x₀.1, x₀.2.take N) = x₀
  rw [List.take_of_length_le h]

/-- **`w1ToR` carries the statement program's outputs** (`htoR`). -/
theorem w1ToROut (pks : Fin n → PubKey p prims) (sp : OracleSplit Y Y₁ Y₂)
    (x : RingSignature.RingStmt Bf) :
    (w1StmtP sp x).AllOut fun x₀ => ∀ (r : RingSignature.Insider.Req Bf PSf adm n × ℕ) σ,
      w1StmtX (w1Enc (Q := Q) pks (.inr (w1ToR x₀ r σ))).stmt = x₀ :=
  (allOut_w1StmtP sp x).mono fun _ h r σ =>
    w1StmtX_enc_toR pks (h.2.trans_le x.ring.2) r σ

omit [Nonempty RMsg] [Nonempty (FIPSSignature p prims)] [AddGroup Y] in
/-- **The signer's position of a signing request** is the position `idxOf` of the signer's key. -/
theorem val_w1Idx_sign (pks : Fin n → PubKey p prims) (s : Fin n) (R : KeyRing (PubKey p prims) N)
    (m : RMsg) :
    (w1Idx (PS := PS) (adm := adm) pks (.sign s R m)).val = R.1.idxOf (pks s) :=
  min_eq_left (List.idxOf_le_length.trans R.2)

omit [AddGroup Y] in
/-- **The relayed witness of a signed request** is the signer's position and the signature. -/
theorem toWit_w1Enc_toR (pks : Fin n → PubKey p prims) (x₀ : X₀f) (s : Fin n)
    (R : KeyRing (PubKey p prims) N) (m : RMsg) (c : ℕ) (σ : FIPSSignature p prims) :
    RingSignature.Insider.RelayWit.toWit (B := Bf)
        (w1Enc (PS := PS) (adm := adm) (Q := Q) pks (.inr (w1ToR x₀ (.sign s R m, c) σ))).wit =
      ⟨R.1.idxOf (pks s), σ⟩ := by
  change (⟨(w1Idx (PS := PS) (adm := adm) pks (.sign s R m)).val, σ⟩ :
    RingSignature.RingWitOf (FIPSSignature p prims)) = _
  rw [val_w1Idx_sign]

/-- **Kept signatures are in the relation** (`KeptInRel`), for decodings reading only the first
component: a signature of a member of a supported ring verifying at `H'` is a witness of the ring
relation at `H'`, hence of the fixed relation for the program statement read at `H'`
(`mem_w1ExpRel_of_ringRel`). -/
theorem w1KeptInRel [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁]
    (sp : OracleSplit Y Y₁ Y₂) (hO : O.ReadsFst sp) (keys : Fin n → (Bf).KeyCoins) :
    KeptInRel (O := O) (M := Mo) (βmin := βmin) (tol := tol) (k := k) (D := D) (bmsg := bmsg)
      (PS := PS) (adm := adm) enc (w1Rel prims O Mo βmin tol enc k D bmsg PS adm n Q)
      (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR keys := by
  intro s R m c σ H' hmem hR hver
  unfold keptQuery
  have hlen := (allOut_w1StmtP (prims := prims) (O := O) (Mo := Mo) (βmin := βmin) (tol := tol)
    (enc := enc) (k := k) (D := D) (bmsg := bmsg) sp
    (⟨R, m, w1Of prims enc ((Bf).pk (keys s)) σ⟩ : RingSignature.RingStmt Bf)).run H'
  simp only [w1Rel, w1Enc, w1ToR,
    w1StmtX, w1Bnd, RingSignature.Insider.RelayWit.toWit]
  rw [List.take_of_length_le (hlen.2.trans_le R.2)]
  erw [val_w1Idx_sign]
  rw [run_w1StmtP]
  refine mem_w1ExpRel_of_ringRel (βmin := βmin) (tol := tol) (L := Lf) prims hO H' _ _ ⟨hR, List.idxOf_lt_length_iff.2 hmem, ?_, ?_⟩
  · dsimp only
    erw [List.getElem_idxOf (α := PubKey p prims)]
    exact hver
  · dsimp only
    erw [List.getElem_idxOf (α := PubKey p prims)]
    rfl

end Objects

/-! ### The prover of the ring is the main prover after the statement program -/

section Prover

open GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP

variable {kh kN kS L e : ℕ} {Y Y₁ : Type} [AddGroup Y] [AddGroup Y₁] [Fintype Y] [DecidableEq Y]
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
  {Qs : ∀ x, Mc.IOPQueries Vr x} {hb : Mc.FormatBounds Qs b b} {R : Type} [Fintype R] [Nonempty R]
  {honest : RingSignature.RingWit (freshBase prims O Mo βmin tol enc k D bmsg) → R →
    CausalProver P τ (W1ExpStmt prims RMsg N)}
  {adm : KeyRing (PubKey p prims) N → Prop}
  [hadm : DecidablePred adm] {n Q : ℕ}
  {chk : RingSignature.RingStmt (freshBase prims O Mo βmin tol enc k D bmsg) → Bool}

local notation "Bf" => freshBase prims O Mo βmin tol enc k D bmsg
local notation "Lf" => freshLoop prims O Mo βmin k D

attribute [local instance] admDecF

variable (sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest) in
/-- **The hedged proof system as the spBCS proof system of the fresh base signer**, for any check
`check` of the ring statements: the spBCS proof system on the second component at the program
statement `w1StmtProg`, the ring witness as the honest input, checking `check`. The hedged and the
fresh base signer have the same statements and witnesses (`comap_w1HPS`); at
`check := fun _ => true` it is `w1PS`. -/
noncomputable abbrev w1HPS (check : RingSignature.RingStmt Bf → Bool) :
    ProofSystem (Bits (queryBits kh kN kS L)) Y (RingSignature.RingStmt (hedgedBase prims O Mo βmin tol enc k D bmsg)) (RingSignature.RingWitOf (FIPSSignature p prims))
      (spbcsPST Mc b R) :=
  (Ring.spbcsSplitProofSystem sp Mc Λ E hb honest (w1StmtProg sp prims O bmsg)
    (2 * N) (w1StmtProg_queries sp prims O bmsg) check fun _ w => some w)

/-- **`w1HPS` read at the fresh statements is the spBCS proof system checking `chk`**, for any
check; at `check := fun _ => true` it is `w1PS`. -/
theorem comap_w1HPS :
    (w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk) =
      Ring.spbcsSplitProofSystem sp Mc Λ E hb honest (w1StmtProg sp prims O bmsg)
        (2 * N) (w1StmtProg_queries sp prims O bmsg) chk fun _ w => some w :=
  rfl

/-- **The proof of a forgery** `(R, m, (y, π))`: the proof of `π`, if any. -/
def w1PrfOf (o : KeyRing (PubKey p prims) N × RMsg × (BucketVec p × Mc.Response b)) :
    Option Mc.NIProof :=
  o.2.2.2.map Subtype.val

local notation "PSh" => w1HPS sp prims O Mo βmin tol enc k D bmsg Mc Λ E hb honest chk

variable (sp Mc Λ E hb honest n Q chk) in
/-- **The main prover on the full oracle**, for any check of `w1HPS`: the compiled honest prover
`encProver` at the program statement and the ring witness of a main statement and witness,
reading the second components of the oracle's values. -/
noncomputable abbrev w1MainProver :
    NARG.Prover (Bits (queryBits kh kN kS L)) Y
      (W1Stmt prims O Mo βmin tol enc k D bmsg PSh adm n Q) (RingSignature.Insider.RelayWit Bf)
      (Mc.Response b) (SaltedCoins (FiatShamirSalt kS) (Mc.ProverCoins R)) :=
  ((RingSignature.Insider.encProver Mc Λ E hb honest).comap w1StmtX
    (RingSignature.Insider.RelayWit.toWit (B := Bf))).mapQuery id fun y => (sp y).2

/-- **The main prover's coins are uniform.** -/
theorem w1MainProver_coins :
    (w1MainProver (adm := adm) sp Mc Λ E hb honest n Q chk).coins = PMF.uniformOfFintype _ :=
  rfl

variable [Nonempty RMsg] [Nonempty (FIPSSignature p prims)]

/-- **The ring prover is the main prover after the statement program** (`ProverRelays`), for any
check of `w1HPS`: the
ring proof of `(R, m, w1Of pk σ)` at an oracle reprogrammed by an assignment keeping the second
component is the compiled prover's proof of the program statement read there, with the signer's
position and `σ`, against the second component, which the assignment keeps; that is the main
prover's proof of the kept proof query. -/
theorem w1ProverRelays (keys : Fin n → (Bf).KeyCoins) :
    ProverRelays (M := Mo) (βmin := βmin) (tol := tol) (k := k) (D := D) (bmsg := bmsg)
      (PS := PSh) (adm := adm) O enc sp (w1MainProver sp Mc Λ E hb honest n Q chk)
      (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR keys := by
  intro s Rg m c σ cp H a ha
  have hprf : prf sp (H.reprogram [a]) = prf sp H := by
    funext z
    simp only [prf, reprogram_singleton_apply]
    split_ifs with hz
    · rw [ha, hz]
    · rfl
  have hlen := (allOut_w1StmtP (prims := prims) (O := O) (Mo := Mo) (βmin := βmin) (tol := tol)
    (enc := enc) (k := k) (D := D) (bmsg := bmsg) sp
    (⟨Rg, m, w1Of prims enc ((Bf).pk (keys s)) σ⟩ : RingSignature.RingStmt Bf)).run
      (H.reprogram [a])
  refine (run_prove_spbcsSplitProofSystem sp Mc Λ E hb honest
    (w1StmtProg sp prims O bmsg) (2 * N)
    (w1StmtProg_queries sp prims O bmsg) chk (fun _ w => some w)
    (H.reprogram [a]) _ _ rfl cp).trans ?_
  unfold keptQuery
  simp only [w1MainProver, NARG.Prover.mapQuery, NARG.Prover.comap, w1Enc, w1ToR,
    w1StmtX, w1Bnd, RingSignature.Insider.RelayWit.toWit]
  rw [List.take_of_length_le (hlen.2.trans_le Rg.2)]
  erw [val_w1Idx_sign]
  rw [run_w1StmtP, hprf]
  exact (OracleProg.run_mapQuery id (fun y => (sp y).2) H _).symm

variable (sp) in
/-- **The main-request encoding of the ML-DSA ring publishing `w₁` is well formed**
(`RingSignature.KeyFree.KFEncoding`) at the users' key coins `keys`: `w1Enc`, `w1StmtX`,
`w1IsDummy`, `w1Idle`, `w1DummyR`, `w1ToR`, `w1StmtP` and the first component. -/
theorem w1KFEncoding [NeZero n] (keys : Fin n → (Bf).KeyCoins) :
    RingSignature.KeyFree.KFEncoding (w1Enc (Q := Q) fun i => (Bf).pk (keys i))
      w1StmtX w1IsDummy w1Idle
      (w1DummyR : _ → W1Rq prims O Mo βmin tol enc k D bmsg PSh adm n Q) w1ToR (w1StmtP sp)
      Prod.fst where
  hdumS := w1DumS _
  hfst := w1Fst sp
  htoR := w1ToROut _ sp
  hidleS := w1IdleS _
  hidleC := w1IdleC

omit [Nonempty RMsg] [Nonempty (FIPSSignature p prims)] in
variable (sp Mc Λ E hb honest n Q chk) in
/-- **The hypotheses of the key-free chain and of route 2 at the ML-DSA ring publishing `w₁`**, for
any check of `w1HPS`, at the users' key coins `keys`: for the relation `w1Rel`, the encoding
`w1Enc`, the dummy statement `w1DummyS` and the test `w1IsDummy`, the check `w1CheckX`, the
key-free signer `w1KFSign`, the statement program `w1StmtP`, the maps `w1ToR` and `w1DummyR`,
the idle request `w1Idle` and the main prover `w1MainProver`: the hypotheses `hrel`, `henc`, `hd`,
`hdisj`, `hpatch` and `hkf` of `RingSignature.KeyFree.kfChain_le`, and `ProverRelays`
and `KeptInRel`. -/
structure W1Route2Hyps [Nonempty RMsg]
    [Nonempty (FIPSSignature p prims)] [NeZero n] [Fintype Y₁] [DecidableEq Y₁]
    [DecidableRel (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)]
    (keys : Fin n → (Bf).KeyCoins) : Prop where
  /-- The relation is `w1ExpRel` through the program statement and the ring witness. -/
  hrel : ∀ x w, w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q x w ↔
    (w1StmtX x, RingSignature.Insider.RelayWit.toWit (B := Bf) w) ∈
      w1ExpRel prims enc bmsg adm
  /-- The encoding is injective. -/
  henc : Function.Injective (w1Enc (PS := PSh) (adm := adm) (Q := Q) fun i => (Bf).pk (keys i))
  /-- The dummy statements. -/
  hd : RingSignature.KeyFree.DummyStmts Bf (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
    (w1Enc fun i => (Bf).pk (keys i)) (w1DummyS PSh adm n Q) w1StmtX w1IsDummy
  /-- A checked statement is not a dummy statement. -/
  hdisj : ∀ x, w1IsDummy x = true →
    ∀ q : (KeyRing (PubKey p prims) N × RMsg × (BucketVec p × Mc.Response b)) ×
      W1ExpStmt prims RMsg N, w1CheckX q.2 q.1 = true → x ≠ q.2
  /-- The signer's assignments keep the second component. -/
  hpatch : ∀ pk Rg c msg (sc : KFCoins (p := p) (T := T) k D Y₁) H o,
    (w1KFSign (RMsg := RMsg) prims O sp βmin tol enc k D bmsg pk Rg c msg sc).run H = some o →
      prf sp (H.reprogram o.2.2) = prf sp H
  /-- The main-request encoding is well formed (`w1KFEncoding`). -/
  kfEncoding : RingSignature.KeyFree.KFEncoding (w1Enc (Q := Q) fun i => (Bf).pk (keys i))
    w1StmtX w1IsDummy w1Idle
    (w1DummyR : _ → W1Rq prims O Mo βmin tol enc k D bmsg PSh adm n Q) w1ToR (w1StmtP sp)
    Prod.fst
  /-- The ring prover is the main prover after the statement program. -/
  prover : ProverRelays (M := Mo) (βmin := βmin) (tol := tol) (k := k) (D := D) (bmsg := bmsg)
    (PS := PSh) (adm := adm) O enc sp (w1MainProver sp Mc Λ E hb honest n Q chk)
    (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR keys
  /-- Kept signatures are in the relation. -/
  kept : KeptInRel (O := O) (M := Mo) (βmin := βmin) (tol := tol) (k := k) (D := D)
    (bmsg := bmsg) (PS := PSh) (adm := adm) enc
    (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)
    (w1Enc fun i => (Bf).pk (keys i)) (w1StmtP sp) w1ToR keys

/-- **The hypotheses of the key-free chain and of route 2 hold at the ML-DSA ring publishing
`w₁`**, for any check of `w1HPS` and decodings reading only the first component. -/
theorem w1Route2Hyps [NeZero n] [Fintype Y₁] [DecidableEq Y₁]
    [DecidableRel (w1Rel prims O Mo βmin tol enc k D bmsg PSh adm n Q)] (hO : O.ReadsFst sp)
    (keys : Fin n → (Bf).KeyCoins) :
    W1Route2Hyps (prims := prims) (O := O) (Mo := Mo) (βmin := βmin) (tol := tol) (enc := enc)
      (k := k) (D := D) (bmsg := bmsg) (adm := adm) sp Mc Λ E hb honest n Q chk keys where
  hrel := w1Rel_iff
  henc := w1Enc_injective _
  hd := w1DummyStmts _
  hdisj x hx q hq := w1Disj x hx q hq
  hpatch pk Rg c msg sc H o ho := prf_reprogram_w1KFSign sp pk Rg c msg sc H o ho
  kfEncoding := w1KFEncoding sp keys
  prover := w1ProverRelays keys
  kept := w1KeptInRel sp hO keys


/-! ### The finiteness the key-free chain asks for

The main statements, the relay's proof requests, the requests and replies of the insider game and
the relayed witnesses are finite with decidable equality, by the instances in scope. -/

section Finite

variable [Fintype Y₁] [NeZero n]

noncomputable example : DecidableEq (W1Stmt prims O Mo βmin tol enc k D bmsg PSh adm n Q) :=
  inferInstance
noncomputable example : DecidableEq (W1Rq prims O Mo βmin tol enc k D bmsg PSh adm n Q) :=
  inferInstance
noncomputable example : Fintype (W1Stmt prims O Mo βmin tol enc k D bmsg PSh adm n Q) :=
  inferInstance
noncomputable example : Fintype (W1Rq prims O Mo βmin tol enc k D bmsg PSh adm n Q) :=
  inferInstance
noncomputable example : Fintype (RingSignature.Insider.Req Bf
    ((PSh)) adm n) :=
  inferInstance
noncomputable example : Fintype (RingSignature.Insider.Resp Bf
    ((PSh)) adm) :=
  inferInstance
noncomputable example : Fintype (RingSignature.Insider.RelayWit Bf) := inferInstance

end Finite

end Prover

end GordieHowe.Ring.MLDSAW1
