-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Ring.MLDSAW1Unforgeability
public import GordieHowe.Applications.Ring.RingForgerSplitChain

@[expose] public section

/-!
# The inputs of the split knowledge-soundness bound for the ML-DSA ring publishing `w₁`

The bound up to the extraction runs (`insiderForgeProb_le_extRun_split`,
`GordieHowe/Applications/Ring/RingForgerSplitChain.lean`) takes a program `P` computing the program
statement of a forgery at the base component of the oracle (`hPst`) and claims factoring through the
program statement (`hcl`). For the proof system `w1PS` of
`GordieHowe/Applications/Ring/MLDSAW1Unforgeability.lean`:

- `w1ForgeStmtProg`: the program statement `w1StmtProg` of the forgery's ring statement, its
  queries read through the base component; `w1ForgeStmtProg_queries`: at most `2N` queries;
  `run_w1ForgeStmtProg_join`: at the oracle `join sp ω h` it is the compiled program statement at
  `ω`.
- `w1Claim`: the claim of a program statement and a proof; `claim_w1PS`: the claims of `w1PS`
  factor through the program statement.
- `causalRBRKnowledgeSound_reject`: the round-by-round knowledge soundness hypothesis of the
  knowledge bound is satisfiable for every relation (the verifier rejecting every transcript).
- `oneMsgSpec`, `oneMsgVerifier`, `oneMsgExtractor`, `causalRBRKnowledgeSound_oneMsg`,
  `oneMsgVerifier_oneMsgTr`: the one-message IOP, in which the prover sends a witness and the
  verifier decides the relation; it is causal round-by-round knowledge sound with error `0` and
  accepts the transcript sending a witness. `instDecidablePredMemW1ExpRel`: `w1ExpRel` is decidable.
-/

namespace GordieHowe.Ring.MLDSAW1

open _root_.MLDSA GordieHowe.MLDSA GordieHowe.RingSignature GordieHowe.RingSignature.OracleSplit
open Quantum GordieHowe.QROM GordieHowe.SPBCS IOP SPTerm GordieHowe.IOP
open scoped ENNReal

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

/-- **The program statement of a forgery**: `w1StmtProg` at the forgery's ring statement
`(R, m, w₁)`, its queries answered by the base component of the oracle. -/
def w1ForgeStmtProg
    (o : KeyRing (PubKey p prims) N × RMsg × (BucketVec p × M.Response b)) :
    OracleProg (Bits (queryBits k kN kS L)) Y (W1ExpStmt prims RMsg N) :=
  (w1StmtProg sp prims O bmsg ⟨o.1, o.2.1, o.2.2.1⟩).mapQuery id fun y => (sp y).1

omit [NeZero (bucketCount p)] [∀ j i, Nonempty ((P j).Challenge i)]
  [∀ j i, Fintype ((M.comp j).MessageWrite i)] in
/-- The program statement of a forgery is read by at most `2N` queries. -/
theorem w1ForgeStmtProg_queries
    (o : KeyRing (PubKey p prims) N × RMsg × (BucketVec p × M.Response b)) :
    (w1ForgeStmtProg sp prims O bmsg M o).QueriesLE (2 * N) := fun H => by
  rw [w1ForgeStmtProg, OracleProg.length_trace_mapQuery]
  exact w1StmtProg_queries sp prims O bmsg _ _

omit [NeZero (bucketCount p)] in
/-- **At the oracle with base component `ω` the program statement of a forgery is the compiled
program statement at `ω`.** -/
theorem run_w1ForgeStmtProg_join
    (o : KeyRing (PubKey p prims) N × RMsg × (BucketVec p × M.Response b))
    (ω : Bits (queryBits k kN kS L) → Y₁) (h : Bits (queryBits k kN kS L) → XOut k e) :
    (w1ForgeStmtProg sp prims O bmsg M o).run (join sp ω h) =
      (compiledBySplit_spbcsSplitProofSystem sp M Λ E hb honest
        (w1StmtProg sp prims O bmsg) (2 * N)
        (w1StmtProg_queries sp prims O bmsg) (fun _ => true)
        fun _ w => some w).stmtAt ω ⟨o.1, o.2.1, o.2.2.1⟩ := by
  rw [w1ForgeStmtProg, OracleProg.run_mapQuery]
  have hω : ((fun y => (sp y).1) ∘ join sp ω h ∘ id) = ω := base_join sp ω h
  rw [hω]
  rfl

variable {Λ E hb honest}

/-- **The claim of a program statement `x₀` and a proof** `π`: `(x₀, π)`, none for the missing
proof. -/
def w1Claim (x₀ : W1ExpStmt prims RMsg N) (π : M.Response b) :
    Option (Claim (W1ExpStmt prims RMsg N) M.NIProof) :=
  π.map fun q => ⟨x₀, q.1⟩

omit [NeZero (bucketCount p)] in
/-- **The claims of `w1PS` factor through the program statement.** -/
theorem claim_w1PS (ω : Bits (queryBits k kN kS L) → Y₁)
    (x : RingSignature.RingStmt (w1BaseSigner prims O βmin tol enc Lp bmsg)) (π : M.Response b) :
    (compiledBySplit_spbcsSplitProofSystem sp M Λ E hb honest
        (w1StmtProg sp prims O bmsg) (2 * N)
        (w1StmtProg_queries sp prims O bmsg) (fun _ => true)
        fun _ w => some w).claim ω x π =
      w1Claim prims M
        ((compiledBySplit_spbcsSplitProofSystem sp M Λ E hb honest
          (w1StmtProg sp prims O bmsg) (2 * N)
          (w1StmtProg_queries sp prims O bmsg) (fun _ => true)
          fun _ w => some w).stmtAt ω x) π :=
  rfl

/-! ### The knowledge-soundness hypothesis is satisfiable -/

section RBR

variable {ι : Type} {τ : SPTerm ι} {nr : ι → ℕ} {P : (j : ι) → ProtocolSpec (nr j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, Nonempty ((P j).Challenge i)] {Stmt Wit : Type}

omit nttOps in
/-- **Causal round-by-round knowledge soundness is satisfiable for every relation**: the verifier
that rejects every transcript is round-by-round knowledge sound for `rel` with errors `0`, at every
causal extractor and the state that is always false. -/
theorem causalRBRKnowledgeSound_reject (rel : Set (Stmt × Wit)) (E : CausalExtractor P τ Stmt Wit) :
    CausalRBRKnowledgeSound rel (fun _ _ => false) E (fun _ _ _ _ _ => False) 0 where
  exists_flip _ _ h := absurd h Bool.false_ne_true
  rbr _ _ _ := le_of_eq_of_le (QROM.probUniform_eq_zero fun _ h => h.2.2) zero_le

end RBR

/-! ### A one-message IOP deciding the relation -/

section OneMsg

variable {Stmt Wit : Type}

variable (Wit) in
/-- **The one-message protocol**: the prover sends a witness (round `0`), the verifier sends the
trivial challenge (round `1`). -/
def oneMsgSpec : ProtocolSpec 2 where
  dir
    | ⟨0, _⟩ => .P_to_V
    | ⟨_ + 1, _⟩ => .V_to_P
  «Type»
    | ⟨0, _⟩ => Wit
    | ⟨_ + 1, _⟩ => Unit

omit nttOps in
/-- Round `0` of `oneMsgSpec` is the prover's. -/
theorem oneMsgSpec_pos (i : (oneMsgSpec Wit).ChallengeIdx) : 0 < (i.1 : ℕ) := by
  obtain ⟨⟨v, hv⟩, h⟩ := i
  match v, hv, h with
  | _ + 1, _, _ => exact Nat.succ_pos _

/-- The challenges of `oneMsgSpec` are the unit. -/
def oneMsgSpec_challengeEquiv (i : (oneMsgSpec Wit).ChallengeIdx) :
    (oneMsgSpec Wit).Challenge i ≃ Unit := by
  obtain ⟨⟨v, hv⟩, h⟩ := i
  match v, hv, h with
  | _ + 1, _, _ => exact Equiv.refl _

instance (i : (oneMsgSpec Wit).ChallengeIdx) : Fintype ((oneMsgSpec Wit).Challenge i) :=
  Fintype.ofEquiv Unit (oneMsgSpec_challengeEquiv i).symm

instance (i : (oneMsgSpec Wit).ChallengeIdx) : Nonempty ((oneMsgSpec Wit).Challenge i) :=
  ⟨(oneMsgSpec_challengeEquiv i).symm ()⟩

instance (i : (oneMsgSpec Wit).ChallengeIdx) : DecidableEq ((oneMsgSpec Wit).Challenge i) :=
  (oneMsgSpec_challengeEquiv i).decidableEq

/-- The witness sent in a transcript of `oneMsgSpec`. -/
def oneMsgWit (f : FullTr (fun _ : Unit => oneMsgSpec Wit) (.leaf ())) : Wit :=
  f (.here ()) ⟨0, Nat.two_pos⟩

/-- The transcript of `oneMsgSpec` sending the witness `w`. -/
def oneMsgTr (w : Wit) : FullTr (fun _ : Unit => oneMsgSpec Wit) (.leaf ()) :=
  fun _ => Fin.cons (α := fun i : Fin 2 => (oneMsgSpec Wit).Type (Fin.castLE (by omega) i)) w
    fun _ => ()

omit nttOps in
/-- The transcript sending `w` sends `w`. -/
@[simp] theorem oneMsgWit_oneMsgTr (w : Wit) : oneMsgWit (oneMsgTr w) = w :=
  rfl

variable (rel : Set (Stmt × Wit)) [DecidablePred (· ∈ rel)]

/-- **The verifier of the one-message IOP**: it accepts when the sent witness is a witness of the
statement. -/
def oneMsgVerifier (x : Stmt) (f : FullTr (fun _ : Unit => oneMsgSpec Wit) (.leaf ())) : Bool :=
  decide ((x, oneMsgWit f) ∈ rel)

/-- **The extractor of the one-message IOP**: the witness sent before the challenge.

Running time: one read of the causal past. -/
def oneMsgExtractor : CausalExtractor (fun _ : Unit => oneMsgSpec Wit) (.leaf ()) Stmt Wit where
  extract c _ past := past.own ⟨0, oneMsgSpec_pos c.idx⟩

omit nttOps in
/-- At the challenge, the extractor reads the witness sent in the transcript. -/
theorem oneMsgExtractor_past (x : Stmt) (f : FullTr (fun _ : Unit => oneMsgSpec Wit) (.leaf ())) :
    oneMsgExtractor ⟨.here (), ⟨1, rfl⟩⟩ x (f.past ⟨.here (), ⟨1, rfl⟩⟩) = oneMsgWit f :=
  rfl

omit nttOps in
/-- **The one-message IOP accepts the honest transcript**: the transcript sending a witness of the
statement is accepted. -/
theorem oneMsgVerifier_oneMsgTr {x : Stmt} {w : Wit} (h : (x, w) ∈ rel) :
    oneMsgVerifier rel x (oneMsgTr w) = true :=
  decide_eq_true (by rwa [oneMsgWit_oneMsgTr])

omit nttOps in
/-- **The one-message IOP is causal round-by-round knowledge sound with error `0`** for `rel`, at
its extractor and the state that is always false: an accepted transcript carries a witness, which
the extractor reads off the causal past of the challenge. -/
theorem causalRBRKnowledgeSound_oneMsg :
    CausalRBRKnowledgeSound rel (oneMsgVerifier rel) oneMsgExtractor (fun _ _ _ _ _ => False) 0
    where
  exists_flip x f hv _ hE :=
    absurd (of_decide_eq_true hv) (oneMsgExtractor_past x f ▸ hE ⟨.here (), ⟨1, rfl⟩⟩)
  rbr _ _ _ := le_of_eq_of_le (QROM.probUniform_eq_zero fun _ h => h.2.2) zero_le

end OneMsg

omit nttOps in
/-- **The fixed relation `w1ExpRel` is decidable**, so the one-message IOP
(`causalRBRKnowledgeSound_oneMsg`) decides it. -/
noncomputable instance instDecidablePredMemW1ExpRel {adm : KeyRing (PubKey p prims) N → Prop}
    [hadm : DecidablePred adm] : DecidablePred (· ∈ w1ExpRel prims enc bmsg adm) :=
  fun q => by
    unfold w1ExpRel
    simp only [Set.mem_ofPred_eq, ← Option.mem_def]
    haveI : ∀ (o : Option (CommitHashBytes p)) (P : CommitHashBytes p → Prop) [DecidablePred P],
        Decidable (∃ c ∈ o, P c) := fun o P _ => match o with
      | none => isFalse (by simp)
      | some a => decidable_of_iff (P a) (by simp)
    exact @instDecidableAnd _ _ (hadm _) (@exists_prop_decidable _ _ inferInstance fun _ =>
      @this _ _ fun _ =>
        @instDecidableAnd _ _ inferInstance ((inferInstance : DecidableEq (BucketVec p)) _ _))

end GordieHowe.Ring.MLDSAW1
