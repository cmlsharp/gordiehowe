-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.FieldFJ
public import GordieHowe.ProofSystem.Program.Transcript.ReaderLoads
public import GordieHowe.ProofSystem.Program.ForkJoinMerge
public import GordieHowe.Foundations.ToMathlib.NNRealDyadic
public import GordieHowe.ProofSystem.Program.BCSFormat

@[expose] public section

/-!
# GordieHowe: the figures of a series–parallel transcript from the ready data

The figures a configuration's setting with merges is built from (rounds, leaves, queried columns,
branches, leaf bytes, loads), for the multi-circuit IOP with forked domains on the generic per-field
domain proofs (`GordieHowe.RealizedProgram.ProofSystem.fieldBranches`), stated through numbers of the domains' ready data
(`GordieHowe.RealizedProgram.FieldReady`) and of the program's circuits only. Those numbers are closed terms at a
configuration, so its figures are checked by `decide`.

* **The domain's numbers**: the tableau's leaves `N`, code dimension, repetitions and opened columns
  are the certificate's (`fieldFork_N`, `fieldFork_k`, `fieldFork_nrep`, `fieldFork_t`); the
  circuits' shapes are the program's (`circW`, `circL`) under the compiler trust
  (`shape_circAt`).
* **The size bounds** (`FitsOk`, decidable; `ForkFits.ofOk`): the arrays at most `Mx` elements, a
  GKR message and the tableau's writes within `2^20` bytes, the challenge reads at most `Lmax`
  (`ForkLoadNumbers` at the circuits' shapes); every domain's (`ForkNumbers`).
* **The transcript's facts** (`fieldForkTranscript_bounds`, `fieldForkTranscriptWith_bounds`)
  and the figures of the composite read through a map (`fieldIop_*`, `fieldIopWith_*`).
* **The rounds** (`forkRoundsAt`, `forkRoundsTotal`): every domain's branches and join from the
  circuits' shapes, and the composite's.
* **The leaves, the queries, the branches and the leaf bytes** of every domain.
-/

namespace GordieHowe.RealizedProgram.ProofSystem.IOP

open SPBCS.Configurations

variable {Stmt W : Type} {rel : Set (Stmt × W)}

/-- **The figures of a multi-circuit IOP with forked domains** a configuration on spBCS
states (`Configuration.Facts`): at most `rounds` rounds, trees of at
most `N` leaves, at most `nq` queried leaves, `kq` bounding the verifier's query count, `D` the
digests of one chain input with the final digests and the seeding's, and `pos` positions. -/
structure Figures (C : IOP Stmt W rel) (rounds N nq kq D pos : ℕ) : Prop where
  /-- The rounds. -/
  rounds_le : ∑ q : C.shape.term.Leaf, C.rounds q.label ≤ rounds
  /-- The leaves of every tree. -/
  leaves_le : ∀ d, (C.oracle d).nLeaves ≤ N
  /-- The queried leaves. -/
  queries_le : ∀ ch, (C.queryList ch).length ≤ nq
  /-- The verifier's query count. -/
  kq_ge : 2 * rounds + ∑ d, C.shape.nb d + nq * (1 + Nat.log 2 (2 * N)) ≤ kq
  /-- The digests of one chain input. -/
  digests_le : max 2 (SPBCS.ProofSystemTranscript.digests (C := C)) + C.merges.nJ + 1 ≤ D
  /-- The positions. -/
  pos_eq : ∑ d, (C.oracle d).nLeaves = pos

end GordieHowe.RealizedProgram.ProofSystem.IOP

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP GordieHowe.QROM GordieHowe.SPBCS SPBCS.Configurations
open scoped NNReal

/-! ## The compiled circuits -/

/-- **The compiled circuits of a configuration**: GKR sources of the program's circuits, related to
the program only by the trust bundle `enforce` (the circuits enforce their entries and have the
circuits' shapes, `CircuitsEnforce`) at the proof system `B` of the sources. -/
structure Compiled {ir : RealizedProgram} {I : Interp} {P : Export.Plan}
    (B : (∀ c : Fin ir.circuits.length, ir.CircuitSource I c) → ir.ProofSystem P I) : Type where
  /-- The GKR sources of the program's circuits. -/
  src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c
  /-- Trust base: the circuits enforce their entries and have the circuits' shapes. -/
  enforce : (B src).CircuitsEnforce

/-! ## The numbers of one domain -/

section Domain

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan}
  (src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c) (R : ir.FieldReady I d P)

/-- The tableau's leaves are the certificate's code length. -/
theorem fieldFork_N : (ir.fieldFork src R).join.N = R.cert.Sh.N := rfl

/-- The tableau's code dimension is the certificate's message block. -/
theorem fieldFork_k : (ir.fieldFork src R).join.code.k = R.cert.Sh.block := rfl

/-- The tableau's low-degree repetitions are the certificate's. -/
theorem fieldFork_nrep : (ir.fieldFork src R).join.cp.nrep = R.cert.Sh.nrep :=
  Ligero.MaskRow.TreeLayout.Numbers.nrep_setup ..

/-- The tableau's opened columns are the certificate's query count. -/
theorem fieldFork_t : (ir.fieldFork src R).join.cp.t = R.cert.Sh.nreq :=
  Ligero.MaskRow.TreeLayout.Numbers.t_setup ..

variable (ir) in
/-- **The width bound of circuit `i` of domain `d`** (`circuitWidth`). -/
abbrev circW (d : ℕ) (i : Fin (ir.circs d).length) : ℕ := ir.circuitWidth (ir.circAt d i)

variable (ir) in
/-- **The layers of circuit `i` of domain `d`.** -/
abbrev circL (d : ℕ) (i : Fin (ir.circs d).length) : ℕ := (ir.circuit (ir.circAt d i)).layers

variable {src} in
/-- **Circuit `i` of domain `d` has the program's shape** under the compiler trust
(`CircuitsEnforce.shape`). -/
theorem shape_circAt (T : ir.CircuitsEnforce I src) (i : Fin (ir.circs d).length) :
    (ir.circSource d src i).ShapeAtMost (ir.circW d i) (ir.circL d i) :=
  (shapeAtMost_circSource src i).2 (T.shape _)

variable (ir) in
/-- **The pads' bound of domain `d`'s circuits**: `layers · (4 · width + 3)`
(`ShapeAtMost.card_padIdx_le`). -/
abbrev padBound (d : ℕ) (i : Fin (ir.circs d).length) : ℕ := ir.circL d i * (4 * ir.circW d i + 3)

/-- **The size bounds of domain `d`'s forked proof, as numbers** (decidable): an array of `Mx`
elements fits, the arrays have at most `Mx` elements (`ForkSizesLe`), a GKR message fits, the
tableau's writes fit (`LigeroFits` at the certificate), the tableau has a low-degree repetition,
and the challenge reads have at most `Lmax` elements at the circuits' shapes (`ForkLoadNumbers`). -/
def FitsOk (fb Mx Lmax : ℕ) : Prop :=
  9 + Mx * fb ≤ 2 ^ 20 ∧ ForkSizesLe R Mx ∧ 2 * (1 + fb) ≤ 2 ^ 20 ∧
    (9 + R.cert.Sh.N * fb) + (9 + R.cert.Sh.N * fb) ≤ 2 ^ 20 ∧
    (9 + R.cert.Sh.block * fb) + ((9 + (2 * R.cert.Sh.block - 1) * fb) +
      (9 + (2 * R.cert.Sh.block - 1) * fb)) ≤ 2 ^ 20 ∧
    9 + R.cert.Sh.nrep * R.cert.Sh.block * fb ≤ 2 ^ 20 ∧ 0 < R.cert.Sh.nrep ∧
    ForkLoadNumbers R (ir.padBound d) (ir.circL d) Lmax

instance (fb Mx Lmax : ℕ) : Decidable (FitsOk R fb Mx Lmax) := by
  unfold FitsOk
  infer_instance

variable {src R} in
/-- **The size bounds of domain `d`'s forked proof from its numbers** (`FitsOk`), the circuits'
shapes under the compiler trust `T`. -/
def ForkFits.ofOk (T : ir.CircuitsEnforce I src)
    (cod : FieldCodec (I (ir.domainField d))) (Mx Lmax : ℕ) (h : FitsOk R cod.fb Mx Lmax)
    (grants : ForkGrants := {}) : ForkFits src R cod where
  Mx := Mx
  mx := h.1
  sizes := h.2.1
  gkr := h.2.2.1
  ligero := ⟨h.2.2.2.1, h.2.2.2.2.1, by rw [fieldFork_nrep, fieldFork_k]; exact h.2.2.2.2.2.1⟩
  Lmax := Lmax
  loads := forkLoadSizesLe_of src R (fun i => (shape_circAt T i).card_padIdx_le)
    (fun i => (shape_circAt T i).tail_depth) (fun i => (shape_circAt T i).outDim_le)
    h.2.2.2.2.2.2.2
  grants := grants

variable {src R} in
/-- **The reads other than the first combination's from their numbers** (`ForkRestNumbers` at the
circuits' shapes), under the compiler trust `T`. -/
theorem forkRestSizesLe_ofOk (T : ir.CircuitsEnforce I src) {Lmax : ℕ}
    (h : ForkRestNumbers R (ir.padBound d) (ir.circL d) Lmax) : ForkRestSizesLe src R Lmax :=
  forkRestSizesLe_of src R (fun i => (shape_circAt T i).card_padIdx_le)
    (fun i => (shape_circAt T i).tail_depth) (fun i => (shape_circAt T i).outDim_le) h

/-- **The rounds of domain `d`'s branches and join at the circuits' shapes**: `forkRoundsConst`
and `(2 + 4 · width) · layers + 1` per circuit. -/
noncomputable def forkRoundsAt : ℕ :=
  forkRoundsConst R + ∑ i, ((2 + 4 * ir.circW d i) * ir.circL d i + 1)

variable {src} in
/-- **The rounds of domain `d`'s branches and join** are at most `forkRoundsAt` under the compiler
trust (`fieldFork_rounds`). -/
theorem fieldFork_rounds_le_at (T : ir.CircuitsEnforce I src) :
    ∑ b, (ir.fieldForkShape src R).bn b + (ir.fieldForkShape src R).jn ≤ forkRoundsAt R := by
  exact (fieldFork_rounds src R).trans
    (Nat.add_le_add_left (Finset.sum_le_sum fun i _ => (shape_circAt T i).circuitLength_le) _)

/-- **The load bound of domain `d`** at the reader `rd` and `Lmax` reads: `forkLoad`, from the
certificate. -/
theorem forkLoad_eq (rd : CReader (I (ir.domainField d)).K) (Lmax : ℕ) :
    forkLoad src R rd Lmax =
      (rd.load.nsmul Lmax).max ⟨R.cert.Sh.nreq, Rejection.byteLen R.cert.Sh.N⟩ := by
  unfold forkLoad
  rw [fieldFork_t]
  rfl

/-! ### The round charges as numerators over the field's size -/

variable (ir) in
/-- **The numerator of a covered batch's phase error** (`cbError`): its rounds, `degree · (width −
1)`, `(degree + 1) · rounds` and `1`. -/
def batchNum (b : ℕ) : ℕ :=
  (ir.batch b).rounds + (ir.batch b).degree * ((ir.batch b).width - 1) +
    ((ir.batch b).degree + 1) * (ir.batch b).rounds + 1

variable (ir) in
/-- **The numerator of a covered merged batch's phase error** (`mbError`): its merging challenge's
`parts − 1` and `batchNum`. -/
def mergedNum (b : ℕ) : ℕ := ((ir.batch b).parts.length - 1) + ir.batchNum b

variable (ir) in
/-- **The numerator of domain `d`'s covered batches' phase errors** (`batchesError`). -/
def batchesNum (d : ℕ) (Pk : (I (ir.domainField d)).Packing) : ℕ :=
  ((ir.cbatches d Pk).map fun cb => ir.batchNum cb.idx).sum +
    ((ir.sumBatches d Pk).map fun sb => ir.batchNum sb.cb.idx + 2 * 4).sum +
    ((ir.mbatches d Pk).map fun cb => ir.mergedNum cb.idx).sum +
    ((ir.sumMBatches d Pk).map fun sb => ir.mergedNum sb.mb.idx + 2 * 4).sum

/-- A covered batch's phase error is `batchNum` over the field's size. -/
theorem cbError_eq {om : OperandMap} (cb : ir.CBatch I d om) :
    ir.cbError cb = (ir.batchNum cb.idx : ℝ≥0) / Fintype.card (I (ir.domainField d)).K := by
  unfold cbError batchNum
  push_cast
  simp only [add_div]

/-- A covered merged batch's phase error is `mergedNum` over the field's size. -/
theorem mbError_eq (cb : ir.MBatch I d) :
    ir.mbError cb = (ir.mergedNum cb.idx : ℝ≥0) / Fintype.card (I (ir.domainField d)).K := by
  unfold mbError mergedNum batchNum
  push_cast
  simp only [add_div]

/-- A covered batch on bits has phase error `batchNum + 8` over the field's
size. -/
theorem sbError_eq (sb : ir.SCBatch I d) :
    ir.sbError sb = ((ir.batchNum sb.cb.idx + 2 * 4 : ℕ) : ℝ≥0) /
      Fintype.card (I (ir.domainField d)).K := by
  unfold sbError
  rw [cbError_eq, Nat.cast_add, add_div]

/-- A covered merged batch on bits has phase error `mergedNum + 8` over the field's
size. -/
theorem smbError_eq (sb : ir.SMBatch I d) :
    ir.smbError sb = ((ir.mergedNum sb.mb.idx + 2 * 4 : ℕ) : ℝ≥0) /
      Fintype.card (I (ir.domainField d)).K := by
  unfold smbError
  rw [mbError_eq, Nat.cast_add, add_div]

/-- **Domain `d`'s covered batches' phase errors** are `batchesNum` over the field's size. -/
theorem batchesError_eq (Pk : (I (ir.domainField d)).Packing) :
    ir.batchesError d Pk = (ir.batchesNum d Pk : ℝ≥0) / Fintype.card (I (ir.domainField d)).K := by
  have key : ∀ {α : Type} (l : List α) (g : α → ℕ) (f : α → ℝ≥0),
      (∀ x, f x = (g x : ℝ≥0) / Fintype.card (I (ir.domainField d)).K) →
      (l.map f).sum = ((l.map g).sum : ℝ≥0) / Fintype.card (I (ir.domainField d)).K := by
    intro α l g f h
    induction l with
    | nil => simp
    | cons a l ih => simp [h, ih, add_div]
  unfold batchesError batchesNum
  rw [key _ _ _ cbError_eq, key _ _ _ sbError_eq, key _ _ _ mbError_eq, key _ _ _ smbError_eq]
  push_cast
  simp only [add_div]

/-- **The round charges of domain `d` from numerators**: on a field of `c` elements, every charge
other than the tableau's (commit, test, column, given) is a numerator over `c` (`batchesNum`,
`max 3 (2 · gkrWidth)` for a GKR round, the edges' one each) within `num / 2^e`. -/
theorem FieldRoundsLe.of_num {c num e : ℕ}
    (hK : Fintype.card (I (ir.domainField d)).K = c)
    (hcommit : R.numbers.bounds.commit ≤ (num : ℝ≥0) / 2 ^ e)
    (htest : R.numbers.bounds.test ≤ (num : ℝ≥0) / 2 ^ e)
    (hcolumn : R.numbers.bounds.column +
      (if npOf R.Pk R.rs = 0 then 0 else
        Ligero.SubfieldTest.jointSubfieldError R.numbers.Sh.block R.numbers.Sh.N R.numbers.Sh.nreq) ≤
      (num : ℝ≥0) / 2 ^ e)
    (hb : ir.batchesNum d R.Pk * 2 ^ e ≤ num * c)
    (hg : max 3 (2 * ir.gkrWidth d) * 2 ^ e ≤ num * c)
    (hr : R.rs.length * 2 ^ e ≤ num * c) :
    ir.FieldRoundsLe R ((num : ℝ≥0) / 2 ^ e) := by
  have hc : 0 < c := hK ▸ Fintype.card_pos
  refine ⟨hcommit, ?_, ?_, ?_, htest, hcolumn⟩
  · rw [batchesError_eq, hK]
    exact ratio_le_dyadic hc hb
  · unfold gkrRoundError
    rw [hK]
    exact ratio_le_dyadic hc hg
  · rw [hK]
    exact ratio_le_dyadic hc hr

end Domain

/-! ## The phases' errors as one fraction -/

/-- **A sum of fractions as one fraction**: `Σ nᵢ / dᵢ` as `(numerator, denominator)`, over the
product of the denominators. -/
def fracSum : List (ℕ × ℕ) → ℕ × ℕ
  | [] => (0, 1)
  | p :: L => (p.1 * (fracSum L).2 + (fracSum L).1 * p.2, p.2 * (fracSum L).2)

/-- **The sum of the fractions is `fracSum`'s**, every denominator positive. -/
theorem fracSum_eq : ∀ L : List (ℕ × ℕ), (∀ p ∈ L, 0 < p.2) →
    0 < (fracSum L).2 ∧ (L.map fun p => (p.1 : ℝ≥0) / p.2).sum = ((fracSum L).1 : ℝ≥0) / (fracSum L).2
  | [], _ => by simp [fracSum]
  | p :: L, h => by
    obtain ⟨hpos, hsum⟩ := fracSum_eq L fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hp := h p List.mem_cons_self
    refine ⟨Nat.mul_pos hp hpos, ?_⟩
    rw [List.map_cons, List.sum_cons, hsum, fracSum]
    have hp' : (p.2 : ℝ≥0) ≠ 0 := by exact_mod_cast hp.ne'
    have hq' : ((fracSum L).2 : ℝ≥0) ≠ 0 := by exact_mod_cast hpos.ne'
    push_cast
    rw [div_add_div _ _ hp' hq']
    congr 1
    ring

section PhaseErrors

variable {ir : RealizedProgram} {I : Interp}

/-- **`Π_P₀`'s round error at the challenge round of a source challenge `j`** is `ε₀ j`. -/
theorem chalError_roundError (ε₀ : ℕ → ℝ≥0) (j : ℕ) :
    ir.chalError I (ir.roundError I ε₀) j = if ir.IsSourceChal j then ε₀ j else 0 := by
  unfold chalError
  split_ifs with h
  · unfold roundError
    rw [show ir.rounds.get (chalIdx (I := I) h).1 = .chal j from ir.get_pos _]
  · rfl

variable (ir) in
/-- **The terms of phase `k + 1`'s error as fractions**: per challenge, the source error `src j`
of a source challenge and the realization's `Σ n / (c − tmax)` on `c = cf f` field elements. -/
def phaseTerms (cf : ℕ → ℕ) (src : ℕ → ℕ × ℕ) (k : Fin ir.phases) : List (ℕ × ℕ) :=
  (ir.chalList k).flatMap fun j =>
    (if ir.IsSourceChal j.1 then [src j.1] else []) ++
      [(((ir.realErrorTerms j.1).map Prod.fst).sum, cf (ir.chalField j.1) - ir.tmaxOf j.1)]

variable (ir) in
/-- **Every phase's error within `num / 2^e`, as numbers** (decidable): the terms' denominators are
positive and their sum (`fracSum`) is within the dyadic. -/
def PhaseErrorsOk (cf : ℕ → ℕ) (src : ℕ → ℕ × ℕ) (num e : ℕ) : Prop :=
  ∀ k, (∀ p ∈ ir.phaseTerms cf src k, 0 < p.2) ∧
    (fracSum (ir.phaseTerms cf src k)).1 * 2 ^ e ≤ num * (fracSum (ir.phaseTerms cf src k)).2

instance (cf : ℕ → ℕ) (src : ℕ → ℕ × ℕ) (num e : ℕ) : Decidable (ir.PhaseErrorsOk cf src num e) := by
  unfold PhaseErrorsOk
  infer_instance

/-- **Every phase's error is at most `num / 2^e`** (`phaseError`): field `f` has `cf f` elements, every source challenge's error `ε₀ j` is at most `src j` as a fraction, and the
phases' terms pass `PhaseErrorsOk`. -/
theorem phaseError_le_of (ε₀ : ℕ → ℝ≥0) {cf : ℕ → ℕ} {src : ℕ → ℕ × ℕ} {num e : ℕ}
    (hcard : ∀ f, Fintype.card (I f).K = cf f)
    (hsrc : ∀ j, ir.IsSourceChal j → ε₀ j ≤ ((src j).1 : ℝ≥0) / (src j).2)
    (h : ir.PhaseErrorsOk cf src num e) (k : Fin ir.phases) :
    ir.phaseError I (ir.roundError I ε₀) k ≤ (num : ℝ≥0) / 2 ^ e := by
  obtain ⟨hpos, hle⟩ := h k
  obtain ⟨hden, hsum⟩ := fracSum_eq _ hpos
  have hl : ir.phaseError I (ir.roundError I ε₀) k =
      ((ir.chalList k).map fun j : ir.ChalAt k =>
        ir.chalError I (ir.roundError I ε₀) j.1 + ir.realError I j.1).sum := by
    unfold phaseError
    rw [← List.sum_toFinset _ (chalList_nodup k)]
    congr 1
    exact (Finset.eq_univ_of_forall fun j => List.mem_toFinset.2 (mem_chalList k j)).symm
  rw [hl]
  refine le_trans ?_ (hsum.le.trans ?_)
  · have key : ∀ (L : List (ir.ChalAt k)) (g : ir.ChalAt k → List (ℕ × ℕ)),
        ((L.flatMap g).map fun p => (p.1 : ℝ≥0) / p.2).sum =
          (L.map fun x => ((g x).map fun p => (p.1 : ℝ≥0) / p.2).sum).sum := by
      intro L g
      induction L with
      | nil => rfl
      | cons x L ih => rw [List.flatMap_cons, List.map_append, List.sum_append, ih]; rfl
    unfold phaseTerms
    rw [key]
    refine List.sum_le_sum fun j _ => ?_
    rw [chalError_roundError, realError_eq, hcard]
    split_ifs with hj
    · simp only [List.singleton_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        add_zero]
      exact add_le_add (hsrc _ hj) le_rfl
    · simp
  · rw [div_le_div_iff₀ (by exact_mod_cast hden) (by positivity)]
    exact_mod_cast hle

end PhaseErrors

/-! ## The readers of the challenges' values -/

section Readers

/-- **The test of a sampler at a field reader `rd` on `c` field elements** (decidable): a sampler
is not of a node, and the lookup challenge of `[0, T)` leaves enough elements for `rd` repeated
until its value is outside the table values (`CReader.avoid`). -/
def samplerOk (rd : Load) (c : ℕ) : Sampler → Prop
  | .full => True
  | .node _ => False
  | .fieldMinusTables (.range T) => 2 * (rd.draws + 1) * 3 ^ rd.draws * T ≤ c
  | .fieldMinusTables (.packedRows _) => True
  | .fieldMinusTables (.union _ _) => True

instance (rd : Load) (c : ℕ) (s : Sampler) : Decidable (samplerOk rd c s) := by
  rcases s with _ | _ | (_ | _ | _) <;> unfold samplerOk <;> infer_instance

/-- **The reader of a sampler's values** at a reader `rd` of the field (`samplerOk` given): `rd`
itself for a whole element, packed rows or a union, and `rd` repeated until its value is outside the
values of `[0, T)` for the lookup challenge of `T` (`CReader.avoid`). -/
def samplerReader {F : FieldInterp} (rd : CReader F.K) :
    (s : Sampler) → samplerOk rd.load (Fintype.card F.K) s → CReader (F.SamplerTy s)
  | .full, _ => rd
  | .node _, h => h.elim
  | .fieldMinusTables (.range T), h => rd.avoid (Range.excluded F.K T)
      ((Nat.mul_le_mul_left _ (Range.card_excluded_le T)).trans h) (Configurations.excludedListing F.K T)
      ⟨T, Range.natCast_notMem_excluded T⟩
  | .fieldMinusTables (.packedRows _), _ => rd
  | .fieldMinusTables (.union _ _), _ => rd

/-- **The load of a sampler's reader**: `rd`'s, or for a lookup challenge two more draws of twice
the bytes (`CReader.avoid`). -/
def samplerLoad (rd : Load) : Sampler → Load
  | .fieldMinusTables (.range _) => ⟨rd.draws + 2, 2 * rd.bytes⟩
  | _ => rd

theorem samplerReader_load {F : FieldInterp} (rd : CReader F.K) (s : Sampler)
    (h : samplerOk rd.load (Fintype.card F.K) s) : (samplerReader rd s h).load = samplerLoad rd.load s := by
  rcases s with _ | _ | (_ | _ | _)
  · rfl
  · exact h.elim
  · rfl
  · rfl
  · rfl

variable {ir : RealizedProgram} {I : Interp}

variable (ir) in
/-- **The readers' test of a program** (decidable): every challenge's sampler passes `samplerOk` at
its field's reader `rd` on `cf` field elements. -/
def ReadersOk (rd : ℕ → Load) (cf : ℕ → ℕ) : Prop :=
  ∀ j : Fin ir.challenges.length, samplerOk (rd (ir.chalField j)) (cf (ir.chalField j))
    (ir.challenge j).sampler

instance (rd : ℕ → Load) (cf : ℕ → ℕ) : Decidable (ir.ReadersOk rd cf) := by
  unfold ReadersOk
  infer_instance

/-- **The readers of the challenges' values** at the fields' readers `rd` (`samplerReader`), on
fields of `cf f` elements passing `ReadersOk`. -/
def stdReaders (rd : ∀ f, CReader (I f).K) {cf : ℕ → ℕ} (hcard : ∀ f, Fintype.card (I f).K = cf f)
    (h : ir.ReadersOk (fun f => (rd f).load) cf) : SamplerReaders I ir := fun j =>
  samplerReader (rd (ir.chalField j)) (ir.challenge j).sampler ((hcard _).symm ▸ h j)

/-- **Every challenge's draws are within `L`** at the readers `stdReaders` when every challenge's
`samplerLoad` repeated `size` times is (decidable). -/
theorem chalLoad_stdReaders_le (rd : ∀ f, CReader (I f).K) {cf : ℕ → ℕ}
    (hcard : ∀ f, Fintype.card (I f).K = cf f) (h : ir.ReadersOk (fun f => (rd f).load) cf)
    {L : Load} (hL : ∀ j : Fin ir.challenges.length,
      ((samplerLoad (rd (ir.chalField j)).load (ir.challenge j).sampler).nsmul
        (ir.challenge j).size).draws ≤ L.draws ∧
      ((samplerLoad (rd (ir.chalField j)).load (ir.challenge j).sampler).nsmul
        (ir.challenge j).size).bytes ≤ L.bytes)
    (k : Fin ir.phases) (j : ir.ChalAt k) : ir.chalLoad (stdReaders rd hcard h) j.1 ≤ L := by
  unfold chalLoad stdReaders
  rw [samplerReader_load, Load.le_iff]
  exact hL j.1

end Readers

/-! ## The numbers of the domains -/

section Domains

variable {ir : RealizedProgram} {I : Interp} {P : Export.Plan}

variable (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)

/-- **The rounds of the composite at the circuits' shapes**: the commitment round, two commit
rounds per domain, two rounds per phase, and every domain's branches and join (`forkRoundsAt`). -/
noncomputable def forkRoundsTotal : ℕ :=
  1 + (2 * ir.domains.length + 2 * ir.phases) + ∑ d, forkRoundsAt (R d)

/-- **The numbers of the forked domains of a configuration**: every domain's field codec, its
largest array `Mx` and its largest challenge read `Lmax`, with their size bounds (`FitsOk`). -/
structure ForkNumbers where
  /-- The codec of domain `d`'s field. -/
  cod : ∀ d : Fin ir.domains.length, FieldCodec (I (ir.domainField d))
  /-- The largest array of domain `d`. -/
  Mx : Fin ir.domains.length → ℕ
  /-- The largest challenge read of domain `d`. -/
  Lmax : Fin ir.domains.length → ℕ
  /-- The size bounds. -/
  ok : ∀ d, FitsOk (R d) (cod d).fb (Mx d) (Lmax d)
  /-- The stream grants of domain `d`'s join (none by default). -/
  grants : Fin ir.domains.length → ForkGrants := fun _ => {}

variable {R} (Nm : ForkNumbers R)

/-- **The size bounds of every domain** (`ForkFits.ofOk`) under the compiler trust `T`. -/
def ForkNumbers.fits {src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c}
    (T : ir.CircuitsEnforce I src) (d : Fin ir.domains.length) : ForkFits src (R d) (Nm.cod d) :=
  ForkFits.ofOk T (Nm.cod d) (Nm.Mx d) (Nm.Lmax d) (Nm.ok d) (Nm.grants d)

/-- **The load bound of domain `d` at the numbers' reads** (`forkLoad`), a closed term. -/
theorem ForkNumbers.forkLoad_fits {src : ∀ c : Fin ir.circuits.length, ir.CircuitSource I c}
    (T : ir.CircuitsEnforce I src) (d : Fin ir.domains.length) :
    forkLoad src (R d) (Nm.cod d).rd (Nm.fits T d).Lmax =
      ((Nm.cod d).rd.load.nsmul (Nm.Lmax d)).max
        ⟨(R d).cert.Sh.nreq, Rejection.byteLen (R d).cert.Sh.N⟩ :=
  forkLoad_eq _ _ _ _

/-- **The bytes of a serialized column of domain `d`**: `nrep + Lmax` field elements and two mask
entries. -/
def ForkNumbers.leafBytes (d : Fin ir.domains.length) : ℕ :=
  (9 + ((R d).cert.Sh.nrep + Nm.Lmax d) * (Nm.cod d).fb) + ((1 + (Nm.cod d).fb) + (1 + (Nm.cod d).fb))

/-- **The bounds of a transcript's figures** (decidable): at most `2^8` domains of at most `2^8`
branches, columns of at most `2^40` bytes and at most `maxRounds` rounds. -/
def ForkNumbers.BoundsOk : Prop :=
  ir.domains.length ≤ 2 ^ 8 ∧ (∀ d : Fin ir.domains.length, ir.nBranch d (R d).Pk ≤ 2 ^ 8) ∧
    (∀ d, Nm.leafBytes d ≤ 2 ^ 40) ∧ forkRoundsTotal R ≤ maxRounds

noncomputable instance : Decidable Nm.BoundsOk := by
  unfold ForkNumbers.BoundsOk
  infer_instance

variable (R) in
/-- **The figures of the composite as numbers** (decidable, `ProofSystem.IOP.Figures`). -/
def FiguresOk (rounds N nq kq D pos : ℕ) : Prop :=
  forkRoundsTotal R ≤ rounds ∧ (∀ d : Fin ir.domains.length, (R d).cert.Sh.N ≤ N) ∧
    ∑ d, (R d).cert.Sh.nreq ≤ nq ∧
    2 * rounds + ∑ d : Fin ir.domains.length, ir.nBranch d (R d).Pk +
      nq * (1 + Nat.log 2 (2 * N)) ≤ kq ∧
    max 2 (forkRoundsTotal R * ir.domains.length) +
      (Finset.univ.sup fun d : Fin ir.domains.length => ir.nBranch d (R d).Pk) + 1 ≤ D ∧
    ∑ d, (R d).cert.Sh.N = pos

noncomputable instance (rounds N nq kq D pos : ℕ) :
    Decidable (FiguresOk R rounds N nq kq D pos) := by
  unfold FiguresOk
  infer_instance

end Domains

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp} (B : ir.ProofSystem P I)
  {R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P} {W : Type}
  {rel : Set (ir.Valuation I × W)}
  (Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
    (GordieHowe.Domain.lowered (B.withFieldProofs R).guardedDomain))

/-- **The composite on the generic per-field domain proofs** before its statement is read
(`FieldBranches.iopOf`). -/
abbrev fieldIopBase := (B.fieldBranches R).iopOf Lw

variable (R) in
/-- **The rounds of the composite** are at most `forkRoundsTotal` under the compiler trust
(`IOP.sum_rounds`, `fieldFork_rounds_le_at`). -/
theorem fieldIopBase_rounds_le (T : B.CircuitsEnforce) :
    ∑ q : (B.fieldIopBase (R := R) Lw).shape.term.Leaf, (B.fieldIopBase Lw).rounds q.label ≤
      forkRoundsTotal R := by
  rw [IOP.sum_rounds]
  have hnc : ∀ d, ((B.fieldIopBase (R := R) Lw).circuit d).nc = 2 := fun d => forkJoin_nc B.src (R d)
  have happ : (B.fieldIopBase (R := R) Lw).app.n = 2 * ir.phases := rfl
  have h1 : ∑ d, ((B.fieldIopBase (R := R) Lw).circuit d).nc + (B.fieldIopBase (R := R) Lw).app.n =
      2 * ir.domains.length + 2 * ir.phases := by
    rw [Finset.sum_congr rfl fun d _ => hnc d, happ, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul, mul_comm]
    rfl
  have h2 : ∑ d, (∑ b, ((B.fieldIopBase (R := R) Lw).circuit d).bn b +
      ((B.fieldIopBase (R := R) Lw).circuit d).jn) ≤ ∑ d, forkRoundsAt (R d) :=
    Finset.sum_le_sum fun d _ => fieldFork_rounds_le_at (R d) T
  exact Nat.add_le_add (Nat.add_le_add_left h1.le 1) h2

variable {Stmt : Type} (f : Stmt → ir.Valuation I)

/-! ### The figures of the composite read through a map

The same facts for `fieldIop` (the statement read through `f`) and `fieldIopWith` (also checked
by `chk`): both keep the domains, their oracles and the application phase's rounds. -/

/-- **Domain `d`'s tree has the certificate's `N` leaves.** -/
theorem fieldIop_nLeaves (d : Fin ir.domains.length) :
    ((B.fieldIop R Lw f).oracle d).nLeaves = (R d).cert.Sh.N :=
  forkJoin_nLeaves B.src (R d)

/-- **Domain `d`'s verdict reads the certificate's `nreq` columns.** -/
theorem fieldIop_queries (d : Fin ir.domains.length)
    (ch : ((B.fieldIop R Lw f).circuit d).join.Challenges) :
    (((B.fieldIop R Lw f).oracle d).queries ch).card = (R d).cert.Sh.nreq :=
  (forkJoin_card_queries B.src (R d) ch.right).trans (fieldFork_t B.src (R d))

/-- **The queried leaves are at most the domains' opened columns.** -/
theorem fieldIop_queryList_le (ch) :
    ((B.fieldIop R Lw f).queryList ch).length ≤ ∑ d, (R d).cert.Sh.nreq :=
  (B.fieldIop R Lw f).length_queryList_le (fun d ch => (B.fieldIop_queries Lw f d ch).le) ch

/-- **The positions are the domains' columns.** -/
theorem fieldIop_pos : ∑ d, ((B.fieldIop R Lw f).oracle d).nLeaves = ∑ d, (R d).cert.Sh.N :=
  Finset.sum_congr rfl fun d _ => B.fieldIop_nLeaves Lw f d

/-- **The verifier's query count** (as `Configuration.GrantedFacts.kq_ge` states it), from the
domains' branches (`nBranch`). -/
theorem fieldIop_kq_ge {r nq N kq : ℕ}
    (h : 2 * r + ∑ d : Fin ir.domains.length, ir.nBranch d (R d).Pk +
      nq * (1 + Nat.log 2 (2 * N)) ≤ kq) :
    2 * r + ∑ d, (B.fieldIop R Lw f).shape.nb d + nq * (1 + Nat.log 2 (2 * N)) ≤ kq :=
  h

/-- **Domain `d`'s tree has the certificate's `N` leaves** (with a statement check). -/
theorem fieldIopWith_nLeaves (chk : Stmt → Bool) (d : Fin ir.domains.length) :
    ((B.fieldIopWith R Lw f chk).oracle d).nLeaves = (R d).cert.Sh.N :=
  forkJoin_nLeaves B.src (R d)

/-- **Domain `d`'s verdict reads the certificate's `nreq` columns** (with a statement check). -/
theorem fieldIopWith_queries (chk : Stmt → Bool) (d : Fin ir.domains.length)
    (ch : ((B.fieldIopWith R Lw f chk).circuit d).join.Challenges) :
    (((B.fieldIopWith R Lw f chk).oracle d).queries ch).card = (R d).cert.Sh.nreq :=
  (forkJoin_card_queries B.src (R d) ch.right).trans (fieldFork_t B.src (R d))

/-- **The queried leaves are at most the domains' opened columns** (with a statement check). -/
theorem fieldIopWith_queryList_le (chk : Stmt → Bool) (ch) :
    ((B.fieldIopWith R Lw f chk).queryList ch).length ≤ ∑ d, (R d).cert.Sh.nreq :=
  (B.fieldIopWith R Lw f chk).length_queryList_le
    (fun d ch => (B.fieldIopWith_queries Lw f chk d ch).le) ch

/-- **The positions are the domains' columns** (with a statement check). -/
theorem fieldIopWith_pos (chk : Stmt → Bool) :
    ∑ d, ((B.fieldIopWith R Lw f chk).oracle d).nLeaves = ∑ d, (R d).cert.Sh.N :=
  Finset.sum_congr rfl fun d _ => B.fieldIopWith_nLeaves Lw f chk d

/-- **The verifier's query count** (with a statement check). -/
theorem fieldIopWith_kq_ge (chk : Stmt → Bool) {r nq N kq : ℕ}
    (h : 2 * r + ∑ d : Fin ir.domains.length, ir.nBranch d (R d).Pk +
      nq * (1 + Nat.log 2 (2 * N)) ≤ kq) :
    2 * r + ∑ d, (B.fieldIopWith R Lw f chk).shape.nb d + nq * (1 + Nat.log 2 (2 * N)) ≤ kq :=
  h

/-- **The rounds of the composite read through `f`** are the composite's (`IOP.sum_rounds`). -/
theorem fieldIop_rounds_le (T : B.CircuitsEnforce) :
    ∑ q : (B.fieldIop R Lw f).shape.term.Leaf, (B.fieldIop R Lw f).rounds q.label ≤
      forkRoundsTotal R := by
  have h := B.fieldIopBase_rounds_le R Lw T
  rw [IOP.sum_rounds] at h ⊢
  exact h

/-- **The rounds of the composite read through `f` and checked** are the composite's. -/
theorem fieldIopWith_rounds_le (T : B.CircuitsEnforce) (chk : Stmt → Bool) :
    ∑ q : (B.fieldIopWith R Lw f chk).shape.term.Leaf, (B.fieldIopWith R Lw f chk).rounds q.label ≤
      forkRoundsTotal R := by
  have h := B.fieldIopBase_rounds_le R Lw T
  rw [IOP.sum_rounds] at h ⊢
  exact h

/-- **The digests of one chain input, the final digests and the seeding's** (as
`Configuration.GrantedFacts.digests_le` states it), from the rounds' bound (`fieldIop_rounds_le`). -/
theorem fieldIop_digests_le (T : B.CircuitsEnforce) {D : ℕ}
    (h : max 2 (forkRoundsTotal R * ir.domains.length) +
      (Finset.univ.sup fun d : Fin ir.domains.length => ir.nBranch d (R d).Pk) + 1 ≤ D) :
    max 2 (ProofSystemTranscript.digests (C := B.fieldIop R Lw f)) +
      (B.fieldIop R Lw f).merges.nJ + 1 ≤ D := by
  rw [IOP.nJ_merges]
  refine le_trans ?_ h
  unfold ProofSystemTranscript.digests
  have hr := Nat.mul_le_mul_right ir.domains.length (B.fieldIop_rounds_le Lw f T)
  have hnb : (Finset.univ.sup (B.fieldIop R Lw f).shape.nb) =
      Finset.univ.sup fun d : Fin ir.domains.length => ir.nBranch d (R d).Pk := rfl
  rw [hnb]
  change max 2 (_ * ir.domains.length) + _ + 1 ≤ _
  omega

/-- **The digests of one chain input** (with a statement check; as `fieldIop_digests_le`). -/
theorem fieldIopWith_digests_le (T : B.CircuitsEnforce) (chk : Stmt → Bool) {D : ℕ}
    (h : max 2 (forkRoundsTotal R * ir.domains.length) +
      (Finset.univ.sup fun d : Fin ir.domains.length => ir.nBranch d (R d).Pk) + 1 ≤ D) :
    max 2 (ProofSystemTranscript.digests (C := B.fieldIopWith R Lw f chk)) +
      (B.fieldIopWith R Lw f chk).merges.nJ + 1 ≤ D := by
  rw [IOP.nJ_merges]
  refine le_trans ?_ h
  unfold ProofSystemTranscript.digests
  have hr := Nat.mul_le_mul_right ir.domains.length (B.fieldIopWith_rounds_le Lw f T chk)
  have hnb : (Finset.univ.sup (B.fieldIopWith R Lw f chk).shape.nb) =
      Finset.univ.sup fun d : Fin ir.domains.length => ir.nBranch d (R d).Pk := rfl
  rw [hnb]
  change max 2 (_ * ir.domains.length) + _ + 1 ≤ _
  omega

/-- **The bytes of a serialized column of domain `d`** are at most `leafBytes`
(`length_ser_forkLeafCodec_le`, the data rows within `Lmax`). -/
theorem forkLeaf_le_leafBytes (Nm : ForkNumbers R) (T : B.CircuitsEnforce)
    (d : Fin ir.domains.length) (c : (ir.fieldForkOracle B.src (R d)).Leaf) :
    ((forkLeafCodec B.src (R d) (Nm.cod d).FB).ser c).length ≤ Nm.leafBytes d := by
  refine (length_ser_forkLeafCodec_le B.src (R d) (Nm.cod d).FB c).trans ?_
  have hR := (Nm.fits T d).loads.R_le
    ((fieldFork_nrep B.src (R d)).symm ▸ (Nm.ok d).2.2.2.2.2.2.1)
  unfold ForkNumbers.leafBytes
  rw [fieldFork_nrep]
  have := Nat.mul_le_mul_right (Nm.cod d).fb (Nat.add_le_add_left hR (R d).cert.Sh.nrep)
  exact Nat.add_le_add_right (Nat.add_le_add_left this 9) _

/-- **The facts the setting is built from**, for the transcript on the generic per-field domain
proofs at the numbers `Nm` (`fieldForkTranscript`): the statement's writes, the label, the digest
length and the branch names given, the rest from `Nm.BoundsOk`. -/
theorem fieldForkTranscript_bounds (Nm : ForkNumbers R) (T : B.CircuitsEnforce)
    {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIop R Lw f).app.spec}
    (hpre : ∀ x, (stmt.ser x).length ≤ 2 ^ 20) (hlabel : label.length ≤ 2 ^ 10)
    (hk : k ≤ 2 ^ 10) (hk0 : 0 < k) (hname : ∀ a, (name a).length ≤ 2 ^ 10)
    (hok : Nm.BoundsOk) :
    (B.fieldForkTranscript R Lw f Nm.cod (Nm.fits T) label k stmt name appWrites
      appReaders).Bounds where
  pre_le := hpre
  label_le := hlabel
  k_le := hk
  k_pos := hk0
  leaf_le d c := (B.forkLeaf_le_leafBytes Nm T d c).trans (hok.2.2.1 d)
  m_le := hok.1
  nb_le d := hok.2.1 d
  name_le := hname
  n_le := (B.fieldIop_rounds_le Lw f T).trans hok.2.2.2

/-- **The facts the setting is built from**, for the transcript of the composite read through `f`
and checked by `chk` (as `fieldForkTranscript_bounds`). -/
theorem fieldForkTranscriptWith_bounds (Nm : ForkNumbers R) (T : B.CircuitsEnforce)
    (chk : Stmt → Bool) {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m, Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) →
      List Byte}
    {appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20)}
    {appReaders : SpecReaders (B.fieldIopWith R Lw f chk).app.spec}
    (hpre : ∀ x, (stmt.ser x).length ≤ 2 ^ 20) (hlabel : label.length ≤ 2 ^ 10)
    (hk : k ≤ 2 ^ 10) (hk0 : 0 < k) (hname : ∀ a, (name a).length ≤ 2 ^ 10)
    (hok : Nm.BoundsOk) :
    (B.fieldForkTranscriptWith R Lw f Nm.cod (Nm.fits T) chk label k stmt name appWrites
      appReaders).Bounds where
  pre_le := hpre
  label_le := hlabel
  k_le := hk
  k_pos := hk0
  leaf_le d c := (B.forkLeaf_le_leafBytes Nm T d c).trans (hok.2.2.1 d)
  m_le := hok.1
  nb_le d := hok.2.1 d
  name_le := hname
  n_le := (B.fieldIopWith_rounds_le Lw f T chk).trans hok.2.2.2

/-- **The figures of the composite read through `f`** from their numbers (`FiguresOk`) under the
compiler trust. -/
theorem fieldIop_figures (T : B.CircuitsEnforce) {rounds N nq kq D pos : ℕ}
    (h : FiguresOk R rounds N nq kq D pos) : (B.fieldIop R Lw f).Figures rounds N nq kq D pos where
  rounds_le := (B.fieldIop_rounds_le Lw f T).trans h.1
  leaves_le d := (B.fieldIop_nLeaves Lw f d).trans_le (h.2.1 d)
  queries_le ch := (B.fieldIop_queryList_le Lw f ch).trans h.2.2.1
  kq_ge := B.fieldIop_kq_ge Lw f h.2.2.2.1
  digests_le := B.fieldIop_digests_le Lw f T h.2.2.2.2.1
  pos_eq := (B.fieldIop_pos Lw f).trans h.2.2.2.2.2

/-- **The figures of the composite read through `f` and checked** (as `fieldIop_figures`). -/
theorem fieldIopWith_figures (T : B.CircuitsEnforce) (chk : Stmt → Bool)
    {rounds N nq kq D pos : ℕ} (h : FiguresOk R rounds N nq kq D pos) :
    (B.fieldIopWith R Lw f chk).Figures rounds N nq kq D pos where
  rounds_le := (B.fieldIopWith_rounds_le Lw f T chk).trans h.1
  leaves_le d := (B.fieldIopWith_nLeaves Lw f chk d).trans_le (h.2.1 d)
  queries_le ch := (B.fieldIopWith_queryList_le Lw f chk ch).trans h.2.2.1
  kq_ge := B.fieldIopWith_kq_ge Lw f chk h.2.2.2.1
  digests_le := B.fieldIopWith_digests_le Lw f T chk h.2.2.2.2.1
  pos_eq := (B.fieldIopWith_pos Lw f chk).trans h.2.2.2.2.2

/-! ### The honest prover of the composite read through a map -/

variable {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-- **The simulator data of the composite read through `f`**: the forked domains' simulators
(`fieldForkSims`) and the phased application phase's simulator at `Lw`
(`FieldBranches.simDataAt`), read through `f` (`IOP.SimData.comap`). -/
def fieldIopSimData : (B.fieldIop R Lw f).SimData :=
  ((B.fieldBranches R).simDataAt Lw (B.fieldForkSims R)).comap f

/-- **The simulator data of the composite read through `f` and checked by `chk`**
(`IOP.SimData.comapWith`). -/
def fieldIopWithSimData (chk : Stmt → Bool) : (B.fieldIopWith R Lw f chk).SimData :=
  ((B.fieldBranches R).simDataAt Lw (B.fieldForkSims R)).comapWith f chk

/-- **The honest prover of the composite read through `f`** at the strategy `H`: the honest prover at
`Lw` (`FieldBranches.honestAt`) on every domain's generic honest provers (`fieldHonestDomains`,
`fieldForkHonestDomains`), read through `f` (`IOP.Honest.comap`). `TA`: the compiler's
completeness (trust base). -/
noncomputable def fieldIopHonest (TA : (B.withFieldProofs R).CircuitsAccept)
    (H : ir.HonestCore I relH) :
    (B.fieldIop R Lw f).Honest (B.fieldIopSimData Lw f) Inp {p | (f p.1, p.2) ∈ relH} :=
  ((B.fieldBranches R).honestAt Lw TA (B.fieldHonestDomains R) (B.fieldForkHonestDomains R TA) H).comap f

/-- **The honest prover of the composite read through `f` and checked by `chk`** (as
`fieldIopHonest`, `IOP.Honest.comapWith`). -/
noncomputable def fieldIopWithHonest (chk : Stmt → Bool) (TA : (B.withFieldProofs R).CircuitsAccept)
    (H : ir.HonestCore I relH) :
    (B.fieldIopWith R Lw f chk).Honest (B.fieldIopWithSimData Lw f chk) Inp
      {p | chk p.1 = true ∧ (f p.1, p.2) ∈ relH} :=
  ((B.fieldBranches R).honestAt Lw TA (B.fieldHonestDomains R) (B.fieldForkHonestDomains R TA)
    H).comapWith f chk

end ProofSystem

end GordieHowe.RealizedProgram
