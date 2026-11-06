-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkFigures
public import GordieHoweNative.ProofSystem.Program.Figures

@[expose] public section

/-!
# GordieHowe: the figures of a program, as functions of its ready data, and their check

A configuration on spBCS states its figures (rounds, leaves, queries, verifier queries, digests,
positions, the digest length, the largest round error and the Chernoff exponent of the loads) as
numerals. Each figure is a function of the program's ready data (`GordieHowe.RealizedProgram.FieldReady`:
the plan's Ligero numbers, the program's circuits and batches and the fields' packing facts),
stated once here; one decidable check per program (`GordieHowe.RealizedProgram.ProgramFigures.Check`),
the part `figuresPartB` of the program's check, ties the numerals to the functions, and its
consequences are the facts a configuration reads (the program's generated `Certified`).

* **Ligero's error terms** (`FieldRoundsOk`, `FieldRoundsLe.of_ok`): every round charge of a
  domain as a fraction of naturals within `num / 2^e`, the commit, test and column bounds those of
  the domain's certificate (`FieldInterp.Packing.numbers_bounds`).
* **The Chernoff test as numbers** (`ChernoffOk`, `ChernoffOk.passes`).
* **The figures** (`figRounds`, `figLeaves`, `figQueries`, `figKq`, `figDigests`, `figPos`).
* **The check** (`ProgramFigures.Check`) and its consequences: the composite's figures
  (`Check.figures`, `Check.figuresWith`), the domains' round charges (`Check.fieldRoundsLe`), the
  phases' errors (`Check.phaseError_le`), the transcript's facts (`Check.transcript_bounds`,
  `Check.transcriptWith_bounds`) and its loads at their grants (`Check.loadsGranted`,
  `Check.loadsGrantedWith`), or on the default stream when nothing is granted (`DefaultLoadsOk`,
  `Check.loads`, `Check.loadsWith`).
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP GordieHowe.QROM GordieHowe.SPBCS SPBCS.Configurations
open scoped NNReal

/-! ## The fields' sizes -/

/-- **The size of field `f` by its specification**: `characteristic ^ degree`, the Lean field's
size under the interpretation's model (`FieldInterp.Model.card`). -/
def Interp.specCard (I : Interp) (f : ℕ) : ℕ :=
  (I f).spec.characteristic ^ (I f).spec.degree

/-! ## The round charges of one domain as fractions -/

section Domain

variable {ir : RealizedProgram} {I : Interp} {d : ℕ} {P : Export.Plan} (R : ir.FieldReady I d P)

/-- **Every round charge of domain `d` within `num / 2^e`, as numbers**, on a field of `q`
elements: the certificate's commit fraction `B^nrep / (q − 1)^nrep`, test fraction `testNum / q`,
column fraction with the joint subfield term when the prefix is nonempty, and the batches', GKR's
and the combinations' numerators over `q`. -/
structure FieldRoundsOk (q num e : ℕ) : Prop where
  /-- The commit round. -/
  commit : R.cert.exceptions ^ R.cert.Sh.nrep * 2 ^ e ≤ num * (q - 1) ^ R.cert.Sh.nrep
  /-- The field is nonempty. -/
  q_pos : 0 < q
  /-- Ligero's constraint challenge. -/
  test : R.cert.testNum * 2 ^ e ≤ num * q
  /-- The column denominator is positive. -/
  den_pos : 0 < R.cert.columnDen
  /-- Ligero's column query with the joint subfield term. -/
  column : (R.cert.columnNum + if npOf R.Pk R.rs = 0 then 0 else R.cert.jointNum) * 2 ^ e ≤
    num * R.cert.columnDen
  /-- The covered batches' phase errors together. -/
  batches : ir.batchesNum d R.Pk * 2 ^ e ≤ num * q
  /-- A GKR round. -/
  gkr : max 3 (2 * ir.gkrWidth d) * 2 ^ e ≤ num * q
  /-- The combinations. -/
  combinations : R.rs.length * 2 ^ e ≤ num * q

/-- `FieldRoundsOk` as one conjunction, for its decision. -/
theorem fieldRoundsOk_iff (q num e : ℕ) :
    FieldRoundsOk R q num e ↔
      R.cert.exceptions ^ R.cert.Sh.nrep * 2 ^ e ≤ num * (q - 1) ^ R.cert.Sh.nrep ∧ 0 < q ∧
        R.cert.testNum * 2 ^ e ≤ num * q ∧ 0 < R.cert.columnDen ∧
        (R.cert.columnNum + if npOf R.Pk R.rs = 0 then 0 else R.cert.jointNum) * 2 ^ e ≤
          num * R.cert.columnDen ∧
        ir.batchesNum d R.Pk * 2 ^ e ≤ num * q ∧ max 3 (2 * ir.gkrWidth d) * 2 ^ e ≤ num * q ∧
        R.rs.length * 2 ^ e ≤ num * q :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ => ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩⟩

instance FieldRoundsOk.decidable (q num e : ℕ) : Decidable (FieldRoundsOk R q num e) :=
  decidable_of_iff _ (fieldRoundsOk_iff R q num e).symm

variable {R} in
/-- **The round charges of domain `d` from their fractions**: on a field of `q` elements, the
checks `FieldRoundsOk` give every charge within `num / 2^e` (`FieldRoundsLe.of_num`, the tableau's
bounds those of its certificate, `FieldInterp.Packing.numbers_bounds`). -/
theorem FieldRoundsLe.of_ok {q num e : ℕ} (hK : Fintype.card (I (ir.domainField d)).K = q)
    (h : FieldRoundsOk R q num e) : ir.FieldRoundsLe R ((num : ℝ≥0) / 2 ^ e) := by
  have hb := R.Pk.numbers_bounds R.cert R.valid
  refine FieldRoundsLe.of_num R hK ?_ ?_ ?_ h.batches h.gkr h.combinations
  · rw [hb, hK]
    exact ratio_pred_pow_le_dyadic h.commit
  · rw [hb, hK]
    exact ratio_le_dyadic h.q_pos h.test
  · have hc := h.column
    rw [hb]
    change (R.cert.columnNum : ℝ≥0) / R.cert.columnDen +
      (if npOf R.Pk R.rs = 0 then 0 else
        (R.cert.jointNum : ℝ≥0) / R.cert.columnDen) ≤ _
    split_ifs with hnp
    · simp only [hnp, ↓reduceIte, add_zero] at hc
      rw [add_zero]
      exact ratio_le_dyadic h.den_pos hc
    · simp only [hnp, ↓reduceIte] at hc
      rw [← add_div]
      exact_mod_cast ratio_le_dyadic h.den_pos hc

end Domain

/-! ## The Chernoff test as numbers -/

/-- **The Chernoff test `2^-E` of a load `⟨D, b⟩` on `N`-byte streams, as numbers** (the
hypotheses of `passesChernoff_of_nat_at`). -/
def ChernoffOk (E N : ℕ) (L : Load) : Prop :=
  65 ^ L.bytes < 2 * 64 ^ L.bytes ∧
    65 ^ (L.bytes * L.draws) * 64 ^ (N + 1) * 2 ^ (E + 1) ≤
      (2 * 64 ^ L.bytes - 65 ^ L.bytes) ^ L.draws * 65 ^ (N + 1) ∧
    L.draws * 2 ^ (E + 1) ≤ 2 ^ N

instance (E N : ℕ) (L : Load) : Decidable (ChernoffOk E N L) := by
  unfold ChernoffOk
  infer_instance

/-- **A load passing the numeric Chernoff test passes it** (`passesChernoff_of_nat_at`). -/
theorem ChernoffOk.passes {E N : ℕ} {L : Load} (h : ChernoffOk E N L) :
    PassesChernoff (65 / 64) ((1 / 2) ^ E) N L :=
  passesChernoff_of_nat_at E (b := L.bytes) (D := L.draws) h.1 h.2.1 h.2.2

/-! ## The largest load of the challenges' readers -/

section ChalLoad

variable {ir : RealizedProgram} {I : Interp}

variable (ir) in
/-- **The largest load of the challenges' readers** at the fields' reader loads `rdl`: the largest
draws and the largest bytes of every challenge's sampler load (`samplerLoad`) repeated `size`
times. -/
def stdChalLoad (rdl : ℕ → Load) : Load :=
  ⟨Finset.univ.sup fun j : Fin ir.challenges.length =>
      ((samplerLoad (rdl (ir.chalField j)) (ir.challenge j).sampler).nsmul (ir.challenge j).size).draws,
    Finset.univ.sup fun j : Fin ir.challenges.length =>
      ((samplerLoad (rdl (ir.chalField j)) (ir.challenge j).sampler).nsmul (ir.challenge j).size).bytes⟩

/-- **Every challenge's draws are within `stdChalLoad`** at the readers `stdReaders`
(`chalLoad_stdReaders_le`). -/
theorem chalLoad_stdReaders_le_std (rd : ∀ f, CReader (I f).K) {cf : ℕ → ℕ}
    (hcard : ∀ f, Fintype.card (I f).K = cf f) (h : ir.ReadersOk (fun f => (rd f).load) cf)
    (k : Fin ir.phases) (j : ir.ChalAt k) :
    ir.chalLoad (stdReaders rd hcard h) j.1 ≤ ir.stdChalLoad fun f => (rd f).load :=
  chalLoad_stdReaders_le rd hcard h (fun j =>
    ⟨Finset.le_sup (f := fun j : Fin ir.challenges.length =>
        ((samplerLoad (rd (ir.chalField j)).load (ir.challenge j).sampler).nsmul
          (ir.challenge j).size).draws) (Finset.mem_univ j),
      Finset.le_sup (f := fun j : Fin ir.challenges.length =>
        ((samplerLoad (rd (ir.chalField j)).load (ir.challenge j).sampler).nsmul
          (ir.challenge j).size).bytes) (Finset.mem_univ j)⟩) k j

end ChalLoad

/-! ## The figures of the composite -/

section Figures

variable {ir : RealizedProgram} {I : Interp} {P : Export.Plan}
  (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)

/-- **The rounds of the composite** (`forkRoundsTotal`): the commitment round, two commit rounds
per domain, two rounds per phase, and every domain's branches and join at the circuits' shapes. -/
noncomputable def figRounds : ℕ := forkRoundsTotal R

/-- **The leaves of the largest tree**: the largest code length `N` of the domains' tableaus. -/
def figLeaves : ℕ := Finset.univ.sup fun d : Fin ir.domains.length => (R d).cert.Sh.N

/-- **The queried leaves**: the domains' opened columns. -/
def figQueries : ℕ := ∑ d, (R d).cert.Sh.nreq

/-- **The verifier's queries on accepting runs**: two per round, one per branch and
`1 + log₂ (2N)` per queried leaf (`Configuration.GrantedFacts.kq_ge`). -/
noncomputable def figKq : ℕ :=
  2 * figRounds R + ∑ d : Fin ir.domains.length, ir.nBranch d (R d).Pk +
    figQueries R * (1 + Nat.log 2 (2 * figLeaves R))

/-- **The digests of one chain input, the final digests and the seeding's**
(`Configuration.GrantedFacts.digests_le`). -/
noncomputable def figDigests : ℕ :=
  max 2 (figRounds R * ir.domains.length) +
    (Finset.univ.sup fun d : Fin ir.domains.length => ir.nBranch d (R d).Pk) + 1

/-- **The positions**: the leaves of all trees. -/
def figPos : ℕ := ∑ d, (R d).cert.Sh.N

/-- **The figures at their functions satisfy `FiguresOk`.** -/
theorem figuresOk_fig :
    FiguresOk R (figRounds R) (figLeaves R) (figQueries R) (figKq R) (figDigests R) (figPos R) :=
  ⟨le_rfl, fun d => Finset.le_sup (f := fun d : Fin ir.domains.length => (R d).cert.Sh.N)
    (Finset.mem_univ d), le_rfl, le_rfl, le_rfl, rfl⟩

end Figures

/-! ## The largest round error -/

section ErrorMax

variable {ir : RealizedProgram} {I : Interp} {P : Export.Plan}

/-- **A fraction `a / b` in units of `2^-e`, rounded up**: `⌈a · 2^e / b⌉`. -/
def dyadicCeil (e : ℕ) (p : ℕ × ℕ) : ℕ := (p.1 * 2 ^ e + p.2 - 1) / p.2

variable {d : ℕ} in
/-- **The round charges of domain `d` as fractions** on a field of `q` elements, in the order of
`FieldRoundsOk`: the commit, test and column rounds, the covered batches, a GKR round and the
combinations. -/
def FieldReady.chargeFracs (R : ir.FieldReady I d P) (q : ℕ) : List (ℕ × ℕ) :=
  [(R.cert.exceptions ^ R.cert.Sh.nrep, (q - 1) ^ R.cert.Sh.nrep), (R.cert.testNum, q),
    (R.cert.columnNum + (if npOf R.Pk R.rs = 0 then 0 else R.cert.jointNum), R.cert.columnDen),
    (ir.batchesNum d R.Pk, q), (max 3 (2 * ir.gkrWidth d), q), (R.rs.length, q)]

/-- **The largest round error in units of `2^-e`, rounded up**: the largest `dyadicCeil e` of every
domain's round charges (`FieldReady.chargeFracs`, on fields of their specifications' sizes) and of
every phase's error (`fracSum` of `phaseTerms`, the source challenges at `src`). -/
noncomputable def figErrorMax (R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P)
    (src : ℕ → ℕ × ℕ) (e : ℕ) : ℕ :=
  max (Finset.univ.sup fun d : Fin ir.domains.length =>
      ((R d).chargeFracs (I.specCard (ir.domainField d))).foldr (fun p m => max (dyadicCeil e p) m) 0)
    (Finset.univ.sup fun k : Fin ir.phases => dyadicCeil e (fracSum (ir.phaseTerms I.specCard src k)))

end ErrorMax

/-! ## The figures of a program and their check -/

namespace ProgramFigures

variable {ir : RealizedProgram} {I : Interp} {P : Export.Plan}
  {R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P}

/-- **The check of a program's figures** `F` at the numbers of its domains `Nm` (codecs, largest
arrays and reads, grants), the source challenges' error fractions `src`, the samplers' readers
`rd` with the challenges' largest load `chal`, the rest reads `Lr` of every domain besides its first
combination, and the transcript's largest grant `mg`:

* the figures are the functions of the ready data (`figRounds`, …, `figPos`), the digest length
  the plan's hash's (`Export.hashBytes`), the verifier's queries at most `2^16`, the digest length
  between `1` and `2^10`;
* the transcript's bounds (`ForkNumbers.BoundsOk`) and its largest grant;
* every load passes the Chernoff test `2^-chernoff` on its stream: every domain's reads at `Lr`, its
  first combination at its grant, the phases' challenges;
* every domain's round charges and every phase's error within `errorMax / 2^errorExp`, on fields
  of their specifications' sizes (`Interp.specCard`), and `errorMax` the largest of them rounded
  up (`figErrorMax`). -/
structure Check (F : ProgramFigures) (Nm : ForkNumbers R) (src : ℕ → ℕ × ℕ)
    (rd : SamplerReaders I ir) (chal : Load) (hL : ∀ k (j : ir.ChalAt k), ir.chalLoad rd j.1 ≤ chal)
    (Lr : Fin ir.domains.length → ℕ) (mg : ℕ) : Prop where
  /-- The rounds. -/
  rounds_eq : F.rounds = figRounds R
  /-- The leaves. -/
  leaves_eq : F.N = figLeaves R
  /-- The queried leaves. -/
  queries_eq : F.nq = figQueries R
  /-- The verifier's queries. -/
  kq_eq : F.kq = figKq R
  /-- The digests. -/
  digests_eq : F.D = figDigests R
  /-- The positions. -/
  pos_eq : F.pos = figPos R
  /-- At most `2^16` verifier queries. -/
  kq_le : F.kq ≤ 2 ^ 16
  /-- The digest length is the plan's hash's (`Export.hashBytes`). -/
  k_eq : Export.hashBytes P.hash = some F.k
  /-- The digest length is positive. -/
  k_pos : 0 < F.k
  /-- The digest length is at most `2^10`. -/
  k_le : F.k ≤ 2 ^ 10
  /-- The transcript's bounds. -/
  bounds : Nm.BoundsOk
  /-- The transcript's largest grant. -/
  grant : mg = ProofSystem.fieldForkGrant R Nm.grants (ir.appReaders rd (fun _ => chal) hL)
  /-- The rest reads of every domain. -/
  rest : ∀ d : Fin ir.domains.length, ForkRestNumbers (R d) (ir.padBound d) (ir.circL d) (Lr d)
  /-- Every domain's reads at `Lr` pass on the default stream. -/
  restGood : ∀ d, ChernoffOk F.chernoff (F.k + fsExtraBytes)
    (((Nm.cod d).rd.load.nsmul (Lr d)).max
      ⟨(R d).cert.Sh.nreq, Rejection.byteLen (R d).cert.Sh.N⟩)
  /-- Every domain's first combination passes on its stream with its grant. -/
  stageGood : ∀ d : Fin ir.domains.length,
    ChernoffOk F.chernoff (F.k + fsExtraBytes + (Nm.grants d).stage 0)
      ((Nm.cod d).rd.load.nsmul (ir.claimCount (d := (d : ℕ)) (Pk := (R d).Pk)))
  /-- The phases' challenges pass on the default stream. -/
  phaseGood : ∀ k : Fin ir.phases, ChernoffOk F.chernoff (F.k + fsExtraBytes)
    (chal.nsmul (ir.chalList k).length)
  /-- Every domain's round charges. -/
  errors : ∀ d : Fin ir.domains.length,
    FieldRoundsOk (R d) (I.specCard (ir.domainField d)) F.errorMax F.errorExp
  /-- Every phase's error. -/
  phases : ir.PhaseErrorsOk I.specCard src F.errorMax F.errorExp
  /-- The bound is the largest round error rounded up. -/
  errorMax_eq : F.errorMax = figErrorMax R src F.errorExp

variable {F : ProgramFigures} {Nm : ForkNumbers R} {src : ℕ → ℕ × ℕ} {rd : SamplerReaders I ir}
  {chal : Load} {hL : ∀ k (j : ir.ChalAt k), ir.chalLoad rd j.1 ≤ chal}
  {Lr : Fin ir.domains.length → ℕ} {mg : ℕ}

variable (F Nm src rd chal hL Lr mg) in
/-- `Check` as one conjunction, for its decision. -/
theorem check_iff : Check F Nm src rd chal hL Lr mg ↔
    F.rounds = figRounds R ∧ F.N = figLeaves R ∧ F.nq = figQueries R ∧ F.kq = figKq R ∧
      F.D = figDigests R ∧ F.pos = figPos R ∧ F.kq ≤ 2 ^ 16 ∧
      Export.hashBytes P.hash = some F.k ∧ 0 < F.k ∧ F.k ≤ 2 ^ 10 ∧
      Nm.BoundsOk ∧
      mg = ProofSystem.fieldForkGrant R Nm.grants (ir.appReaders rd (fun _ => chal) hL) ∧
      (∀ d : Fin ir.domains.length, ForkRestNumbers (R d) (ir.padBound d) (ir.circL d) (Lr d)) ∧
      (∀ d, ChernoffOk F.chernoff (F.k + fsExtraBytes)
        (((Nm.cod d).rd.load.nsmul (Lr d)).max
          ⟨(R d).cert.Sh.nreq, Rejection.byteLen (R d).cert.Sh.N⟩)) ∧
      (∀ d : Fin ir.domains.length,
        ChernoffOk F.chernoff (F.k + fsExtraBytes + (Nm.grants d).stage 0)
          ((Nm.cod d).rd.load.nsmul (ir.claimCount (d := (d : ℕ)) (Pk := (R d).Pk)))) ∧
      (∀ k : Fin ir.phases, ChernoffOk F.chernoff (F.k + fsExtraBytes)
        (chal.nsmul (ir.chalList k).length)) ∧
      (∀ d : Fin ir.domains.length,
        FieldRoundsOk (R d) (I.specCard (ir.domainField d)) F.errorMax F.errorExp) ∧
      ir.PhaseErrorsOk I.specCard src F.errorMax F.errorExp ∧
      F.errorMax = figErrorMax R src F.errorExp :=
  ⟨fun h => ⟨h.1, h.2, h.3, h.4, h.5, h.6, h.7, h.8, h.9, h.10, h.11, h.12, h.13, h.14, h.15,
      h.16, h.17, h.18, h.19⟩,
    fun ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩ =>
      ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩⟩

variable (F Nm src rd chal hL Lr mg) in
/-- **The decision of a program's figures' check**, the one instance every program's generated
module decides. -/
noncomputable instance Check.decidable : Decidable (Check F Nm src rd chal hL Lr mg) :=
  decidable_of_iff _ (check_iff F Nm src rd chal hL Lr mg).symm

/-- **Every domain's reads at its largest read pass the Chernoff test on the default stream**, as
numbers: the check of a program whose transcript grants no extended stream, whose loads then pass
at `k + fsExtraBytes` (`Check.loads`). -/
def DefaultLoadsOk (F : ProgramFigures) (Nm : ForkNumbers R) : Prop :=
  ∀ d, ChernoffOk F.chernoff (F.k + fsExtraBytes)
    (((Nm.cod d).rd.load.nsmul (Nm.Lmax d)).max
      ⟨(R d).cert.Sh.nreq, Rejection.byteLen (R d).cert.Sh.N⟩)

/-- The decision of `DefaultLoadsOk`. -/
instance DefaultLoadsOk.decidable (F : ProgramFigures) (Nm : ForkNumbers R) :
    Decidable (DefaultLoadsOk F Nm) := by
  unfold DefaultLoadsOk
  infer_instance

/-! ### The consequences of the check -/

/-- **The figures at their functions.** -/
theorem Check.figuresOk (h : Check F Nm src rd chal hL Lr mg) :
    FiguresOk R F.rounds F.N F.nq F.kq F.D F.pos := by
  rw [h.rounds_eq, h.leaves_eq, h.queries_eq, h.kq_eq, h.digests_eq, h.pos_eq]
  exact figuresOk_fig R

/-- **Every domain's round charges are within `errorMax / 2^errorExp`** (`FieldRoundsLe.of_ok`) on
fields of their specifications' sizes. -/
theorem Check.fieldRoundsLe (h : Check F Nm src rd chal hL Lr mg)
    (hcard : ∀ f, Fintype.card (I f).K = I.specCard f) (d : Fin ir.domains.length) :
    ir.FieldRoundsLe (R d) ((F.errorMax : ℝ≥0) / 2 ^ F.errorExp) :=
  FieldRoundsLe.of_ok (hcard _) (h.errors d)

/-- **Every phase's error is within `errorMax / 2^errorExp`** (`phaseError_le_of`) when every
source challenge's error `ε₀ j` is within its fraction `src j`. -/
theorem Check.phaseError_le (h : Check F Nm src rd chal hL Lr mg)
    (hcard : ∀ f, Fintype.card (I f).K = I.specCard f) (ε₀ : ℕ → ℝ≥0)
    (hsrc : ∀ j, ir.IsSourceChal j → ε₀ j ≤ ((src j).1 : ℝ≥0) / (src j).2) (k : Fin ir.phases) :
    ir.phaseError I (ir.roundError I ε₀) k ≤ (F.errorMax : ℝ≥0) / 2 ^ F.errorExp :=
  phaseError_le_of ε₀ hcard hsrc h.phases k

namespace Check

variable {P : Export.Plan} {B : ir.ProofSystem P I} {R : ∀ d : Fin ir.domains.length, ir.FieldReady I d P}
  {W : Type} {rel : Set (ir.Valuation I × W)}
  {Lw : Lowering (ir.layout I) (Constraint.guard (ir.stmtOk I) (Constraint.ofRel rel))
    (GordieHowe.Domain.lowered (B.withFieldProofs R).domains)}
  {Stmt : Type} {f : Stmt → ir.Valuation I}
  {F : ProgramFigures} {Nm : ForkNumbers R} {src : ℕ → ℕ × ℕ} {rd : SamplerReaders I ir}
  {chal : Load} {hL : ∀ k (j : ir.ChalAt k), ir.chalLoad rd j.1 ≤ chal}
  {Lr : Fin ir.domains.length → ℕ} {mg : ℕ}

/-- **The figures of the composite read through `f`** (`ProofSystem.fieldIop_figures`). -/
theorem figures (h : Check F Nm src rd chal hL Lr mg) :
    (B.fieldIop R Lw f).Figures F.rounds F.N F.nq F.kq F.D F.pos :=
  B.fieldIop_figures Lw f h.figuresOk

/-- **The figures of the composite read through `f` and checked by `chk`**
(`ProofSystem.fieldIopWith_figures`). -/
theorem figuresWith (h : Check F Nm src rd chal hL Lr mg) (chk : Stmt → Bool) :
    (B.fieldIopWith R Lw f chk).Figures F.rounds F.N F.nq F.kq F.D F.pos :=
  B.fieldIopWith_figures Lw f chk h.figuresOk

/-- **The facts the setting is built from** for the transcript at the numbers `Nm`, `k`-byte
digests and the phases' readers at `rd` (`ProofSystem.fieldForkTranscript_bounds`): the
statement's writes, the label and the branch names given. -/
theorem transcript_bounds (h : Check F Nm src rd chal hL Lr mg) {label : List Byte}
    {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20)}
    (hpre : ∀ x, (stmt.ser x).length ≤ 2 ^ 20) (hlabel : label.length ≤ 2 ^ 10)
    (hname : ∀ a, (name a).length ≤ 2 ^ 10) :
    (B.fieldForkTranscript R Lw f Nm.cod (Nm.fits B.enforce) label F.k stmt name appWrites
      (ir.appReaders rd (fun _ => chal) hL) mg).Bounds :=
  B.fieldForkTranscript_bounds Lw f Nm hpre hlabel h.k_le h.k_pos hname h.bounds h.grant

/-- **The facts the setting is built from** for the transcript of the composite checked by `chk`
(as `transcript_bounds`, `ProofSystem.fieldForkTranscriptWith_bounds`). -/
theorem transcriptWith_bounds (h : Check F Nm src rd chal hL Lr mg) (chk : Stmt → Bool)
    {label : List Byte} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m,
      Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20)}
    (hpre : ∀ x, (stmt.ser x).length ≤ 2 ^ 20) (hlabel : label.length ≤ 2 ^ 10)
    (hname : ∀ a, (name a).length ≤ 2 ^ 10) :
    (B.fieldForkTranscriptWith R Lw f Nm.cod (Nm.fits B.enforce) chk label F.k stmt name
      appWrites (ir.appReaders rd (fun _ => chal) hL) mg).Bounds :=
  B.fieldForkTranscriptWith_bounds Lw f Nm chk hpre hlabel h.k_le h.k_pos hname h.bounds h.grant

/-- The Chernoff test `2^-chernoff` at a round's own stream length, `k + fsExtraBytes` plus its
grant. -/
abbrev GoodAt (F : ProgramFigures) (g : ℕ) (L : Load) : Prop :=
  PassesChernoff (65 / 64) ((1 / 2) ^ F.chernoff) (F.k + fsExtraBytes + g) L

/-- Larger grants keep the test. -/
theorem goodAt_mono (F : ProgramFigures) (g : ℕ) (L : Load) (h : GoodAt F 0 L) : GoodAt F g L :=
  h.anti (by norm_num) (by omega)

/-- The rest reads of every domain (`forkRestSizesLe_ofOk`). -/
theorem restSizes (h : Check F Nm src rd chal hL Lr mg) (d : Fin ir.domains.length) :
    ForkRestSizesLe B.src (R d) (Lr d) :=
  forkRestSizesLe_ofOk B.enforce (h.rest d)

/-- Every domain's reads at `Lr` pass on the default stream. -/
theorem restGoodAt (h : Check F Nm src rd chal hL Lr mg) (d : Fin ir.domains.length) (L : Load)
    (hle : L ≤ forkLoad B.src (R d) (Nm.cod d).rd (Lr d)) : GoodAt F 0 L := by
  rw [forkLoad_eq] at hle
  exact ((h.restGood d).passes.anti (by norm_num) (by omega)).of_le (by norm_num) hle

/-- Every domain's first combination passes on its stream with its grant. -/
theorem stageGoodAt (h : Check F Nm src rd chal hL Lr mg) (d : Fin ir.domains.length) (n : ℕ)
    (hn : n ≤ ir.claimCount (d := (d : ℕ)) (Pk := (R d).Pk)) :
    GoodAt F ((CReader.pi n (Nm.cod d).rd).extend ((Nm.fits B.enforce d).grants.stage 0)).grant
      ((Nm.cod d).rd.load.nsmul n) := by
  rw [CReader.extend_grant, CReader.pi_grant, h.bounds.2.2.2.2 d, Nat.mul_zero, Nat.zero_add]
  refine (h.stageGood d).passes.of_le (by norm_num) ?_
  simp only [Load.nsmul, Load.le_iff]
  exact ⟨Nat.mul_le_mul_right _ hn, le_rfl⟩

/-- The phases' readers pass on the default stream. -/
theorem appGood (h : Check F Nm src rd chal hL Lr mg) :
    (ir.appReaders rd (fun _ => chal) hL).AllGranted (GoodAt F) :=
  SpecReaders.AllGranted.of_allLoads (goodAt_mono F)
    (ir.appReaders_allLoads rd (fun _ => chal) hL fun k => (h.phaseGood k).passes)

/-- **Every round's load passes the Chernoff test `2^-chernoff` at its own stream length**
(`ProofSystem.fieldForkLoadsGranted`). -/
theorem loadsGranted (h : Check F Nm src rd chal hL Lr mg) {label : List Byte} {k : ℕ}
    {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20)} :
    ∀ j, ((B.fieldForkTranscript R Lw f Nm.cod (Nm.fits B.enforce) label k stmt name appWrites
      (ir.appReaders rd (fun _ => chal) hL) mg).readers j).AllGranted (GoodAt F) :=
  B.fieldForkLoadsGranted R Lw f Nm.cod (Nm.fits B.enforce) (goodAt_mono F) (h.restSizes)
    (h.restGoodAt) (fun d n hn => h.stageGoodAt d n hn) h.appGood

/-- **Every round's load of the transcript checked by `chk` passes the Chernoff test
`2^-chernoff` at its own stream length** (`ProofSystem.fieldForkLoadsGrantedWith`). -/
theorem loadsGrantedWith (h : Check F Nm src rd chal hL Lr mg) (chk : Stmt → Bool)
    {label : List Byte} {k : ℕ} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m,
      Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20)} :
    ∀ j, ((B.fieldForkTranscriptWith R Lw f Nm.cod (Nm.fits B.enforce) chk label k stmt name
      appWrites (ir.appReaders rd (fun _ => chal) hL) mg).readers j).AllGranted (GoodAt F) :=
  B.fieldForkLoadsGrantedWith R Lw f Nm.cod (Nm.fits B.enforce) (goodAt_mono F) (h.restSizes)
    (h.restGoodAt) (fun d n hn => h.stageGoodAt d n hn) h.appGood

/-- **Every round's load passes the Chernoff test `2^-chernoff` on the default stream**, the
transcript's `k + fsExtraBytes` at `k`-byte digests (`ProofSystem.fieldForkLoads`), every domain's
reads within its largest read (`DefaultLoadsOk`). -/
theorem loads (h : Check F Nm src rd chal hL Lr mg) (hu : DefaultLoadsOk F Nm) {label : List Byte}
    {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIop R Lw f).m, Fin ((B.fieldIop R Lw f).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIop R Lw f).app.spec (2 ^ 20)} :
    ∀ j, ((B.fieldForkTranscript R Lw f Nm.cod (Nm.fits B.enforce) label F.k stmt name appWrites
      (ir.appReaders rd (fun _ => chal) hL) mg).readers j).AllLoads
      (PassesChernoff (65 / 64) ((1 / 2) ^ F.chernoff)
        ((B.fieldForkTranscript R Lw f Nm.cod (Nm.fits B.enforce) label F.k stmt name appWrites
          (ir.appReaders rd (fun _ => chal) hL) mg).k + fsExtraBytes)) :=
  B.fieldForkLoads R Lw f Nm.cod (Nm.fits B.enforce)
    (fun d L hle => by
      rw [Nm.forkLoad_fits B.enforce d] at hle
      exact (hu d).passes.of_le (by norm_num) hle)
    (ir.appReaders_allLoads rd (fun _ => chal) hL fun k => (h.phaseGood k).passes)

/-- **Every round's load of the transcript checked by `chk` passes the Chernoff test
`2^-chernoff` on the default stream** (`ProofSystem.fieldForkLoadsWith`). -/
theorem loadsWith (h : Check F Nm src rd chal hL Lr mg) (hu : DefaultLoadsOk F Nm)
    (chk : Stmt → Bool) {label : List Byte} {stmt : Codec Stmt}
    {name : (Σ d : Fin (B.fieldIopWith R Lw f chk).m,
      Fin ((B.fieldIopWith R Lw f chk).circuit d).nb) → List Byte}
    {appWrites : SpecWrites (B.fieldIopWith R Lw f chk).app.spec (2 ^ 20)} :
    ∀ j, ((B.fieldForkTranscriptWith R Lw f Nm.cod (Nm.fits B.enforce) chk label F.k stmt name
      appWrites (ir.appReaders rd (fun _ => chal) hL) mg).readers j).AllLoads
      (PassesChernoff (65 / 64) ((1 / 2) ^ F.chernoff)
        ((B.fieldForkTranscriptWith R Lw f Nm.cod (Nm.fits B.enforce) chk label F.k stmt name
          appWrites (ir.appReaders rd (fun _ => chal) hL) mg).k + fsExtraBytes)) :=
  B.fieldForkLoadsWith R Lw f Nm.cod (Nm.fits B.enforce)
    (fun d L hle => by
      rw [Nm.forkLoad_fits B.enforce d] at hle
      exact (hu d).passes.of_le (by norm_num) hle)
    (ir.appReaders_allLoads rd (fun _ => chal) hL fun k => (h.phaseGood k).passes)

end Check

end ProgramFigures

end GordieHowe.RealizedProgram
