-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.Errors
public import GordieHowe.Language.Realizations.Derivation.Honest
public import GordieHowe.Language.Realizations.Derivation.Placed

@[expose] public section

/-!
# GordieHowe: the honest prover of a program's proof system

**The honest prover** (`GordieHowe.RealizedProgram.HonestCore`, the paper's completeness hypothesis, whose completeness
error `errc` is `HonestCore.Complete`, `def:o-guarantees` (1)), on honest inputs `Inp` related to
statements by `relH`:

* the honest statements pass the program's member checks (`checks`, `GordieHowe.RealizedProgram.StatementOk`), which
  the verifier makes first;
* the honest committed values (`val`) and the honest late values as functions of the challenges and
  the pads (`late`), reading only what each late value's exported reads list (`respects`,
  `GordieHowe.RealizedProgram.RespectsReads`; with the late reads of `GordieHowe.RealizedProgram.ChallengeOrder` (`late`) and
  `GordieHowe.RealizedProgram.PadOrderValid` it gives challenge causality and the pad order);
* completeness events charged to each phase (`bad`), which may read the challenges of every
  phase; the honest strategy (`GordieHowe.RealizedProgram.HonestStrategy`) adds their probabilities, at most `δ` over
  the phase's challenge whatever the other phases' challenges (`badBound`), whose sum is a
  completeness error (`HonestStrategy.complete`);
* the honest committed values lie in their cells' bases in every domain (`base`: the packing-tree
  node of their value);
* off the events, at the honest environment (`GordieHowe.RealizedProgram.honestEnv`: the realized assignment of the
  committed assignment read from every domain's cells of the honest values and pads,
  `GordieHowe.RealizedProgram.honestAsg`, so a value bound to its digits is read through them; the honest run), the
  program holds (`sat`; its realization predicates included, so the quotient of a one-digit `mod_q`
  lies in the range of its `in`), every group's histograms count its needles (`histograms`,
  `GordieHowe.RealizedProgram.HistogramsCount`) and the two-sided and digit lookups' digits are below their bases
  (`digits`, `GordieHowe.RealizedProgram.DigitsBelow`), and every MAC's tag is its honest tag (`tags`,
  `GordieHowe.RealizedProgram.MacTagsHonest`: `U = Σ_c β^(c+1) · chunk_c(X_H)` where `x`'s domain hosts the MAC,
  `U = Σ_c β^(c+1) · chunk_c(X_A)` where no domain does). The histograms, the digits and the MAC
  tags are obligations of the honest strategy while the C++ generators have no Lean statement;
* the pad copies are computed from the pads (`GordieHowe.RealizedProgram.copyVal`, `Interp.padCopyBit`: each blind of a
  MAC is the `polynomialBits` copy of its tag's pad, drawn with the pad before the commitment), so
  the MACs' blinds are honest by construction (`macBlinds_honestEnv`, `BlindsArePadCopies`).

**The honest prover** (`GordieHowe.RealizedProgram.ProofSystem.prover`): the phased honest prover (`GordieHowe.RealizedProgram.ProofSystem.phasedHonest`: the late
values of the strategy, the circuits' honest inputs encoded from the honest cells by every domain's
honest prover) as the application phase's, and every domain proof's honest prover. Off the events, the
realized program holds and so does every domain's predicate on its cells, where the domain proofs' honest provers apply. The
late values are computed after their phase's challenge and read only the pads of earlier messages
(`ChallengeOrder.late` and `GordieHowe.RealizedProgram.PadOrderValid`, `challengeCausal_of_respectsReads`,
`padOrder_of_respectsReads`), so the simulator's messages are uniform (`PadOrder.uniform`).

**The domains' honest provers** (`GordieHowe.RealizedProgram.ProofSystem.HonestDomains`): from the compiler's completeness
(`CircuitsAccept`), every domain proof's honest prover at the domain's predicate
(`GordieHowe.RealizedProgram.ProofSystem.honestPred`), as the domain proofs provide them.
-/

namespace GordieHowe.RealizedProgram

open Export ProofSystem.PhaseLayout IOP
open scoped NNReal

section

/-- **The image of a pad under a copy map**: for `polynomialBits`, bit `i` of the integer reading of
the pad `p` (its coordinates in the field's polynomial basis, `FieldInterp.toNat`); `false` for any
other map, which the exporter does not emit. -/
def _root_.GordieHowe.RealizedProgram.Interp.padCopyBit (I : Interp) (m : String) {f : ℕ} (p : (I f).K) (i : ℕ) : Bool :=
  m == "polynomialBits" && ((I f).toNat p).testBit i

variable (ir : RealizedProgram) (I : Interp)

/-! ## The honest environment -/

/-- **The pads as a valuation**: coordinate `i` of late value `v`'s pad, `0` off the late values'
coordinates. -/
def padsOf (π : (ir.layout I).Pads) : ir.Valuation I := fun v i =>
  if h : v < ir.values.length ∧ ir.IsLate v ∧ i < (ir.value v).size then
    ((show ir.Mask I v from π ⟨⟨v, h.1⟩, h.2.1⟩) ⟨i, h.2.2⟩ : (I (ir.valueField v)).K)
  else 0

/-- **The committed values with their pad copies** of the committed values `val` and the pads
`π`: a pad copy `padCopy u m` (the image of late value `u`'s pad under the map `m`, drawn with the
pad before the commitment) reads its map at `u`'s pad (`Interp.padCopyBit`); every other value
reads `val`. -/
def copyVal (val : ir.Valuation I) (π : (ir.layout I).Pads) : ir.Valuation I := fun v i =>
  match (ir.value v).kind with
  | .padCopy u m => (I (ir.valueField v)).ofBool (I.padCopyBit m (ir.padsOf I π u 0) i)
  | _ => val v i

/-- **The cells of domain `d` of the committed values `val` and the pads `π`**
(`RealizedProgram.toCells`): the committed values with their pad copies computed from the pads
(`copyVal`), and the pads. -/
def honestCells (d : ℕ) (val : ir.Valuation I) (π : (ir.layout I).Pads) :
    ir.Cell d → (I (ir.domainField d)).K :=
  ir.toCells I d ⟨ir.copyVal I val π, ir.padsOf I π⟩

/-- **The honest committed assignment**: the committed assignment read from every domain's cells of
the committed values `val` and the pads `π` (`RealizedProgram.ofAllCells`). -/
def honestAsg (val : ir.Valuation I) (π : (ir.layout I).Pads) : ir.Assignment I :=
  ir.ofAllCells I fun d => ir.honestCells I d val π

/-- **The honest environment** at the statement `x`, the committed values `val`, the late values
`late`, the challenges `c` and the pads `π`: the layout's environment at the realized assignment
(`bindAsg`) of the honest committed assignment and the honest run. -/
def honestEnv (x : ir.Valuation I) (val : ir.Valuation I)
    (late : (∀ k, (ir.layout I).Ch k) → (ir.layout I).Pads → ∀ l, (ir.layout I).Mask l)
    (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) : ir.Env I :=
  ir.layoutEnv I x (ir.bindAsg (ir.honestAsg I val π)) ((ir.layout I).honestRun late c π)

/-- **Every MAC's blinds are the pad copy `polynomialBits` of its tag's pad** (compiler/mac.h): for
a cross-field `equal`, each blind (`blind`, and `blindX` where no domain hosts the MAC, `mac_odd`:
both sides copy the one pad `P`) is a value of kind `padCopy tag "polynomialBits"` with a cell at
each of its `width` coordinates in its domain, and the tag's pad has a cell at coordinate `0`. A
property of the program. -/
def BlindsArePadCopies : Prop :=
  ∀ p ∈ ir.predicates, ∀ dx x dy y k real, p.body = .cross dx x dy y k real →
    ∀ b ∈ real.blind.toList ++ real.blindX.toList,
    (ir.value b).kind = .padCopy real.tag "polynomialBits" ∧
      (ir.value b).domain < ir.domains.length ∧
      (∀ i < real.width, CellKey.val b i ∈ ir.cellKeys (ir.value b).domain) ∧
      (ir.value real.tag).domain < ir.domains.length ∧
      CellKey.pad real.tag 0 ∈ ir.cellKeys (ir.value real.tag).domain

/-- **Every MAC's tag is honest** in the environment `e` (the tag part of `MacsHonest`): where the
compiler states no H predicate, the tag is the honest tag at the key (`MacTagAt`: the MAC of the H
operand where `x`'s domain hosts the MAC, of the `x` side's chunks where no domain does). -/
def MacTagsHonest (e : ir.Env I) : Prop :=
  ∀ p ∈ ir.predicates, ∀ dx x dy y k real, p.body = .cross dx x dy y k real →
    real.hPredicate = none → ir.MacTagAt (ir.reader e) dx x real (castElt (e.chal real.key 0))

/-- **The honest prover of a program** on honest inputs `Inp` related to statements by `relH`: the
honest strategy (see the module docstring) without the probabilities of its completeness events.
Every field is a property of the honest prover. Its completeness error is `HonestCore.Complete`. -/
structure HonestCore {Inp : Type} (relH : Set (ir.Valuation I × Inp)) where
  /-- The honest committed values. -/
  val : Inp → ir.Valuation I
  /-- The honest late values, from the challenges and the pads. -/
  late : Inp → (∀ k, (ir.layout I).Ch k) → (ir.layout I).Pads → ∀ l, (ir.layout I).Mask l
  /-- Every late value reads only its exported reads. -/
  respects : ∀ y, ir.RespectsReads (late y)
  /-- The completeness event charged to phase `k + 1`, at the challenges of every phase. -/
  bad : (k : Fin ir.phases) → ir.Valuation I → Inp → (∀ k, (ir.layout I).Ch k) → Prop
  /-- The honest statements pass the program's member checks. -/
  checks : ∀ x y, (x, y) ∈ relH → ir.StatementOk I x
  /-- The honest statements lie within the declared bounds (automatic for a program declaring
  none, `stmtBounded_of_nil`). -/
  bounded : ∀ x y, (x, y) ∈ relH → ir.StmtBounded I x := by
    exact fun x _ _ => Program.stmtBounded_of_nil (by decide +kernel) x
  /-- On the relation and off the events, the honest committed values and their pad copies lie in
their cells' bases (for a pad copy, a property of its map's values; for a source value, its type
set in the accepting execution). -/
  base : ∀ x y, (x, y) ∈ relH → ∀ c : (∀ k, (ir.layout I).Ch k), (∀ k, ¬ bad k x y c) →
    ∀ π d v i
    (h : CellKey.val v i ∈ ir.cellKeys d),
    (castElt (ir.copyVal I (val y) π v i) : (I (ir.domainField d)).K) ∈ ir.cellBase I d ⟨_, h⟩
  /-- Off the events, the program holds at the honest environment. -/
  sat : ∀ x y, (x, y) ∈ relH → ∀ c π, (∀ k, ¬ bad k x y c) →
    ir.SatAt (ir.honestEnv I x (val y) (late y) c π)
  /-- Off the events, every group's histograms count its needles at the honest environment. -/
  histograms : ∀ x y, (x, y) ∈ relH → ∀ c π, (∀ k, ¬ bad k x y c) →
    HistogramsCount (ir.honestEnv I x (val y) (late y) c π)
  /-- Off the events, the two-sided and digit lookups' digits are below their bases at the honest
  environment. -/
  digits : ∀ x y, (x, y) ∈ relH → ∀ c π, (∀ k, ¬ bad k x y c) →
    DigitsBelow (ir.reader (ir.honestEnv I x (val y) (late y) c π))
  /-- Every MAC's blind is the pad copy `polynomialBits` of its tag's pad, with its cells
  (a property of the program). -/
  blinds : ir.BlindsArePadCopies
  /-- Off the events, every MAC's tag is honest at the honest environment (the C++ MAC
  generator, compiler/mac.h, has no Lean statement); the blinds are by `blinds`
  (`macBlinds_honestEnv`). -/
  tags : ∀ x y, (x, y) ∈ relH → ∀ c π, (∀ k, ¬ bad k x y c) →
    ir.MacTagsHonest I (ir.honestEnv I x (val y) (late y) c π)

/-- **The completeness error `errc` of an honest prover** (the paper's `def:o-guarantees` (1)): on
the relation, the challenges of the phases meet some completeness event with probability at most
`errc`; off the events the program holds (`HonestCore.sat`). -/
def HonestCore.Complete {ir : RealizedProgram} {I : Interp} {Inp : Type} {relH : Set (ir.Valuation I × Inp)} (H : ir.HonestCore I relH)
    (errc : ir.Valuation I → ℝ≥0) : Prop :=
  ∀ x y, (x, y) ∈ relH → Pr[c ← (∀ k, (ir.layout I).Ch k) : ∃ k, H.bad k x y c] ≤ errc x

/-- **The completeness error `errc` of an honest prover over the prover's coins** (the paper's
`def:o-guarantees` (1) for a prover with coins, `def:o-honest`): for honest inputs `J` related to
statements by `relJ`, read with uniform coins `ω` as the honest inputs `inp y ω`, on `relJ`, over
uniform coins and challenges of the phases, the input with its coins is off the relation or the
challenges meet some completeness event with probability at most `errc`. At one coin
(`Ω = Unit`) and `relJ = relH` this is `HonestCore.Complete`. -/
def HonestCore.CoinComplete {ir : RealizedProgram} {I : Interp} {Inp : Type}
    {relH : Set (ir.Valuation I × Inp)} (H : ir.HonestCore I relH) {J Ω : Type} [Fintype Ω]
    [Nonempty Ω] (relJ : Set (ir.Valuation I × J)) (inp : J → Ω → Inp)
    (errc : ir.Valuation I → ℝ≥0) : Prop :=
  ∀ x y, (x, y) ∈ relJ → Pr[u ← (Ω × ∀ k, (ir.layout I).Ch k) :
    (x, inp y u.1) ∉ relH ∨ ∃ k, H.bad k x (inp y u.1) u.2] ≤ errc x

open Classical in
/-- **The honest strategy of a program** on honest inputs `Inp` related to statements by `relH`:
the honest prover (`HonestCore`) with the completeness events charged to each phase as completeness
error (`δ`). Its summed errors are a completeness error (`HonestStrategy.complete`). -/
structure HonestStrategy {Inp : Type} (relH : Set (ir.Valuation I × Inp)) extends
    ir.HonestCore I relH where
  /-- The completeness error at every phase. -/
  δ : Fin ir.phases → ℝ≥0
  /-- On the relation, at the challenges `c` of every phase, the completeness event of phase
  `k + 1` has probability at most `δ k` over that phase's challenge, the others those of `c`. -/
  badBound : ∀ k x y, (x, y) ∈ relH → ∀ c : ∀ k, (ir.layout I).Ch k,
    Pr[c' ← (ir.layout I).Ch k : bad k x y (Function.update c k c')] ≤ δ k

variable {ir I}

/-- **The honest cells lie in their bases**: a committed value's by the strategy (`base`), a pad's
in its pad space (the masking space of its late value), a filler input anywhere. -/
theorem honestCells_mem_cellBase {Inp : Type} {relH : Set (ir.Valuation I × Inp)}
    (H : ir.HonestCore I relH) {x : ir.Valuation I} {y : Inp} (hy : (x, y) ∈ relH)
    {c : ∀ k, (ir.layout I).Ch k} (hc : ∀ k, ¬ H.bad k x y c) (π : (ir.layout I).Pads)
    (d : ℕ) (k : ir.Cell d) :
    ir.honestCells I d (H.val y) π k ∈ ir.cellBase I d k := by
  rcases k with ⟨⟨v, i⟩ | ⟨v, i⟩ | ⟨c, j⟩, hk⟩
  · exact H.base x y hy c hc π d v i hk
  · obtain ⟨hv, -, hl, hi⟩ := (ir.mem_cellKeys_pad).1 hk
    have hlate : ir.IsLate v := ir.isLateOf_isLate hl
    have hdom : ir.valueField v = ir.domainField d := by
      rw [ir.isLateOf_valueField hl]
    change (castElt (ir.padsOf I π v i) : (I (ir.domainField d)).K) ∈
      ((I (ir.domainField d)).space (ir.value v).padSpace : Set _)
    refine castElt_mem_space hdom ?_
    simp only [padsOf, hv, hlate, hi, and_self, ↓reduceDIte]
    exact Subtype.prop _
  · trivial

/-- **The honest assignment reads the honest cells of a value's own domain** at a committed
coordinate with a cell there. -/
theorem honestAsg_val {val : ir.Valuation I} {π : (ir.layout I).Pads} {v i : ℕ}
    (hd : (ir.value v).domain < ir.domains.length)
    (hk : CellKey.val v i ∈ ir.cellKeys (ir.value v).domain) :
    (ir.honestAsg I val π).val v i = ir.copyVal I val π v i := by
  simp only [honestAsg, ofAllCells, hd, ↓reduceDIte, honestCells]
  exact ofCells_toCells_val _ hk

/-- **The honest assignment reads the pads** at a pad coordinate with a cell in the late value's
domain. -/
theorem honestAsg_pad {val : ir.Valuation I} {π : (ir.layout I).Pads} {v i : ℕ}
    (hd : (ir.value v).domain < ir.domains.length)
    (hk : CellKey.pad v i ∈ ir.cellKeys (ir.value v).domain) :
    (ir.honestAsg I val π).pad v i = ir.padsOf I π v i := by
  simp only [honestAsg, ofAllCells, hd, ↓reduceDIte, honestCells]
  exact ofCells_toCells_pad _ hk

/-- **The blinds of the honest environment are honest** (`MacsHonest.blind`): every MAC's blind is
the pad copy `polynomialBits` of its tag's pad (`BlindsArePadCopies`), which the honest cells compute
from the pads (`copyVal`). -/
theorem macBlinds_honestEnv (hB : ir.BlindsArePadCopies) (x val : ir.Valuation I)
    (late : (∀ k, (ir.layout I).Ch k) → (ir.layout I).Pads → ∀ l, (ir.layout I).Mask l)
    (c : ∀ k, (ir.layout I).Ch k) (π : (ir.layout I).Pads) :
    ∀ p ∈ ir.predicates, ∀ dx x' dy y k real, p.body = .cross dx x' dy y k real →
      ∀ b ∈ real.blind.toList ++ real.blindX.toList, ∀ i < real.width,
        ir.reader (ir.honestEnv I x val late c π) b i =
          if ((I (ir.valueField real.tag)).toNat
              ((ir.honestEnv I x val late c π).asg.pad real.tag 0)).testBit i then 1 else 0 := by
  intro p hp dx x' dy y k real hb b hbm i hi
  obtain ⟨hkind, hbd, hbk, htd, htk⟩ := hB p hp dx x' dy y k real hb b hbm
  rw [reader_of_padCopy _ hkind]
  simp only [honestEnv, layoutEnv]
  rw [ir.bindAsg_val_of_isBound (v := b) _ (by rw [hkind]; rfl), honestAsg_val hbd (hbk i hi)]
  simp only [copyVal, hkind, bindAsg, honestAsg_pad htd htk, Interp.padCopyBit, beq_self_eq_true,
    Bool.true_and, FieldInterp.ofBool]

/-- **The MACs of the honest environment are honest** (`MacsHonest`): the tags by the strategy
(`HonestCore.tags`), the blinds by the pad copies (`macBlinds_honestEnv`). -/
theorem macsHonest_honestEnv {Inp : Type} {relH : Set (ir.Valuation I × Inp)}
    (H : ir.HonestCore I relH) {x : ir.Valuation I} {y : Inp} (hy : (x, y) ∈ relH)
    {c : ∀ k, (ir.layout I).Ch k} {π : (ir.layout I).Pads} (hc : ∀ k, ¬ H.bad k x y c) :
    ir.MacsHonest (ir.honestEnv I x (H.val y) (H.late y) c π) where
  tag := H.tags x y hy c π hc
  blind := macBlinds_honestEnv H.blinds x (H.val y) (H.late y) c π

end

namespace ProofSystem

variable {P : Export.Plan} {ir : RealizedProgram} {I : Interp} (B : ir.ProofSystem P I)
  {Inp : Type} {relH : Set (ir.Valuation I × Inp)}

/-! ## The domains' honest provers -/

/-- **The honest predicate of domain `d`**: the domain's predicate (`RealizedProgram.domainOf`), without the
compiler trust. -/
abbrev honestPred (d : Fin ir.domains.length) :
    (ir.layout I).Constraint (ir.Valuation I) (B.guardedDomain d).Cells :=
  fun x a r => (ir.domainOf I d).Holds x a r

/-- **The domains' simulator data**: every domain proof's (`FieldProof.Sim`). -/
abbrev DomainSims : Type 1 := ∀ d, (B.proof d).proof.Sim

/-- **The domains' honest provers**, simulated by `DS`: from the compiler's completeness, every
domain proof's honest prover at the domain's predicate. -/
abbrev HonestDomains (DS : B.DomainSims) : Type 1 :=
  B.CircuitsAccept → ∀ d, (B.proof d).Honest (B.honestPred d) (DS d)

/-! ## The honest prover -/

/-- **Domain `d`'s predicate holds on the honest cells** off the completeness events: the value
ranges hold at the bounded statement (`ranges_reader`), the realized program holds
(`realizedAt_of_honest_derivs`), so every domain's predicate does on its cells
(`holds_of_sat_derivs`, by the domains' locality). -/
theorem holds_honest (B : ir.ProofSystem P I) (H : ir.HonestCore I relH) {x : ir.Valuation I} {y : Inp}
    (hy : (x, y) ∈ relH) {c : ∀ k, (ir.layout I).Ch k} {π : (ir.layout I).Pads}
    (hc : ∀ k, ¬ H.bad k x y c) (d : Fin ir.domains.length) :
    (ir.domainOf I d).Holds x (ir.honestCells I d (H.val y) π)
      ((ir.layout I).honestRun (H.late y) c π) := by
  have hsat := H.sat x y hy c π hc
  have hS := ranges_reader B.lawful B.opaqueModel
    (ir.layoutEnv I x (ir.bindAsg (ir.ofAllCells I fun d => ir.honestCells I d (H.val y) π))
      ((ir.layout I).honestRun (H.late y) c π)) (H.bounded x y hy)
  obtain ⟨D, hD⟩ := B.realization
  exact holds_of_sat_derivs (a := fun d => ir.honestCells I d (H.val y) π)
    B.valid.program.wellFormed B.registered B.lawful B.cells B.locality hD
    (fun d => honestCells_mem_cellBase H hy hc π d) hsat
    (realizedAt_of_honest_derivs B.valid.program.wellFormed hD B.registered B.lawful
      (layoutEnv_sampled _ _ _) hsat (H.histograms x y hy c π hc) (H.digits x y hy c π hc)
      (macsHonest_honestEnv H hy hc) hS
      (fun _ hvl _ hk => reader_bindAsg_of_boundOk hD.bound rfl hvl hk)) d

/-- **The phased honest prover of the protocol**: the strategy's late values and completeness events;
every circuit's honest input encoded from the honest cells by its domain's honest prover; the late
values computed after their phase's challenge and in pad order (`ChallengeOrder.late` and
`RealizedProgram.PadOrderValid`, from the exported reads); off the events, every circuit's honest input lies
in its domain (`holds_honest`). -/
def phasedHonest (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    (H : ir.HonestCore I relH) :
    (((B.baseLowering fun _ _ => ()).check (ir.stmtOk I)).toPhased B.enforcement).Honest Inp relH
      (fun d => (HD A d).In) fun d => (HD A d).dom where
  wit d y π := (HD A d).encode (ir.honestCells I d (H.val y) π)
  late := H.late
  challengeCausal y π := challengeCausal_of_respectsReads B.valid.program.order (H.respects y) π
  padOrder y := padOrder_of_respectsReads B.valid.program.pads (H.respects y)
  bad := H.bad
  ok_honest x _ hy _ _ _ := stmtOk_iff.2 ⟨H.checks x _ hy, H.bounded x _ hy⟩
  dom_honest x _ hy _ _ hc d := (HD A d).dom_of x _ _ (B.holds_honest H hy hc d)

/-- **The simulator data of the protocol**: the phased application phase's simulator
(`Phased.appSim`) and the domains' simulator data `DS`. -/
def simData (DS : B.DomainSims) : B.protocol.SimData where
  app := (((B.baseLowering fun _ _ => ()).check (ir.stmtOk I)).toPhased B.enforcement).appSim
  circuit d := (DS d)

/-- **The honest prover of the protocol**: the phased honest prover as the application phase's, and
every domain proof's honest prover, simulated by `simData DS`. -/
def honest (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    (H : ir.HonestCore I relH) : B.protocol.Honest (B.simData DS) Inp relH where
  In d := (HD A d).In
  dom d := (HD A d).dom
  app := (B.phasedHonest A HD H).toAppHonest
  circuit d := (HD A d).circuit

/-- The honest prover's coins: the pads of the late values and every domain proof's coins. -/
abbrev Coins (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS) (H : ir.HonestCore I relH) :
    Type :=
  (B.honest A HD H).Coins

/-- **The honest prover of the proof system** at the honest input `y` and the coins `c`: commit to every
domain's honest cells, send the strategy's late values masked by the pads, then run every domain
proof's honest prover (`MultiCircuitIOP.honest`). -/
noncomputable def prover (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    (H : ir.HonestCore I relH) (y : Inp) (c : B.Coins A HD H) :
    Prover B.spec (ir.Valuation I) :=
  B.protocol.honest (B.honest A HD H) y c

/-- **The simulator of the proof system**: uniform messages for the late values at the given challenges
(`PadOrder.uniform`), then every domain proof's simulator on the public input the simulated
transcript fixes (`MultiCircuitIOP.simulator`).

Running time: one element of every late value's masking space written into the transcript, every
domain proof's simulator (`FieldProof.simulator`), the verifier's computation of the public
inputs and the assembly of the view.
This running time is argued here, not proved in Lean. -/
def simulator (DS : B.DomainSims) : B.iop.Simulator :=
  B.protocol.simulator (B.simData DS)

/-- **The exception event of the simulation**: a completeness event of the strategy occurs at the
phases' challenges of the protocol's challenges `ch`. -/
def exception (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS) (H : ir.HonestCore I relH)
    (x : ir.Valuation I) (y : Inp) (ch : B.spec.Challenges) : Prop :=
  ¬ (B.honest A HD H).app.Avoids x y (B.protocol.appChallenges ch)

/-- The completeness events of the protocol's application phase have together the honest prover's
completeness error (`HonestCore.Complete`). -/
theorem errorBound_honest (A : B.CircuitsAccept) {DS : B.DomainSims} (HD : B.HonestDomains DS)
    (H : ir.HonestCore I relH) {errc : ir.Valuation I → ℝ≥0} (hc : H.Complete errc) :
    (B.honest A HD H).app.ErrorBound errc :=
  Phased.Honest.errorBound_toAppHonest hc

end ProofSystem

end GordieHowe.RealizedProgram
