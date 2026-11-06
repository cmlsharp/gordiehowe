-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.ProofSystem.Program.ForkNums
public import GordieHoweNative.ProofSystem.Program.Figures
public import GordieHoweNative.Language.FieldNums
public import GordieHoweNative.Language.Realizations.Realized

/-!
# GordieHowe: the figures' check on numbers

The figures' facts of a program (`RuntimeInputs.FiguresFacts`, Mathlib-side: the readers' test, the
domains' size bounds, the messages' bound, `ProgramFigures.Check` and the loads on the default
stream) read the ready data, the codecs and the readers only through numbers: every domain's
numbers (`ForkReader.DomainNums`), its tableau's (`TableauNums`), its field's element bytes, reader
load and grant, and the fields' sizes (`FieldNums`). Here they are tests on those numbers
(`FigCheck`); the equalities with the Mathlib-side figures are in
`GordieHowe/ProofSystem/Program/FiguresCheck.lean`.
-/

public section

namespace GordieHowe.RealizedProgram

open Export

namespace FigCheck

/-! ## Loads and the Chernoff test -/

/-- A load as numbers: draws and bytes per draw (`SPBCS.Load`). -/
abbrev LoadN := Nat × Nat

/-- `Load.nsmul`. -/
@[expose] def nsmulL (n : Nat) (L : LoadN) : LoadN := (n * L.1, L.2)

/-- `Load.max`. -/
@[expose] def maxL (L L' : LoadN) : LoadN := (max L.1 L'.1, max L.2 L'.2)

/-- **The Chernoff test `2^-E` of a load on `N`-byte streams** (`ChernoffOk`). -/
@[expose] def chernoffB (E N : Nat) (L : LoadN) : Bool :=
  decide (65 ^ L.2 < 2 * 64 ^ L.2) &&
    decide (65 ^ (L.2 * L.1) * 64 ^ (N + 1) * 2 ^ (E + 1) ≤ (2 * 64 ^ L.2 - 65 ^ L.2) ^ L.1 *
      65 ^ (N + 1)) &&
    decide (L.1 * 2 ^ (E + 1) ≤ 2 ^ N)

/-- The bits of `n` (`Nat.size`). -/
@[expose] def sizeN (n : Nat) : Nat := if n = 0 then 0 else Nat.log2 n + 1

/-- The bytes of `n` (`Sampler.byteLen`). -/
@[expose] def byteLenN (n : Nat) : Nat := (sizeN n + 7) / 8

/-- The stream bytes the extended stream adds (`fsExtraBytes`). -/
@[expose] def extraBytes : Nat := 206848

/-- The largest rounds of a configuration (`Configurations.maxRounds`). -/
@[expose] def maxRoundsN : Nat := 20795

/-- `Export.hashBytes`. -/
@[expose] def hashBytesN (name : String) : Option Nat :=
  if name = "SHA-256" then some 32 else if name = "SHA-384" then some 48 else none

/-! ## The samplers -/

/-- `samplerOk`. -/
@[expose] def samplerOkB (rd : LoadN) (c : Nat) : Sampler → Bool
  | .full => true
  | .node _ => false
  | .fieldMinusTables (.range T) => decide (2 * (rd.1 + 1) * 3 ^ rd.1 * T ≤ c)
  | .fieldMinusTables (.packedRows _) => true
  | .fieldMinusTables (.union _ _) => true

/-- `samplerLoad`. -/
@[expose] def samplerLoadN (rd : LoadN) : Sampler → LoadN
  | .fieldMinusTables (.range _) => (rd.1 + 2, 2 * rd.2)
  | _ => rd

/-! ## Fractions -/

/-- `fracSum`. -/
@[expose] def fracSumN : List (Nat × Nat) → Nat × Nat
  | [] => (0, 1)
  | p :: L => (p.1 * (fracSumN L).2 + (fracSumN L).1 * p.2, p.2 * (fracSumN L).2)

/-- `dyadicCeil`. -/
@[expose] def dyadicCeilN (e : Nat) (p : Nat × Nat) : Nat := (p.1 * 2 ^ e + p.2 - 1) / p.2

/-- The falling factorial `n (n − 1) ⋯ (n − k + 1)` (`Nat.descFactorial`). -/
@[expose] def descFac (n : Nat) : Nat → Nat
  | 0 => 1
  | k + 1 => (n - k) * descFac n k

/-! ## The program's challenges and phases -/

variable (ir : RealizedProgram)

/-- The challenges of phase `k + 1` (`chalList`). -/
@[expose] def chalsOf (k : Nat) : List Nat :=
  (List.range ir.challenges.length).filter fun j => (ir.challenge j).phase == k + 1

/-- `IsSourceChal`. -/
@[expose] def isSourceChal (j : Nat) : Bool :=
  decide (j < ir.challenges.length) && decide (1 ≤ (ir.challenge j).phase) &&
    decide ((ir.challenge j).phase ≤ ir.phases) && ir.chalIsSource j

/-- `realGroups`. -/
@[expose] def realGroupsN (j : Nat) : List (Nat × Nat) :=
  ((List.range ir.tables.length).filter fun t => ir.alphaOf t = j).flatMap fun t =>
    (List.range (ir.groupCountOf t)).map fun g => (t, g)

/-- `macChunksOf`. -/
@[expose] def macChunksOfN (j p : Nat) : Option Nat :=
  match (ir.predicate p).body with
  | .cross _ _ _ _ _ real => if real.key = j then some real.chunks else none
  | _ => none

/-- `realErrorTerms`. -/
@[expose] def realErrorTermsN (j : Nat) : List (Nat × Nat) :=
  ((realGroupsN ir j).map fun tg => (ir.groupCount tg.1 tg.2 + ir.tableSize tg.1 - 1, ir.tmaxOf j)) ++
    ((List.range ir.predicates.length).filterMap (macChunksOfN ir j)).map (fun n => (n, ir.tmaxOf j)) ++
    (List.range ir.predicates.length).filterMap fun q =>
      (ir.kernelSel? q).bind fun sh => if sh.chal = j then some (sh.deg, ir.tmaxOf j) else none

/-- **The terms of phase `k + 1`'s error** (`phaseTerms`) on fields of `cf f` elements. -/
@[expose] def phaseTermsN (cf : Nat → Nat) (src : Nat → Nat × Nat) (k : Nat) : List (Nat × Nat) :=
  (chalsOf ir k).flatMap fun j =>
    (if isSourceChal ir j then [src j] else []) ++
      [(((realErrorTermsN ir j).map Prod.fst).sum, cf (ir.chalField j) - ir.tmaxOf j)]

/-- **Every phase's error within `num / 2^e`** (`PhaseErrorsOk`). -/
@[expose] def phaseErrorsB (cf : Nat → Nat) (src : Nat → Nat × Nat) (num e : Nat) : Bool :=
  (List.range ir.phases).all fun k =>
    (phaseTermsN ir cf src k).all (fun p => decide (0 < p.2)) &&
      decide ((fracSumN (phaseTermsN ir cf src k)).1 * 2 ^ e ≤
        num * (fracSumN (phaseTermsN ir cf src k)).2)

/-- **The largest load of a challenge** (`stdChalLoad`) at the fields' reader loads `rdl`. -/
@[expose] def chalLoadN (rdl : Nat → LoadN) : LoadN :=
  ((List.range ir.challenges.length).map fun j =>
      nsmulL (ir.challenge j).size (samplerLoadN (rdl (ir.chalField j)) (ir.challenge j).sampler)).foldr
    maxL (0, 0)

/-- **The readers' test** (`ReadersOk`) at the fields' reader loads and sizes. -/
@[expose] def readersB (rdl : Nat → LoadN) (cf : Nat → Nat) : Bool :=
  (List.range ir.challenges.length).all fun j =>
    samplerOkB (rdl (ir.chalField j)) (cf (ir.chalField j)) (ir.challenge j).sampler

/-- **The bytes of phase `k + 1`'s message** (`msgB`) at the fields' element bytes `fb`. -/
@[expose] def msgN [r : PReader] (fb : Nat → Nat) (k : Nat) : Nat :=
  9 + ((List.range r.nValues).map fun v =>
    if decide (PReader.IsLate ir v) && (r.value v).phase - 1 == k then
      9 + (r.value v).size * fb (ir.valueField v)
    else 0).sum

/-! ## A domain's figures -/

/-- **A domain's numbers for the figures**: its forked proof's (`ForkReader.DomainNums`) and grants
(`ForkGrants`), its tableau's, its field's element bytes, reader load and grant and size, its largest array and read,
and its reads besides its first combination. -/
structure DomainFig where
  N : ForkReader.DomainNums
  t : TableauNums
  fb : Nat
  load : LoadN
  grant : Nat
  grants : ForkGrants
  q : Nat
  Mx : Nat
  Lmax : Nat
  Lr : Nat

namespace DomainFig

variable (x : DomainFig)

/-- `forkRoundsAt`: the batches' rounds, one per circuit, the join's and every circuit's. -/
@[expose] def rounds : Nat :=
  (x.N.batches.map fun b =>
      2 * b.rounds + 5 + (if b.bits then 8 else 0) + (if b.merged then 1 else 0)).sum +
    x.N.circuits.length + (2 * x.N.degrees.length + 3) +
    (x.N.circuits.map fun c => (2 + 4 * c.1) * c.2 + 1).sum

/-- The branches: one per covered batch, then GKR (`nBranch`). -/
@[expose] def branches : Nat := x.N.batches.length + 1

/-- `ForkNumbers.leafBytes`. -/
@[expose] def leafBytes : Nat := (9 + (x.t.nrep + x.Lmax) * x.fb) + ((1 + x.fb) + (1 + x.fb))

/-- `batchesNum`. -/
@[expose] def batchesNum : Nat :=
  (x.N.batches.map fun b =>
      b.rounds + b.degree * (b.width - 1) + (b.degree + 1) * b.rounds + 1 +
        (if b.merged then b.parts - 1 else 0) + (if b.bits then 2 * 4 else 0)).sum

/-- `gkrWidth`. -/
@[expose] def gkrWidth : Nat := (x.N.circuits.map (·.1)).foldr max 0

/-- `LigeroCert.columnNum` with the mask test. -/
@[expose] def columnNum : Nat := descFac (x.t.agree - 1) x.t.nreq + descFac (2 * x.t.block - 1) x.t.nreq

/-- `LigeroCert.jointNum`. -/
@[expose] def jointNum : Nat := descFac (x.t.block - 1) x.t.nreq

/-- `LigeroCert.columnDen`. -/
@[expose] def columnDen : Nat := descFac x.t.N x.t.nreq

/-- **The round charges as fractions** (`FieldReady.chargeFracs`) with the mask test. -/
@[expose] def chargeFracs : List (Nat × Nat) :=
  [(x.t.exceptions ^ x.t.nrep, (x.q - 1) ^ x.t.nrep), (1, x.q),
    (x.columnNum + (if x.N.np = 0 then 0 else x.jointNum), x.columnDen), (x.batchesNum, x.q),
    (max 3 (2 * x.gkrWidth), x.q), (x.N.degrees.length, x.q)]

/-- **The round charges within `num / 2^e`** (`FieldRoundsOk`), with the mask test. -/
@[expose] def fieldRoundsB (num e : Nat) : Bool :=
  x.t.split &&
  decide (x.t.exceptions ^ x.t.nrep * 2 ^ e ≤ num * (x.q - 1) ^ x.t.nrep) && decide (0 < x.q) &&
    decide (1 * 2 ^ e ≤ num * x.q) && decide (0 < x.columnDen) &&
    decide ((x.columnNum + if x.N.np = 0 then 0 else x.jointNum) * 2 ^ e ≤ num * x.columnDen) &&
    decide (x.batchesNum * 2 ^ e ≤ num * x.q) &&
    decide (max 3 (2 * x.gkrWidth) * 2 ^ e ≤ num * x.q) &&
    decide (x.N.degrees.length * 2 ^ e ≤ num * x.q)

/-- `restGood` at the Chernoff exponent `E` and the digest length `k`. -/
@[expose] def restGoodB (E k : Nat) : Bool :=
  chernoffB E (k + extraBytes) (maxL (nsmulL x.Lr x.load) (x.t.nreq, byteLenN x.t.N))

/-- `stageGood`, including the first combination's stream grant. -/
@[expose] def stageGoodB (E k : Nat) : Bool :=
  chernoffB E (k + extraBytes + x.grants.stage 0) (nsmulL x.N.claims x.load)

/-- **A sufficient check for the largest stage grant.** Every visited stage after the first
must grant zero. A nonzero first-stage grant requires at least two touching claims, certified
using the passing-claim bound `DomainNums.later`. Unvisited stage values and the linear grant
are unrestricted. -/
@[expose] def grantsB : Bool :=
  (List.range x.N.degrees.length).all (fun i => i == 0 || x.grants.stage i == 0) &&
    (x.grants.stage 0 == 0 ||
      (decide (0 < x.N.degrees.length) && decide (2 + x.N.later ≤ x.N.claims)))

/-- **The join's largest grant** when `grantsB` holds. -/
@[expose] def joinGrant : Nat := max (x.grants.stage 0) x.grants.linear

/-- `DefaultLoadsOk` at one domain. -/
@[expose] def defaultGoodB (E k : Nat) : Bool :=
  chernoffB E (k + extraBytes) (maxL (nsmulL x.Lmax x.load) (x.t.nreq, byteLenN x.t.N))

end DomainFig

/-! ## The program's figures -/

variable (ds : List DomainFig)

/-- `forkRoundsTotal`. -/
@[expose] def roundsTotal : Nat := 1 + (2 * ds.length + 2 * ir.phases) + (ds.map (·.rounds)).sum

/-- `figLeaves`. -/
@[expose] def leaves : Nat := (ds.map (·.t.N)).foldr max 0

/-- `figQueries`. -/
@[expose] def queries : Nat := (ds.map (·.t.nreq)).sum

/-- `figKq`. -/
@[expose] def kqN : Nat :=
  2 * roundsTotal ir ds + (ds.map (·.branches)).sum + queries ds * (1 + Nat.log2 (2 * leaves ds))

/-- `figDigests`. -/
@[expose] def digestsN : Nat :=
  max 2 (roundsTotal ir ds * ds.length) + (ds.map (·.branches)).foldr max 0 + 1

/-- `figPos`. -/
@[expose] def posN : Nat := (ds.map (·.t.N)).sum

/-- **The largest round error**, in units of `2^-e`, rounded up. -/
@[expose] def errorMaxN (cf : Nat → Nat) (src : Nat → Nat × Nat) (e : Nat) : Nat :=
  max ((ds.map fun x => (x.chargeFracs.foldr
      (fun p m => max (dyadicCeilN e p) m) 0)).foldr max 0)
    (((List.range ir.phases).map fun k =>
      dyadicCeilN e (fracSumN (phaseTermsN ir cf src k))).foldr max 0)

/-- **The figures' check** (`ProgramFigures.Check`, `FitsOk`, the messages' bound, `ReadersOk`
and `DefaultLoadsOk`) on the numbers: the domains `ds`, the plan's hash `hash`, the fields' reader
loads `rdl` and sizes `cf`, and the figures' data `F`. Each join's grants pass `DomainFig.grantsB`; the field readers grant
none, and the transcript's largest grant is the largest join grant. -/
@[expose] def figuresB [PReader] (hash : String) (rdl : Nat → LoadN) (cf : Nat → Nat) (fb : Nat → Nat)
    (F : FiguresData) : Bool :=
  let G := F.figures
  readersB ir rdl cf &&
  ds.all (fun x => x.N.fitsB x.t x.fb x.Mx x.Lmax) &&
  (List.range ir.phases).all (fun k => decide (msgN ir fb k ≤ 2 ^ 20)) &&
  decide (G.rounds = roundsTotal ir ds) && decide (G.N = leaves ds) &&
  decide (G.nq = queries ds) && decide (G.kq = kqN ir ds) && decide (G.D = digestsN ir ds) &&
  decide (G.pos = posN ds) && decide (G.kq ≤ 2 ^ 16) && hashBytesN hash == some G.k &&
  decide (0 < G.k) && decide (G.k ≤ 2 ^ 10) &&
  decide (ds.length ≤ 2 ^ 8) && ds.all (fun x => decide (x.branches ≤ 2 ^ 8)) &&
  ds.all (fun x => decide (x.leafBytes ≤ 2 ^ 40)) && decide (roundsTotal ir ds ≤ maxRoundsN) &&
  ds.all (fun x => x.grant == 0) &&
  ds.all (·.grantsB) && F.grantMax == (ds.map (·.joinGrant)).foldr max 0 &&
  ds.all (fun x => x.N.restB x.t x.Lr) &&
  ds.all (fun x => x.restGoodB G.chernoff G.k) &&
  ds.all (fun x => x.stageGoodB G.chernoff G.k) &&
  (List.range ir.phases).all (fun k =>
    chernoffB G.chernoff (G.k + extraBytes) (nsmulL (chalsOf ir k).length (chalLoadN ir rdl))) &&
  ds.all (fun x => x.fieldRoundsB G.errorMax G.errorExp) &&
  phaseErrorsB ir cf F.sourceErrors G.errorMax G.errorExp &&
  decide (G.errorMax = errorMaxN ir ds cf F.sourceErrors G.errorExp) &&
  (!F.defaultLoads || ds.all (fun x => x.defaultGoodB G.chernoff G.k))

end FigCheck

end GordieHowe.RealizedProgram
