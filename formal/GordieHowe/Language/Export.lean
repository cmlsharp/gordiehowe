-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

@[expose] public section

/-!
# GordieHowe: the plan data schema

The schema of the generated plan files `GordieHowe/Generated/<Scheme>/<Arm>/<Params>/Plan.lean`. The
C++ writes one such file per configuration from a bench binary: a single `def` of type
`GordieHowe.RealizedProgram.Export.Plan` holding the compiled plan and its parameters. The files hold data only (no proofs,
no tactics); the plan-level validity (`Plan.Valid`, `GordieHowe/Language/Export/Valid.lean`) checks the planner's
conditions on it by `decide` (admissibility, certificates, needle counts).

Lists are in the C++ order (declaration order for requests, node-id order for challenges, message
order for messages). Names are the C++ node or constraint names. Sizes are counts and structured
ranges; nothing here is per cell or per needle.

Changing a field's meaning, renaming or removing a field or constructor increments `schemaVersion`;
adding a field with a default does not. From version 2 on, the packing modes are `squaringChain`
and `subfieldMasks` and the Ligero data has no field `A`. From version 3 on, the Ligero data has
the field `ldtReps`, the number of repetitions of the low-degree test (absent means one).
-/

namespace GordieHowe.RealizedProgram.Export

/-! ## Fields -/

/-- One step of a tower basis: a variable `x` of degree `degree` over the previous steps, with
`x ^ degree = Σ coeff · Π vars ^ exps`, the exponents listed over the previous steps' variables and
then `x` itself (each below its step's degree). `u^4 = 11` is `⟨"u", 4, [(11, [0])]⟩`; over it,
`v^5 = u + 2` is `⟨"v", 5, [(1, [1, 0]), (2, [0, 0])]⟩`. -/
structure TowerStep where
  /-- The variable's name. -/
  name : String
  /-- Its degree over the previous steps. -/
  degree : Nat
  /-- The defining relation's terms `(coefficient, exponents)`. -/
  relation : List (Int × List Nat)
  deriving Repr, DecidableEq

/-- A field as the C++ declares it. -/
structure FieldSpec where
  /-- The C++ name (`GF2_256`, `Goldilocks4`, …). -/
  name : String
  /-- The characteristic. -/
  characteristic : Nat
  /-- The degree over the prime field. -/
  degree : Nat
  /-- The defining polynomial's nonzero exponents, highest first (`[256, 10, 5, 2, 0]`); empty for a
  prime field. For an extension of a prime field other than `GF(2)`, the coefficients follow in
  `modulusCoeffs`. -/
  modulus : List Nat := []
  /-- The defining polynomial's coefficients matching `modulus`, if not all `1`. -/
  modulusCoeffs : List Nat := []
  /-- A tower basis over the prime field, innermost step first; when nonempty it replaces
  `modulus` (the field is the tower's top). -/
  tower : List TowerStep := []
  deriving Repr, DecidableEq

/-! ## Domains -/

/-- How a packing edge makes the Frobenius twists of its masks available to the rows. -/
inductive PackingMode where
  /-- Squaring-chain masks: the mask's Frobenius twists are committed by a chain of squarings. -/
  | squaringChain
  /-- Subfield masks: subfield-valued masks in the prefix rows, checked by the prefix-row subfield
  test. -/
  | subfieldMasks
  deriving Repr, DecidableEq

/-- One edge of a domain's packing tree. -/
structure PackingEdge where
  /-- The child node (a declared subfield, or `bit`). -/
  child : String
  /-- The parent node. -/
  parent : String
  /-- The mode. -/
  mode : PackingMode
  /-- The relative degree `[parent : child]`. -/
  degree : Nat
  /-- The masked measurements of this stage. -/
  measurements : Nat
  /-- The mask coordinates of this stage. -/
  masks : Nat
  /-- The squaring-chain cells (`squaringChain` mode only). -/
  chainCells : Nat := 0
  /-- The child node's degree over the prime field (`0`: not exported). -/
  childDegree : Nat := 0
  /-- The parent node's degree over the prime field (`0`: not exported). -/
  parentDegree : Nat := 0
  /-- The child is a declared subfield (`false`: an intermediate node the planner added). -/
  declared : Bool := true
  /-- The rows routed to this stage (`TreePlan::routed`, `tree_zk.h:1146`): input, GKR, affine,
  remainder and child measurement rows. `0` on the root's children, whose stages the root runs. -/
  routedRows : Nat := 0
  deriving Repr, DecidableEq

/-- How a Ligero tableau masks its responses. -/
inductive MaskingKind where
  | listRadius
  | split
  | uniqueDecoding
  deriving Repr, DecidableEq

/-- A domain's Ligero tableau. -/
structure Ligero where
  /-- The rate parameter. -/
  rate : Nat
  /-- `block_enc`. -/
  blockEnc : Nat
  /-- The block length `N`. -/
  N : Nat
  /-- The code dimension `k`. -/
  k : Nat
  /-- The opened columns `t`. -/
  t : Nat
  /-- The blinding width `r`. -/
  r : Nat
  /-- The committed rows. -/
  nrow : Nat
  /-- The masking. -/
  masking : MaskingKind
  /-- The number of repetitions of the low-degree test (`ldtReps`; the export writes it only when it
  is above one). -/
  ldtReps : Nat := 1
  deriving Repr, DecidableEq

/-- A category of committed coordinates: a contiguous range of one kind. -/
structure CoordRange where
  /-- The C++ node name. -/
  name : String
  /-- The first coordinate. -/
  offset : Nat
  /-- The number of coordinates. -/
  length : Nat
  /-- The cell type (`Bit`, `Subfield`, `Field`) as the C++ resolves it. -/
  cellType : String
  /-- The storage class (`committed`, `public`, `pad`, `view`). -/
  storage : String
  /-- The phase. -/
  phase : Nat := 0
  deriving Repr, DecidableEq

/-- A domain circuit's size. -/
structure CircuitStats where
  /-- The constraint name. -/
  name : String
  /-- The GKR layers. -/
  layers : Nat
  /-- The wires. -/
  wires : Nat
  /-- The quadratic terms. -/
  quadTerms : Nat
  deriving Repr, DecidableEq

/-- A batched relation. -/
structure Batch where
  /-- The batch name. -/
  name : String
  /-- The operand field (a node of the packing tree). -/
  operandField : String
  /-- The relation's arity `K`. -/
  arity : Nat
  /-- The relation's degree `D`. -/
  degree : Nat
  /-- The instances. -/
  instances : Nat
  /-- The skip width. -/
  width : Nat
  /-- The sumcheck rounds. -/
  rounds : Nat
  /-- The pads. -/
  pads : Nat
  /-- The merge group, if merged as `Σ γ^i Q_i` (members share a label). -/
  mergeGroup : Option String := none
  /-- The calls sharing this batch (name, instances), in instance order; empty for one call. -/
  calls : List (String × Nat) := []
  deriving Repr, DecidableEq

/-- An internal Fiat–Shamir point whose stream the C++ extends (`extend_point_budget_for`): a
packing stage's combination, the root combination, or Ligero's linear-test coefficients
(`gen_alphal`). -/
structure StreamPoint where
  /-- The point (`stage:<child>`, `root`, `ligero.alphal`). -/
  name : String
  /-- The rows combined at the point, `n_i`. -/
  rows : Nat
  /-- The stream length `N_i = k + kFSStreamExtraBytes + 4 · n_i · F::kBytes`, in bytes. -/
  streamBytes : Nat
  deriving Repr, DecidableEq

/-- Where an unpacked domain checks a `Bit` cell's Booleanity `x(x − 1) = 0`. -/
inductive BitCheckPlacement where
  /-- As a quadratic triple of the commitment. -/
  | triple
  /-- As a circuit constraint of the domain's GKR circuit. -/
  | circuit
  deriving Repr, DecidableEq

/-- The Boolean checks of one node's `Bit` cells in an unpacked domain. -/
structure BitCheck where
  /-- The node. -/
  node : String
  /-- The cells checked. -/
  cells : Nat
  /-- The placement, chosen by the profile's cell/term cost ratio. -/
  placement : BitCheckPlacement
  deriving Repr, DecidableEq

/-- **A placement target** (`placement.h`, `Placement`): where a predicate group is realized. -/
inductive PlacementTarget where
  /-- As affine rows of the commitment. -/
  | affine
  /-- As quadratic triples of the commitment. -/
  | quadratic
  /-- In a batch of the domain (`Placement.batch` names it). -/
  | batch
  /-- As constraints of the domain's GKR circuit. -/
  | circuit
  deriving Repr, DecidableEq

/-- **A placed predicate group** (`plan_export.h`, `DomainPlan::Placed`): its name, its target, the
number of same-shaped predicates merged into it, its instances and, for a batch target, the batch.
The program's per-predicate targets (`RealizedProgram.TargetsAdmit`) subsume it. -/
structure Placement where
  /-- The group's name. -/
  name : String
  /-- The target. -/
  target : PlacementTarget
  /-- The predicates merged into the group (the export omits `1`). -/
  predicates : Nat := 1
  /-- The instances. -/
  instances : Nat
  /-- The batch, for a batch target (`""` otherwise). -/
  batch : String := ""
  deriving Repr, DecidableEq

/-- One field domain. -/
structure Domain where
  /-- The domain name (`H`, `A`). -/
  name : String
  /-- The field. -/
  field : FieldSpec
  /-- The declared subfields, by name. -/
  subfields : List FieldSpec
  /-- The subfield that holds the masks (the prefix-row test's subfield). -/
  maskingSubfield : String
  /-- The `DomainProfile::prime` setting. -/
  prime : String
  /-- The Ligero tableau. -/
  ligero : Ligero
  /-- The packing tree. -/
  packing : List PackingEdge
  /-- The committed coordinates by category. -/
  coords : List CoordRange
  /-- The circuit inputs. -/
  inputs : Nat
  /-- The public inputs. -/
  publicInputs : Nat
  /-- The circuit constraints. -/
  circuits : List CircuitStats
  /-- The circuit's id. -/
  circuitId : String
  /-- The affine rows, by constraint name and count. -/
  affineRows : List (String × Nat)
  /-- The quadratic triples. -/
  quadTriples : Nat
  /-- The batches. -/
  batches : List Batch
  /-- The internal Fiat–Shamir points with extended streams, in transcript order. -/
  streamPoints : List StreamPoint := []
  /-- The integer bound the no-wrap certificates of this domain use (`characteristic_floor`):
  the C++ exporter writes the characteristic `p`; `0` means the characteristic. -/
  characteristicFloor : Nat := 0
  /-- Boolean checks of `Bit` cells in an unpacked domain, by node and placement. -/
  bitChecks : List BitCheck := []
  /-- The placement of each predicate group (emitted only when nonempty). -/
  placements : List Placement := []
  deriving Repr, DecidableEq

/-! ## The range plan -/

/-- An operand of an integer-affine expression. -/
inductive Term where
  /-- A node's value (coordinatewise). -/
  | node (name : String)
  /-- The sum of a node's coordinates. -/
  | sum (name : String)
  /-- The output of a named operator node. -/
  | op (name : String)
  deriving Repr, DecidableEq

/-- An integer-affine expression over named operands: `Σ coeffs[i] · operands[i] + const`. -/
structure IntAffine where
  /-- The operand node names (plain node values); superseded by `terms` when that is nonempty. -/
  operands : List String := []
  /-- The operands as terms, one per coefficient; when nonempty it replaces `operands`. -/
  terms : List Term := []
  /-- The coefficients, one per operand. -/
  coeffs : List Int
  /-- The constant term. -/
  const : Int
  /-- Per-coordinate constants, if they differ across coordinates (then `const` is unused). -/
  coordConsts : List Int := []
  deriving Repr, DecidableEq

/-- A range realization's kind. -/
inductive RealizationKind where
  | direct
  | directLate
  | shifted
  | scaled
  | digits
  | twoSided
  | implied
  | complement
  deriving Repr, DecidableEq

/-- How a request is realized. -/
structure Realization where
  /-- The kind. -/
  kind : RealizationKind
  /-- The index in `Plan.tables` of the table entry (one entry per range group). -/
  table : Nat := 0
  /-- The group index within its domain's lookup; equals that entry's `Table.group`. -/
  group : Nat := 0
  /-- The limbs (digits, two-sided). -/
  limbs : Nat := 0
  /-- The scale `c` (scaled). -/
  scale : Nat := 0
  /-- The shift `T − n` (shifted). -/
  shift : Nat := 0
  /-- The interval's lower end over the operands' bounds (implied, complement). -/
  intervalLo : Int := 0
  /-- The interval's upper end (implied, complement). -/
  intervalHi : Int := 0
  /-- The proven (established) bound. -/
  bound : Nat
  /-- Static needles per coordinate. -/
  staticNeedles : Nat
  /-- Late needles per coordinate. -/
  lateNeedles : Nat
  deriving Repr, DecidableEq

/-- A range request `expr < n` (or in `[n, m]` with slack), with its realization. -/
structure Request where
  /-- The request name. -/
  name : String
  /-- The domain. -/
  domain : String
  /-- The coordinates. -/
  dim : Nat
  /-- The expression. -/
  expr : IntAffine
  /-- The honest bound `n`. -/
  honest : Nat
  /-- The largest admissible bound `m` (`MaxBound`). -/
  max : Nat
  /-- The phase of the latest operand. -/
  phase : Nat
  /-- The realization. -/
  realization : Realization
  deriving Repr, DecidableEq

/-- A storage binding: `value` is read as its view. -/
inductive BindingKind where
  | digits
  | offset
  deriving Repr, DecidableEq

/-- A storage binding. -/
structure Binding where
  /-- The bound value's node. -/
  value : String
  /-- The request whose digits it reads (digits). -/
  request : String := ""
  /-- The kind. -/
  kind : BindingKind
  /-- The offset `c` in `x + c` (offset). -/
  offset : Int := 0
  deriving Repr, DecidableEq

/-- How a table's histogram is committed. -/
inductive HistogramForm where
  /-- A committed histogram `m0` for the static needles and a late `m1` for the late ones. -/
  | split
  /-- One late histogram for all needles. -/
  | lateOnly
  deriving Repr, DecidableEq

/-- A lookup table of a domain (one range group of it, when the table is split). -/
structure Table where
  /-- The table or group label. -/
  name : String := ""
  /-- The domain. -/
  domain : String
  /-- The group index within the domain's range lookup. -/
  group : Nat := 0
  /-- The group's needle capacity (`0`: unbounded). -/
  capacity : Nat := 0
  /-- The histogram form. -/
  histogram : HistogramForm := .split
  /-- The table `[0, size)`. -/
  size : Nat
  /-- The late histogram's support `Sdyn`. -/
  sdyn : Nat
  /-- The static needles. -/
  staticNeedles : Nat
  /-- The late needles. -/
  lateNeedles : Nat
  /-- The challenge's label. -/
  challenge : String
  deriving Repr, DecidableEq

/-! ## Lowerings -/

/-- How a MAC's accumulator tail is realized. -/
inductive MacTail where
  | constant
  | bit
  | oneDigit
  | digits
  deriving Repr, DecidableEq

/-- A MAC equality. -/
structure MAC where
  /-- The label. -/
  name : String
  /-- The domain holding `U` and `T`. -/
  tagDomain : String
  /-- The domain holding the accumulator rows. -/
  accDomain : String
  /-- The vector width `w`. -/
  width : Nat
  /-- The chunks `nch`. -/
  nch : Nat
  /-- The basis taps. -/
  taps : List Nat
  /-- `convMax`. -/
  convMax : Nat
  /-- `acc_max`. -/
  accMax : Nat
  /-- The limb radix bits `e` (when the radix is `2^e`). -/
  radixBits : Nat := 0
  /-- The high limb's coefficient in `acc = bits(T) + 2·low + radix·high`, so `radix = 2·nLow`
  (`2^e` for Falcon, `2·116 = 232` for ML-DSA); `0` means `2^radixBits`. -/
  radix : Nat := 0
  /-- The tail's quotient form. -/
  tail : MacTail := .constant
  /-- The tail's digits (for `digits`). -/
  tailDigits : Nat := 0
  /-- Per group, the chunk range `(first, count)` (grouped form; empty for one group). -/
  groupChunks : List (Nat × Nat) := []
  /-- The tail quotient's digits (grouped form). -/
  quotientDigits : Nat := 0
  /-- The tail quotient's digit base (grouped form). -/
  quotientBase : Nat := 0
  /-- The per-group accumulator bound (grouped form). -/
  groupBound : Nat := 0
  /-- The member equalities of a merged MAC, by name or, for an unnamed view, its node name
  (empty for a single equality). -/
  members : List String := []
  /-- The groups (1 for the single-group form). -/
  groups : Nat := 1
  /-- `n_low`. -/
  nLow : Nat
  /-- `n_high`. -/
  nHigh : Nat
  /-- The challenge's label. -/
  challenge : String
  deriving Repr, DecidableEq

/-- An ordered selection's scan. -/
inductive SelectionKind where
  | fixedCutoff
  | risingThreshold
  deriving Repr, DecidableEq

/-- An ordered selection. -/
structure Selection where
  /-- The label. -/
  name : String
  /-- The domain. -/
  domain : String
  /-- The kind. -/
  kind : SelectionKind
  /-- The candidates `S`. -/
  candidates : Nat
  /-- The outputs `n`. -/
  outputs : Nat
  /-- The sample width in bits. -/
  width : Nat
  /-- The cutoff (fixed) or `τ` (rising). -/
  bound : Nat
  /-- The challenge's label. -/
  challenge : String
  deriving Repr, DecidableEq

/-- A SampleInBall (ML-DSA): the challenge polynomial's record permutation. -/
structure SampleInBall where
  /-- The label. -/
  name : String
  /-- The domain. -/
  domain : String
  /-- The weight `τ`. -/
  tau : Nat
  /-- The records of the permutation (the larger side's count; the degree the C++ charges). -/
  records : Nat
  /-- The fields per record. -/
  arity : Nat := 0
  /-- The records that are public constants (not committed). -/
  constRecords : Nat := 0
  /-- The challenge's label. -/
  challenge : String
  deriving Repr, DecidableEq

/-- How a modular equality's quotient is realized. -/
inductive ModQuotient where
  /-- A constant quotient (no committed digits). -/
  | constant
  /-- The modulus is the characteristic: the field equality itself. -/
  | fieldEquality
  /-- A Bit quotient. -/
  | bit
  /-- A digit decomposition of the quotient. -/
  | digits
  deriving Repr, DecidableEq

/-- A modular equality `expr ≡ 0 (mod modulus)` (`assert_mod`). -/
structure ModEquality where
  /-- The label. -/
  name : String
  /-- The domain. -/
  domain : String
  /-- The modulus. -/
  modulus : Nat
  /-- The expression. -/
  expr : IntAffine
  /-- The coordinates. -/
  dim : Nat := 1
  /-- The quotient's realization. -/
  quotient : ModQuotient
  /-- The quotient's digits and base (digits; a single derived digit is one digit in base
  `Qmax + 1`). -/
  digits : Nat := 0
  base : Nat := 0
  /-- The top digit is derived from the others rather than committed (digits). -/
  topDerived : Bool := false
  /-- The integer interval of `expr` the lowering relies on. -/
  intervalLo : Int := 0
  intervalHi : Int := 0
  deriving Repr, DecidableEq

/-- A gadget's or a `certify` condition's parameters, by name (`B`, `La`, `Wc`, `betaSq`,
`high_from`, …). The instance file reads them by name. A `certify` condition has `lhs`, `rhs` and
`op` (`0` for `<`, `1` for `≤`, `2` for `=`). -/
structure GadgetParams where
  /-- The label. -/
  name : String
  /-- The gadget kind (`native-norm`, `certify`, …). -/
  kind : String
  /-- The domain. -/
  domain : String
  /-- The parameters. -/
  params : List (String × Int)
  deriving Repr, DecidableEq

/-- One window of a filtered permutation: `len` bytes read at a private offset in `[first, last]` of
the message. The C++ exports `last = end − len`, where the message records cover the bytes
`[first, end)` (`match_windows`, `lib/gordiehowe/lib/windows.h`). -/
structure PermWindow where
  /-- The window's node. -/
  name : String
  /-- Its length `L`. -/
  len : Nat
  /-- The least allowed offset. -/
  first : Nat
  /-- The greatest allowed offset. -/
  last : Nat
  deriving Repr, DecidableEq

/-- A filtered permutation (`match_windows`, through `assert_filtered_multiset_equal`): message
records `(α^i, byte_i, f_i)` against window records `(κ·α^j, w_j, 1)` with `κ = α^offset` committed
in the offset field. The no-wrap condition is `end − first + L ≤ 2^bits − 1` per window, with `end`
exclusive (the header comment of `lib/gordiehowe/lib/windows.h`); in the exported fields it is
`last − first + 2 · len ≤ 2^bits − 1`, since `last = end − len`. -/
structure FilteredPermutation where
  /-- The label. -/
  name : String
  /-- The domain. -/
  domain : String
  /-- The message node. -/
  message : String
  /-- The message length in bytes. -/
  messageLen : Nat
  /-- The windows. -/
  windows : List PermWindow
  /-- The field the offsets' powers `κ` are committed in (`GF(2^16)`). -/
  offsetField : String
  /-- The bit width of the position encoding (`16`). -/
  positionBits : Nat
  /-- The records on the message side and on the window side. -/
  messageRecords : Nat
  windowRecords : Nat
  /-- The challenge's label. -/
  challenge : String
  deriving Repr, DecidableEq

/-! ## Challenges and the transcript -/

/-- A challenge. -/
structure Challenge where
  /-- The label. -/
  label : String
  /-- The domain whose field it is drawn from. -/
  domain : String
  /-- The inferred phase. -/
  phase : Nat
  /-- The sampler (`field`, …). -/
  sampler : String
  /-- The degree bound the C++ charges for its event. -/
  degreeBound : Nat
  /-- The inferred tests, by node name. -/
  tests : List String
  /-- The XOF stream length this challenge node may squeeze, if extended; `0` means the default
  `k + kFSStreamExtraBytes`. Internal extended points are `Domain.streamPoints`. -/
  streamBytes : Nat := 0
  deriving Repr, DecidableEq

/-- A masked late message. -/
structure Message where
  /-- The value's node. -/
  name : String
  /-- The domain whose cells it masks. -/
  domain : String
  /-- The phase. -/
  phase : Nat
  /-- The elements. -/
  size : Nat
  /-- The bytes on the wire. -/
  bytes : Nat
  /-- The masking space (`Field`, `Subfield`). -/
  maskingSpace : String
  /-- The message lies in a packed subfield `E` (the verifier refuses an encoding outside `E`). -/
  subfieldMessage : Bool := false
  /-- The pad's packing-tree node, named as `PackingEdge.child`; `""`: the space `maskingSpace`
  names. -/
  padSpace : String := ""
  deriving Repr, DecidableEq

/-! ## The plan -/

/-- **A compiled GordieHowe plan** of one configuration. -/
structure Plan where
  /-- The schema version it was written against. -/
  schemaVersion : Nat
  /-- The configuration's C++ name (`mldsa-native-narrow` for `MLDSA44.Native.ROMParams`, …). -/
  config : String
  /-- The C++ commit of the bench binary. -/
  cppCommit : String
  /-- The bench run id. -/
  runId : String
  /-- The system digest (hex). -/
  digest : String
  /-- The message length in bytes. -/
  msgLen : Nat
  /-- The context string length in bytes (ML-DSA). -/
  ctxLen : Nat := 0
  /-- The protocol hash. -/
  hash : String
  /-- The phases. -/
  phases : Nat
  /-- The domains. -/
  domains : List Domain
  /-- The range requests, in declaration order. -/
  requests : List Request
  /-- The storage bindings. -/
  bindings : List Binding
  /-- The lookup tables. -/
  tables : List Table
  /-- The MAC equalities. -/
  macs : List MAC
  /-- The ordered selections. -/
  selections : List Selection
  /-- The SampleInBall permutations. -/
  sampleInBalls : List SampleInBall := []
  /-- The modular equalities. -/
  modEqualities : List ModEquality := []
  /-- Gadget parameters and `certify` conditions. -/
  gadgets : List GadgetParams := []
  /-- The filtered permutations. -/
  filteredPermutations : List FilteredPermutation := []
  /-- The challenges, in node-id order. -/
  challenges : List Challenge
  /-- The masked late messages, in message order. -/
  messages : List Message
  deriving Repr

/-! ## Lookups

Lookups by name over a plan's lists, for the hand-written instance files' checks. A lookup returns
the first entry of that name, or `none`. -/

/-- The domain named `name`. -/
def Plan.domain (P : Plan) (name : String) : Option Domain := P.domains.find? (·.name = name)

/-- The range request named `name`. -/
def Plan.request (P : Plan) (name : String) : Option Request := P.requests.find? (·.name = name)

/-- The radix of a MAC's accumulator limbs: `radix`, or `2^radixBits` when `radix` is `0`. -/
def MAC.radixValue (m : MAC) : Nat := if m.radix = 0 then 2 ^ m.radixBits else m.radix

/-! ## The extended Fiat–Shamir points -/

/-- **The row slots before a domain's first packing stage**: one per GKR layer of its circuits, the
input row (absent for a domain with no circuit, which runs no GKR), its affine rows and two
reduction rows per batch (`TreePlan::stream_rows`, `CompiledDomain::extra_rows`). -/
def Domain.firstSlots (d : Domain) : Nat :=
  (d.circuits.map (·.layers)).sum + (if d.circuits = [] then 0 else 1) +
    (d.affineRows.map (·.2)).sum + 2 * d.batches.length

/-- The inner packing stages: the edges whose parent is not the domain's field, in plan order
(`PackingTree::inner`). -/
def Domain.innerEdges (d : Domain) : List PackingEdge := d.packing.filter (·.parent ≠ d.field.name)

/-- The root's measurements: those of the edges into the domain's field (`TreePlan::root_m`). -/
def Domain.rootMeasurements (d : Domain) : Nat :=
  ((d.packing.filter (·.parent = d.field.name)).map (·.measurements)).sum

/-- **The inner stages with their row slots** from `slots` on: each stage paired with the slots so
far, the bound its combination is extended by; each stage adds its measurements to the slots,
whether or not it combines (`TreePlan::stream_rows`). -/
def stageSlots : List PackingEdge → Nat → List (PackingEdge × Nat)
  | [], _ => []
  | e :: es, slots => (e, slots) :: stageSlots es (slots + e.measurements)

/-- **The rows of the points after the stages**: when the root has children, the root combination
at the slots after every stage and Ligero's linear test at the root's measurements and its combined
row; otherwise Ligero's linear test at every slot (`TreePlan::stream_rows`). -/
def Domain.finalRows (d : Domain) : List Nat :=
  let slots := d.firstSlots + (d.innerEdges.map (·.measurements)).sum
  if d.packing.any (·.parent = d.field.name) then [slots, d.rootMeasurements + 1] else [slots]

/-- **The row slots of the inner stages that open a point**: the slots (`stageSlots`, from
`firstSlots`) of the stages two or more rows are routed to (`routedRows`), in stage order. A stage
that one row reaches runs that row without a weight (`TreePlan::stream_rows`). -/
def Domain.stageRows (d : Domain) : List Nat :=
  ((stageSlots d.innerEdges d.firstSlots).filter (2 ≤ ·.1.routedRows)).map (·.2)

/-- **The rows and length of a point of `n` rows** at the default budget `base` and `kBytes`-byte
field elements: `(n, base + 4 · n · kBytes)` (`extend_point_budget_for(n, F)`). -/
def pointOf (base kBytes n : Nat) : Nat × Nat := (n, base + 4 * n * kBytes)

/-- A domain's extended points as rows and lengths, in transcript order. -/
def Domain.pointRows (d : Domain) : List (Nat × Nat) :=
  d.streamPoints.map fun p => (p.rows, p.streamBytes)

/-- The stage points: the extended points before the last `finalRows.length`. -/
def Domain.stagePoints (d : Domain) : List (Nat × Nat) :=
  d.pointRows.take (d.streamPoints.length - d.finalRows.length)

/-- The final points: the last `finalRows.length` extended points. -/
def Domain.finalPoints (d : Domain) : List (Nat × Nat) :=
  d.pointRows.drop (d.streamPoints.length - d.finalRows.length)

/-- **A domain's extended points follow the C++ rule** (`TreePlan::stream_rows`) at the default
budget `base` and `kBytes`-byte field elements (`pointOf`). The points are, in transcript order, one
point for each inner stage that two or more rows are routed to, at its row slots (`stageRows`), then
the final points at `finalRows`. Every inner stage has a routed row: `TreePlan::route` adds no
measurement rows for a stage with none, and the verifier's measurement count then fails. -/
structure Domain.FollowsStreamRule (d : Domain) (base kBytes : Nat) : Prop where
  /-- Every inner stage has a routed row. -/
  routed : ∀ e ∈ d.innerEdges, 1 ≤ e.routedRows
  /-- The stage points are at `stageRows`. -/
  stages : d.stagePoints = d.stageRows.map (pointOf base kBytes)
  /-- The final points are at `finalRows`. -/
  final : d.finalPoints = d.finalRows.map (pointOf base kBytes)

theorem Domain.followsStreamRule_iff (d : Domain) (base kBytes : Nat) :
    d.FollowsStreamRule base kBytes ↔
      (∀ e ∈ d.innerEdges, 1 ≤ e.routedRows) ∧
      d.stagePoints = d.stageRows.map (pointOf base kBytes) ∧
      d.finalPoints = d.finalRows.map (pointOf base kBytes) :=
  ⟨fun h => ⟨h.routed, h.stages, h.final⟩, fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

instance (d : Domain) (base kBytes : Nat) : Decidable (d.FollowsStreamRule base kBytes) :=
  decidable_of_iff _ (d.followsStreamRule_iff base kBytes).symm

/-! ## The packing tree's shape and its edges' realizability -/

/-- **The degree of the domain's masking subfield** `S0` over the prime field: the declared
subfield named `maskingSubfield`, or the field itself (an unpacked domain). -/
def Domain.maskingDegree (d : Domain) : Nat :=
  ((d.subfields.find? (·.name = d.maskingSubfield)).map (·.degree)).getD d.field.degree

/-- **An edge's mode and counts follow the planner's rule** (`tree.h`) for a field of degree `n`
with masking subfield of degree `s0`, in characteristic 2 when `char2`, for a child of degree
`b = childDegree` and relative degree `d = degree`: squaring-chain masks exactly when `char2` and
(`b = 1` or `s0 ∤ b`), with `d` masks and `b · d(d − 1)/2` chain cells; subfield masks otherwise,
which need `s0 ∣ b` (`S0 ⊆ B`), with `d · (n / s0)` masks in the prefix and no chain cell. -/
def PackingEdge.EdgeCounts (n s0 : Nat) (char2 : Bool) (e : PackingEdge) : Prop :=
  match e.mode with
  | .squaringChain => char2 = true ∧ (e.childDegree = 1 ∨ ¬ s0 ∣ e.childDegree) ∧
      e.masks = e.degree ∧ e.chainCells = e.childDegree * (e.degree * (e.degree - 1) / 2)
  | .subfieldMasks => s0 ∣ e.childDegree ∧ ¬ (char2 = true ∧ e.childDegree = 1) ∧
      e.masks = e.degree * (n / s0) ∧ e.chainCells = 0

instance (n s0 : Nat) (char2 : Bool) (e : PackingEdge) : Decidable (e.EdgeCounts n s0 char2) := by
  unfold PackingEdge.EdgeCounts
  split <;> infer_instance

/-- **An edge is realizable** (`tree.h`, the planner's final check): the parent's degree is the
child's times the relative degree and divides the field's, the relative degree is at least 2, the
stage measures once per coordinate of its group, and the mode and counts follow the planner's rule
(`EdgeCounts`). -/
def PackingEdge.Realizable (n s0 : Nat) (char2 : Bool) (e : PackingEdge) : Prop :=
  e.parentDegree = e.childDegree * e.degree ∧ e.parentDegree ∣ n ∧ 2 ≤ e.degree ∧
    e.measurements = e.degree ∧ e.EdgeCounts n s0 char2

instance (n s0 : Nat) (char2 : Bool) (e : PackingEdge) : Decidable (e.Realizable n s0 char2) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _))

/-- **The domain's edges are realizable** where the exporter writes the degrees
(`childDegree ≠ 0`; the defaults `0` mean not exported). -/
def Domain.EdgesRealizable (d : Domain) : Prop :=
  ∀ e ∈ d.packing, e.childDegree ≠ 0 →
    e.Realizable d.field.degree d.maskingDegree (d.field.characteristic == 2)

instance (d : Domain) : Decidable d.EdgesRealizable :=
  inferInstanceAs (Decidable (∀ e ∈ d.packing, _))

/-- **The packing edges form a tree in processing order** (`tree.h`, `bottom_up`): no edge's child
is the field, each child has one edge, and every parent is the field or the child of a later edge
(children are processed before their parents, deepest first). -/
def Domain.IsTree (d : Domain) : Prop :=
  (∀ e ∈ d.packing, e.child ≠ d.field.name) ∧ (d.packing.map (·.child)).Nodup ∧
    ∀ i : Fin d.packing.length, d.packing[i].parent = d.field.name ∨
      ∃ j : Fin d.packing.length, i < j ∧ d.packing[j].child = d.packing[i].parent

instance (d : Domain) : Decidable d.IsTree :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **A domain's packing is well formed**: its edges form a tree in processing order (`IsTree`) and
every edge with exported degrees is realizable (`EdgesRealizable`). -/
structure Domain.WellFormed (d : Domain) : Prop where
  /-- The edges form a tree in processing order. -/
  isTree : d.IsTree
  /-- Every edge with exported degrees is realizable. -/
  edgesRealizable : d.EdgesRealizable

theorem Domain.wellFormed_iff (d : Domain) : d.WellFormed ↔ d.IsTree ∧ d.EdgesRealizable :=
  ⟨fun h => ⟨h.isTree, h.edgesRealizable⟩, fun h => ⟨h.1, h.2⟩⟩

instance (d : Domain) : Decidable d.WellFormed :=
  decidable_of_iff _ d.wellFormed_iff.symm

end GordieHowe.RealizedProgram.Export
