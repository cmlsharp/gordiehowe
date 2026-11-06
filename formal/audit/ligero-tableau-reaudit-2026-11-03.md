# Ligero tableau and layout audit, 2026-11-03

Scope: 25 declarations at source commit `c200ddb3a`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.MaskedPolynomialTest.maskCode` | 9729443351162732406 | 9436037791079581607 |
| `GordieHowe.GKR.LayeredCircuit.instDecidableEqPadIdx` | 8447559830241001942 | 5189235986104949681 |
| `GordieHowe.GKR.LayeredCircuit.instFintypePadIdx` | 10782152950780209617 | 8350266336368567747 |
| `GordieHowe.Ligero.Relative.Shape.mk` | 3435622811 | 1390493408 |
| `GordieHowe.Ligero.Relative.Shape.shape` | 1875009790284394635 | 3918795538668179460 |
| `GordieHowe.Ligero.Relative.Shape.w` | 11634738083042778359 | 18391236070086709708 |
| `GordieHowe.Ligero.Tableau.Challenge` | 16469685286396656874 | 6892951395573739487 |
| `GordieHowe.Ligero.Tableau.Commitment` | 716534305 | 2948236344 |
| `GordieHowe.Ligero.Tableau.Commitment.leaf` | 3978597070268011910 | 13493667847104958018 |
| `GordieHowe.Ligero.Tableau.Commitment.masks` | 6478403564269970551 | 6356254924100214984 |
| `GordieHowe.Ligero.Tableau.Commitment.mk` | 805342309 | 666019378 |
| `GordieHowe.Ligero.Tableau.Commitment.ofLeaves` | 15385120119975977520 | 4334938149195364129 |
| `GordieHowe.Ligero.Tableau.Commitment.tableau` | 6368348683546607939 | 16064691678556877101 |
| `GordieHowe.Ligero.Tableau.Leaf` | 279695275 | 716534305 |
| `GordieHowe.Ligero.Tableau.Leaf.column` | 2599703557223780557 | 8005461691791867176 |
| `GordieHowe.Ligero.Tableau.Leaf.dotMask` | 10873042402339919214 | 18098262867929497864 |
| `GordieHowe.Ligero.Tableau.Leaf.equivProd` | 1275022560169218629 | 7961754739168721058 |
| `GordieHowe.Ligero.Tableau.Leaf.mk` | 520239014 | 2776813587 |
| `GordieHowe.Ligero.Tableau.Leaf.quadMask` | 17778519266764856215 | 2924316795275293993 |
| `GordieHowe.Ligero.Tableau.Response` | 17098124200203659434 | 3753914126482779368 |
| `GordieHowe.Ligero.Tableau.Response.codeEval` | 493749961629128004 | 5920823021984934524 |
| `GordieHowe.Ligero.Tableau.Response.dotEval` | 15773184152067497960 | 9180718916603409333 |
| `GordieHowe.Ligero.Tableau.Response.quadEval` | 16426407769476075620 | 14821979286035284212 |
| `GordieHowe.Ligero.Tableau.accept` | 11688004742120232886 | 3235308067963659760 |
| `GordieHowe.Ligero.UntestedMaskRow.constraintBad` | 14665797119557445763 | 9058884052244359064 |

## Evidence and classification

Read the current Tableau encoding, executable acceptance and its semantic
 equivalence; RelativeLayout dimensions and validity; maskCode; and the selected
constraint event. Historical comparisons use Tableau at 5831d8fbc, ef8908bfd
and 6354acbd7, Relative/Layout at 5831d8fbc and ef8908bfd and RelativeLayout at
f01311529, and MaskedPolynomialTest/TableauList at 5831d8fbc. Compared the
implementation's per-repetition low-degree column loop and the paper's untested
mask argument. All selected sources/fingerprints match the compiled closure.

The main substantive changes are repetition-indexed rows/challenges/responses,
explicit leaf records, a separately configurable privacy width, and the weaker
sufficient mask-code rate. These changes are not claimed to be old-expression
identity. The general layout no longer derives twice-query-count ≤ block;
mask-test hiding must supply its own covering condition. The untested-mask
protocol does not need that condition.

## Per-declaration review

Tableau names have prefix `GordieHowe.Ligero.Tableau`.

- `Challenge`: all nrep low-degree vectors, followed by linear and quadratic
  batching vectors. Full field-valued function spaces retain every challenge.
- `Commitment`: all encoded ILDT/data rows and both arbitrary mask oracles.
  There is no honest-generation or low-degree premise attached to masks.
- `Commitment.mk`: constructs exactly the rows and mask pair without adding
  consistency assumptions about an adversarial commitment.
- `Commitment.masks`: projects the full pair of N-column mask oracles.
- `Commitment.tableau`: selects ILDT zero plus the common data rows, with a
  nonzero repetition instance making index zero valid.
- `Leaf`: contains all ILDT/data entries of a column and both mask entries.
- `Leaf.mk`: preserves all three fields, with no mask omitted from openings.
- `Leaf.column`: projects the full repetition-indexed column.
- `Leaf.dotMask`: projects the linear mask entry.
- `Leaf.quadMask`: projects the quadratic mask entry.
- `Leaf.equivProd`: encodes all ILDT entries before all data entries, then the
  two masks. Column.equivFin proves both inverse directions; no slot collides.
- `Commitment.leaf`: reads all components at the same actual column index.
- `Commitment.ofLeaves`: reconstructs rows and both masks pointwise. Its leaf
  equation is reflexive, and leaf injectivity preserves the complete oracle.
- `Response`: nrep blocks of k values and two blocks of 2k-1 values enforce the
  respective interpolation degree bounds. This is a polynomial representation,
  not byte-level identity with the implementation's compressed quadratic data.
- `Response.codeEval`: evaluates the selected repetition's response through
  Lagrange interpolation at the k response nodes.
- `Response.dotEval`: evaluates the linear block at its 2k-1 response nodes.
- `Response.quadEval`: evaluates the separate quadratic block at those nodes.
- `accept`: checks the linear witness-position sum, zero quadratic values at
  every witness node, every repetition at every queried column, and both mask
  column equations. The proven accept_eq_true_iff equates this Bool test with
  all four semantic conjuncts. Arbitrary masks are checked, not assumed valid.

Names in RelativeLayout:

- `GordieHowe.GKR.LayeredCircuit.instFintypePadIdx`: enumerates the bounded
  dependent layer/round/claim sum used by CircuitFlatten.PadIndex. Historical
  bodies use the same derivation through the older source name; changed circuit
  parameters do not replace the full finite index set with a subset.
- `GordieHowe.GKR.LayeredCircuit.instDecidableEqPadIdx`: derives equality on that
  same bounded sum/sigma type, without semantic pad-value equality assumptions.
- `GordieHowe.Ligero.Relative.Shape.mk`: records rate, query count, encoded
  length, positive-in-validity repetition count and privacy width r. Defaults
  nrep=1 and r=nreq preserve the common layout configuration; arbitrary records
  still need Valid proofs before becoming a checked layout.
- `GordieHowe.Ligero.Relative.Shape.w`: computes block-r. Valid's r<block
  proves positivity, so natural subtraction cannot silently give an empty
  witness row in a valid layout.
- `GordieHowe.Ligero.Relative.Shape.shape`: passes exactly w and r to the
  placement shape, retaining total positions, product count and extra rows.
  code_k proves r+w=block using the validity bound. Query count is not silently
  used as the privacy width after the generalization.

Two supporting entries:

- `GordieHowe.MaskedPolynomialTest.maskCode`: retains the original code points,
  uses dimension 2k-1 and radius floor((N-(2k-1))/2). The new hypothesis 2k-1≤N
  suffices for this radius and positive dimension because original k>0. It does
  not weaken a required arbitrary-mask consistency check.
- `GordieHowe.Ligero.UntestedMaskRow.constraintBad`: selects the linear list
  event if some fixed pinned-row linear claim fails; otherwise selects the
  quadratic event. Selection depends on the fixed rows/system, not on the
  random constraint coefficients. Thus the count pays for one selected family,
  rather than choosing the favorable family after sampling. It uses the same
  linear/quad predicate bodies as the historical counterpart, with updated
  names and the sufficient mask-code rate.

## Boundaries and limitations

The response node fallback beyond the code domain is irrelevant to degree
reconstruction once k≤N and 2k-1≤N are established by the code/setup conditions.
Every repetition is checked; the representative zero ILDT row used by the
constraint tableau does not replace the other low-degree checks. Query positions
are embeddings, hence distinct. The mask oracles may be arbitrary field words.
The paper's additional subfield soundness term belongs to the outer subfield
composition; this tableau verifier alone is not represented as that entire
protocol. Encoding re-interpolation and omitted-zero quadratic positions are
explained by the Response contract, not a claim of literal wire-byte equality.

This is an audit-only change. No source definition, headline, hypothesis,
distribution or exception is edited. Final closure reconciliation remains due.
