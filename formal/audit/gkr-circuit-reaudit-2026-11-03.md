# GKR circuit semantics and interpolation-node review, 2026-11-03

Scope: 17 declarations at source commit `255bd0fd8`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.GKR.Circuit` | 2038582257 | 279695275 |
| `GordieHowe.GKR.Circuit.AssertionsHold` | 9380721615274740815 | 13043401439462214092 |
| `GordieHowe.GKR.Circuit.Satisfied` | 15583489102947714473 | 1673137507982787083 |
| `GordieHowe.GKR.Circuit.brecOn.go` | 17562144943682220594 | 13912451216684317408 |
| `GordieHowe.GKR.Circuit.depth` | 8144288278322336383 | 8115825795735285432 |
| `GordieHowe.GKR.Circuit.eval` | 3031848596769524389 | 3097453800805023239 |
| `GordieHowe.GKR.Circuit.input` | 3754036149 | 558371985 |
| `GordieHowe.GKR.Circuit.inputDim` | 15495949023808714411 | 15461681935468675291 |
| `GordieHowe.GKR.Circuit.layer` | 3166942568 | 1257801687 |
| `GordieHowe.GKR.Circuit.rec` | 2397741476 | 4081578461 |
| `GordieHowe.GKR.CircuitBudget.WidthsAtMost` | 211035516438641287 | 2676302015464400551 |
| `GordieHowe.GKR.ConcreteNodes.gf2_128Nodes` | 5212572818668831973 | 15876291750048332769 |
| `GordieHowe.GKR.ConcreteNodes.gf2_128SubfieldGen_ne_one` | 4239269803 | 3897568750 |
| `GordieHowe.GKR.ConcreteNodes.gf2_128SubfieldGen_ne_zero` | 480217149 | 3876972525 |
| `GordieHowe.GKR.ConcreteNodes.gf2_256Nodes` | 17504969924930892556 | 17358373463444352062 |
| `GordieHowe.GKR.ConcreteNodes.gf2_256SubfieldGen_ne_one` | 3999169260 | 255769431 |
| `GordieHowe.GKR.ConcreteNodes.zeroOneGen` | 14866046089780998403 | 17501926303063297977 |

## Method and historical change

Reviewed `Circuit`, `CircuitBudget.WidthsAtMost`, and six concrete-node entries
against `ef8908bfd`; `zeroOneGen` was also compared at `5831d8fbc`. The current
source and fingerprint snapshot is the compiled acceptance source. Checked the
local paper's `sections/gkr-appendix.tex`, Definition `def:layered-circuit`, and
`lib/sumcheck/quad.h::prep_v` for the intended grouped assertion meaning. The
paper file is reference material from the research checkout, not changed here.

The old circuit constructor required `UniqueAssertions` and its satisfaction
predicate required each zero-coefficient corner product to vanish separately.
The current interface instead checks the sum of those products at every gate,
and no longer needs the uniqueness field. This is a substantive generalization
of the generic relation. It is not an equality claim for unrestricted old/new
relations. On unique assertion gates, `Layer.assertions_zero_iff` identifies the
two predicates. Without uniqueness, cancellation within one gate is permitted
by the grouped assertion relation; an application demanding each separate
product must establish the appropriate compiler relation, not infer it from
this generic circuit alone. The local paper defines satisfaction by the grouped
assertion table, and `prep_v` replaces each zero coefficient with the batching
coefficient, accumulating its contribution in the same way.

## Individual entries

Names are relative to `GordieHowe.GKR`.

- `Circuit`: a structurally finite layer chain with the exact padded width at
  each boundary. Its tail's output dimension is the layer's input dimension.
  It contains no prover-selected internal wire assignment.
- `Circuit.input`: the terminal input table at dimension `d`; dimension zero
  still means one table entry (`2^0`), not an empty vector.
- `Circuit.layer`: appends the complete indexed corner array and tail. Removal
  of `UniqueAssertions` generalizes the circuit data as described above; it
  neither filters corners nor introduces a hidden semantic assumption.
- `Circuit.rec`: the generated dependent eliminator covers both constructors
  and gives the recursive hypothesis for the actual tail. Its changed type
  follows the removed constructor field; it is not a custom soundness axiom.
- `Circuit.brecOn.go`: the generated structural recursion auxiliary follows the
  same inductive shape. This entry is reviewed as compiler-generated machinery
  of this datatype; no separate source implementation or protocol behavior is
  attributed to it, and no raw expression identity with the old auxiliary is claimed.
- `Circuit.inputDim`: follows every tail to the terminal dimension. Intermediate
  dimensions cannot replace the actual input dimension.
- `Circuit.depth`: counts each layer once and assigns zero to the terminal input.
- `Circuit.eval`: recursively computes the tail and sums every corner's ordinary
  coefficient times its two input values at the selected output gate. Assertion
  corners have coefficient zero in this ordinary output. There is no existential
  intermediate assignment that could make an unsatisfied input appear satisfied.
- `Circuit.AssertionsHold`: requires the grouped assertion table to vanish at
  every gate of every layer, evaluated on the actual computed tail. The terminal
  input imposes no assertion. This is the historical semantic change explained above.
- `Circuit.Satisfied`: conjuncts zero at every output gate with all those assertion
  constraints. A zero-layer circuit requires the input itself to be all zero;
  it is not automatically satisfied. An empty corner array evaluates to zero,
  as the represented zero circuit should.
- `CircuitBudget.WidthsAtMost`: bounds every layer's input dimension recursively.
  It does not by itself bound the top output dimension; `LayeredCircuit.ShapeAtMost`
  supplies `outDim_le` separately. The base case has no layers to bound. The
  unchanged dimension-sum argument counts `inDim` once per layer, matching depth.
- `ConcreteNodes.zeroOneGen`: uses exactly the three points zero, one, and `g`;
  the explicit `g ≠ 0` and `g ≠ 1` assumptions, together with field nontriviality,
  prove all three indices distinct. They are parameter requirements, not challenge
  exclusions. Its point values agree with the historical source.
- `ConcreteNodes.gf2_128SubfieldGen_ne_zero`: derives nonzeroness from the named
  nonzero root raised to the fixed exponent, with no new assumption.
- `ConcreteNodes.gf2_128SubfieldGen_ne_one`: uses the proved order 65535; equality
  to one would force order one. It does not confuse polynomial-basis bits with
  a natural-number cast in characteristic two.
- `ConcreteNodes.gf2_256SubfieldGen_ne_one`: the same order contradiction for the
  separately named 256-bit field generator.
- `ConcreteNodes.gf2_128Nodes`: instantiates the three-node construction with the
  actual selected subfield generator and the named distinctness proofs.
- `ConcreteNodes.gf2_256Nodes`: does the same in the 256-bit field. Both C++ fields
  initialize the polynomial-basis element with `of_scalar_field(0b10)` and use
  its specified subfield-generator powers for interpolation points. Neither Lean
  construction substitutes the field cast of the natural number two.

## Outcome

These 17 entries pass the current-source review, with the grouped-assertion
semantic change explicitly classified. Namespace migration and removal of old
unnecessary noncomputable markers also contribute to the historical changes.
This audit edits no circuit, theorem, hypothesis, or headline; it does not claim
that a generic grouped assertion implies individual-corner assertions without
the stated uniqueness property. Final-head closure reconciliation remains required.
