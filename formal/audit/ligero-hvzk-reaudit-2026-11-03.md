# Ligero honest-view and coin audit, 2026-11-03

Scope: 34 declarations at source commit `8152b3023`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Ligero.HVZK.BlindingFields.mk` | 3916812843 | 3459912334 |
| `GordieHowe.Ligero.HVZK.Coins` | 3497837843 | 3698155777 |
| `GordieHowe.Ligero.HVZK.Coins.equivProd` | 14075514040036421095 | 904516380489410707 |
| `GordieHowe.Ligero.HVZK.Coins.mk` | 1812717477 | 575507793 |
| `GordieHowe.Ligero.HVZK.Coins.privacy` | 10214271331478286263 | 4535987855143329726 |
| `GordieHowe.Ligero.HVZK.Coins.response` | 16997056728115041217 | 5246131694705357051 |
| `GordieHowe.Ligero.HVZK.DotMasks` | 3925241160275001561 | 15733680625002354489 |
| `GordieHowe.Ligero.HVZK.HidingLayout.mk` | 276952549 | 3923347589 |
| `GordieHowe.Ligero.HVZK.QuadMasks` | 12135718018054041242 | 4144057190620136094 |
| `GordieHowe.Ligero.HVZK.ResponseCoins` | 1431737114 | 4250057465 |
| `GordieHowe.Ligero.HVZK.ResponseCoins.dotMask` | 3179765914921787639 | 11270839097775090142 |
| `GordieHowe.Ligero.HVZK.ResponseCoins.equivProd` | 18442432496297962527 | 7250438421037440680 |
| `GordieHowe.Ligero.HVZK.ResponseCoins.ildt` | 6575496729843251915 | 9693479283342387947 |
| `GordieHowe.Ligero.HVZK.ResponseCoins.mk` | 2622463042 | 1844527695 |
| `GordieHowe.Ligero.HVZK.ResponseCoins.quadMask` | 13406116974212852411 | 2041990465317428563 |
| `GordieHowe.Ligero.HVZK.SimCoins` | 2839541606 | 2408058585 |
| `GordieHowe.Ligero.HVZK.SimCoins.equivProd` | 7153603527311850388 | 16655433423808249470 |
| `GordieHowe.Ligero.HVZK.SimCoins.mk` | 3023920392 | 1429718471 |
| `GordieHowe.Ligero.HVZK.SimCoins.openings` | 8540379512273767203 | 12659221805713555878 |
| `GordieHowe.Ligero.HVZK.SimCoins.response` | 6714012222343812410 | 1550801269104546832 |
| `GordieHowe.Ligero.HVZK.View` | 8269262626385994363 | 16091936613641132845 |
| `GordieHowe.Ligero.HVZK.commitOf` | 16059256483199788725 | 4458598026393942137 |
| `GordieHowe.Ligero.HVZK.instFintypeCoins` | 8083955363745823727 | 13830882740317846182 |
| `GordieHowe.Ligero.HVZK.instFintypeDotMasks` | 633928770337619864 | 2384509151653513811 |
| `GordieHowe.Ligero.HVZK.instFintypeQuadMasks` | 17685964649836219091 | 6909615717820591085 |
| `GordieHowe.Ligero.HVZK.instFintypeResponseCoins` | 13537290959290151928 | 5325212798463422547 |
| `GordieHowe.Ligero.HVZK.instFintypeSimCoins` | 6217705866616867653 | 5404355215055952052 |
| `GordieHowe.Ligero.HVZK.instNonemptyCoins` | 1905612756 | 3981475024 |
| `GordieHowe.Ligero.HVZK.publicView` | 13414098335789471847 | 18077047023089506686 |
| `GordieHowe.Ligero.HVZK.responseOf` | 17104257503430761818 | 14411285947077166628 |
| `GordieHowe.Ligero.HVZK.rows` | 12538703421268859877 | 17538124591332880320 |
| `GordieHowe.Ligero.HVZK.rowsEval` | 6105174314491220128 | 7301653669176783838 |
| `GordieHowe.Ligero.HVZK.simResponse` | 15427214503541444463 | 11940148471658556985 |
| `GordieHowe.Ligero.HVZK.simulate` | 8892207267668622680 | 2656604537934156079 |

## Evidence and classification

Read the selected definitions and the final distribution proof in HVZK, including
response translation, row-opening uniformity and reconstruction of the public
view. Compared the counterparts at 5831d8fbc (coin/repetition changes), ef8908bfd
(mask types) and f01311529 (blinding/hiding constructors). The first attempted
ef8908bfd path was absent; the actual counterpart is Ligero/HVZK, and only that
file was used. Current source bytes and fingerprints match the accepted compiled
closure. The paper's Ligero simulator draws responses and data openings, then
solves the mask-opening equations, matching the construction reviewed here.

Substantive changes are repetition-indexed ILDT coins and openings, the weaker
sufficient mask-code rate, explicit decidable subfield membership and field
equality, and a computable complete enumeration for simulator coins. Product
records replace older tuple representations without restricting the underlying
sample space. These changes are not classified as namespace-only identity.

## Per-declaration review

All names below have prefix `GordieHowe.Ligero.HVZK`.

- `BlindingFields.mk`: associates each data row with a subfield and an actual
  membership decision procedure. It does not assert that all elements lie in a
  proper subfield or impose a predicate on an adversary.
- `HidingLayout.mk`: retains off-witness and nonempty-witness parameter facts,
  node/code-point membership and the exclusion of ILDT from quadratic triples;
  adds decidable field equality. These facts justify interpolation and the
  linear-response offset. They concern the layout, not successful transcripts.
- `DotMasks`: polynomials of degree below 2k-1 with zero witness-position sum.
  This is the kernel of the linear mask check, not all low-degree polynomials.
- `QuadMasks`: the same degree bound with every witness-node quadratic check
  zero; no witness node is omitted.
- `instFintypeDotMasks`: establishes finiteness by injectivity of the first
  2k-1 coefficients. High coefficients vanish by the degree bound.
- `instFintypeQuadMasks`: applies the same injectivity argument to its distinct
  zero-at-each-node predicate. Neither finite instance changes the mask set.
- `ResponseCoins`: contains independent message-value vectors for each ILDT
  repetition and one IDOT and IQUAD mask, shared by the constraint tests.
- `ResponseCoins.mk`: accepts exactly those three coordinates, with mask
  validity enforced by their subtype types and no hidden relation between them.
- `ResponseCoins.ildt`: projects every repetition's k message values.
- `ResponseCoins.dotMask`: projects the linear mask with its original proof.
- `ResponseCoins.quadMask`: projects the quadratic mask with its original proof.
- `ResponseCoins.equivProd`: the forward projections and inverse constructor
  have reflexive inverse laws; the full product sample space is retained.
- `instFintypeResponseCoins`: transports the complete product enumeration
  through that equivalence; no conditioning on challenges occurs.
- `Coins`: pairs the data rows' privacy values in their own subfields with the
  response coins. Witness-position values are not part of these random coins.
- `Coins.mk`: builds precisely those independent coordinates.
- `Coins.privacy`: retains each row's subfield-valued function over the privacy
  complement, including the empty-complement case.
- `Coins.response`: returns the entire response block, not one repetition.
- `Coins.equivProd`: a coordinate bijection with reflexive inverse laws.
- `instFintypeCoins`: transports full finite product membership. Its classical
  construction remains noncomputable; this re-audit does not exempt it from
  runtime checks or claim a compiled sampler.
- `instNonemptyCoins`: supplies zero privacy values and existing response-coin
  inhabitation. This is a Prop witness, not the distribution used for sampling;
  it does not replace uniform randomness with a default coin.
- `rows`: the semantic polynomial tableau of repetition zero, which exists
  under `NeZero nrep`; all repetitions share the same data rows.
- `rowsEval`: executable Lagrange evaluation of the same zero-indexed ILDT row
  or the selected successor data row, as confirmed by `eval_rows`.
- `commitOf`: evaluates every ILDT repetition and every data row at each code
  point and adds the two mask evaluations. It reads cells/coins only, so the
  commitment is fixed before the linear system is supplied.
- `responseOf`: forms every low-degree response from its own ILDT values and
  challenge-weighted data rows, and adds the linear/quadratic mask to its
  corresponding batched constraint. Response-node ranges are k and 2k-1;
  the product expression has target minus product with the intended sign.
- `View`: includes the entire response and, at each queried column, all ILDT
  and data entries plus both masks. No verifier-observed value is discarded.
- `SimCoins`: combines each queried data opening in its row's blinding field
  with independent response coins. Its dimensions are query count and nrep.
- `SimCoins.mk`: imposes no extra correlations between the two coordinates.
- `SimCoins.openings`: projects precisely the query-indexed data openings.
- `SimCoins.response`: retains the full response-coin block.
- `SimCoins.equivProd`: reorders nothing internally and has reflexive inverse
  laws; it supports the same finite uniform law on the full product.
- `instFintypeSimCoins`: uses supplied decidable membership/equality and the
  explicit response-mask enumeration. `polyEnum` maps filtered coefficient
  vectors injectively to polynomials and proves completeness via toFn/ofFn,
  so it neither duplicates masks nor excludes a valid polynomial.
- `simResponse`: interpolates each independent ILDT response, adds the batched
  public target times the unit-dot polynomial to IDOT, and keeps IQUAD in its
  zero-check kernel. The unit-dot uses a known witness node and has check one.
- `publicView`: reconstructs each ILDT opening as response minus the weighted
  data sum, then both mask openings as response minus the corresponding
  constraint sum, using actual query code points and public coefficients.
- `simulate`: computes that public reconstruction from the explicit coins.
  It has no witness input and samples no hidden favorable event. All ILDT
  repetitions are solved separately against the same sampled data openings.

## Distribution, vacuity and runtime limits

For fixed privacy values, `responseShift` is injective: equal ILDT coordinates
cancel their fixed shifts; equal data tableaux then let the two mask shifts
cancel. Finiteness yields a bijection, establishing the response law without
assuming the shifts are independent random variables. The final proof combines
that conditional response law with uniform row openings, then applies the same
public reconstruction to both distributions. The row-opening argument requires
query injectivity, off-witness code points and t ≤ k minus witness cardinality;
these are explicit layout/query conditions. Zero queried columns give an empty
opening view and do not introduce an invalid index.

The explicit finite mask enumeration is exhaustive and may be exponential. The
simulator docstring's polynomial-time sampling argument describes sampling a
linear solution space via a basis; this audit does not claim that the exhaustive
Fintype enumeration implements that algorithm. Likewise, noncomputable semantic
polynomials and honest coin finiteness have not been converted by this ledger
change. The compiled simulator map itself takes explicit coins and uses field
operations. These distinctions preserve the scope of the existing runtime gate.

Only the ledger and this report change. No headline, distribution, hypothesis,
Lean implementation or CostLint exception is modified. Final closure
reconciliation remains required.
