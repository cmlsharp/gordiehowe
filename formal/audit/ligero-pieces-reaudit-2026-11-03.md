# Ligero mask-piece protocol audit, 2026-11-03

Scope: 38 declarations at source commit `b1dff4104`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Ligero.MaskTest.Pieces.Bad` | 13321457364883210013 | 12740692222073173358 |
| `GordieHowe.Ligero.MaskTest.Pieces.Claim` | 7472369554278539149 | 9627956029024140847 |
| `GordieHowe.Ligero.MaskTest.Pieces.Input` | 1192723577162694863 | 15500714827748600233 |
| `GordieHowe.Ligero.MaskTest.Pieces.Setup.mk` | 2450843154 | 2117510235 |
| `GordieHowe.Ligero.MaskTest.Pieces.Setup.pieces` | 4243645357505202725 | 5419168027661516087 |
| `GordieHowe.Ligero.MaskTest.Pieces.commitProve` | 10385102519601015344 | 8741953935690651238 |
| `GordieHowe.Ligero.MaskTest.Pieces.query_count` | 2852773669 | 4015202889 |
| `GordieHowe.Ligero.MaskTest.Pieces.sound` | 16687529282494167957 | 17779371004997841377 |
| `GordieHowe.Ligero.MaskTest.Pieces.testAccept` | 4474938875466194311 | 1825863836317072457 |
| `GordieHowe.Ligero.MaskTest.Pieces.testProof` | 16198118157612878185 | 7158322918198468432 |
| `GordieHowe.Ligero.MaskTest.Pieces.test_count` | 551537141 | 355051280 |
| `GordieHowe.Ligero.MaskTest.Pieces.verdict` | 3586869665375893555 | 17206711488386918185 |
| `GordieHowe.Ligero.MaskTest.Pieces.Hiding.mk` | 3236121696 | 3102553639 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.Coins` | 2298003475 | 1606093550 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.Coins.dotKernel` | 13638703823750112749 | 2898315112625064364 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.Coins.dotMask` | 6480064480194217514 | 550531249808455646 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.Coins.equivProd` | 7121378943446772038 | 5105932358258268512 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.Coins.inner` | 9603614289416206164 | 15819376495709719068 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.Coins.mk` | 2812650906 | 2999619097 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.Coins.quadKernel` | 16543597331131949100 | 17905125488879203077 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.Coins.quadMask` | 4542791048783915290 | 15263440998818021026 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.SimCoins` | 2839541606 | 2408058585 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.SimCoins.dot` | 9600042306471033792 | 14845504338302226434 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.SimCoins.equivProd` | 6053884293871695199 | 16813841520601949914 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.SimCoins.inner` | 1666296855907233841 | 8352802278370695355 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.SimCoins.mk` | 105225102 | 3867090259 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.SimCoins.quad` | 3460082630149244364 | 13783508877611777836 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.honestLdtResponse` | 18419858597833879387 | 4191313157111007642 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.honestMasked` | 10570163843954191237 | 3851110150204093427 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.honestRows` | 12378356601919201943 | 18185357356391570729 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.instFintypeCoins` | 12745723833317861876 | 3466233339893731649 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.instFintypeSimCoins` | 15977178088602111968 | 8373828968069194832 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.instNonemptyCoins` | 1537277895 | 1622228035 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.simData` | 5582317096049421886 | 13650262173102874878 |
| `GordieHowe.Ligero.MaskTest.Pieces.ZK.simulate` | 17488057678311545914 | 14386008457932539645 |
| `GordieHowe.Ligero.MaskTest.Pieces.honest` | 4926488539194570007 | 1325121481196937692 |
| `GordieHowe.Ligero.MaskTest.Pieces.simulate` | 14151928483862119566 | 15014657811369141870 |
| `GordieHowe.Ligero.MaskTest.Pieces.viewOf` | 12236536344124144939 | 14256681828909659410 |

## Evidence and classification

Read Pieces and PiecesHonest, including the pinned-mask count, transcript
construction, honest splitting, simulator and final distribution proof. Compared
SplitMask and SplitMaskHonest at 5831d8fbc with the current files. Changes include
repeated low-degree tests, the sufficient mask-code rate, separation of honest
completeness from hiding, and executable simulator coin enumeration. Fingerprints
and source bytes agree with the accepted compiled closure. These are semantic
re-audits, not claims of historical byte identity.

The paper's three-piece mask construction is A + X^(k-t) C + X^k B. Soundness
allows each committed piece degree below k, so the recombination can have degree
2k-1; the response has degree below 2k-1. The root-count bound therefore charges
2k-1 columns. It must not use the tighter honest B-piece degree to reduce the
adversarial bound. Hiding separately needs 2t≤k and enough privacy positions.

## Protocol entries

Names have prefix `GordieHowe.Ligero.MaskTest.Pieces`.

- `Setup.mk`: shared threshold/placement/query/repetition data, explicit
  2k-1≤N and the two triples of piece rows. No honest separation condition is
  imposed on the adversarial encoded rows for soundness.
- `Setup.pieces`: projects the exact two row triples used by mask recombination.
- `Input`: public context, committed encoded rows and the full commit
  transcript; there is no independent unchecked mask oracle.
- `verdict`: runs the tableau verifier with masks computed from the committed
  piece entries at the same column points, using the actual commit responses.
- `commitProve`: exposes all encoded columns, the concrete common-agreement
  extractor and the existing two/three round protocols. Read congruence proves
  recombined masks depend only on queried columns.
- `Claim`: all-repetitions exceptional event OR satisfaction at extracted cells.
  The exceptional event remains charged in the commit error.
- `Bad`: selects the cancellation event for the pinned masks/pinned rows. The
  analytical mask argument is unused because the commitment determines masks;
  it is not used to choose a favorable mask after the challenge.
- `testAccept`: identical tableau acceptance with those recombined masks; its
  analytical mask argument is also unused for the same reason.
- `test_count`: charges one field reciprocal, by the single selected affine
  event and positive finite field cardinality, for every fixed committed input.
- `query_count`: under a false claim and a nonbad constraint challenge, bounds
  every response by the sum of the small-agreement and pinned-mask root counts,
  divided by the full distinct-query space. Pinned rows include all six pieces.
- `testProof`: composes those two bounds without narrowing adversarial
  responses. It is proof/error data, not an executable simulator.
- `sound`: drops the analytical mask round using masks determined by the
  commitment, proves the same Bool verdict by reflexivity and charges the
  all-repetitions commit event explicitly.

## Honest and simulator entries

The same prefix applies, with `ZK` where shown.

- `Hiding.mk`: retains the placement's free-piece conditions and requires both
  t≤k-witness-cardinality and 2t≤k. The latter was not lost when privacy width
  became separately configurable; completeness is separated from these bounds.
- `ZK.Coins`: unsplit honest coins and one independent kernel coin for each mask.
- `ZK.Coins.mk`: keeps those three coordinates without a challenge-dependent
  constraint; kernel membership enforces zero recombination.
- `ZK.Coins.inner`: the complete unsplit privacy/response coins, including nrep.
- `ZK.Coins.dotKernel`: the linear mask's splitting-kernel coordinate.
- `ZK.Coins.quadKernel`: the separate quadratic splitting-kernel coordinate.
- `ZK.Coins.dotMask`: exactly the inner response's linear polynomial mask.
- `ZK.Coins.quadMask`: exactly the inner response's quadratic polynomial mask.
- `ZK.Coins.equivProd`: flattens privacy, response and the two kernels with
  reflexive inverse laws, preserving the complete uniform product space.
- `ZK.instFintypeCoins`: finite enumeration transported through that bijection;
  it remains noncomputable and is not presented as a compiled sampler.
- `ZK.instNonemptyCoins`: inhabitation from an existing inner coin and zero
  kernels. This Prop witness does not define or replace the uniform law.
- `ZK.honestRows`: fills the six piece rows with the block split plus kernel
  coins and retains unsplit rows elsewhere. Separate/free assumptions justify
  disjointness, no row-zero replacement and no change to source constraints.
- `ZK.honestLdtResponse`: every repetition's actual projected polynomial,
  including all piece rows, evaluated at k response nodes. It does not read the
  later constraint challenge or public linear system.
- `ZK.honestMasked`: original masks plus their correct batched constraints at
  2k-1 response nodes. Constraints ignore the piece rows by separation.
- `ZK.SimCoins`: the unsplit simulator coins plus independent C/B openings for
  each mask; A openings are subsequently determined by recombination.
- `ZK.SimCoins.mk`: stores precisely those three independent components.
- `ZK.SimCoins.inner`: retains every simulated response and data opening.
- `ZK.SimCoins.dot`: the linear mask's two query-indexed piece openings.
- `ZK.SimCoins.quad`: the quadratic mask's separate two opening vectors.
- `ZK.SimCoins.equivProd`: explicit coordinate bijection with reflexive inverses.
- `ZK.instFintypeSimCoins`: full computable enumeration using the hiding
  layout's decision procedures and complete response-mask enumeration. No
  polynomial-time bound on that exhaustive enumeration is asserted here.
- `ZK.simData`: computes each mask opening from its response minus constraint
  source, assigns C and B from coins, and solves A as mask-x^(k-t)C-x^kB.
  Other data openings remain supplied values; the temporary ILDT value zero is
  ignored by the relevant constraints under the layout conditions.
- `ZK.simulate`: obtains public simulated responses, fills the piece data and
  uses the shared public view reconstruction to solve all ILDT openings. It is
  computable on explicit coins and has no witness argument.
- `viewOf`: keeps full response transcripts and queried encoded columns. It
  discards separately reconstructed mask entries because these are not separate
  leaves in the piece protocol; masks are determined from the column itself.
- `simulate`: computes the context's public linear system, passes the actual
  challenges/query/coins to ZK.simulate and assembles that exact system view.
- `honest`: named placement commitment/prover and explicit admissibility,
  complete at every honest coin/challenge, hiding against separate honestSim
  under both query bounds. It remains noncomputable through the inherited
  polynomial/placement construction; this report adds no runtime exception.

## Distribution and boundaries

The piece-induced ILDT offset is independent of the ILDT coordinates being
shifted. The proof supplies addition/subtraction inverses for the full nrep
vector, leaving masks and kernel coins intact. Then the unsplit response law
and each mask's uniform C/B openings combine through a dependent-distribution
argument. The opening surjectivity uses distinct query points and 2t≤k;
row-opening uniformity separately uses the privacy budget. The final public
reconstruction is the same for honest and simulated views. No unproved
independence between a mask and its deterministic split is assumed.

The commitment is fixed before low-degree challenges, and the common agreement
set before column queries. The small-set count uses A-1; the large-set count
uses 2k-1, not 2k-2. Missing valid-response conditions yield zero acceptance in
the corresponding branch. Positive nrep justifies index zero. This audit
changes only records and reports, with no new hypotheses, distributions,
headlines or exceptions; final-head reconciliation remains required.
