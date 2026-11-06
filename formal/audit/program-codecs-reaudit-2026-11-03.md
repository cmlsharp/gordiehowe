# Program transcript codec review, 2026-11-03

Scope: 8 declarations at source commit `7be9f22d4`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.SPBCS.Configurations.LigeroFits` | 75406392 | 4167315583 |
| `GordieHowe.SPBCS.SpecReaders.ldtCommit` | 4463493056362485896 | 12970340634043296938 |
| `GordieHowe.SPBCS.SpecWrites.ldtCommit` | 6976641130522498322 | 5290453930008051407 |
| `GordieHowe.colCodec` | 1997931926156533183 | 7218268510961441259 |
| `GordieHowe.Ligero.MaskRow.Setup.commitReaders` | 3654312600206244313 | 9404248035161243358 |
| `GordieHowe.Ligero.MaskRow.Setup.commitWrites` | 2799920964525579405 | 16469943300552819791 |
| `GordieHowe.Ligero.MaskRow.Setup.leafCodec` | 4346122322794407604 | 11454027640712614846 |
| `GordieHowe.SPBCS.SpecReaders.sourceInteraction` | 5821082399486182989 | 938136120437951113 |

## Review method and historical changes

Reviewed current codec bodies, the two-round low-degree commitment specification,
`Tableau.Column.equivFin`, `Tableau.LdtResponse.equivFin`, and `Leaf.equivProd`.
Compared the historical `CircuitCodecs`, `Format`, and `Readers` at `5831d8fbc`,
and `PrefixCodecs` at `c0304fc4a`. The low-degree change is substantive: one test
became an explicit repetition count, affecting dimensions and serialization. It
is not classified as a namespace-only change. The source-circuit reader also
follows the later per-gate circuit interface and multidimensional initial point.

The repetition order agrees with `lib/ligero/ligero_prover.h::ldt_commit` and
`ligero_verifier.h::receive_ldt`: one repetition-major challenge message with
`reps * nldt` elements and one repetition-major response with `reps * block`
elements. The verifier checks that response size before absorption.

## Individual declarations

- `GordieHowe.SPBCS.Configurations.LigeroFits`: retains the auxiliary and masked
  response bounds and adds `9 + nrep * k * fb ≤ B` for the complete low-degree
  response. This is a serialization-capacity condition on parameters, not a
  restriction on adversarial messages. The response field is conservative for
  the proof-phase-only write; no smaller bound is substituted for the commit write.
- `GordieHowe.SPBCS.SpecReaders.ldtCommit`: at round zero uses nested `CReader.pi`
  for exactly `nrep` groups of `R` coefficients; round one is a prover message,
  so the impossible challenge-index branch is eliminated. The protocol has two
  rounds even when either dimension is zero. No challenge value is filtered.
- `GordieHowe.SPBCS.SpecWrites.ldtCommit`: the dual indexing excludes round zero
  and writes all `nrep * k` responses at round one. The curry/product-index
  equivalence preserves repetition-major order and has actual inverses. Its byte
  proof applies to the entire flattened array, including its header.
- `GordieHowe.colCodec`: serializes all `nrep` ILDT entries followed by all `R`
  data entries and the two separate mask elements. `Column.equivFin` uses the
  left and right injections into `Fin (nrep + R)`; its inverse covers both halves.
  The old `R + 1` interface has deliberately been generalized, not asserted
  byte-identical for arbitrary repetition counts.
- `GordieHowe.Ligero.MaskRow.Setup.commitReaders`: both setup constructors select
  the reader with their own `S.nrep`, common row count, and code dimension. There
  is no default-to-one branch or dropped repetition.
- `GordieHowe.Ligero.MaskRow.Setup.commitWrites`: both constructors likewise pass
  their repetition count and the bound for the full response. The abstract setup
  carries the data needed for the chosen commit protocol.
- `GordieHowe.Ligero.MaskRow.Setup.leafCodec`: the list-radius branch uses the
  complete column plus the two untested mask entries; the split-mask branch uses
  the column codec because those masks are already tableau rows. Both include all
  repetition entries. The common size upper bound deliberately allows two extra
  mask entries for the split branch; it does not omit bytes from the actual codec.
- `GordieHowe.SPBCS.SpecReaders.sourceInteraction`: transports the source's input
  dimension equality and invokes `gkrSpec` for its complete layer and tail. The
  current `gkrSpec` reads all `outDim` initial coordinates, then per-layer batching
  coefficients, each sumcheck challenge, and the final input-binding element.
  Removal of the historical `unique`/`hbound` constructor fields does not remove
  a challenge branch. Load bounds use `max outDim 2`, rather than the old scalar
  initial-point assumption. This declaration constructs readers, not soundness;
  source relation soundness remains separately proved for the per-gate interface.

## Outcome and limits

All eight entries pass this source review. Empty dimensions have empty vectors,
not fabricated samples; positivity requirements for security belong to the
relevant concrete setup and soundness theorem, not these serialization functions.
The audit changes no production source, acceptance predicate, distribution, or
headline. Current bytes and fingerprints are checked against the compiled review
snapshot; final-head closure reconciliation remains required.
