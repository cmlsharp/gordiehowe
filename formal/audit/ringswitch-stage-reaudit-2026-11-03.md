# Ring-switching mask and stage semantic re-audit, 2026-11-03

Scope: 9 declarations at source commit `cda2c9932`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.FieldProof.MaskedReduction.Honest.measure` | 14670000493057388093 | 12409723466423222730 |
| `GordieHowe.FieldProof.MaskedReduction.Honest.stage` | 14756740891919950947 | 6776435667248617184 |
| `GordieHowe.FieldProof.MaskedReduction.measure` | 9437753289413784732 | 4113050985057659592 |
| `GordieHowe.MaskScheme.Valid` | 5664501416932762521 | 12018396581602527462 |
| `GordieHowe.MaskScheme.mk` | 4147916545 | 514719333 |
| `GordieHowe.MaskScheme.products` | 5893619991228613692 | 11867619103867174484 |
| `GordieHowe.MaskScheme.squaringChain` | 7794555216208636453 | 12708898202603766466 |
| `GordieHowe.MaskScheme.squaringChainOver` | 8240913461990767921 | 15968234262629341211 |
| `GordieHowe.MaskScheme.subfieldMasks` | 2271147547510320428 | 3430252340780498231 |

The current module was reviewed against historical sources `4cd3a9bb1`, `28705d8ee`,
`c0304fc4a` and `407240beb`. Changes include `power`/`twist` and `ClaimIP` naming,
explicit product-index encodings, generalized squaring chains, and separation of the
named simulator from honest correctness. Current bytes and the nine fingerprints
match the compiled acceptance snapshot. This update edits only audit records.

- `MaskScheme.mk` requires mask forms, twist forms, a finite encoded product index,
  actual product constraints, an external `Valid` predicate and a theorem deriving
  the twist equation from those products and validity. The new `Encodable Q` supplies
  numbering; it does not certify products or weaken the twist equation. Renaming
  `power` to `twist` did not change the required Frobenius exponent.
- `MaskScheme.products` returns exactly the supplied product layout, with the same
  index type. Its structure projection moved after the encoding field; no product
  obligation is filtered away by that projection.
- `MaskScheme.Valid` remains an explicit predicate on all committed cell values.
  It can be false, so a generic soundness result conditional on validity must not be
  advertised as unconditional. The honest bundle proves it from commitments; full
  soundness must establish it separately for the relevant cells.
- `MaskScheme.squaringChain` uses characteristic two and `m = 1`. Mask and twist
  are single cells, and every chain product is `prev * prev = chain`. For index
  `k`, the last of `k` squarings is exponent `2^k`; at `k = 0`, twist is the mask
  itself. `Valid = True` is justified by those product constraints, not by assuming
  the chain values. Empty dimensions have no masks or chain constraints.
- `MaskScheme.squaringChainOver` generalizes to `b * k` squarings and exponent
  `2^(b*k)`, retaining characteristic two. The last index is `b*k - 1` only in the
  nonzero branch. At `b*k = 0`, twist is the original mask and the exponent is one.
  The definition proves this algebraic identity even at `b = 0`; its informal
  finite-field interpretation requires the surrounding field data, not an added
  hidden positivity assumption in this constructor.
- `MaskScheme.subfieldMasks` defines sigma as `sum γ_i s_i` and twist as
  `sum phi(γ_i) s_i`, with no product triples. Its `Valid` predicate requires every
  coordinate to lie in `S0`; `S0_le` ensures Frobenius fixes them. A spanning or
  independent basis is unnecessary for this twist identity. Uniform honest masks
  would require a separate honest bundle and its proved uniformity; this constructor
  alone does not claim that arbitrary coefficients yield a uniform distribution.
- `MaskedReduction.measure` appends a prover-only message of `d` field elements,
  retains existing linear/product constraints, adds mask products and replaces the
  one input claim by the remainder row followed by the `d` measurement rows. Thus
  the output has exactly `d + 1` claims and no new random challenge. Its soundness
  uses the explicit validity and relative-Frobenius conditions.
- `Honest.measure` appends the actual masked measurement, pairs old pads with fresh
  mask pads, and retains both commitment relations. Word consistency and the mask
  equations justify completeness. Distribution equality fixes the previous pads
  and translates the independent uniform mask vector; it does not condition away
  a failure event. The current simulator is named explicitly rather than stored
  inside the honest bundle.
- `Honest.stage` composes the honest combination and measurement. This generic
  stage includes a combination challenge even when a specialized routed stage
  might omit it. Its named simulator follows the same two steps; pads and word
  commitments are passed consistently. The corresponding stage bound still adds
  `1/card F` for that combination, with zero added error for measurement.

No unconditional validity, uniformity of an arbitrary subfield presentation, or
identity of all historical protocol types is claimed. The reviewed constructors
preserve explicit obligations, and this audit adds no new hypothesis or exemption.
