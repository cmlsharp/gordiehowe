# Application input re-audit, 2026-11-03

Scope: ten declarations at source commit `2cbeadad7`. Historical source comparisons
use the predecessor repository's last matching snapshots from the stale inventory:
`46a573ae` for the two Valid records, `5831d8fb` for the two HonestInput
constructors, `ef8908bf` for the emulated key coefficients, `60172ac0` for the
old 136-byte stream and challenge, and `f01311529` for the matrix, approximate
commitment and possession relation. The original audit references are C50–C58,
C62, C65 and C71. This is a current semantic review, not a claim that all these
historical changes preserve the old protocol.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Falcon512.PoP.HonestInput.Valid` | 1676623922 | 3683410446 |
| `GordieHowe.Falcon512.PoP.HonestInput.mk` | 1704353337 | 3325379044 |
| `GordieHowe.MLDSA44.Emulated.Rows.tKeyOf` | 6643082231125171584 | 8743236866893452557 |
| `GordieHowe.MLDSA44.Native.Rows.aHat` | 4458599725173221803 | 1493358100849169001 |
| `GordieHowe.MLDSA44.PoP.Compose.honestWApprox` | 6402780013163063003 | 1654271061937923394 |
| `GordieHowe.MLDSA44.PoP.HonestInput.Valid` | 2120862316 | 2393131381 |
| `GordieHowe.MLDSA44.PoP.HonestInput.mk` | 3326121772 | 331567979 |
| `GordieHowe.MLDSA44.PoP.challenge` | 14153915683655423816 | 17022990869362520447 |
| `GordieHowe.MLDSA44.PoP.stream` | 7753438912629444415 | 374509686111855574 |
| `GordieHowe.MLDSA44.PoP.rel` | 2326827163592572550 | 88084195784827031 |

## Falcon honest input

`Falcon512.PoP.HonestInput.mk` takes the public key, nonce, message, selected
samples and signature polynomial, with the declared finite lengths. Its fields
are data, not a proof that the signature is valid or an axiom about the circuit.
The constructor remains usable for invalid inputs. The later bridge from a
serialized witness is a separate definition and theorem; adding that bridge did
not smuggle its premises into this constructor.

`Falcon512.PoP.HonestInput.Valid` explicitly requires byte bounds for nonce
and message, successful fixed-stream selection equal to the supplied samples,
the algebraic verification equation, and signature encoding bounds. Historical
`rawSamples` became `acceptedCandidates`; the current function reads the fixed
717-candidate stream. The key in the algebraic check is the input's key, and
the selected samples are exactly those of its own nonce and message. There is
no independently supplied challenge that an honest input may choose to fit its
signature. This is an honest-completeness restriction: `relSupported` explicitly
combines ordinary verification with fixed-stream success, and
`HonestInput.valid_ofWitness` assumes that supported relation. It is not a
restriction on the soundness adversary, nor a claim of completeness for every
signature accepted by the longer-stream serialized verifier. The separately
named unsupported-fraction bound accounts for this distinction; this audit
does not assume it is zero.

Disposition: both current declarations pass the data and honest-input review.

## ML-DSA stream and challenge

`MLDSA44.PoP.stream` now returns 272 bytes rather than 136, using the named
`MLDSA44.Native.sibLen` from `System/Hash.lean`. It hashes exactly the commitment
hash bytes in vector order. This agrees with `kSibBytes=272` and
`challenge_from_mu` in the C++ ML-DSA hash circuit. The first eight bytes supply
sign bits and the remaining 264 supply position candidates; the extra bytes
are not inserted before the sign region.

`MLDSA44.PoP.challenge` still applies `MemoryShuffle.shuffle` to the supplied
positions and the sign bits of that same commitment hash's stream. Sign `s`
reads bit `s mod 8` of byte `s/8`; at ML-DSA-44, all 39 used signs lie within
the first eight bytes. The shuffle starts from zero and, in increasing step
order, first assigns `c[i]=c[j]`, then assigns `c[j]` to the selected sign.
When `i=j`, the sign assignment is the final assignment, as required. Arbitrary
out-of-range supplied positions have a total fallback in this specification;
they do not acquire a SampleInBall correctness claim. That claim is explicitly
conditional on `acceptedCandidates = some positions` in `sampleInBall_eq`.
The selector checks the non-strict condition `j <= N-tau+s`, preserves order,
and returns none when the candidates run out. The C++ slices bits `0..tau-1`
for signs and bytes `8..271` for candidates and passes these to its selection
and shuffle. No successful-selection condition is silently asserted by the
bare challenge definition.

Disposition: both definitions pass current stream-layout and shuffle review.
The larger stream is a substantive sampler-budget change, not a rename.

## ML-DSA key and approximate commitment

`MLDSA44.Emulated.Rows.tKeyOf` applies the vendored `power2RoundShift` to row
`i` of `t1`, then reads canonical natural representatives with `KeyNTT.vals`.
`power2RoundShift` multiplies every coefficient by `2^d` in the residue field;
`vals` reads `.val`, so the output is in `[0,q)`. It is not an unbounded
integer shift masquerading as a residue, and it neither changes row order nor
performs an NTT. The old source used the same formula under `MLDSAKeyNTT`.
The current coefficient lemma `congruent_rhs_eq` makes the factor `2^d`
explicit in the row equation.

`MLDSA44.Native.Rows.aHat` changed from the vendored finite-budget `expandA`
to the named total semantic `expandAFull`. It remains a k-by-l NTT-domain
matrix at the public key's rho. The underlying candidate construction absorbs
rho followed by column then row bytes, masks the top bit of each three-byte
candidate and rejects candidates at or above q. `expandAFull` chooses the
first sufficient prefix when all entries terminate and the zero matrix
otherwise. The current docstring distinguishes this semantic value from the
bounded implementation. On `ExpandAWithin`, the named theorem
`expandABounded_eq_expandAFull` proves equality with the bounded matrix.
This audit does not certify `aHat` as an executable algorithm: it is explicitly
noncomputable semantic data, and runtime acceptance is audited separately.

`MLDSA44.PoP.Compose.honestWApprox` uses that same full matrix in
`computeWApprox` with the concrete NTT ring operations. It converts the integer
challenge coefficients to residues and computes `A*z - c*t1*2^d`; there is no
read of the commitment hash and no ability to choose a different matrix for
each verifier check. The historical matrix source changed exactly as for
`aHat`. Within the explicit bounded relation below, the equality theorem
eliminates the otherwise-zero totalization branch. This is a semantic helper,
not an assertion that its noncomputable definition has runtime code.

Disposition: all three declarations pass the stated semantic and representation
review. Their runtime use and computability are not certified by these ledger entries.

## ML-DSA honest input and relation

`MLDSA44.PoP.HonestInput.mk` stores the encoded key and context, message,
commitment hash, selected positions, response vector and hints. Finite lengths
are part of the field types. The constructor does not include a signature-validity
proof or a new trust premise; validity is separate. The encoded statement's
key/context fields are used consistently by the current decoder and framing.

`MLDSA44.PoP.HonestInput.Valid` explicitly requires fixed-stream selection to
produce the stored positions and `MLDSA44.Verifies` on the decoded key, framed
context/message and stored signature components. The current `Verifies`
requires ExpandA to finish within 1008 bytes per entry, SampleInBall to finish
within 272 bytes, and the concrete verification checks at the full semantic
matrix. This replaces the old vendored verifier Boolean and is a substantive
change to the stated bounded verification domain. The norm inequality remains
strict, the hint-weight bound non-strict, and commitment equality uses the
same supplied message and key. The `Valid.checks` theorem derives these checks;
it does not replace them with an unconstrained witness.

`MLDSA44.PoP.rel` similarly replaces `verifyBytes = true` with the explicitly
bounded `VerifiesBytes`. Its statement carries the encoded public key and
context; its witness carries the message and serialized signature. The context
length must be at most 255, and signature decoding must succeed with exactly
the decoded components that satisfy `Verifies`. Malformed serialized hints
cannot bypass the existential because it includes equality to the successful
decoder result. Framing prefixes the mode byte and context-length byte; the
255-byte condition rules out length-byte wraparound. The full matrix's fallback
value cannot admit a key whose expansion fails the declared budget because
`Verifies.expandA` is independently required.

The relation's documentation explicitly states both sampling budgets. This
review accepts it as that bounded relation, not as unconditional verification
with an unbounded XOF loop. `HonestInput.valid_ofWitness` establishes that every
pair of this relation yields a valid honest input: its SampleInBall success
premise is already in the relation and is not added as an extra hypothesis
of the bridge. No new source edit, hypothesis or acceptance weakening is made
by this audit. Any broader claim equating this relation to all unbounded
standard-verification inputs would need separate evidence and is not certified here.

Disposition: the constructor, supported-input predicate and documented bounded
relation pass the current review, with the domain distinction above retained.

## Validation scope

Each own fingerprint matches the completed combined environment and tracked
closure; all reviewed source files are byte-identical to that built environment.
Only these ten ledger rows and this report change. Existing kernel-checked
bridges substantiate the identified boundaries; no new equality theorem or
computability test is claimed. Final develop closure reconciliation and the
other stale declarations remain separate work.
