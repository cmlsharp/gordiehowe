# Parameter and algebra re-audit, 2026-11-03

Scope: the eight declarations listed below, at source commit `c48368d9b`.
This is a fresh review of their current meanings. The old and new definitions
are not claimed to be definitionally equal. No Lean source or headline is
changed by this audit. The fingerprint is the declaration's own fingerprint;
this review does not certify every transitive dependency or clear other ledger entries.

Historical comparisons use the last matching snapshots recorded in the stale
inventory: `54b23c22` for `applyConv` and the subfield nonzero theorem,
`ce1a1e5f` for the two convolution bounds, `c92d56ad2` for the MAC profiles,
and `f01311529` for the Falcon parameters and Goldilocks points. These snapshots
belong to the predecessor repository. Original review references were the
September 30 closure audit and C59, C64, C67 and C77 in its audit record.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Conv.applyConv` | 12896390872165959944 | 18152941879573381012 |
| `GordieHowe.Conv.convMax_gf2_128` | 2351791662 | 1216667239 |
| `GordieHowe.Conv.convMax_gf2_256` | 1833836712 | 2039754156 |
| `GordieHowe.MACProfile.rom` | 3829873919077416897 | 15095298997202968332 |
| `GordieHowe.MACProfile.qrom` | 1048278882999986205 | 3907719758168097059 |
| `GordieHowe.falcon512` | 1357415618336483155 | 3139863575530295863 |
| `GordieHowe.Ligero.Relative.Shape.goldPoints` | 14263750785288971136 | 12507134261367515937 |
| `GordieHowe.gf2_256SubfieldGen_ne_zero` | 3696368253 | 2555192163 |

## Convolution and the two MAC profiles

`Conv.applyConv` changed substantively. The old algorithm repeatedly reduced
integer coefficients down from degree `2w-2`; the current algorithm reduces each
monomial in the binary polynomial quotient first and sums the resulting 0/1
coefficient vectors with integer multiplicities. These are different integer
lifts of the same binary product, so carrying the old audit through a rename
would be incorrect.

The current definition sums exactly `k = 0,...,2w-2`. `prodCoeffs` sums every
ordered pair of input indices with `i+j=k`, and `reduceBit` is bit `m` of
`X^k mod (X^w + sum X^t)`. This matches `mac_reduction`, `mac_reduce`,
`mac_columns` and `mac_conv_max` in `lib/gordiehowe/ops/operators.h`: reduction
supports are computed with XOR, then integer product multiplicities are added
once into each supported output coordinate. No modulo reduction of those integer
multiplicities is silently inserted. Width zero has no output coordinate and
an empty supremum; the concrete profiles have positive widths and taps below
those widths. The multiplication interpretation uses the explicit characteristic
two and reduction-rule hypotheses in `applyConv_eval`; the bit-input bound uses
explicit `rb <= 1` and `x <= 1` hypotheses in `applyConv_le_convMax`. Neither
restricts a cheating prover by an unstated assumption.

`Conv.convMax_gf2_128` now states exactly `504`, replacing `506`;
`Conv.convMax_gf2_256` states exactly `1017`, replacing `1027`.
Their named packed-computation theorem proves the same supremum as the direct
sum. The 32-bit lanes cannot overflow: each row sum is below `(2w-1)*w`, which
is below `2^32` at both widths. Both concrete proofs use kernel evaluation.
An independent exact integer calculation reduced the monomials by polynomial
long division and summed their triangular multiplicities; maxima were `504`
at row 7 and `1017` at row 10. This calculation corroborates the statement
review; it is not used as a Lean axiom.

`MACProfile.rom` uses width 128, taps `{0,1,2,7}`, bound 504 and its proved
equality. `MACProfile.qrom` uses width 256, taps `{0,2,5,10}`, bound 1017 and
its proved equality. Each profile agrees with the corresponding
`Shape<128>`/`Shape<256>` in `lib/circuits/mac/linear_mac.h` and the current
C++ integer lift above. These are corrected bounds for the current operation,
not smaller bounds asserted for the old operation. No new hypothesis or change
to the underlying binary-field distribution is introduced by either profile.

Disposition: all five declarations pass the current semantic/conformance review.

## Falcon-512 parameters

`falcon512.S` changed from `512+127 = 639` to `512+205 = 717`.
The remaining fields remain `q=12289`, `n=512`, squared norm bound `34034726`,
40 nonce bytes and 625 payload bytes. They agree with `FalconSpec512` and
`FalconSet` in `lib/gordiehowe/examples/falcon/falcon_params.h`; the payload is
`666 - 1 - 40 = 625`, and its unary budget is `8*625 - 9*512 = 392`.
The arithmetic side conditions are closed facts, including
`2048 <= 12289`, `34034726 < 12289^2`, `512 <= 717`,
`5*12289 = 61445 < 65536`, and `128` dividing `16*512`.

The C++ bounded sampler chooses the least count with
`Pr[Bin(K,61445/65536) < 512] <= 2^-256`.
An exact integer comparison of
`sum(j=0..511, binom(K,j)*61445^j*4091^(K-j)) * 2^256`
with `65536^K` fails at 716 and succeeds at 717. The failure event is monotone
in K by coupling successive trials, so checking these adjacent counts establishes
the boundary. At the old count 639 the inequality fails. Rounded logarithms
are about -253.983 and -256.187 for 716 and 717; these are explanatory only,
while the acceptance comparison used integers. Increasing this bounded loop
changes honest completeness accounting and the circuit shape; it does not
exclude adversarial randomness or add an uncharged conditioning event.

Disposition: the updated parameter record passes; this does not certify every
consumer's sampler theorem or claim that the old and new protocols are identical.

## Goldilocks evaluation points

`Ligero.Relative.Shape.goldPoints` changed from subgroup points `P_i` to
`Y_i=(P_i-P_0)/(P_1-P_0)`. `goldSubgroupPoints` retains the primitive
`2^32`-th root and 32-bit reversal order used by
`BasicFpReedSolomon` in `lib/algebra/reed_solomon_fp.h` and the subgroup encoder.
`Points.normalize` proves injectivity from the original point injectivity and
`1 < 2^32`; hence its denominator is nonzero. In particular `Y_0=0` and `Y_1=1`.

The C++ `split_points` in `lib/ligero/ligero_param.h` interpolates exactly the
line with values zero and one at positions zero and one. Its values are these
normalized points. The affine change of variable has nonzero slope, so it
preserves polynomial degree bounds and the evaluation vectors (including the
message coordinates) after composition. It does not collapse the evaluation
domain. The new statement is faithful to mask recombination; interpreting it
as the old raw subgroup point function would be incorrect. The explicit
field/algebra parameters permit the intended Goldilocks extensions without
adding an assumption about a prover or challenge. The subfield membership
proof closes under subtraction and division.

Disposition: the normalized point definition passes the current review.

## Nonzero subfield generator

`gf2_256SubfieldGen_ne_zero` still states that the named subfield generator is
nonzero, without a new binder or premise. Its representation changed from the
abstract quotient field to executable `BitVec 256` field operations.
`gf2_256ToSpec_root` maps the executable root (bits `2`) to the old quotient
root, and the ring equivalence preserves powers, zero and one.
The exponent remains `(2^256-1)/(2^16-1)`, exactly the product of the factors
`2^(2^i)+1` for `i=4,...,7` in the C++ `subfield_generator` loop.

The current proof uses the independently established equality `g^65535=1`:
assuming `g=0` gives `0=1` since 65535 is positive. There is no probabilistic
premise, nonzero assumption hidden in a new parameter, or circular use of this
theorem. The preceding power theorem uses the nonzero polynomial root, proved
from its failure to lie in the subfield. This is a representation migration,
not a weakened nonzero claim.

Disposition: this theorem passes the current statement review.

## Validation and scope

The latest completed combined native environment built successfully, with all
714 own headline fingerprints and axiom sets unchanged versus its integration
baseline and trust count zero. The eight reviewed declaration fingerprints in
that environment agree with the inventory and tracked closure. Their source
files are unchanged between that environment and the reviewed source commit.
This audit changes only the ledger and this report; it does not claim the final
develop gate has run or the remaining stale declarations have been reviewed.
