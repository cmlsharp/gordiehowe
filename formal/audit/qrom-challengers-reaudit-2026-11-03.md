# QROM challenger re-audit, 2026-11-03

Scope: 3 declarations at source commit `46c629440`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.QROM.simExtChallenger` | 6264781432830878881 | 7208292455709280566 |
| `GordieHowe.QROM.realChallenger` | 2552015291673630600 | 5487251572875582294 |
| `GordieHowe.QROM.simChallenger` | 11488529948045557720 | 15083829551878611835 |

## Shared game boundary

These are mathematical challengers that store a coin distribution and reply
programs. Their current program arguments are `NARG.Prover` and
`NARG.Simulator`, the counted program forms previously named ProverProg and
SimulatorProg. This ancestry is explicit in pass P5, not the earlier
function-valued prover/simulator names.

All three use a tape indexed by Fin Q and the independent product of the
original per-request coin law. They preserve the exact request budget Q and
the underlying program's query budget. They select coins at history.length
only after proving it is strictly below Q; an exhausted budget gives a pure
none response with no assignments. At Q=0 every response takes that branch.
The query proof uses the original program bound on the successful branch and
zero queries otherwise. Binding a pure reply adds no query. The definitions
do not erase failed requests from the game history to obtain extra coins.

## Real challenger

`QROM.realChallenger` is compared with `f01311529`, in
`Model/Quantum/Interactive/ZeroKnowledge.lean`. Its reply equations are
unchanged apart from the program interface's name. For a request within budget,
it checks the supplied relation on exactly the requested statement/witness.
A valid request runs P.prog on those inputs and that index's coins, returns
its proof and no assignments. An invalid request returns none and no
assignments. It does not require the adversary to submit valid requests as an
external hypothesis, replace P.coins by uniform coins, or reprogram the oracle.

Disposition: the real challenger passes input, coin-law and relation-branch
review.

## Simulated zero-knowledge challenger

`QROM.simChallenger` is compared with `3761d9300` in the same historical
module. It checks the same relation and budget as the real challenger but
runs S.prog with only the statement and current coins. The witness is used
only in the common validity check, not passed to the simulator program. The
actual simulated proof and assignment list are returned together; invalid
or exhausted requests produce neither assignments nor a proof. Its product
coin law uses S.coins, the uniform finite simulator law, without conditioning
on validity or successful simulation. Current bisimulation lemmas retain the
link with the corresponding pure-oracle environments.

Disposition: the simulated challenger passes witness-access, assignment and
coin-law review. No equality with the honest prover's distribution is assumed
by this definition; zero knowledge is a separate theorem obligation.

## Simulation-extractability challenger

`QROM.simExtChallenger` is compared with `5831d8fbc` in
`PQ/Quantum/Interactive/SimChallenger.lean`. Its reply body is now the named
`simExtRespond`, whose branches are the same as the old inline body. Unlike
the zero-knowledge request type, its request is only a statement. Every
statement within the request budget is passed to S.prog; no witness, relation
membership test or valid-statement hypothesis was added. Thus the simulated
proof oracle is available on arbitrary statements as required by this game.
It returns that run's proof and assignments unchanged, and reads only the
current request index's coins.

Disposition: the simulation-extractability challenger passes unrestricted-input,
program-extraction and budget review. This audit does not mistake the game
challenger for the extractor or claim the extraction theorem from its existence.

## Validation scope

All three own fingerprints match the tracked closure and the completed combined
environment. Both reviewed source files are unchanged from that compiled
snapshot. Only these ledger rows and this report change. The noncomputable
mathematical PMF bundles are not certified as executable samplers by this
review, and no runtime exception is added. Final-head closure reconciliation
and the separate computability acceptance remain required.
