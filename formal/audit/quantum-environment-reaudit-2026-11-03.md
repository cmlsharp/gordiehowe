# Quantum environment re-audit, 2026-11-03

Scope: 8 declarations at source commit `ab214973d`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Quantum.Env` | 3672836471 | 3185776673 |
| `GordieHowe.Quantum.Env.mk` | 3882931785 | 2253415929 |
| `GordieHowe.Quantum.Env.oracle₀` | 17212977515988608050 | 9894562570119978872 |
| `GordieHowe.Quantum.Env.respond` | 2631582100783361286 | 5791302014047112539 |
| `GordieHowe.Quantum.Env.μ` | 6297665998928804193 | 8092156322464688834 |
| `GordieHowe.Quantum.GameReg` | 9757933727867967714 | 5653839460107206146 |
| `GordieHowe.Quantum.requests` | 2896473710484860726 | 8826765475161672042 |
| `GordieHowe.Quantum.splitLogs` | 13889366409348113397 | 11979771202967763789 |

## Environment interface

All eight entries were last matched in `54b23c22b`, in
`PQ/Quantum/Game.lean`. The current source is `Model/Quantum/Pure/Game.lean`.
The historical environment state was exactly an oracle function. The current
`Quantum.Env` has an explicit state type St, defaulting to that function
type, and a named `EnvReply` holding the optional answer and updated state.
This is a real interface generalization, not just a namespace rename.

`Env` still stores a tape PMF, an initial state function of the tape, and a
deterministic response function of tape, bounded request index, request and
current state. It does not store a quantum operation under the name of a
classical response. A consumer needing an oracle from a general state obtains
it through `OracleState.toOracle`; the default function instance is identity.
An arbitrary Env alone does not promise any correctness or security property.

`Env.mk` requires all three fields and adds no hidden property of requests or
adversaries. `Env.μ` projects the original tape law; it does not condition on
successful replies. `Env.oracle₀` projects the initial state function, despite
its historical name, and does not itself assert that St is a function type.
`Env.respond` projects the exact supplied transition. Its index is `Fin Q`,
so the transition cannot be called with an out-of-budget index through that
interface. It may return none while changing state; none denotes an absent
response and is not by itself an assertion that no transition occurred.

The consuming `update` and `answerAfter` implement the boundary explicitly:
requests numbered Q or later preserve the state and return none, respectively.
`oracleIn` applies transitions in request order with zero-based indices.
At Q=0 no bounded response index exists, and every consumer uses the
out-of-budget branch. The previous implementation had the same boundary and
sequence, with product projections instead of the named reply fields.

Disposition: the structure, constructor and three field projections pass the
state, distribution and budget-boundary review. This semantic review does not
certify arbitrary PMFs or quantum game states as executable algorithms.

## Registers and logs

`Quantum.GameReg` retains the old nested-product layout: a query register
whose workspace includes W, the request register, the optional response and
one optional request log for each of m slots. It contains both the adversary
registers and the logs; it does not discard the logs or replace them by their
length. The query registers remain outside that workspace product as required
by `QueryReg`.

`Quantum.splitLogs` is the explicit reassociation into a distinguisher register
and the log function. Its forward map preserves workspace, request, response
and query registers and extracts the original log component; its inverse
reinserts exactly that component. Both inverses remain reflexive. Thus this
operation cannot identify two different histories or erase entanglement by
collapsing basis coordinates. It is a basis equivalence, not a measurement
or an assertion that the two components are probabilistically independent.

`Quantum.requests` still calls `requestsBefore lg m`. That recursion appends
slot k when passing from k to k+1, using Option.toList to omit blank slots.
The result therefore contains all filled logs in increasing slot order,
including repeated equal requests. At m=0 it is empty. It does not filter
invalid requests, deduplicate them, sort by request value, or truncate at the
environment's Q; the environment's separate request budget handles the latter.
For a general log array it records every filled slot, while reachable-log
invariants elsewhere justify which slots can be filled during an execution.
No reachability hypothesis is silently required by this list function.

Disposition: the register abbreviation, basis equivalence and request-list
function pass preservation and order review. This does not independently
certify all deferred-measurement or quantum-unitarity theorems using them.

## Validation scope

All eight own fingerprints match the tracked closure and the completed combined
environment. The reviewed source file is identical to that compiled snapshot.
Only these eight ledger rows and this report change. Final-head closure
reconciliation and runtime acceptance remain separate checks.
