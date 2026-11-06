# Interactive quantum register re-audit, 2026-11-03

Scope: 37 declarations at source commit `c96123763`.

| Declaration | Previous fingerprint | Reviewed fingerprint |
|---|---:|---:|
| `GordieHowe.Quantum.Challenger.outWith` | 2039419890956860901 | 12462548479466560586 |
| `GordieHowe.Quantum.Challenger.regState` | 10310365286284411716 | 5006452829902833267 |
| `GordieHowe.Quantum.IAlg.step` | 2993301576484914606 | 3901030443335616718 |
| `GordieHowe.Quantum.IAlg.toKindAlg` | 17469582994115709223 | 14461722115500812337 |
| `GordieHowe.Quantum.KindAlg` | 434269858 | 3476572296 |
| `GordieHowe.Quantum.KindAlg.CCl` | 12516034291280220531 | 14600347947183450524 |
| `GordieHowe.Quantum.KindAlg.CW` | 11517981148805686209 | 2503062812981808682 |
| `GordieHowe.Quantum.KindAlg.R` | 802735830363262547 | 12187809034096347082 |
| `GordieHowe.Quantum.KindAlg.W` | 1492629125451695158 | 9032849229463425953 |
| `GordieHowe.Quantum.KindAlg.advAss` | 18297519989506273551 | 4754413128478650741 |
| `GordieHowe.Quantum.KindAlg.advKraus` | 16088662288833353994 | 513553221699853913 |
| `GordieHowe.Quantum.KindAlg.advQueries` | 16064484967669979827 | 14705549996860246848 |
| `GordieHowe.Quantum.KindAlg.advSplit` | 1192585207722482728 | 940356453767749201 |
| `GordieHowe.Quantum.KindAlg.advSwap` | 12774305173869811645 | 15964838013355281892 |
| `GordieHowe.Quantum.KindAlg.ansOf` | 10130010947453820526 | 16383503156604674462 |
| `GordieHowe.Quantum.KindAlg.chalAss` | 9360078969286360629 | 10377742065740042432 |
| `GordieHowe.Quantum.KindAlg.chalInput` | 16341382922941291208 | 2640186479219192311 |
| `GordieHowe.Quantum.KindAlg.chalQueries` | 13587805035773674773 | 14067580319152863566 |
| `GordieHowe.Quantum.KindAlg.copyReq` | 12484422399060585847 | 15884041944944473978 |
| `GordieHowe.Quantum.KindAlg.garSwap` | 14762125923313350233 | 17651507675432041052 |
| `GordieHowe.Quantum.KindAlg.init` | 14084009566180528778 | 7823667546799696643 |
| `GordieHowe.Quantum.KindAlg.initSys` | 1404917162572628326 | 6452930501905912132 |
| `GordieHowe.Quantum.KindAlg.kind` | 5462233480354076745 | 8661072938971272946 |
| `GordieHowe.Quantum.KindAlg.measReq` | 12858501480382863573 | 3138038314335632778 |
| `GordieHowe.Quantum.KindAlg.mk` | 1759387734 | 296402561 |
| `GordieHowe.Quantum.KindAlg.post` | 1568685477834797307 | 16215994407730126660 |
| `GordieHowe.Quantum.KindAlg.postAss` | 14672249885573480496 | 10918432390592064777 |
| `GordieHowe.Quantum.KindAlg.postCirc` | 8703842593547008355 | 9109103512822970370 |
| `GordieHowe.Quantum.KindAlg.prepChal` | 16846149775276062100 | 7657699265390708662 |
| `GordieHowe.Quantum.KindAlg.reply` | 439442597707466569 | 18279419362298108841 |
| `GordieHowe.Quantum.KindAlg.reqOutcome` | 5864424669217532469 | 11734365184976980003 |
| `GordieHowe.Quantum.KindAlg.slots` | 5103893251394965675 | 10689310958036282998 |
| `GordieHowe.Quantum.KindAlg.stateAt` | 12738626076609083845 | 12095269571618747052 |
| `GordieHowe.Quantum.KindAlg.step` | 7648535262941571431 | 11142247056251081553 |
| `GordieHowe.Quantum.KindAlg.width` | 12577163240408666779 | 10310018983576047174 |
| `GordieHowe.Quantum.KindAlg.writeReply` | 16435662338100032336 | 1545754532752858033 |
| `GordieHowe.Quantum.instDecidableEqCWork` | 2136983800765299462 | 11649280712279390178 |

## Historical changes and scope

The last matching sources are `5831d8fbc` in
`PQ/Quantum/Interactive/Basic.lean` and `f01311529` in
`GordieHowe/Model/Quantum/Interactive/Basic.lean`, as recorded per entry in the
inventory. The complete diff from the latter source separates KindShape from
KindAlg and moves OracleProg's import. The earlier source also precedes the
extraction of outWithOf/regStateOf, which lets state reconstruction read the
reply programs without reading their stored mathematical distribution. The
review below checks the actual current computations, not only those diffs.

## Algorithm shape and fields

`KindAlg` now takes `KindShape` as a type index. The shape holds the same
workspace, its finite/equality instances, positive width, slot and post counts,
and finite Kraus index that were formerly fields of KindAlg. `KindAlg.mk`
still requires kind, initial state, step maps and output, with their types
indexed by precisely that shape. No new predicate on adversaries, request
values or oracle answers is inserted. Positive width was already required.

`KindAlg.W`, `R`, `width`, `slots` and `post` read those exact shape components.
They no longer unfold algorithm bodies to recover the types/counts. The
projections `kind`, `init` and `step` return the supplied kind function, mixed
state and Kraus-map family. StepIdx still contains slots+post+1 indices,
including the final step; zero slots/post does not remove that final map.
`IAlg.step` retains the corresponding static-schedule step family. These
fields do not silently impose trace preservation beyond their declared types;
that property is stated separately where needed.

Disposition: the two KindAlg data declarations, five shape accessors, three
behavior projections and IAlg.step pass field, parameter and index review.

## Reconstructing challenger state

`Challenger.outWith` forwards the original reply program and supplied answer
list to outWithOf. If the program has not returned, its default is no response
and no assignments. It does not select an answer making the program succeed.
`Challenger.regState` forwards only Q and the reply programs to regStateOf.
The recursion starts with empty history/assignments, reads each slot below j
in order, ignores blank logs and appends a request and its response only while
the existing history length is below Q. Its assignment list appends after the
old list, consistent with later-update precedence. Requests yielding none
still consume a history entry while within budget; failed replies are not
removed to grant extra requests. Slots beyond the log-array length preserve
state. These are the same equations as the earlier recursive definition.

`KindAlg.CCl` is the challenger registers at exactly the shape's slot count
and C.q, with C.Coins. `CW` pairs these with the adversary's registers at its
workspace and width. `instDecidableEqCWork` transports equality through the
explicit product equivalence and supplied component instances, so different
coin/log/query components are not identified.

`ansOf` lists answer components for every challenger query position in order.
`stateAt` reconstructs the challenger state using those answers, that register's
coins and its logs, at the supplied prefix length. Neither reads an external
oracle to invent missing answers. `reply` returns none for a blank slot or an
exhausted request budget; otherwise it reads outWith at the state before the
slot. These six register/state entries preserve the actual transcript rather
than a successful subhistory.

Disposition: the six register/state entries and two challenger wrappers pass
component and budget review.

## Request measurement and reversible register operations

`reqOutcome` returns some request exactly on branches whose workspace kind is
true; query branches have outcome none. `copyReq` swaps none and that request
in the selected log on request branches and leaves other components unchanged.
Its map is an involution even on arbitrary nonblank logs; fresh-log reachability
is a separate execution invariant. `measReq` first measures reqOutcome and then
applies the copying permutation, as given by KrausMap.comp's order.

`writeReply` acts only when the slot log is filled, swapping none and the
computed reply in the response register. It is not a destructive overwrite
on arbitrary basis states. `garSwap` exchanges the active query pair with
exactly the challenger's slot/query coordinate. `advSwap` exchanges it with
exactly the chosen adversary query coordinate. The pairSwap update laws and
involution proofs retain all other registers. `advSplit` is a reversible
reassociation of adversary and remaining registers, with reflexive inverse
laws. `advKraus` tensors the actual adversary step with identity on those
remaining registers and reindexes through that equivalence; it does not give
the adversary operations on challenger coins or logs.

Disposition: these eight measurement/permutation/lifting entries pass branch,
register-preservation and operation-order review.

## Queries and assignments

`chalInput` uses the next query of the reply program after the first i stored
answers, at the history before slot j. Blank logs, exhausted Q and terminated
programs use the fixed padding input. `chalAss` supplies the assignments in
force only if that same request is within budget and its program still wants
a query at that answer prefix. Otherwise it supplies padding assignments.
`prepChal` swaps the padding input with chalInput without changing the answer
component; the swap is involutive.

`advAss` uses the assignments after the slot on a query branch and padding on
a request branch. On a blank request log, reconstruction leaves the state
unchanged, so reading j+1 does not introduce an unmade request. `postAss` reads
the assignments after all slots. These definitions use the original fixed
padding construction; this audit does not replace its mathematical choice or
certify it as an executable extractor.

`advQueries` emits exactly width query steps in finite-index order, swapping
each pair in and back around its reprogrammed query. `chalQueries` emits
exactly C.q steps, preparing each input and moving its query pair to the
appropriate saved register. Terminated branches still use padding; the query
count is an upper bound and does not discard those steps. `postCirc` applies
the appropriate adversary map followed by width queries at the final
assignments. The existing query-count lemmas confirm these exact counts.

Disposition: these eight query/assignment entries pass prefix, branch and
count review. The padding and quantum mathematical constructions remain
subject to the separate runtime policy; no exception is added here.

## Initialization and static-schedule translation

`initSys` mixes over exactly C.coins, tensors the original adversary initial
state with blank logs and clean challenger/active query registers, and
reassociates them through advSplit. The adversary state does not depend on the
sampled challenger coins. No successful-response event conditions the mixture.

`IAlg.toKindAlg` keeps the old counter translation. Its shape has workspace
A.W times Fin(slots+1), the same width, slot/post counts and Kraus index. The
counter starts at zero. The maps before slots advance it once, and cntKind
reads schedule[counter-1] on nonzero counters. The counter has room for values
zero through slots, so the final slot does not wrap to zero; post maps do not
advance it. The old adversary map is tensored with identity on the counter
and then followed by that counter permutation. Output discards only the
counter. The translation does not claim a static schedule models every
adaptive schedule; it embeds the declared static one.

Disposition: both entries pass distribution, counter and zero-slot review.

## Validation scope

Each of the 37 listed entries is covered above and has its own old/current
fingerprint in the table. The current hashes match the tracked closure and
completed combined environment; the source module is identical to that built
snapshot. No Lean source, hypothesis, distribution or acceptance predicate
changes. This is a semantic audit of these declarations, not a new proof of
the complete quantum simulation theorem or a runtime exemption. Final-head
closure reconciliation remains required.
