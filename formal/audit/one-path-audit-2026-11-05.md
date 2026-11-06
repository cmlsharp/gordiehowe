# One construction path audit, 2026-11-05

Scope: the declarations that the one-path change to a program's certified objects adds, moves or
restates. A program's data (`ProgramData`) now extends its computational inputs (`RuntimeInputs`,
`CompletionInputs`). Every condition and accessor that reads only those inputs is defined once, on
`RuntimeInputs`. The proof system and the certified data are built only by
`RuntimeInputs.proofSystemOf` and `RuntimeInputs.certified`. Rows whose declaration is unchanged
keep their existing ledger rows. Fingerprints were computed with the statement closure's formula at
the change's source tree, over its modules `GordieHoweNative.Language.ProgramData`,
`GordieHowe.Language.ProgramCheck` and `GordieHowe.Applications.Program.{Conditions,Runtime,FiguresCheck}`.
The next closure regeneration must reconcile them.

## Findings

No row has a semantic defect. Each condition states the same predicate as the `ProgramData` form it
replaces, now read through `d.inputs` and `d.completion`.

- `FieldOkAt`, `TableausFit` and `ProgramData.FiguresOk` still quantify over proofs of an earlier
  condition, so each holds vacuously when that condition fails. Every reached use supplies the proof
  from the same structure: `RuntimeInputs.ready` uses `h.fields i h.tableaus`, and
  `ProgramConditions.fullFacts` uses `h.figures h.toCoreConditions h.coded`.
- `ProgramData.FiguresOk` quantifies over `CoreConditions` only because the application frontends
  call it as `conditions.figures conditions.toCoreConditions conditions.coded`. The same fact is
  `conditions.fullFacts.figures`.
- `CodedOk` is unsatisfiable for `MDL.ECDSA.ROMParams`, unchanged: that program is core-only.

## Declarations read

Names are relative to `GordieHowe`.

**Data.** `ProgramData.inputs` and `ProgramData.completion` are the two parent projections;
`d.program`, `d.plan`, `d.fieldTable`, `d.tableaus` and `d.figures` are `d.inputs`'s fields, and
`d.records`, `d.gens`, `d.cderivs` and `d.nodes` are `d.completion`'s. `Hints` keeps the expression
annotations, the realization's derivations and the assignment-read rows, which only `programOkB`
reads. `ProgramData.mk`, `hints`, `circuits`, `shapes` and `sourceRoles` are the remaining fields.

**Conditions.** `RuntimeInputs.FieldOkAt` states `fieldOkB` at the program's domain field, the
registry's packing and the tableau of every proof of `TableausOk`. `FieldsOk` ranges over
`Fin r.program.domains.length`. `FieldTableOk` applies `RealizedProgram.FieldTable` to the field
table's lengths and lookups. `NoProduct` and `NoFieldForm` are implications from the field table's
flags, as before. `CompletionOk r c` is `completionB` at the plan's prime nodes and `c`'s nodes,
records, generators and derivations, the same term as `ProgramData.completionPartB` at `d.inputs` and
`d.completion`. `RolesOk r c` is `honestRolesB` at `c`'s nodes and records, the same term as
`rolesB`. `ProgramData.CircuitsOk` is unchanged in text; its fingerprint moved because `d.interp`
and `d.fieldTable` now read through `d.inputs`. `ProgramData.FiguresOk` is
`RuntimeInputs.FiguresFacts` at `h.readyFacts` for every `h : CoreConditions d` and codec fact.
`RuntimeInputs.FiguresFacts.loads` is the Chernoff test at the default stream's byte count when the
figures claim default loads, the field `ProgramData.FiguresAt` had.

**Construction.** `RuntimeInputs.ready` builds `FieldReady` from the registry's packing, the tableau,
`h.fields i h.tableaus` and well-formedness. `RuntimeInputs.certified` reads only the inputs, the
completion inputs and erased facts; `completionOk` and `rolesOk` take `FullFacts.completion` and
`FullFacts.roles`, whose types are `CompletionOk r c` and `RolesOk r c`. `FullFacts.figures` is
`FiguresFacts` at its `ready` and `coded`. `ReadyFacts.fields` is `r.FieldsOk`.

**Transport.** `CoreConditions.readyFacts`, `coreFacts`, `checks` and `hdom` state the facts the
proof system reads, at the program's own data. `CoreConditions.certs` states that the GKR certificates
exist at source parts equal to `d.parts`, inside `Nonempty`. `ProgramConditions.fullFacts` states
`d.FullFacts d.completion`.

## Shallow rows

The rows marked shallow are structure projections and constructors. Their content is the declaring
structure's, reviewed above.

## Rows

| Declaration | Kind | Fingerprint |
|---|---|---:|
| `GordieHowe.CoreConditions.certs` | read | 1644386542 |
| `GordieHowe.CoreConditions.checks` | read | 4120281443 |
| `GordieHowe.CoreConditions.coreFacts` | read | 1313127504 |
| `GordieHowe.CoreConditions.hdom` | read | 3847052753 |
| `GordieHowe.CoreConditions.readyFacts` | read | 2345383751 |
| `GordieHowe.CoreConditions.tableaus` | shallow | 151018182 |
| `GordieHowe.CoreConditions.wellFormed` | shallow | 2994672687 |
| `GordieHowe.Hints.mk` | shallow | 3106827317 |
| `GordieHowe.ProgramConditions.fullFacts` | read | 1345315091 |
| `GordieHowe.ProgramData.CircuitsOk` | read | 14399290469102063671 |
| `GordieHowe.ProgramData.FiguresOk` | read | 4421659910585372023 |
| `GordieHowe.ProgramData.circuits` | shallow | 1020898817606266969 |
| `GordieHowe.ProgramData.completion` | shallow | 7146586874030583656 |
| `GordieHowe.ProgramData.hints` | shallow | 5537337718852365425 |
| `GordieHowe.ProgramData.inputs` | shallow | 2660472481873609812 |
| `GordieHowe.ProgramData.mk` | shallow | 94854744 |
| `GordieHowe.ProgramData.shapes` | shallow | 13759274717328862888 |
| `GordieHowe.ProgramData.sourceRoles` | shallow | 9222483647985846212 |
| `GordieHowe.RuntimeInputs.CompletionOk` | read | 2200572227312023760 |
| `GordieHowe.RuntimeInputs.FieldOkAt` | read | 657870614899094220 |
| `GordieHowe.RuntimeInputs.FieldTableOk` | read | 12103113184476247830 |
| `GordieHowe.RuntimeInputs.FieldsOk` | read | 3496194084601005267 |
| `GordieHowe.RuntimeInputs.FiguresFacts.loads` | shallow | 852100960 |
| `GordieHowe.RuntimeInputs.FullFacts.completion` | shallow | 4201649948 |
| `GordieHowe.RuntimeInputs.FullFacts.figures` | shallow | 2154032816 |
| `GordieHowe.RuntimeInputs.FullFacts.roles` | shallow | 4149783306 |
| `GordieHowe.RuntimeInputs.NoFieldForm` | read | 18343980910332830347 |
| `GordieHowe.RuntimeInputs.NoProduct` | read | 13344536711332741213 |
| `GordieHowe.RuntimeInputs.ReadyFacts.fields` | shallow | 1643932532 |
| `GordieHowe.RuntimeInputs.RolesOk` | read | 10432577996593376492 |
| `GordieHowe.RuntimeInputs.certified` | read | 13690310007553054300 |
| `GordieHowe.RuntimeInputs.ready` | read | 4327973469753882581 |
