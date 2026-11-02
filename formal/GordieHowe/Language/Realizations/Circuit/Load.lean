-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public meta import Lean.Elab.Command
public meta import GordieHowe.Language.CertCheck
public meta import GordieHoweNative.Codecs

public meta section

/-!
# GordieHowe: loading a `.ghc` file, and the GKR certificates' checks

`load_ghc "path.ghc" "hash"` reads a `.ghc` file (the container of `GordieHoweNative/Ghc.lean`,
written by the C++ compiler's GHC writer) beside the current source file at elaboration time,
checks its FNV-1a 64 hash against `hash` (so the `.lean` text changes whenever the data does, and
Lake rebuilds), and adds one definition per section, in the file's order, named by the section
under the current namespace and of the section's type (`Ghc.loadDefs`). The value is the
expression of the section's decoded value: every natural number a raw literal, each value's
repeated subterms shared, an index map the program's `idx<j>` resolved in scope, a reference to an
earlier section that section's definition, and a list longer than `Ghc.listRun` items continued in
definitions `<def>_l<i>` of `Ghc.listRun` items each, so no term nests deeper than about
`Ghc.listRun`. Nothing is elaborated per value. The decoding and the term building are compiled
code (the precompiled library `GordieHoweNative`). A section flagged `compile` gets compiled code
with its runs; the writer flags the parts a proof system built from the data runs (for a GKR
circuit, the parts its GKR source reads, `ProgramCerts.src`: `name.consts`, every
`name.layer<d>`, `name.layered`, `name.width`), and the data only the checks read gets none. Both
check modes load the file this way (`loadFile`); in native mode (`GordieHowe.certCheckNative`)
`LoadNative.lean` elaborates the command, adding run-time readers for the sections flagged
`reader` after the definitions. The kernel checks every added definition, so loading adds no
trust; it is not a search.

A GKR circuit's certificate file (`GKR/<domain>.ghc`) has the sections of `name : CircuitData`
(`name.consts`, the DAG's large subtrees `name.dagPart<i>` and `name.dag`, per layer
`name.layer<d>` and `name.wtab<d>` with their names' last component extended, `name.layered`,
`name.width`, `name.sched`, the node table's large subtrees `name.nodes<i>` and `name.table`,
`name.entries`, and `name`), the composite ones in spine form, referring to their parts.

`check_entry name ar k [parts]` adds
`name.entry<k>_ok : entryCertB Program.program name.c ar name k = true` by the entry's plan
`parts`, which the C++ exporter computes (`emit_export.h`'s `plan_entry`, the one planner) and
writes into the module text: a list of triples, `(0, 0, m)` a run of `m` consecutive nodes,
`(1, S, m)` one node's cuts in `m` slices of `S` (the last one every cut left), and last
`(2, S, m)` the family cuts in `m` slices of `S`. Its **leaf theorems**, numbered in order, are the
entry's head (`entry<k>_head`), then per part its nodes' theorem (`entry<k>_p<j>`) or its slices'
(`entry<k>_p<j>_s<i>`, `entry<k>_f<i>`), each by `gh_cert_check`. They are composed with no
re-check: the parts in a balanced tree by `entryNodesB_append` (a large node's slices by
`nodeSliceB_append` and `nodeSliceB_cons`), the family slices by `famSliceB_cons`, and the whole by
`entryCertB_of_parts`. A plan is untrusted: a wrong one fails a check or the composition.

An entry too large for one module is checked in part modules that build in parallel:
`check_entry_leaves name ar k [parts] i j` adds only the leaf theorems `i` to `j - 1`, and
`compose_entry name ar k [parts]`, in a module importing the part modules, adds
`name.entry<k>_ok` from the imported leaf theorems, checking none. Its statement is
`check_entry`'s. `check_circuit name ar` adds
`name.circuit_ok : circuitCertB Program.program name.c ar name = true` from the header and the
entries' theorems (`circuitCertB_of_entries`). The header is checked by parts (`headerB_of_parts`),
each by `gh_cert_check` except two whose checks read every gate:

* the scheduling certificate (part 1, `check_of_parts`): the layers one by one (`layersOk_cons`), a
  layer of more than `layerSliceGates` gates in slices of that many gates (`layerSliceOk_cons`,
  `layerOk_of_slices`); the asserted nodes by `assertsOk_of_cover`, with no sort: per layer its
  gate count and asserting-gate count (`infoSliceB`, in the same slices, `infoSliceB_cons`, then
  `layersInfoB_cons`), the asserted nodes in slices of `assertSliceNodes`, each node with a
  witness the elaborator finds, an asserting gate's layer and wire or a last-layer assertion's
  index (`assertSliceOk`, `assertsFrom_cons`), and their number against the counts;
* the bridge's checks (part 2, `uniqueAssertsB_shapeB_of_info`): the same per-layer theorems, and
  the shape from the gate counts (`shapeLensB`).

Part 2 and `assertsOk`'s theorem are composed with every argument named and checked by the kernel
alone: the elaborator, comparing the data's two spellings of the width, would evaluate the checks. Every circuit takes
this path; a small layer, or a small set of asserted nodes, is one slice.
-/

namespace GordieHowe.Load

open Lean Elab Command

/-! ## Loading the file -/

/-- Add the definition `name : type := value` as it is, with the elaborator's height hint, and
compiled code when `compile` (a section flagged `compile`, and its runs). -/
def addDefRaw (name : Name) (type value : Expr) (compile : Bool := false) : CommandElabM Unit := do
  let h := getMaxHeight (← getEnv) value + 1
  -- exported, so modules importing the data (and their kernel checks) see its values
  withExporting do
    liftCoreM <| addDecl <| .defnDecl <|
      mkDefinitionValEx name [] type value (.regular h) .safe [name]
    -- the definitions are data: closed-term extraction would make each literal of a list its own
    -- auxiliary definition (the module's compilation time and its `.olean.private`)
    if compile then
      liftCoreM <| withOptions (·.setBool `compiler.extract_closed false) <| compileDecls #[name]

/-- **A loaded `.ghc` file**: the file's path and hash, the program's index maps `idx0, idx1, …` in
scope, the loading namespace, and the file's sections. -/
structure Loaded where
  /-- The file's path. -/
  path : System.FilePath
  /-- The file's FNV-1a 64 hash. -/
  hash : String
  /-- The index maps' constants, by number. -/
  idxs : Array Name
  /-- The loading namespace. -/
  ns : Name
  /-- The sections. -/
  secs : Array Ghc.Section

/-- **The file of `load_ghc "path.ghc" "hash"`, read and loaded**, in either check mode: the file
beside the current source file, its hash checked, its sections decoded (the index maps as
stand-ins) and the definitions of `Ghc.loadDefs` added in order. -/
def loadFile (stx : Syntax) : CommandElabM Loaded := do
  let some rel := stx[1].isStrLit? | throwError "load_ghc: expected a file name"
  let some hash := stx[2].isStrLit? | throwError "load_ghc: expected a hash"
  let dir := (System.FilePath.mk (← getFileName)).parent.getD "."
  let path ← IO.FS.realPath (dir / rel)
  let bytes ← IO.FS.readBinFile path
  let h := Ghc.fnv1a bytes
  unless h == hash do throwError "load_ghc: {rel}: hash {h}, expected {hash}"
  -- the program's index maps `idx0, idx1, …`, resolved in scope
  let env ← getEnv
  let scope ← getScope
  let resolve (j : Nat) : Option Name :=
    match ResolveName.resolveGlobalName env scope.opts scope.currNamespace scope.openDecls
        (Name.mkSimple s!"idx{j}") with
    | (n, []) :: _ => some n
    | _ => none
  let mut idxs : Array Name := #[]
  while true do
    match resolve idxs.size with
    | some n => idxs := idxs.push n
    | none => break
  let nIdx := idxs.size
  let ns ← getCurrNamespace
  let secs ← match Ghc.sections bytes with
    | .ok s => pure s
    | .error s => throwError "load_ghc: {rel}: {s}"
  let defs ← match Ghc.loadDefs Ghc.sectionTypes ns bytes secs
      (fun j => if j < nIdx then some (Ghc.stub j) else none) idxs with
    | .ok defs => pure defs
    | .error s => throwError "load_ghc: {rel}: {s}"
  for d in defs do addDefRaw d.name d.type d.value d.compile
  pure { path, hash, idxs, ns, secs }

/-- `load_ghc "path.ghc" "hash"`: see the module docstring. -/
syntax (name := loadGhc) "load_ghc " str str : command

/-- The elaborator of `load_ghc` in kernel mode (`loadFile`). In native mode `LoadNative.lean`
elaborates the command: the same loading, then its readers. -/
@[command_elab loadGhc]
def elabLoadGhc : CommandElab := fun stx => do
  if GordieHowe.certCheckNative then throwUnsupportedSyntax
  let l ← loadFile stx
  logInfo m!"load_ghc: {stx[1].isStrLit?.getD ""}: {l.secs.size} sections"

/-! ## The checks -/

/-- The natural of a literal (`OfNat` form or raw). -/
def natOfExpr (x : Expr) : Nat :=
  match x.getAppFnArgs with
  | (``OfNat.ofNat, #[_, .lit (.natVal n), _]) => n
  | _ => match x with
    | .lit (.natVal n) => n
    | _ => 0

/-- The items of a list expression: a `List.cons` chain, through the definitions `Ghc.chainLists`
added for its tail. -/
partial def listsOfExpr (e : Expr) : CommandElabM (List Expr) := do
  let (xs, tl) := Ghc.consChain e
  match tl with
  | .const n _ =>
    match (← getEnv).find? n with
    | some (.defnInfo v) => pure (xs.toList ++ (← listsOfExpr v.value))
    | _ => pure xs.toList
  | _ => pure xs.toList

/-- The naturals of a list expression of `OfNat` literals. -/
def natsOfExpr (e : Expr) : CommandElabM (List Nat) := do
  pure ((← listsOfExpr e).map natOfExpr)

/-- The value of a loaded definition. -/
def defValue (n : Name) : CommandElabM Expr := do
  match (← getEnv).find? n with
  | some (.defnInfo v) => pure v.value
  | _ => throwError "no definition {n}"

/-- The program's identifier `Program.program`, resolved in scope. -/
def programIdent : CommandElabM Ident := do
  let env ← getEnv
  let scope ← getScope
  for id in [`Program.program, `program] do
    match ResolveName.resolveGlobalName env scope.opts scope.currNamespace scope.openDecls id with
    | (n, []) :: _ => return mkIdent n
    | _ => pure ()
  throwError "check_entry: no Program.program in scope"

/-- The constant an identifier names in scope. -/
def constOf (id : Syntax) : CommandElabM Name := do
  let env ← getEnv
  let scope ← getScope
  match ResolveName.resolveGlobalName env scope.opts scope.currNamespace scope.openDecls id.getId with
  | (n, []) :: _ => pure n
  | _ => throwError "check_entry: unknown constant {id}"

/-- `okB x = true`. -/
def okTrue (x : Expr) : Expr :=
  mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool)
    (mkApp3 (mkConst `GordieHowe.Twin.okB) (mkConst `GordieHowe.RealizedProgram.CertFailure)
      (mkConst ``Unit) x) (mkConst ``Bool.true)

/-- `b = true`. -/
def isTrue (b : Expr) : Expr := mkApp3 (mkConst ``Eq [levelOne]) (mkConst ``Bool) b (mkConst ``Bool.true)

/-- Add the theorem `name : type := value`; the kernel checks it. -/
def addThm (name : Name) (type value : Expr) : CommandElabM Unit :=
  withExporting do
    liftCoreM <| addDecl <| .thmDecl { name, levelParams := [], type, value }

/-- A natural-number literal in the elaborator's form. -/
def lit (n : Nat) : Expr := mkNatLit n

/-- A proof of `0 < n` for a positive literal `n`. -/
def posLit (n : Nat) : Expr := mkApp (mkConst ``Nat.zero_lt_succ) (lit (n - 1))

/-- **The items joined in a balanced tree** by `join`, so a composed proof nests only
logarithmically deep; `none` for no items. -/
partial def balanced {α : Type} (join : α → α → α) (xs : Array α) : Option α :=
  go 0 xs.size
where
  go (lo hi : Nat) : Option α :=
    if hi ≤ lo then none
    else if hi = lo + 1 then xs[lo]?
    else
      let mid := (lo + hi) / 2
      match go lo mid, go mid hi with
      | some x, some y => some (join x y)
      | x, none => x
      | none, y => y

/-- `check_entry name ar k [parts]`: see the module docstring. -/
syntax (name := checkEntry) "check_entry " ident ident num "[" num,* "]" : command

/-- `check_entry_leaves name ar k [parts] i j`: see the module docstring. -/
syntax (name := checkEntryLeaves) "check_entry_leaves " ident ident num "[" num,* "]" num num :
  command

/-- `compose_entry name ar k [parts]`: see the module docstring. -/
syntax (name := composeEntry) "compose_entry " ident ident num "[" num,* "]" : command

/-- **An entry's check by its parts** (see the module docstring): its leaf theorems numbered
`i` in `leaves` (`[i, j)`; `none` for all) each by `gh_cert_check`, then, when `compose`,
`name.entry<k>_ok` from all of its leaf theorems, which must exist. -/
def runCheckEntry (stx : Syntax) (leaves : Option (Nat × Nat)) (compose : Bool) :
    CommandElabM Unit := do
  let cert := (← getCurrNamespace) ++ stx[1].getId
  let k := stx[3].isNatLit?.getD 0
  let parts := (stx[5].getSepArgs.map fun x => x.isNatLit?.getD 0).toList
  let ir ← programIdent
  let arN ← constOf stx[2]
  let certI := mkIdent cert
  let arI := mkIdent arN
  let kL := Syntax.mkNumLit (toString k)
  let entries ← listsOfExpr (← defValue (cert ++ `entries))
  let some ec := entries[k]? | throwError "check_entry: no entry {k}"
  let (elo, ehi) := match ec.getAppFnArgs with
    | (_, #[_, lo, hi, _, _, _]) => (natOfExpr lo, natOfExpr hi)
    | _ => (0, 0)
  let base := (← getCurrNamespace) ++ stx[1].getId
  -- the leaf theorems in order, each checked when its number is in `[lo, hi)`
  let leaf ← IO.mkRef 0
  let check (n : Name) (t : Term) : CommandElabM Expr := do
    let i ← leaf.modifyGet fun i => (i, i + 1)
    if leaves.all fun (lo, hi) => lo ≤ i && i < hi then
      elabCommand (← `(command| theorem $(mkIdent (`_root_ ++ n)) :
          $(mkIdent `GordieHowe.Twin.okB) $t = true := by
        gh_cert_check))
    else if compose && !(← getEnv).contains n then
      throwError "compose_entry: no leaf theorem {n} (leaf {i}); import its part module"
    pure (mkConst n)
  -- the four leading arguments of every checker and lemma
  let pre : Array Expr := #[mkConst ir.getId, mkApp (mkConst `GordieHowe.RealizedProgram.CircuitData.c)
    (mkConst cert), mkConst arN, mkConst cert]
  let rp (n : String) := mkConst (Name.mkStr `GordieHowe.RealizedProgram n)
  let num (n : Nat) := Syntax.mkNumLit (toString n)
  let headN := base ++ Name.mkSimple s!"entry{k}_head"
  let head ← check headN
    (← `($(mkIdent `GordieHowe.RealizedProgram.entryHeadE) $ir ($certI).c $arI $certI $kL))
  -- each part's proof with its first node and node count
  let mut items : Array (Expr × Nat × Nat) := #[]
  let mut fam : Option Expr := none
  let mut a := elo
  let mut j := 0
  let mut q := 0
  while q + 2 < parts.length do
    let tag := parts[q]!
    let sz := parts[q + 1]!
    let m := parts[q + 2]!
    q := q + 3
    if tag == 2 then
      -- the family cuts in `m` slices of `sz` cuts, the last one every cut left
      let mut fs := #[]
      for i in [0:m] do
        let len := if i + 1 == m then 0 else sz
        fs := fs.push (← check (base ++ Name.mkSimple s!"entry{k}_f{i}")
          (← `($(mkIdent `GordieHowe.RealizedProgram.famSliceE) $ir ($certI).c $arI $certI $kL
            $(num (i * sz)) $(num len))))
      let mut rest : Option Expr := none
      for i' in [0:m] do
        let i := m - 1 - i'
        match rest with
        | none => rest := some fs[i]!
        | some r =>
          rest := some (mkAppN (rp "famSliceB_cons") (pre ++ #[lit k, lit (i * sz), lit sz,
            mkApp (mkConst ``Nat.zero_lt_succ) (lit (sz - 1)), fs[i]!, r]))
      fam := rest
      continue
    let (pf, n) ← if tag == 0 then do
        let pf ← check (base ++ Name.mkSimple s!"entry{k}_p{j}")
          (← `($(mkIdent `GordieHowe.RealizedProgram.entryNodesE) $ir ($certI).c $arI $certI $kL
            $(num a) $(num m)))
        pure (pf, m)
      else do
        -- one node in `m` slices of `sz` cuts, the last one every cut left
        let mut slices : Array (Expr × Nat × Nat) := #[]
        for i in [0:m] do
          let len := if i + 1 == m then 0 else sz
          let pf ← check (base ++ Name.mkSimple s!"entry{k}_p{j}_s{i}")
            (← `($(mkIdent `GordieHowe.RealizedProgram.nodeSliceE) $ir ($certI).c $arI $certI
              $kL $(num a) $(num (i * sz)) $(num len)))
          slices := slices.push (pf, i * sz, len)
        let some (last, _, _) := slices.back? | throwError "check_entry: no slice"
        -- the full slices joined (`nodeSliceB_append`), then the last one (`nodeSliceB_cons`)
        let joinS (x y : Expr × Nat × Nat) : Expr × Nat × Nat :=
          (mkAppN (rp "nodeSliceB_append") (pre ++ #[lit k, lit a, lit x.2.1, lit x.2.2, lit y.2.2,
            posLit x.2.2, posLit y.2.2, x.1, y.1]), x.2.1, x.2.2 + y.2.2)
        let rest := match balanced joinS (slices.pop) with
          | none => last
          | some (f, s0, n0) =>
            mkAppN (rp "nodeSliceB_cons")
              (pre ++ #[lit k, lit a, lit s0, lit n0, posLit n0, f, last])
        pure (mkAppN (rp "entryNodesB_of_slices") (pre ++ #[lit k, lit a, rest]), 1)
    items := items.push (pf, a, n)
    a := a + n
    j := j + 1
  let nleaves ← leaf.get
  if let some (lo, hi) := leaves then
    unless compose || (lo < hi && hi ≤ nleaves) do
      throwError "check_entry_leaves: leaves {lo} to {hi}, the plan has {nleaves}"
  unless compose do return
  -- the parts joined in a balanced tree (`entryNodesB_append`)
  let joinP (x y : Expr × Nat × Nat) : Expr × Nat × Nat :=
    (mkAppN (rp "entryNodesB_append") (pre ++ #[lit k, lit x.2.1, lit x.2.2, lit y.2.2, x.1, y.1]),
      x.2.1, x.2.2 + y.2.2)
  let (nodes, _, n) := (balanced joinP items).getD
    (mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Bool) (mkConst ``Bool.true), elo, 0)
  unless n == ehi - elo do throwError "check_entry: parts cover {n} nodes, the block {ehi - elo}"
  let some famPf := fam | throwError "check_entry: no family part"
  let ty := isTrue (mkAppN (rp "entryCertB") (pre.push (lit k)))
  let pf := mkAppN (rp "entryCertB_of_parts") (pre ++ #[lit k, lit elo, lit n,
    mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Nat) (lit elo),
    mkApp2 (mkConst ``Eq.refl [levelOne]) (mkConst ``Nat) (lit n), head, nodes, famPf])
  addThm (base ++ Name.mkSimple s!"entry{k}_ok") ty pf

/-- The elaborator of `check_entry`: every leaf theorem, then the entry's. -/
@[command_elab checkEntry]
def elabCheckEntry : CommandElab := fun stx => runCheckEntry stx none true

/-- The elaborator of `check_entry_leaves`: the leaf theorems `i` to `j - 1`. -/
@[command_elab checkEntryLeaves]
def elabCheckEntryLeaves : CommandElab := fun stx =>
  runCheckEntry stx (some (stx[7].isNatLit?.getD 0, stx[8].isNatLit?.getD 0)) false

/-- The elaborator of `compose_entry`: the entry's theorem from its imported leaf theorems. -/
@[command_elab composeEntry]
def elabComposeEntry : CommandElab := fun stx => runCheckEntry stx (some (0, 0)) true

/-- **The gates of one layer slice** in `check_circuit`: a layer with more gates is checked in
slices of this many gates, one theorem each (`layerSliceOk`, `infoSliceB`), so a kernel check does
not grow with the layer. In kernel mode every slice of the `MLDSA44` ring circuit of domain `A`
checks within a quarter of the default heartbeat limit (50,000), in at most 51 s; its layer 1,
30,254 gates checked in one theorem, exceeds the limit. -/
def layerSliceGates : Nat := 2048

/-- **The asserted nodes of one slice** in `check_circuit`: the asserted nodes are checked in
slices of this many, one theorem each (`assertSliceOk`). The statement lists each node's witness,
so the elaboration of a slice's statement grows with it: at 2048 nodes it exceeds a quarter of the
default heartbeat limit (50,000). -/
def assertSliceNodes : Nat := 512

/-- `check_circuit name ar`: see the module docstring. -/
syntax (name := checkCircuit) "check_circuit " ident ident : command

/-- A gate chunk's fields, as the checker reads them (`gateNode`, `flagged`, and whether its terms
have an assertion term): the chunk `x` at the term width `w`. -/
def gateFields (w x : Nat) : Nat × Bool × Bool := Id.run do
  let cnt := x % 2 ^ w / 2
  let mut tm := x >>> (3 * w)
  let mut has := false
  for _ in [0:cnt] do
    if tm % 2 ^ w == 0 then has := true
    tm := tm >>> (3 * w)
  ((x >>> (2 * w)) % 2 ^ w, x % 2 ^ w % 2 == 1, has)

/-- The arguments of a constructor application, through constant references. -/
partial def ctorArgs (e : Expr) : CommandElabM (Array Expr) := do
  match e with
  | .const n _ => match (← getEnv).find? n with
    | some (.defnInfo v) => ctorArgs v.value
    | _ => pure #[]
  | _ => pure e.getAppArgs

/-- The value of an expression, through constant references. -/
partial def resolveExpr (e : Expr) : CommandElabM Expr := do
  match e with
  | .const n _ => match (← getEnv).find? n with
    | some (.defnInfo v) => resolveExpr v.value
    | _ => pure e
  | _ => pure e

/-- The arguments of the checker of a theorem `c … = true`. -/
def lhsArgs (n : Name) : CommandElabM (Array Expr) := do
  let ty := (← getConstInfo n).type
  pure (ty.getAppArgs[1]?.getD (mkConst ``Bool.true)).getAppArgs

/-- A list of numerals. -/
def numList (xs : List Nat) : CommandElabM Term := do
  let ts : Array Term := xs.toArray.map fun x => Syntax.mkNumLit (toString x)
  `([$ts,*])

/-- The elaborator of `check_circuit`. -/
@[command_elab checkCircuit]
def elabCheckCircuit : CommandElab := fun stx => do
  let cert := (← getCurrNamespace) ++ stx[1].getId
  let ir ← programIdent
  let arN ← constOf stx[2]
  let certI := mkIdent cert
  let base := (← getCurrNamespace) ++ stx[1].getId
  let n := (← listsOfExpr (← defValue (cert ++ `entries))).length
  let pre : Array Expr := #[mkConst ir.getId, mkApp (mkConst `GordieHowe.RealizedProgram.CircuitData.c)
    (mkConst cert), mkConst arN, mkConst cert]
  let rp (s : String) := mkConst (Name.mkStr `GordieHowe.RealizedProgram s)
  let hN := base ++ `header_ok
  let arI := mkIdent arN
  let cc (s : String) := mkIdent (`GordieHowe.GKR.Certificate ++ s.toName)
  let cb (s : String) := mkIdent (`GordieHowe.GKR.CertificateBridge ++ s.toName)
  -- the header's parts, each its own theorem; the scheduling certificate (part 1) and the bridge's
  -- checks (part 2) from per-layer and per-slice theorems
  let partN (i : Nat) := base ++ Name.mkSimple s!"header_p{i}"
  for i in [0, 3, 4, 5, 6, 7, 8, 9] do
    elabCommand (← `(command| theorem $(mkIdent (`_root_ ++ partN i)) :
        $(mkIdent `GordieHowe.RealizedProgram.headerPartB) $ir ($certI).c $arI $certI
          $(Syntax.mkNumLit (toString i)) = true := by
      gh_cert_check))
  -- the layers: `cert.layer<i>` against the tables `cert.wtab<i>`
  let env ← getEnv
  let mut nl := 0
  while env.contains (base.appendAfter s!"layer{nl}") do nl := nl + 1
  let layerI (i : Nat) := mkIdent (`_root_ ++ base.appendAfter s!"layer{i}")
  let tabI (i : Nat) := mkIdent (`_root_ ++ base.appendAfter s!"wtab{i}")
  let tp (i : Nat) : CommandElabM Term :=
    if i == 0 then `($(cc "Table.ident")) else pure (tabI (i - 1))
  let wp (i : Nat) : CommandElabM Term :=
    if i == 0 then `(($certI).layered.inputs) else `(List.length $(layerI (i - 1)))
  let lo := cc "layersOk"
  let chk (n : String) := mkIdent (`_root_ ++ base ++ Name.mkSimple n)
  let num (n : Nat) := Syntax.mkNumLit (toString n)
  let w := natOfExpr (← resolveExpr (← defValue (base ++ `width)))
  let wT ← `(($certI).sched.width)
  let S := layerSliceGates
  -- per layer: its gate count, its asserting gates' count, and its asserting gates' nodes
  let mut ms : Array Nat := #[]
  let mut cs : Array Nat := #[]
  let mut wit : Std.HashMap Nat (Nat × Nat) := {}
  for i in [0:nl] do
    let gates := (← natsOfExpr (← defValue (base.appendAfter s!"layer{i}"))).toArray
    let g := gates.size
    let args : Array Term := #[wT, ← `(($certI).dag), ← tp i, ← wp i, tabI i, layerI i]
    -- the slices `[j * S, (j + 1) * S)`, the last one every gate left; one slice for a small layer
    let m := max 1 ((g + S - 1) / S)
    let mut sc : Array Nat := #[]
    for j in [0:m] do
      let mut c := 0
      for k in [j * S:min g ((j + 1) * S)] do
        let (node, copy, has) := gateFields w gates[k]!
        if !copy && has then
          c := c + 1
          unless wit.contains node do wit := wit.insert node (i + 1, k)
      sc := sc.push c
    ms := ms.push g
    cs := cs.push (sc.foldl (· + ·) 0)
    let infoArgs : Array Term := #[wT, layerI i]
    if m == 1 then
      elabCommand (← `(command| theorem $(chk s!"chk_layer{i}") :
          $(cc "layerOk") $args* = true := by
        gh_cert_check))
      elabCommand (← `(command| theorem $(chk s!"chk_info{i}") :
          $(cb "infoSliceB") $infoArgs* 0 0 $(num g) $(num sc[0]!) = true := by
        gh_cert_check))
      continue
    for j in [0:m] do
      let len := if j + 1 == m then 0 else S
      elabCommand (← `(command| theorem $(chk s!"chk_layer{i}_s{j}") :
          $(cc "layerSliceOk") $args* $(num (j * S)) $(num len) = true := by
        gh_cert_check))
      elabCommand (← `(command| theorem $(chk s!"chk_info{i}_s{j}") :
          $(cb "infoSliceB") $infoArgs* $(num (j * S)) $(num len)
            $(num (if j + 1 == m then g - j * S else S)) $(num sc[j]!) = true := by
        gh_cert_check))
    let mut rest : Term := chk s!"chk_layer{i}_s{m - 1}"
    let mut restI : Term := chk s!"chk_info{i}_s{m - 1}"
    let mut cRest := sc[m - 1]!
    for j' in [1:m] do
      let j := m - 1 - j'
      rest ← `(@$(cc "layerSliceOk_cons") $args* $(num (j * S))
        $(num S) (Nat.zero_lt_succ $(num (S - 1))) $(chk s!"chk_layer{i}_s{j}") $rest)
      restI ← `(@$(cb "infoSliceB_cons") $infoArgs* $(num (j * S)) $(num S) $(num S)
        $(num sc[j]!) $(num (g - (j + 1) * S)) $(num cRest) (Nat.zero_lt_succ $(num (S - 1)))
        $(chk s!"chk_info{i}_s{j}") $restI)
      cRest := cRest + sc[j]!
    elabCommand (← `(command| theorem $(chk s!"chk_layer{i}") :
        $(cc "layerOk") $args* = true :=
      @$(cc "layerOk_of_slices") $args* $rest))
    elabCommand (← `(command| theorem $(chk s!"chk_info{i}") :
        $(cb "infoSliceB") $infoArgs* 0 0 $(num g) $(num cRest) = true := $restI))
  -- the suffixes, from the last-layer assertions back to the first layer
  elabCommand (← `(command| theorem $(chk s!"chk_suffix{nl}") :
      $lo ($certI).sched.width ($certI).dag ($certI).sched.outputs ($certI).sched.outWires
        $(← tp nl) $(← wp nl) [] [] = true := by
    gh_cert_check))
  for i' in [0:nl] do
    let i := nl - 1 - i'
    let ts : Array Term := (Array.range (nl - i)).map fun j => tabI (i + j)
    let ls : Array Term := (Array.range (nl - i)).map fun j => layerI (i + j)
    elabCommand (← `(command| theorem $(chk s!"chk_suffix{i}") :
        $lo ($certI).sched.width ($certI).dag ($certI).sched.outputs ($certI).sched.outWires
          $(← tp i) $(← wp i) [$ts,*] [$ls,*] = true :=
      $(cc "layersOk_cons") $(chk s!"chk_layer{i}") $(chk s!"chk_suffix{i + 1}")))
  -- every layer's counts (`layersInfoB`), then the bridge's checks (part 2)
  let msT ← numList ms.toList
  let csT ← numList cs.toList
  let lsAll : Array Term := (Array.range nl).map fun i => layerI i
  let mut infos : Term ← `($(cb "layersInfoB_nil"))
  for i' in [0:nl] do
    let i := nl - 1 - i'
    infos ← `($(cb "layersInfoB_cons") $(chk s!"chk_info{i}") $infos)
  elabCommand (← `(command| theorem $(chk "chk_infos") :
      $(cb "layersInfoB") $wT [$lsAll,*] $msT $csT = true := $infos))
  elabCommand (← `(command| theorem $(chk "chk_shape") :
      $(cb "shapeLensB") $msT (($ir).circuitWidth ($certI).c) (($ir).circuit ($certI).c).layers
        = true := by
    gh_cert_check))
  -- the compositions name every argument and are checked by the kernel alone
  let cdE (f : String) := mkApp (mkConst (`GordieHowe.RealizedProgram.CircuitData ++ f.toName))
    (mkConst cert)
  let chkN (n : String) := base ++ Name.mkSimple n
  let infoA ← lhsArgs (chkN "chk_infos")
  let shapeA ← lhsArgs (chkN "chk_shape")
  addThm (partN 2) (isTrue (mkAppN (rp "headerPartB") (pre.push (lit 2))))
    (mkAppN (mkConst `GordieHowe.GKR.CertificateBridge.uniqueAssertsB_shapeB_of_info)
      #[infoA[0]!, shapeA[1]!, shapeA[2]!, cdE "layered", infoA[2]!, infoA[3]!,
        mkConst (chkN "chk_infos"), mkConst (chkN "chk_shape")])
  -- the asserted nodes in slices, each with its witness: an asserting gate's layer and wire, or a
  -- last-layer assertion's index
  let dagArgs ← ctorArgs (← defValue (base ++ `dag))
  let asserts := (← natsOfExpr (← resolveExpr (dagArgs[3]?.getD (mkConst ``List.nil)))).toArray
  let schedArgs ← ctorArgs (← defValue (base ++ `sched))
  let outs ← listsOfExpr (← resolveExpr (schedArgs[2]?.getD (mkConst ``List.nil)))
  let mut outIdx : Std.HashMap Nat Nat := {}
  for j in [0:outs.length] do
    let o := natOfExpr (← resolveExpr ((← ctorArgs outs[j]!)[3]?.getD (lit 0)))
    unless outIdx.contains o do outIdx := outIdx.insert o j
  let A := assertSliceNodes
  let na := asserts.size
  let ma := max 1 ((na + A - 1) / A)
  let aArgs : Array Term := #[wT, ← `(($certI).dag), ← `(($certI).sched.outputs),
    ← `(($certI).sched.tables), msT]
  let at? (k : Nat) : Nat := if k < na then asserts[k]! else 0
  for j in [0:ma] do
    let s := j * A
    let len := if j + 1 == ma then 0 else A
    let e := if j + 1 == ma then na else s + A
    let mut ps : Array Term := #[]
    for k in [s:e] do
      let x := asserts[k]!
      let (d, g) ← match wit.get? x, outIdx.get? x with
        | some p, _ => pure p
        | none, some o => pure (0, o)
        | none, none => throwError "check_circuit: asserted node {x} is neither carried nor a \
            last-layer assertion"
      ps := ps.push (← `(($(num d), $(num g))))
    let loV := if s == 0 then 0 else at? (s - 1)
    let hiV := if e == 0 then 0 else at? (e - 1)
    elabCommand (← `(command| theorem $(chk s!"chk_asserts_s{j}") :
        $(cc "assertSliceOk") $aArgs* $(num s) $(num len) $(num loV) $(num hiV) [$ps,*] = true := by
      gh_cert_check))
  let hiAll := if na == 0 then 0 else at? (na - 1)
  let mut cover : Term ← `($(cc "assertsFrom_of_slice") $(chk s!"chk_asserts_s{ma - 1}"))
  for j' in [1:ma] do
    let j := ma - 1 - j'
    let s := j * A
    cover ← `(@$(cc "assertsFrom_cons") $aArgs* $(num s) $(num A)
      $(num (if s == 0 then 0 else at? (s - 1))) $(num (at? (s + A - 1))) $(num hiAll) _
      (Nat.zero_lt_succ $(num (A - 1))) $(chk s!"chk_asserts_s{j}") $cover)
  elabCommand (← `(command| theorem $(chk "chk_assertsFrom") :
      $(cc "AssertsFrom") $aArgs* 0 0 $(num hiAll) := $cover))
  for (n, t) in [("chk_one", ← `($(cc "oneOk") ($certI).dag)),
      ("chk_inputs", ← `(Nat.beq ($certI).layered.inputs ($certI).dag.inputs)),
      ("chk_count", ← `(Nat.ble (List.length ($certI).sched.outputs + List.sum $csT)
        (List.length ($certI).dag.asserts))),
      ("chk_cover", ← `($(cc "lastCoverB") ($certI).sched.width
        ($certI).sched.outputs ($certI).sched.outWires ($certI).layered.layers))] do
    elabCommand (← `(command| theorem $(chk n) : $t = true := by gh_cert_check))
  let hiE := ((← getConstInfo (chkN "chk_assertsFrom")).type.getAppArgs.back?).getD (lit 0)
  let gc (n : String) := mkConst (`GordieHowe.GKR.Certificate ++ n.toName)
  addThm (chkN "chk_asserts")
    (isTrue (mkAppN (gc "assertsOk") #[cdE "dag", cdE "layered", cdE "sched"]))
    (mkAppN (gc "assertsOk_of_cover") #[cdE "dag", cdE "layered", cdE "sched", infoA[2]!,
      infoA[3]!, hiE, mkConst (chkN "chk_one"), mkConst (chkN "chk_inputs"),
      mkConst (chkN "chk_suffix0"),
      mkAppN (mkConst `GordieHowe.GKR.CertificateBridge.layersCountB_of_info) (infoA.push
        (mkConst (chkN "chk_infos"))),
      mkConst (chkN "chk_assertsFrom"), mkConst (chkN "chk_count")])
  elabCommand (← `(command| theorem $(mkIdent (`_root_ ++ partN 1)) :
      $(mkIdent `GordieHowe.RealizedProgram.headerPartB) $ir ($certI).c $arI $certI 1 = true :=
    $(cc "check_of_parts") $(chk "chk_one") $(chk "chk_inputs")
      $(chk "chk_suffix0") $(chk "chk_asserts") $(chk "chk_cover")))
  elabCommand (← `(command| theorem $(mkIdent (`_root_ ++ hN)) :
      $(mkIdent `GordieHowe.RealizedProgram.headerB) $ir ($certI).c $arI $certI = true :=
    $(mkIdent `GordieHowe.RealizedProgram.headerB_of_parts) $ir ($certI).c $arI $certI
      $(mkIdent (`_root_ ++ partN 0)) $(mkIdent (`_root_ ++ partN 1))
      $(mkIdent (`_root_ ++ partN 2))
      $(mkIdent (`_root_ ++ partN 3)) $(mkIdent (`_root_ ++ partN 4))
      $(mkIdent (`_root_ ++ partN 5))
      $(mkIdent (`_root_ ++ partN 6)) $(mkIdent (`_root_ ++ partN 7))
      $(mkIdent (`_root_ ++ partN 8))
      $(mkIdent (`_root_ ++ partN 9))))
  -- the property of an entry, `fun k => entryCertB … k = true`
  let P := Expr.lam `k (mkConst ``Nat) (isTrue (mkAppN (rp "entryCertB") (pre.push (.bvar 0)))) .default
  let mut pf := mkApp (rp "forall_lt_zero") P
  for k in [0:n] do
    pf := mkAppN (rp "forall_lt_succ_of") #[P, lit k, pf, mkConst (base ++ Name.mkSimple s!"entry{k}_ok")]
  let ty := isTrue (mkAppN (rp "circuitCertB") pre)
  addThm (base ++ `circuit_ok) ty (mkAppN (rp "circuitCertB_of_entries") (pre ++ #[mkConst hN, pf]))

end GordieHowe.Load
