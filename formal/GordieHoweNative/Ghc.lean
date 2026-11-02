-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Data
public import Lean.Expr
public import Lean.ToExpr
public import Lean.Util.ReplaceExpr
public import Std.Data.HashMap
public import Std.Sync.Mutex

@[expose] public section

/-!
# GordieHowe: the `.ghc` container and the type-directed decoder

A `.ghc` file (version 3, written by `lib/gordiehowe/compiler/ghc.h`) is the magic `GHC`, the
version byte `3`, then its sections, then an end marker. Each section is

* `name`, the definition it becomes, relative to the loading namespace (a string: its byte count,
  then its UTF-8 bytes); the end marker is the empty name;
* `type`, the Lean type of the definition (`Ty`: `0` then a constant's full name, or `1` then a
  function and its argument);
* `flags`: bit 0, the definition gets compiled code; bit 1, the value is in spine form (below);
  bit 2, native mode adds a run-time reader for it (`LoadNative.lean`);
* `length`, the value's byte count, and `value`, the encoding of one value of `type`.

**A value is written by its type** (`Decode`): a natural as LEB128, an integer zigzag then LEB128,
a `Bool` as `0` or `1`, a string as its byte count then its UTF-8 bytes, an `Option` as `0`, or `1`
then the value, a `List` as its count then its items, a structure (a pair included) as its fields
in order, any other inductive as its constructor's index then its fields. A type may override its
encoding with a hand-written instance; the one override is `IndexMap`, written as the index `j` of
the program's index map `idx<j>`, resolved in scope by the loader (from Lean text or an earlier
loaded file alike) and by the given table at run time. Every other type's instance is derived
(`deriving instance Decode for …`, `GordieHoweNative/Derive.lean`) from the inductive's
constructors.

**The spine form** lets a value refer to earlier sections. At each position of a spine-form value
a tag precedes the value: `0`, the value follows in the plain encoding above; `1`, the index of an
earlier section of the position's type follows, whose definition stands there; `2`, the value's
constructor follows as above (its index, unless a structure, or a list's count), each field again
in spine form. So a definition built from other definitions (a circuit's certificate from its
parts, a trie whose large subtrees are definitions of their own) is a section of a few bytes, and
the writer chooses where to split.

`Decode` gives every type the readers of a value (`dec`, `spine`) and of its expression (`toE`,
`spineE`; a reference is the earlier definition's constant). The loader (`Terms.lean`) builds the
definitions from the expressions; native mode's run-time reader (`readSectionUnsafe`) decodes the
values. Both run as native code: the library `GordieHoweNative` is precompiled (`lakefile.toml`).
-/

namespace GordieHowe.Ghc

open Lean GordieHowe.RealizedProgram

/-! ## Type descriptors and sections -/

/-- **A section's type**: a constant, by its full name, or an application. -/
inductive Ty where
  /-- The constant of this full name. -/
  | const (name : String)
  /-- `f a`. -/
  | app (f a : Ty)
  deriving BEq, Hashable, Repr, Inhabited

/-- The descriptor of a type expression (constants and applications; universe levels dropped). -/
def Ty.ofExpr : Expr → Option Ty
  | .const n _ => some (.const (n.toString (escape := false)))
  | .app f a => do pure (.app (← Ty.ofExpr f) (← Ty.ofExpr a))
  | _ => none

/-- A type descriptor as Lean text. -/
partial def Ty.toString : Ty → String
  | .const n => n
  | .app f a =>
    let s := a.toString
    s!"{f.toString} {if a matches .app .. then s!"({s})" else s}"

instance : ToString Ty := ⟨Ty.toString⟩

/-- **A section of a file**: its name, its type, its flags, and its value's byte range. -/
structure Section where
  /-- The definition's name, relative to the loading namespace. -/
  name : String
  /-- The definition's type. -/
  ty : Ty
  /-- The flags (`compile`, `spine`, `reader`). -/
  flags : Nat
  /-- The value's first byte. -/
  off : Nat
  /-- The value's byte count. -/
  len : Nat
  deriving Inhabited

/-- The definition gets compiled code. -/
def Section.compile (s : Section) : Bool := s.flags &&& 1 != 0

/-- The value is in spine form. -/
def Section.spine (s : Section) : Bool := s.flags &&& 2 != 0

/-- Native mode adds a run-time reader for the definition. -/
def Section.reader (s : Section) : Bool := s.flags &&& 4 != 0

/-! ## The reader monad -/

/-- **What a decoding reads**: the file's bytes and sections, the section being decoded (a
reference names an earlier one), the index maps by number, and, for the expressions, the sections'
definitions and the index maps' constants by number. -/
structure Ctx where
  /-- The file's bytes. -/
  bytes : ByteArray
  /-- The file's sections. -/
  secs : Array Section := #[]
  /-- The section being decoded. -/
  cur : Nat := 0
  /-- The index maps by number (the loader's stand-ins, or the program's maps at run time). -/
  idx : Nat → Option IndexMap := fun _ => none
  /-- The sections' definitions (full names), for the expressions. -/
  names : Array Name := #[]
  /-- The index maps' constants by number, for the expressions. -/
  idxNames : Array Name := #[]

/-- The decoder: a position in the bytes, the context, and failure with a message. -/
abbrev D := StateT Nat (ReaderT Ctx (Except String))

instance {α : Type} : Inhabited (D α) := ⟨throw "Ghc: unreachable"⟩

/-- One byte. -/
def byte : D Nat := do
  let c ← read
  let i ← get
  if h : i < c.bytes.size then
    set (i + 1)
    pure c.bytes[i].toNat
  else throw s!"unexpected end of data at byte {i}"

/-- The natural of the LEB128 groups `b[i], …, b[j - 1]` (`j - i ≤ 9`, so it fits 63 bits). -/
def groupsSmall (b : ByteArray) (i j : Nat) : Nat := Id.run do
  let mut x : UInt64 := 0
  for k in [0:j - i] do
    x := x ||| ((b[i + k]!.toUInt64 &&& 127) <<< (7 * k).toUInt64)
  pure x.toNat

/-- The natural of the LEB128 groups `b[i], …, b[j - 1]`, its halves combined (so a long natural
costs `O(n log n)`, not the `O(n²)` of one shift per group). -/
partial def groups (b : ByteArray) (i j : Nat) : Nat :=
  if j - i ≤ 9 then groupsSmall b i j
  else
    let m := i + (j - i) / 2
    groups b i m ||| (groups b m j <<< (7 * (m - i)))

/-- An unsigned LEB128 natural. -/
def nat : D Nat := do
  let c ← read
  let i ← get
  let mut j := i
  while j < c.bytes.size && c.bytes[j]! &&& 128 != 0 do j := j + 1
  unless j < c.bytes.size do throw s!"unexpected end of data at byte {c.bytes.size}"
  set (j + 1)
  pure (groups c.bytes i (j + 1))

/-- A string: its byte count, then its UTF-8 bytes. -/
def string : D String := do
  let n ← nat
  let c ← read
  let i ← get
  unless i + n ≤ c.bytes.size do throw s!"unexpected end of data in a string at byte {i}"
  set (i + n)
  match String.fromUTF8? (c.bytes.extract i (i + n)) with
  | some s => pure s
  | none => throw s!"a string at byte {i} is not UTF-8"

/-- A constructor index outside the type's. -/
def badCtor {α : Type} (ty : String) (i : Nat) : D α := throw s!"{ty}: no constructor {i}"

/-- A type descriptor (`0` and a name, or `1` and a function and its argument). -/
partial def ty : D Ty := do
  match ← nat with
  | 0 => pure (.const (← string))
  | 1 => pure (.app (← ty) (← ty))
  | i => badCtor "Ty" i

/-! ## The class -/

/-- **The decoder of a type** (see the module docstring): its type's expression, the expression
of a value, and the readers of a value and of its expression, in the plain and the spine form. -/
class Decode (α : Type) where
  /-- The type, as an expression. -/
  tyE : Expr
  /-- The expression of a value (natural numbers as raw literals). -/
  toE : α → Expr
  /-- A value, plain. -/
  dec : D α
  /-- A value, in spine form. -/
  spine : D α
  /-- A value's expression, in spine form. -/
  spineE : D Expr

/-- The descriptor of a type expression (`?` for none). -/
def tyOf (e : Expr) : Ty := (Ty.ofExpr e).getD (.const "?")

/-- **Section `j`, decoded** by `plain` or `spine` (its form), after checking that it is earlier than
the current one and of type `t`. The position is restored after. -/
def atSection {α : Type} (t : Ty) (j : Nat) (plain spine : D α) : D α := do
  let c ← read
  unless j < c.cur do throw s!"section {c.cur}: section {j} is not an earlier one"
  let s := c.secs[j]!
  unless s.ty == t do throw s!"section {c.cur}: section {j} is a {s.ty}, not a {t}"
  let back ← get
  set s.off
  let x ← withReader ({ · with cur := j }) (if s.spine then spine else plain)
  unless (← get) == s.off + s.len do throw s!"section {s.name}: trailing bytes"
  set back
  pure x

/-- **The constant of section `j`**, after the checks of `atSection`. -/
def refE (t : Ty) (j : Nat) : D Expr := do
  let c ← read
  unless j < c.cur do throw s!"section {c.cur}: section {j} is not an earlier one"
  let s := c.secs[j]!
  unless s.ty == t do throw s!"section {c.cur}: section {j} is a {s.ty}, not a {t}"
  match c.names[j]? with
  | some n => pure (mkConst n)
  | none => throw s!"section {j} has no definition"

/-- **A value in spine form**: its tag, then the plain value (`0`), an earlier section (`1`), or
its constructor and fields in spine form (`inline`, `2`). -/
@[inline] def spineWith {α : Type} (t : Ty) (plain spine inline : D α) : D α := do
  match ← nat with
  | 0 => plain
  | 1 => atSection t (← nat) plain spine
  | 2 => inline
  | k => throw s!"{t}: spine tag {k}"

/-- An index map's expression: Lean's `ToExpr` of the list, the natural numbers raw. -/
def indexMapE (m : IndexMap) : Expr :=
  let natT := mkConst ``Nat
  let intT := mkConst ``Int
  let pT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) intT natT
  let tT := mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) natT pT
  m.foldr (fun (a, b, c) acc =>
      mkApp3 (mkConst ``List.cons [Level.zero]) tT
        (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) natT pT (mkRawNatLit a)
          (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) intT natT (toExpr b)
            (mkRawNatLit c))) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) tT)

/-- **The stand-in of index map `j`** while the loader decodes: a map no program prints (a negative
step over no entries), whose expression is replaced by the constant `idx<j>` (`replaceStubs`). -/
def stub (j : Nat) : IndexMap := [(j, Int.negSucc 1000002, 0)]

/-- **The number `j` of a stand-in**, if `e` is the expression of `stub j`. -/
def stubIndex? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``List.cons 3 then
    match e.appFn!.appArg!.getAppFnArgs with
    | (``Prod.mk, #[_, _, .lit (.natVal j), _]) => if e == indexMapE (stub j) then some j else none
    | _ => none
  else none

/-- **`e` with every stand-in replaced** by the constant of its index map, `idxs[j]`. -/
def replaceStubs (idxs : Array Name) (e : Expr) : Expr :=
  e.replace fun x => (stubIndex? x).bind fun j => idxs[j]?.map mkConst

/-- **The expression of a plain value**: its `toE`, maximally shared (`ShareCommon.shareCommon'`
merges structurally equal subterms into one object), the stand-ins replaced by their index maps'
constants (after the sharing a stand-in is one object, so the replacement visits it once). -/
def valueExpr (idxs : Array Name) (e : Expr) : Expr :=
  replaceStubs idxs (ShareCommon.shareCommon' e)

/-- **A value's expression in spine form**: the plain value's (`valueExpr`), an earlier section's
constant, or `inline`. -/
@[inline] def spineEWith {α : Type} (t : Ty) (toE : α → Expr) (plain : D α) (inline : D Expr) :
    D Expr := do
  match ← nat with
  | 0 => do pure (valueExpr (← read).idxNames (toE (← plain)))
  | 1 => refE t (← nat)
  | 2 => inline
  | k => throw s!"{t}: spine tag {k}"

/-- The spine reader of a type with no constructor form (a natural, a string, an index map). -/
partial def leafSpine {α : Type} (t : Ty) (plain : D α) : D α :=
  spineWith t plain (leafSpine t plain) (throw s!"{t}: no constructor form")

/-! ## The primitive types -/

instance : Decode Nat where
  tyE := mkConst ``Nat
  toE := mkRawNatLit
  dec := nat
  spine := leafSpine (.const "Nat") nat
  spineE := spineEWith (.const "Nat") mkRawNatLit nat (throw "Nat: no constructor form")

/-- An integer, zigzag. -/
def int : D Int := do
  let z ← nat
  pure (if z % 2 == 0 then Int.ofNat (z / 2) else Int.negSucc (z / 2))

instance : Decode Int where
  tyE := mkConst ``Int
  toE := toExpr
  dec := int
  spine := leafSpine (.const "Int") int
  spineE := spineEWith (.const "Int") toExpr int (throw "Int: no constructor form")

/-- A `Bool`, `0` or `1`. -/
def bool : D Bool := do
  match ← nat with
  | 0 => pure false
  | 1 => pure true
  | i => badCtor "Bool" i

instance : Decode Bool where
  tyE := mkConst ``Bool
  toE := toExpr
  dec := bool
  spine := leafSpine (.const "Bool") bool
  spineE := spineEWith (.const "Bool") toExpr bool (throw "Bool: no constructor form")

instance : Decode String where
  tyE := mkConst ``String
  toE := mkStrLit
  dec := string
  spine := leafSpine (.const "String") string
  spineE := spineEWith (.const "String") mkStrLit string (throw "String: no constructor form")

section
variable {α β : Type} [Decode α] [Decode β]

/-- `n` values. -/
def items (n : Nat) (d : D α) : D (List α) := do
  let mut xs := #[]
  for _ in [0:n] do xs := xs.push (← d)
  pure xs.toList

/-- `n` expressions. -/
def itemsE (n : Nat) (d : D Expr) : D (Array Expr) := do
  let mut xs := #[]
  for _ in [0:n] do xs := xs.push (← d)
  pure xs

/-- The list `[e₀, e₁, …]` of element type `t`. -/
def listE (t : Expr) (es : Array Expr) : Expr :=
  es.foldr (fun e acc => mkApp3 (mkConst ``List.cons [Level.zero]) t e acc)
    (mkApp (mkConst ``List.nil [Level.zero]) t)

/-- The list type. -/
def listTyE : Expr := mkApp (mkConst ``List [Level.zero]) (Decode.tyE (α := α))

/-- A list's expression. -/
def listToE (xs : List α) : Expr :=
  xs.foldr (fun x acc => mkApp3 (mkConst ``List.cons [Level.zero]) (Decode.tyE (α := α)) (Decode.toE x) acc)
    (mkApp (mkConst ``List.nil [Level.zero]) (Decode.tyE (α := α)))

/-- A list: its count, then its items. -/
def listDec : D (List α) := do items (← nat) Decode.dec

/-- A list in spine form. -/
partial def listSpine : D (List α) :=
  spineWith (tyOf (listTyE (α := α))) listDec listSpine (do items (← nat) Decode.spine)

instance : Decode (List α) where
  tyE := listTyE (α := α)
  toE := listToE
  dec := listDec
  spine := listSpine
  spineE := spineEWith (α := List α) (tyOf (listTyE (α := α))) listToE listDec
    (do pure (listE (Decode.tyE (α := α)) (← itemsE (← nat) (Decode.spineE (α := α)))))

/-- The option type. -/
def optionTyE : Expr := mkApp (mkConst ``Option [Level.zero]) (Decode.tyE (α := α))

/-- An option's expression. -/
def optionToE : Option α → Expr
  | none => mkApp (mkConst ``Option.none [Level.zero]) (Decode.tyE (α := α))
  | some x => mkApp2 (mkConst ``Option.some [Level.zero]) (Decode.tyE (α := α)) (Decode.toE x)

/-- An option's constructor and field, the field by `d`. -/
def optionWith (d : D α) : D (Option α) := do
  match ← nat with
  | 0 => pure none
  | 1 => pure (some (← d))
  | i => badCtor "Option" i

/-- An option in spine form. -/
partial def optionSpine : D (Option α) :=
  spineWith (tyOf (optionTyE (α := α))) (optionWith Decode.dec) optionSpine
    (optionWith Decode.spine)

instance : Decode (Option α) where
  tyE := optionTyE (α := α)
  toE := optionToE
  dec := optionWith Decode.dec
  spine := optionSpine
  spineE := spineEWith (α := Option α) (tyOf (optionTyE (α := α))) optionToE (optionWith Decode.dec) do
    match ← nat with
    | 0 => pure (mkApp (mkConst ``Option.none [Level.zero]) (Decode.tyE (α := α)))
    | 1 => do
      let e ← Decode.spineE (α := α)
      pure (mkApp2 (mkConst ``Option.some [Level.zero]) (Decode.tyE (α := α)) e)
    | i => badCtor "Option" i

/-- The pair type. -/
def prodTyE : Expr :=
  mkApp2 (mkConst ``Prod [Level.zero, Level.zero]) (Decode.tyE (α := α)) (Decode.tyE (α := β))

/-- A pair's expression. -/
def prodToE (p : α × β) : Expr :=
  mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (Decode.tyE (α := α)) (Decode.tyE (α := β))
    (Decode.toE p.1) (Decode.toE p.2)

/-- A pair, its fields by `a` and `b`. -/
def prodWith (a : D α) (b : D β) : D (α × β) := do
  let x ← a
  pure (x, ← b)

/-- A pair in spine form. -/
partial def prodSpine : D (α × β) :=
  spineWith (tyOf (prodTyE (α := α) (β := β))) (prodWith Decode.dec Decode.dec) prodSpine
    (prodWith Decode.spine Decode.spine)

instance : Decode (α × β) where
  tyE := prodTyE (α := α) (β := β)
  toE := prodToE
  dec := prodWith Decode.dec Decode.dec
  spine := prodSpine
  spineE := spineEWith (α := α × β) (tyOf (prodTyE (α := α) (β := β))) prodToE
    (prodWith Decode.dec Decode.dec) do
      let a ← Decode.spineE (α := α)
      let b ← Decode.spineE (α := β)
      pure (mkApp4 (mkConst ``Prod.mk [Level.zero, Level.zero]) (Decode.tyE (α := α)) (Decode.tyE (α := β)) a b)

end

/-! ## The override: index maps -/

/-- An index map, by its number. -/
def idxMap : D IndexMap := do
  let j ← nat
  match (← read).idx j with
  | some m => pure m
  | none => throw s!"no idx{j}"

/-- **Index maps** are written as the number `j` of the program's `idx<j>`: in the loader a
stand-in (`stub j`) that the expression replaces by the constant, at run time the map. (An
`IndexMap` is a `List (Nat × Int × Nat)`: this instance has priority over the list's, so every such
list reads as an index map.) -/
instance (priority := high) : Decode IndexMap where
  tyE := mkConst ``IndexMap
  toE := indexMapE
  dec := idxMap
  spine := leafSpine (.const "GordieHowe.RealizedProgram.IndexMap") idxMap
  spineE := spineEWith (.const "GordieHowe.RealizedProgram.IndexMap") indexMapE idxMap
    (throw "IndexMap: no constructor form")

/-! ## The file -/

/-- **FNV-1a 64** of the bytes, as 16 lowercase hex digits. -/
def fnv1a (b : ByteArray) : String := Id.run do
  let mut h : UInt64 := 0xcbf29ce484222325
  for x in b do
    h := (h ^^^ x.toUInt64) * 0x100000001b3
  let s := String.ofList (Nat.toDigits 16 h.toNat)
  pure (String.ofList (List.replicate (16 - s.length) '0') ++ s)

/-- **The file's sections**: the magic `GHC 3`, then each section's header (its value skipped), up
to the end marker, then the end of the file. Section names are distinct. -/
def sectionsD : D (Array Section) := do
  let b0 ← byte
  let b1 ← byte
  let b2 ← byte
  let b3 ← byte
  unless b0 == 0x47 && b1 == 0x48 && b2 == 0x43 && b3 == 3 do throw "not a GHC version 3 file"
  let mut secs : Array Section := #[]
  let mut names : Std.HashSet String := {}
  repeat
    let name ← string
    if name.isEmpty then break
    if names.contains name then throw s!"section {name}: a second section of this name"
    names := names.insert name
    let t ← ty
    let flags ← nat
    let len ← nat
    let off ← get
    unless off + len ≤ (← read).bytes.size do throw s!"section {name}: length {len} past the end"
    set (off + len)
    secs := secs.push { name, ty := t, flags, off, len }
  unless (← get) == (← read).bytes.size do throw "bytes after the end marker"
  pure secs

/-- The sections of a file's bytes. -/
def sections (bytes : ByteArray) : Except String (Array Section) :=
  (sectionsD.run' 0).run { bytes }

/-- **Section `j` decoded at type `α`**: its type checked, the whole value read. -/
def decodeSection {α : Type} [Decode α] (c : Ctx) (j : Nat) : Except String α := do
  let some s := c.secs[j]? | throw s!"no section {j}"
  let t := tyOf (Decode.tyE (α := α))
  unless s.ty == t do throw s!"section {s.name} is a {s.ty}, not a {t}"
  let d : D α := do
    let x ← if s.spine then Decode.spine else Decode.dec
    unless (← get) == s.off + s.len do throw s!"section {s.name}: trailing bytes"
    pure x
  (d.run' s.off).run { c with cur := j }

/-! ## The run-time reader -/

/-- **A file read in this process**: the index maps it is decoded with, its bytes and sections,
and the values decoded so far by section (each of its section's type, `readSectionUnsafe`). -/
structure Read where
  /-- The index maps. -/
  idxs : Array IndexMap
  /-- The bytes. -/
  bytes : ByteArray
  /-- The sections. -/
  secs : Array Section
  /-- The decoded values by section. -/
  values : Std.HashMap Nat NonScalar := {}

/-- **The files read in this process**, by path and hash: the run-time reader reads and checks a
file once per process and decodes each section once, so the leaf theorems of a module share them. -/
initialize readCache : Std.Mutex (Std.HashMap (String × String) Read) ← Std.Mutex.new {}

/-- **The run-time reader**: section `j` of the file at `path`, whose FNV-1a 64 hash must be
`hash`, decoded at type `α` (which must be the section's), the index maps by number from `idxs`.
The first call for a path and hash reads the file and checks its hash, the first call for a
section decodes it, and the later ones return the value (`readCache`). A value is kept by section
and returned at the type it was decoded at: `decodeSection` checks that type against the section's,
which the hash fixes. A failure (no file, another hash, a decoding error) prints the reason and
exits the process: the compiled check has no other way to fail loudly. -/
unsafe def readSectionUnsafe {α : Type} [Decode α] (path hash : String) (idxs : Array IndexMap)
    (j : Nat) : α :=
  match unsafeIO (go ()) with
  | .ok x => x
  | .error e =>
    match unsafeIO
        (do IO.eprintln s!"Ghc.readSection: {path}: {e}"; IO.Process.exit 1 : IO α) with
    | .ok x => x
    | .error _ => unsafeCast ()
where
  go (_ : Unit) : IO α := readCache.atomically do
    let r ← match (← get)[(path, hash)]? with
      | some r =>
        if ptrEq r.idxs idxs || r.idxs == idxs then pure r
        else pure { r with idxs, values := {} }
      | none =>
        let bytes ← IO.FS.readBinFile path
        let h := fnv1a bytes
        unless h == hash do throw (IO.userError s!"hash {h}, expected {hash}")
        match sections bytes with
        | .ok secs => pure { idxs, bytes, secs }
        | .error s => throw (IO.userError s)
    if let some v := r.values[j]? then
      modify (·.insert (path, hash) r)
      return unsafeCast v
    match decodeSection (α := α) { bytes := r.bytes, secs := r.secs, idx := (idxs[·]?) } j with
    | .ok x =>
      modify (·.insert (path, hash) { r with values := r.values.insert j (unsafeCast x) })
      pure x
    | .error s => throw (IO.userError s)

end GordieHowe.Ghc
