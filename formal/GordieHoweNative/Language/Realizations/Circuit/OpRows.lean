-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Circuit.Emit

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Circuit.OpRows`

The definitions of `GordieHowe.Language.Realizations.Circuit.OpRows` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Circuit/OpRows.lean`, which imports this module.
-/

local notation "ℕ" => Nat
local notation "ℤ" => Int

@[expose] public section

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Fold (CodeArith)

namespace OpList

section Parity

variable {α : Type _} {β : Type _}

/-- **The entries at even positions** of a list. -/
def evenPart : List α → List α
  | [] => []
  | [x] => [x]
  | x :: _ :: l => x :: evenPart l

/-- **The entries at odd positions** of a list. -/
def oddPart : List α → List α
  | [] => []
  | [_] => []
  | _ :: y :: l => y :: oddPart l

end Parity

end OpList

open OpList

section Codes

variable {F : Type _}

/-- **The code of `c^e`** by binary powering, with fuel `fuel ≥ e`. -/
def codePowF (ar : CodeArith) : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 1
  | fuel + 1, c, e =>
    cond (Nat.beq e 0) 1
      (cond (Nat.beq (e % 2) 1) (ar.mul (codePowF ar fuel (ar.mul c c) (e / 2)) c)
        (codePowF ar fuel (ar.mul c c) (e / 2)))

/-- **The code of `c^e`**, by the code arithmetic. -/
def codePow (ar : CodeArith) (c e : ℕ) : ℕ := codePowF ar e c e

/-- **The codes `w, w·c, …, w·c^(L−1)`**, each from the last by the code arithmetic (the
C++ loops `w = mulf(w, step)`). -/
def powList (ar : CodeArith) (c : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | L + 1, w => w :: powList ar c L (ar.mul w c)

end Codes

namespace OpList

section Entries

variable {α : Type _} {β : Type _}

/-- **A list in chunks of `n`**, with fuel. -/
def chunksF (n : ℕ) : ℕ → List α → List (List α)
  | _, [] => []
  | 0, _ :: _ => []
  | fuel + 1, x :: xs => (x :: xs).take n :: chunksF n fuel ((x :: xs).drop n)

end Entries

end OpList

section TrieOfList

variable {α : Type}

/-- **A list as a trie**, with fuel: the even positions left, the odd ones right. -/
def Trie.ofListF : ℕ → List α → Trie α
  | _, [] => .nil
  | _, [x] => .leaf x
  | 0, _ :: _ :: _ => .nil
  | fuel + 1, x :: y :: l =>
    .node (ofListF fuel (evenPart (x :: y :: l))) (ofListF fuel (oddPart (x :: y :: l)))

/-- **A list as a trie** (`Trie.get` reads entry `k` in `O(log n)`). -/
def Trie.ofList (l : List α) : Trie α := Trie.ofListF l.length l

/-- **The first `n` entries of `l`, of length `L`**: `l` itself when `n = L`, with no pass over
it. -/
def takeL (n L : ℕ) (l : List α) : List α := cond (Nat.beq n L) l (l.take n)

/-- **A list of lists joined**: one list as it is, with no pass over it. -/
def flattenL : List (List α) → List α
  | [l] => l
  | ls => ls.flatten

/-- **One run `(s, d, c)` of an index map read from `xs`** (of length `L`): a run of step `1` is
the slice of `c` entries from `s`, a run of step `0` entry `s` repeated, any other run read entry
by entry from the trie `T` of `xs`. A run that starts past its own count `c` (`c < s`) is read from
the trie too, so reaching its start costs no more than its entries. -/
def pickRun [Inhabited α] (xs : List α) (L : ℕ) (T : Trie α) (s : ℕ) (d : ℤ) (c : ℕ) : List α :=
  cond (d == 1 && Nat.ble s c) (cond (Nat.beq s 0) (takeL c L xs) ((xs.drop s).take c))
    (cond (d == 0) (List.replicate c (cond (Nat.ble s c) (xs.getD s default) (T.get s)))
      ((List.range c).map fun t : ℕ => T.get ((s : ℤ) + d * t).toNat))

/-- **The entries of `xs` (of length `L`) at an index map's entries**, run by run (`pickRun`), `T`
the trie of `xs` for the runs of other steps. -/
def pickRuns [Inhabited α] (xs : List α) (L : ℕ) (T : Trie α) : IndexMap → List α
  | [] => []
  | (s, d, c) :: rest => pickRun xs L T s d c ++ pickRuns xs L T rest

/-- **The entries of `xs` at the entries of `idx`**: `idx.toList.map (Trie.ofList xs).get` for
an index map in range of `xs` (`pickL_eq`), with no trie for runs of step `0` or `1` that start
within their count. -/
def pickL [Inhabited α] (xs : List α) (idx : IndexMap) : List α :=
  pickRuns xs xs.length (Trie.ofList xs) idx

end TrieOfList

section Codes

variable (ir : RealizedProgram)

/-- **The codes of a constant of circuit `c`'s field** (`Logic.constInB`): its entries; `none` for
a value of another field or of another kind. -/
def constCodes? (c v : ℕ) : Option (List ℕ) :=
  cond (Nat.beq (ir.valueField v) (ir.circField c) && ir.isConstant v) (some (ir.constEntries v))
    none

end Codes

section Named

variable (ir : RealizedProgram)

/-- **Rows shifted per block**: `m` copies of `rows`, copy `b` reading the columns `+ b·C`
(`BatchedOperator`'s `emit`, `linear.h`). -/
def shiftRows (C m : ℕ) (rows : List (List (ℕ × ℕ))) : List (List (ℕ × ℕ)) :=
  ((List.range m).map fun b => rows.map fun r => r.map fun t => (t.1 + b * C, t.2)).flatten

/-- **The row of `sum w`**: `(i, 1)` for `i < w` (`Sum`, `linear.h`). -/
def sumRow (w : ℕ) : List (ℕ × ℕ) := (List.range w).map fun i => (i, 1)

/-- **The row of `fromDigits`** from column `l`: `(l + i, w·base^i)` for `i < k`, each weight from
the last by the code arithmetic (`FromDigits`, `linear.h`). -/
def opDigitRow (ar : GKR.Fold.CodeArith) (base : ℕ) : ℕ → ℕ → ℕ → List (ℕ × ℕ)
  | _, 0, _ => []
  | l, k + 1, w => (l, w) :: opDigitRow ar base (l + 1) k (ar.mul w base)

/-- **The rows of a constant diagonal** of `n` entries with codes `es`: row `j` is `(j, e_j)`
(`ConstDiagonal`, `linear.h`). -/
def diagRows (n : ℕ) (es : List ℕ) : List (List (ℕ × ℕ)) :=
  (List.range n).map fun j => [(j, es.getD j 0)]

/-- **The constant rows of a named operator** in circuit `c` (`OpSpec::emit`, `linear.h`): `sum`,
`fromDigits`, `constDiagonal` (a constant of the circuit's field, `constCodes?`) and `batched` of
these; `none` for every other kind. -/
def emitRows (env : TEnv) (c : ℕ) : NamedOp → Option (List (List (ℕ × ℕ)))
  | .sum w => some [sumRow w]
  | .fromDigits k base => some [opDigitRow env.ar base 0 k 1]
  | .constDiagonal d => (constCodes? ir c d).map (diagRows (ir.value d).size)
  | .batched b op => (emitRows env c op).map (shiftRows (NamedOp.cols ir op) b)
  | _ => none

end Named

section Sparse

variable (ir : RealizedProgram)

/-- **A printed coefficient's code** in circuit `c`: a constant's own code, or entry `i` of a
constant `v` of the circuit's field (`constCodes?`); `none` otherwise. -/
def coefCode (c : ℕ) : Coef → Option ℕ
  | .const a => some a
  | .node v i => (constCodes? ir c v).map fun es => es.getD i 0

end Sparse

end GordieHowe.RealizedProgram
