-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHoweNative.Language.Realizations.Circuit.RelTable

/-!
# GordieHowe: the compiled definitions of `GordieHowe.Language.Realizations.Circuit.RelFamily`

The definitions of `GordieHowe.Language.Realizations.Circuit.RelFamily` that the certificate checkers run, and the
facts their bodies use, in the Mathlib-free library `GordieHoweNative`, which Lake compiles to
a shared library (`precompileModules`): native mode runs the checkers as compiled code. The
declarations keep their names. Their lemmas are in
`GordieHowe/Language/Realizations/Circuit/RelFamily.lean`, which imports this module.
-/

local notation "ℕ" => Nat

public section

namespace GordieHowe.GKR.Rel

open GordieHowe.RealizedProgram (Trie teW)

/-- **The first leaf of fraction `i`'s span**, with `fuel` levels: a leaf (`i < n`) itself, an inner
node its left kid's first leaf. `T` holds the inner nodes. -/
@[expose] def fracLo (T : Trie Frac) (n : ℕ) : ℕ → ℕ → ℕ
  | 0, i => i
  | f + 1, i => cond (Nat.blt i n) i (fracLo T n f (T.get (i - n)).l)

/-- **One past the last leaf of fraction `i`'s span**, with `fuel` levels. -/
@[expose] def fracHi (T : Trie Frac) (n : ℕ) : ℕ → ℕ → ℕ
  | 0, i => i + 1
  | f + 1, i => cond (Nat.blt i n) (i + 1) (fracHi T n f (T.get (i - n)).r)

/-- **Inner node `k` of a tree of `n` leaves is well placed**: its kids lie below it (fraction
`n + k`), and the left kid's span ends where the right kid's begins. -/
@[expose] def fracNodeOkB (T : Trie Frac) (n : ℕ) (f : Frac) (k : ℕ) : Bool :=
  Nat.blt f.l (n + k) && Nat.blt f.r (n + k) &&
    Nat.beq (fracHi T n (n + k) f.l) (fracLo T n (n + k) f.r)

/-- **The tree is well formed**: at least one leaf, every inner node well placed, and the root (the
last fraction) spanning every leaf. -/
@[expose] def FracTree.okB (tr : FracTree) : Bool :=
  let n := tr.dens.length
  let m := tr.inner.length
  let T := Trie.ofList tr.inner
  Nat.blt 0 n && tr.inner.zipIdx.all (fun p => fracNodeOkB T n p.1 p.2) &&
    Nat.beq (fracLo T n (n + m) (n + m - 1)) 0 && Nat.beq (fracHi T n (n + m) (n + m - 1)) n

/-- **The fractions by index**: per leaf no numerator (one) and its denominator, then per inner node
its numerator and denominator. -/
@[expose] def FracTree.fracs (tr : FracTree) : Trie (Option Wire × Wire) :=
  Trie.ofList (tr.dens.map (fun d => (none, d)) ++ tr.inner.map fun f => (some f.num, f.den))

/-- **`n_a · d_b`** over the fractions `F`: `d_b` alone when `a`'s numerator is one. -/
@[expose] def fracTerm (F : Trie (Option Wire × Wire)) (a b : ℕ) : TE :=
  match (F.get a).1 with
  | none => teW (F.get b).2
  | some na => .mul (teW na) (teW (F.get b).2)

/-- **The cuts of the inner nodes**: the numerator against `n_l·d_r + n_r·d_l`, the denominator
against `d_l·d_r`. -/
@[expose] def FracTree.cuts (tr : FracTree) : List (Wire × TE) :=
  let F := tr.fracs
  tr.inner.flatMap fun f =>
    [(f.num, .add (fracTerm F f.l f.r) (fracTerm F f.r f.l)),
     (f.den, .mul (teW (F.get f.l).2) (teW (F.get f.r).2))]

/-- **The root's numerator and denominator** as tree expressions (a leaf root's numerator: one). -/
@[expose] def FracTree.rootTE (tr : FracTree) : TE × TE :=
  let x := tr.fracs.get (tr.dens.length + tr.inner.length - 1)
  (match x.1 with
    | none => .const 1
    | some w => teW w, teW x.2)

end GordieHowe.GKR.Rel

namespace GordieHowe.RealizedProgram

open GordieHowe.GKR.Certificate GordieHowe.GKR.Fold GordieHowe.Twin
open GordieHowe.GKR.Rel (Wire TE EntryCert Assert Frac FracTree LogupCert MacHCert FamCert relOkE)

/-- **Wire `i` of table node `k`.** -/
@[expose] def wireAt (E : ETable) (k i : ℕ) : Wire := (E.get k).wires.getD i default

/-- **Table node `k`'s wires as a trie**, with their count: read many times, a node's wires are
looked up by key (`wireAtT`), not walked as a list. -/
@[expose] def wiresT (E : ETable) (k : ℕ) : Trie Wire × ℕ :=
  (Trie.ofList (E.get k).wires, (E.get k).wires.length)

/-- **Wire `i` of a node's wire trie** (the default past its count). -/
@[expose] def wireAtT (T : Trie Wire × ℕ) (i : ℕ) : Wire := cond (Nat.blt i T.2) (T.1.get i) default

/-- **The needle coordinates of a group**: per member, in order, its node `y` and each coordinate
`first, …, first + count − 1` it reads. -/
@[expose] def needleCoords (ms : List Member) (ys : List ℕ) : List (ℕ × ℕ) :=
  (ms.zip ys).flatMap fun p => (List.range (Member.count p.1)).map fun j =>
    (p.2, Member.first p.1 + j)

/-- **The needles' wires of a group**: per member, its node's wires at its coordinates, read through
the node's wire trie (`needleCoords`' wires, `needleWires_eq`). -/
@[expose] def needleWires (E : ETable) (ms : List Member) (ys : List ℕ) : List Wire :=
  (ms.zip ys).flatMap fun p =>
    let T := wiresT E p.2
    (List.range (Member.count p.1)).map fun j => wireAtT T (Member.first p.1 + j)

section

variable (ir : RealizedProgram)

/-- **The histogram values of group `g` of table `t`**: the static, then the late one, the present
ones. -/
@[expose] def histVals (t g : ℕ) : List ℕ :=
  [(ir.groupOf t g).staticMult, (ir.groupOf t g).lateMult].filterMap id

/-- **Whether table `t`'s rows are a range.** -/
@[expose] def rangeRowsB (t : ℕ) : Bool :=
  match (ir.table t).rows with
  | .range _ => true
  | _ => false

/-- **Every challenge's value lies in the challenge's field** (a sweep of the values). -/
@[expose] def chalFieldsB : Bool :=
  (List.range ir.values.length).all fun v =>
    match (ir.value v).kind with
    | .challenge j => Nat.beq (ir.valueField v) (ir.chalField j)
    | _ => true

variable (c : ℕ) (ar : CodeArith) (cd : CircuitData)

/-- **The cuts of a range LogUp entry** (group `g` of table `t`): per needle coordinate, its leaf's
denominator against `α − needle`; the fraction tree's inner nodes; the sum against the histograms'
coordinates times the weights' inputs. -/
@[expose] def logupCuts (t g : ℕ) (lc : LogupCert) : List (Wire × TE) :=
  let E := cd.table
  let aT := teW (wireAt E lc.alpha 0)
  let leaves := (lc.tree.dens.zip (needleCoords (ir.members t g) lc.needles)).map fun p =>
    (p.1, TE.add aT (.scale cd.neg1 (teW (wireAt E p.2.1 p.2.2))))
  let a := ((ir.circuit c).inputs.getD lc.weights default).first
  let sumT := TE.sumL (lc.hists.flatMap fun h =>
    (List.range (E.get h).len).map fun j => TE.mul (teW (wireAt E h j)) (.wire 0 1 (a + j)))
  leaves ++ lc.tree.cuts ++ [(lc.sum, sumT)]

/-- **The assertion item of a range LogUp entry**: `N − D·S` at its one assertion pair. -/
@[expose] def logupItem (lc : LogupCert) (as : List Assert) : ℕ × ℕ × TE :=
  let a := as.headD default
  (a.Z, a.U, .add lc.tree.rootTE.1 (.scale cd.neg1 (.mul lc.tree.rootTE.2 (teW lc.sum))))

/-- **The guards of a range LogUp entry**: each pointer of the record against the printed program
(see the module docstring). -/
@[expose] def logupGuardE (k t g : ℕ) (lc : LogupCert) (as : List Assert) : Except CertFailure Unit :=
  let E := cd.table
  let env := cd.env ar
  let T := ir.tableSize t
  let fail (r : FamReason) : CertFailure := ⟨k, 0, .family r⟩
  seqE (guardE (Nat.blt t ir.tables.length && Nat.blt g (ir.groupCountOf t) && ir.rangeRowsB t &&
      Nat.beq (ir.chalField (ir.alphaOf t)) (ir.circField c)) (fail .kind))
    (seqE (guardE (Nat.blt lc.alpha E.size && (E.get lc.alpha).cut &&
        Nat.ble 1 (E.get lc.alpha).len &&
        match (E.get lc.alpha).node with
        | .value u _ =>
          Nat.blt u ir.values.length && Nat.beq (ir.valueField u) (ir.circField c) &&
            E.eqB env lc.alpha (.leaf u) &&
            match (ir.value u).kind with
            | .challenge j => Nat.beq j (ir.alphaOf t)
            | _ => false
        | _ => false) (fail .alpha))
      (seqE (guardE (Nat.beq lc.needles.length (ir.members t g).length &&
          ((ir.members t g).zip lc.needles).all fun p =>
            Nat.blt p.2 E.size && (E.get p.2).cut &&
              E.eqB env p.2 (ir.needleExpr (Member.pred p.1) (Member.needle p.1)) &&
              Nat.ble (Member.first p.1 + Member.count p.1) (E.get p.2).len) (fail .needles))
        (seqE (guardE (Nat.beq lc.hists.length (ir.histVals t g).length &&
            ((ir.histVals t g).zip lc.hists).all fun p =>
              Nat.blt p.1 ir.values.length && Nat.blt p.2 E.size && (E.get p.2).cut &&
                E.eqB env p.2 (.leaf p.1) && Nat.beq (E.get p.2).len (ir.value p.1).size &&
                Nat.ble (ir.value p.1).size T) (fail .hists))
          (seqE (guardE (Nat.blt lc.weights (ir.circuit c).inputs.length &&
              match (ir.circuit c).inputs.getD lc.weights default with
              | .realizationPub (.weights t') a n =>
                Nat.beq t' t && Nat.beq n T && Nat.ble 1 a &&
                  Nat.ble (a + n) (ir.circuit c).publicInputs
              | _ => false) (fail .weights))
            (seqE (guardE (Nat.beq lc.tree.dens.length (ir.groupCount t g) && lc.tree.okB)
                (fail .tree))
              (guardE (Nat.beq as.length 1) (fail .asserts)))))))

/-- **A range LogUp entry checks**, as its twin: its guards, its cuts, its item. -/
@[expose] def logupE (k t g : ℕ) (lc : LogupCert) (as : List Assert) : Except CertFailure Unit :=
  seqE (ir.logupGuardE c ar cd k t g lc as)
    (seqE (mapE (fun r => ⟨k, 0, .rel r⟩)
      (relOkE cd.w cd.dag cd.consts ar (ir.logupCuts c cd t g lc) []))
      (mapE (fun r => ⟨k, 0, .rel r⟩) (relOkE cd.w cd.dag cd.consts ar [] [logupItem cd lc as])))

/-- **The assertion item of a MAC H entry**: `U − Σ_c chunk_c · r_c` at its one assertion pair. -/
@[expose] def macHItem (mc : MacHCert) (as : List Assert) : ℕ × ℕ × TE :=
  let a := as.headD default
  (a.Z, a.U, .add (teW (wireAt cd.table mc.tag 0)) (.scale cd.neg1 (TE.sumL
    (mc.chunks.zipIdx.map fun q => TE.mul (teW q.1) (teW (wireAt cd.table mc.powers q.2))))))

/-- **The guards of a MAC H entry**: each pointer of the record against the printed program (see
the module docstring). -/
@[expose] def macHGuardE (k p : ℕ) (mc : MacHCert) (as : List Assert) : Except CertFailure Unit :=
  let E := cd.table
  let env := cd.env ar
  let fail (r : FamReason) : CertFailure := ⟨k, 0, .family r⟩
  match (ir.predicate p).body with
  | .cross dx x _ _ _ real =>
    seqE (guardE (Nat.blt p ir.predicates.length && real.hPredicate.isNone &&
        Nat.beq dx (ir.circuit c).domain && Nat.beq real.macField (ir.circField c) &&
        Nat.blt real.macField ir.fields.length && Nat.blt 1 (ir.charOf real.macField)) (fail .kind))
      (seqE (guardE (Nat.blt mc.powers E.size && (E.get mc.powers).cut &&
          Nat.ble real.chunks (E.get mc.powers).len &&
          match (E.get mc.powers).node with
          | .value r _ => E.eqB env mc.powers (.leaf r) &&
              ir.powersB r real.key real.chunks real.macField
          | _ => false) (fail .powers))
        (seqE (guardE (Nat.blt mc.tag E.size && (E.get mc.tag).cut &&
            Nat.ble 1 (E.get mc.tag).len &&
            E.eqB env mc.tag (.leaf real.tag) && ir.macTagB real) (fail .tag))
          (seqE (guardE (Nat.blt mc.bits E.size && (E.get mc.bits).cut &&
              Nat.beq (E.get mc.bits).len (real.chunks * real.width) &&
              ir.zeroPadB (ir.domainField dx) (real.chunks * real.width) (E.print env mc.bits) x)
              (fail .bits))
            (seqE (guardE (Nat.beq mc.chunks.length real.chunks) (fail .chunks))
              (guardE (Nat.beq as.length 1) (fail .asserts))))))
  | _ => .error (fail .kind)

/-- **An alignment entry's pairs read its filler block** `b`, in order: `n` pairs, pair `i` reading
input `a + i` of the block `.filler a n`. -/
@[expose] def fillerGuardB (n b : ℕ) (as : List Assert) : Bool :=
  Nat.blt b (ir.circuit c).inputs.length &&
    match (ir.circuit c).inputs.getD b default with
    | .filler a n' => Nat.beq n' n && Nat.beq as.length n &&
        as.zipIdx.all fun q => Nat.beq q.1.U (a + q.2)
    | _ => false

/-- **`logupCuts`, its wires read by key**: the needles' and the histograms' wires through their
nodes' wire tries (`logupCutsT_eq`). -/
@[expose] def logupCutsT (t g : ℕ) (lc : LogupCert) : List (Wire × TE) :=
  let E := cd.table
  let aT := teW (wireAt E lc.alpha 0)
  let leaves := (lc.tree.dens.zip (needleWires E (ir.members t g) lc.needles)).map fun p =>
    (p.1, TE.add aT (.scale cd.neg1 (teW p.2)))
  let a := ((ir.circuit c).inputs.getD lc.weights default).first
  let sumT := TE.sumL (lc.hists.flatMap fun h =>
    let T := wiresT E h
    (List.range (E.get h).len).map fun j => TE.mul (teW (wireAtT T j)) (.wire 0 1 (a + j)))
  leaves ++ lc.tree.cuts ++ [(lc.sum, sumT)]

/-- **`macHCuts`, the operand's wires read by key** (`macHCutsT_eq`). -/
@[expose] def macHCutsT (p : ℕ) (mc : MacHCert) : List (Wire × TE) :=
  match (ir.predicate p).body with
  | .cross _ _ _ _ _ real =>
    let w := real.width
    let G := Trie.ofList (powList ar 2 w 1)
    let B := wiresT cd.table mc.bits
    mc.chunks.zipIdx.map fun q =>
      (q.1, TE.sumL ((List.range w).map fun i =>
        TE.scale (G.get i) (teW (wireAtT B (q.2 * w + i)))))
  | _ => []

/-- **The family cuts of entry `k`**: a range LogUp's, a MAC H's; none for any other entry. Wires
are read by key (`logupCutsT`, `macHCutsT`), so a slice's cost does not grow with its offset. -/
@[expose] def famCuts (k : ℕ) : List (Wire × TE) :=
  match (ir.circuit c).entries.getD k default, (cd.entries.getD k default).fam with
  | .realization (.logup t g), some (.logup lc) => ir.logupCutsT c cd t g lc
  | .realization (.macH p), some (.macH mc) => ir.macHCutsT ar cd p mc
  | _, _ => []

/-- **The head of a family entry `k`** with family record `f`: the guards, and the relational
check of its assertion items (an alignment entry's pairs read their inputs). -/
@[expose] def famHeadE (k : ℕ) (f : FamCert) : Except CertFailure Unit :=
  let en := cd.entries.getD k default
  let rel (zs : List (ℕ × ℕ × TE)) : Except CertFailure Unit :=
    mapE (fun r => ⟨k, 0, .rel r⟩) (relOkE cd.w cd.dag cd.consts ar [] zs)
  match (ir.circuit c).entries.getD k default, f with
  | .alignment n, .alignment b =>
    seqE (guardE (ir.fillerGuardB c n b en.asserts) ⟨k, 0, .family .filler⟩)
      (rel (en.asserts.map fun a => (a.Z, a.U, .wire 0 1 a.U)))
  | .realization (.logup t g), .logup lc =>
    seqE (ir.logupGuardE c ar cd k t g lc en.asserts) (rel [logupItem cd lc en.asserts])
  | .realization (.macH p), .macH mc =>
    seqE (ir.macHGuardE c ar cd k p mc en.asserts) (rel [macHItem cd mc en.asserts])
  | _, _ => .error ⟨k, 0, .family .kind⟩

/-- **Family cuts `s, …, s + n − 1` of entry `k`** (`n = 0`: every cut from `s` on), accepted by the
relational check: a large family is checked in slices. -/
@[expose] def famSliceE (k s n : ℕ) : Except CertFailure Unit :=
  let cs := ir.famCuts c ar cd k
  mapE (fun r => ⟨k, s, .rel r⟩)
    (relOkE cd.w cd.dag cd.consts ar (cond (Nat.beq n 0) (cs.drop s) ((cs.drop s).take n)) [])

end

end GordieHowe.RealizedProgram
