-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Language.Realizations.Lowering
public import GordieHowe.ProofSystem.Program.Basic

@[expose] public section

/-!
# The domains of the GordieHowe lowered system

The constraints and domains of the lowered system of the C++ core (`lib/gordiehowe/system.h`,
`compile(const System&)`; a shallow embedding with reviewed C++ correspondence):

* **constraints by kind**: affine rows (`AffineRow`: a linear form on the cells and a constant,
  both read from the statement and the run, since coefficients may be public computations of
  challenges and a late value is read as its message minus its pad), quadratic triples
  (`QuadRow`) and batched relations (`BatchRelation`);
* **the domains** (`Domain`): each with its field, its committed coordinates (`Domain.Cells`,
  every committed cell of the domain, pads included), the base of every coordinate, and its
  constraints by kind, the circuit constraints (predicates, the domain's GKR kernel) among them.
  Their conjunction is the domain's predicate (`Domain.Holds`). The lowered constraint of a family
  of domains (`Domain.lowered`) is the conjunction of the domains' predicates on the product of
  their cells (`Domain.Assignment`). Each domain's constraints read only its own cells and the run,
  by the type of `Domain.Holds`. A constraint across domains is assigned to one domain and reads
  the other through the run's messages, as the C++ does: the MAC's `U = T - B` is an `H`
  constraint reading the message `T` and `H`'s pad `B`; the MAC rows `acc - B_A - MACConv(r)(c_A) = 0`
  are `A` rows reading `acc` as its message minus `A`'s pad and `r` from the challenge `β`.

**The circuit proof of a domain** (`DomainProof`): a `GordieHowe.FieldProof` with its public input read
from the statement and the run, the domain's cells decoded from its witness, and the bridge
`enforce`: the circuit proof's relation at its public input gives the domain's predicate on the
decoded cells. Its honest prover (`DomainProof.Honest`) encodes the circuit's honest input from the
domain's cells, in the circuit's domain wherever the domain's honest predicate holds.
-/

namespace GordieHowe
open IOP RealizedProgram.ProofSystem.PhaseLayout
open scoped NNReal

variable {K : ℕ} {L : RealizedProgram.ProofSystem.PhaseLayout K} {Stmt : Type}

/-! ### Constraints by kind -/

/-- **An affine row** of a domain with field `F` and cell coordinates `ι` (`domain.h`, affine
rows): the linear form `form x r` on the cells and the constant `const x r`, both read from the
statement and the run (a coefficient may be a public computation of a challenge, the MAC's
`r_c = β^(c+1)`; a late value is its message minus its pad, the message entering the constant and
the pad the form). -/
structure AffineRow (L : RealizedProgram.ProofSystem.PhaseLayout K) (Stmt F ι : Type) [Field F] where
  /-- The linear form on the cells. -/
  form : Stmt → L.Run → (ι → F) →ₗ[F] F
  /-- The constant. -/
  const : Stmt → L.Run → F

/-- **An affine row holds**: `form x r a + const x r = 0`. -/
def AffineRow.Holds {F ι : Type} [Field F] (ρ : AffineRow L Stmt F ι) (x : Stmt) (a : ι → F)
    (r : L.Run) : Prop :=
  ρ.form x r a + ρ.const x r = 0

/-- **A quadratic triple** of a domain (`domain.h:2797-2801`: the batch's pad products and squaring
chains): `left a * right a = out a`, for linear forms on the cells (the C++ triples are
coordinates). -/
structure QuadRow (F ι : Type) [Field F] where
  /-- The left factor. -/
  left : (ι → F) →ₗ[F] F
  /-- The right factor. -/
  right : (ι → F) →ₗ[F] F
  /-- The product. -/
  out : (ι → F) →ₗ[F] F

/-- **A quadratic triple holds**: `left a * right a = out a`. -/
def QuadRow.Holds {F ι : Type} [Field F] (q : QuadRow F ι) (a : ι → F) : Prop :=
  q.left a * q.right a = q.out a

/-- **A batched relation** of a domain over statements `Stmt` (`batch.h`, `BatchKernel`: "for every
instance t, Q(L_1(W, t), ..., L_K(W, t)) = 0 ... each operand L_j is an affine view of phase-0
tables W"): the relation `Q` on `arity` operands, the same at every instance (`FieldRelation`, whose
coefficients are fixed), and for every instance the operands as affine views of the cells: an
additive part (`operand`) and a constant part read from the statement (`offset`); the zerocheck
proves `Q` at every instance. A per-instance public coefficient is an operand with no additive
part, its value the offset: the C++ reads a constant monomial this way (`domain.h`,
`batch_parts`: the constant operand `{f.one(), {}}`), so `Q` itself has no constant term. The
additive part is not necessarily linear over `F`: a batch over a table of subfield words reads its
operands from the words' bits (`batch.h`, `BitOperandMap`), and bit `i` of a word is a trace form,
linear over the prime field only. -/
structure BatchRelation (Stmt F ι : Type) [Field F] where
  /-- The number of operands. -/
  arity : ℕ
  /-- The relation. -/
  Q : (Fin arity → F) → F
  /-- The instances. -/
  Inst : Type
  /-- The additive part of operand `j` of instance `i`. -/
  operand : Inst → Fin arity → (ι → F) →+ F
  /-- The constant part of operand `j` of instance `i`, read from the statement. -/
  offset : Stmt → Inst → Fin arity → F

/-- **A batched relation holds** at the statement `x`: `Q` vanishes on the operands of every
instance. -/
def BatchRelation.Holds {Stmt F ι : Type} [Field F] (b : BatchRelation Stmt F ι) (x : Stmt)
    (a : ι → F) : Prop :=
  ∀ i, b.Q (fun j => b.operand i j a + b.offset x i j) = 0

/-! ### Domains -/

/-- **A domain** of the lowered system (`domain.h`, `CompiledDomain`): its field, its committed
coordinates (every committed cell of the domain, pads included; packed and bound values are views
of them), the base of every coordinate, and its constraints by kind: the circuit constraints (the
domain's GKR kernel, as predicates on the statement, the cells and the run), the affine rows, the
quadratic triples and the batched relations. The base of a coordinate is the set its value lies in
by the domain's packing tree (`domain.h`, the packing tree's membership: decoded coordinates lie in
their base): `{0, 1}` for a bit-packed cell, a subfield for a relatively packed one. The packing
itself is data of the domain's circuit proof (`DomainProof`), which establishes the bases. -/
structure Domain (L : RealizedProgram.ProofSystem.PhaseLayout K) (Stmt : Type) where
  /-- The domain's field. -/
  F : Type
  [field : Field F]
  /-- The committed coordinates. -/
  ι : Type
  /-- The base of each coordinate. -/
  base : ι → Set F
  /-- The circuit constraints. -/
  Circ : Type
  /-- The predicate of each circuit constraint. -/
  circuit : Circ → L.Constraint Stmt (ι → F)
  /-- The affine rows. -/
  Row : Type
  /-- Each affine row. -/
  affine : Row → AffineRow L Stmt F ι
  /-- The quadratic triples. -/
  Quad : Type
  /-- Each quadratic triple. -/
  quad : Quad → QuadRow F ι
  /-- The batched relations. -/
  Batch : Type
  /-- Each batched relation. -/
  batch : Batch → BatchRelation Stmt F ι
  /-- **The view coordinates**: logical coordinates of the domain's packing tree that rows read
  besides the cells (the bits of designated words of a stage; none by default). -/
  View : Type := Empty
  /-- The value of each view coordinate, read from the cells (bit `b` of a word is a trace form of
  the word, linear over the prime field only). -/
  view : (ι → F) → View → F := by exact fun _ v => nomatch v
  /-- **The rows on views** (`Placement::kAffine` rows reading packed bits and bit views; their
  claims join the stage's combined measurement): affine forms on the cells and the view
  coordinates (none by default). -/
  ViewRow : Type := Empty
  /-- Each row on views. -/
  viewRow : ViewRow → AffineRow L Stmt F (ι ⊕ View) := by exact fun i => nomatch i

attribute [instance] Domain.field

namespace Domain

/-- The committed cells of a domain. -/
abbrev Cells (D : Domain L Stmt) : Type := D.ι → D.F

/-- **The predicate of a domain** on its cells `a`, at the statement `x` and the run `r`: every
coordinate lies in its base, and every circuit constraint, affine row, quadratic triple, batched
relation and row on views holds (a row on views at the cells and the view coordinates read from
them). -/
structure Holds (D : Domain L Stmt) (x : Stmt) (a : D.Cells) (r : L.Run) : Prop where
  /-- Every coordinate lies in its base. -/
  base : ∀ i, a i ∈ D.base i
  /-- Every circuit constraint holds. -/
  circuit : ∀ c, D.circuit c x a r
  /-- Every affine row holds. -/
  affine : ∀ i, (D.affine i).Holds x a r
  /-- Every quadratic triple holds. -/
  quad : ∀ i, (D.quad i).Holds a
  /-- Every batched relation holds. -/
  batch : ∀ i, (D.batch i).Holds x a
  /-- Every row on views holds. -/
  viewRow : ∀ i, (D.viewRow i).Holds x (Sum.elim a (D.view a)) r

/-- **The assignment of a family of domains**: the cells of every domain. -/
abbrev Assignment {m : ℕ} (D : Fin m → Domain L Stmt) : Type := ∀ d, (D d).Cells

/-- **The lowered constraint of a family of domains**: every domain's predicate on its own cells. -/
def lowered {m : ℕ} (D : Fin m → Domain L Stmt) : L.Constraint Stmt (Assignment D) :=
  fun x a r => ∀ d, (D d).Holds x (a d) r

end Domain

/-! ### The circuit proof of a domain -/

/-- **The circuit proof of a domain** `D`: a circuit proof (`FieldProof`) for a relation `holds`
on public inputs `Pub` and witnesses `Wit`, the public input read from the statement and the run
(the verifier's public computations: challenge powers, weights, message coordinates), the domain's
cells decoded from the witness (computable, polynomial time: it is part of the extraction), and
the bridge: the relation at the public input gives the domain's predicate on the decoded cells. -/
structure DomainProof (L : RealizedProgram.ProofSystem.PhaseLayout K) (Stmt : Type) (D : Domain L Stmt) where
  /-- The circuit's public input. -/
  Pub : Type
  /-- The circuit's witness. -/
  Wit : Type
  /-- The circuit's relation. -/
  holds : Pub → Wit → Prop
  /-- The circuit proof. -/
  proof : FieldProof Pub Wit holds
  /-- The public input, from the statement and the run. -/
  pub : Stmt → L.Run → Pub
  /-- The domain's cells decoded from the witness. -/
  decode : Wit → D.Cells
  /-- The relation at the public input gives the domain's predicate on the decoded cells. -/
  enforce : ∀ x r w, holds (pub x r) w → D.Holds x (decode w) r

/-- **The honest prover of a domain's circuit proof** at the domain's honest predicate `hpred`,
simulated by `S`: the circuit's honest inputs and domain, the honest input encoded from the domain's
cells, in the domain wherever `hpred` holds, and the circuit proof's honest prover. -/
structure DomainProof.Honest {D : Domain L Stmt} (P : DomainProof L Stmt D)
    (hpred : L.Constraint Stmt D.Cells) (S : P.proof.Sim) where
  /-- The circuit's honest inputs. -/
  In : Type
  /-- The circuit's domain. -/
  dom : P.Pub → In → Prop
  /-- The honest input, encoded from the domain's cells. -/
  encode : D.Cells → In
  /-- Where the honest predicate holds, the encoded input lies in the circuit's domain. -/
  dom_of : ∀ x a r, hpred x a r → dom (P.pub x r) (encode a)
  /-- The circuit proof's honest prover. -/
  circuit : P.proof.Honest S In dom

end GordieHowe
