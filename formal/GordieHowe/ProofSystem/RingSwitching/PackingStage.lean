-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.FieldProof.MaskedReduction
public import GordieHowe.ProofSystem.RingSwitching.StageAlgebra

@[expose] public section

/-!
# One packing stage of a GordieHowe domain as a masked row reduction

A packing stage `B < T` (`lib/gordiehowe/compiler/stage.h`, `PackingStage`;
`GordieHowe/ProofSystem/RingSwitching/StageAlgebra.lean`) reduces a claim on a child node's coordinates, `ng` groups of
`d = [T : B]` coordinates each packed into words `W_g` of the parent's region, to `d` masked
measurements and rows on the words (`tree_zk.h`, `TreeRows::stage`). The reduction is ring switching
(Diamond–Posen, ePrint 2024/504, section 1.2) in its Frobenius-twist form (Hashcaster): the claim
becomes `rest + Σ_k φ^k(⟨a_k, W⟩)`, the twist `φ^k` moved onto the forms
(`StageBasis.linear_identity`), and the `d` forms are revealed masked. A measurement is such a
masked twisted form.

* the measurements `M_k = Σ_g a_{k,g} W_g + σ_k` (`k < d`), sent by the prover, with
  `a_{k,g} = StageBasis.form` of the claim's coefficients on group `g` (`measureRow`, the row
  `Σ_g a_{k,g} W_g + σ_k = M_k`);
* the remainder `rest − Σ_k φ^k(σ_k) = −Σ_k φ^k(M_k)` (`remainderRow`), with `rest` the claim's
  part off the child's coordinates (`restPart`).

The mode says how the masks `σ_k` and their Frobenius twists `φ^k(σ_k)` are affine in committed
cells (`MaskScheme`): **squaring-chain masks** (`MaskScheme.squaringChain`, `B = GF(2)`): `σ_k` and
the squaring chain `s_{k,j} = σ_k^(2^j)` are cells in `K`, with `d(d−1)/2` product triples;
**subfield masks** (`MaskScheme.subfieldMasks`, `B ⊇ S0`): `σ_k = Σ_i γ_i s_{k,i}` with `s_{k,i}`
cells in the designated subfield `S0` (the prefix rows), so `φ^k(σ_k) = Σ_i φ^k(γ_i) s_{k,i}` when
the cells lie in `S0` (`Valid`, supplied by the commitment's prefix-row subfield test).

`MaskedReduction.measure` appends the measurement message to a masked reduction whose one claim is on the level
`Y ⊕ PackedCoord ng d` (the child's coordinates decoded from the words, `Stage.level`) and replaces
it by the `d + 1` rows on `Y`. **Soundness** (`Sound.measure`) is exact: the rows, the masks'
products and `Valid` give the claim (`claim_of_rows`, from `StageBasis.linear_identity`), so the
stage adds no event and the relation becomes "`Valid` implies the relation". **Hiding**
(`Honest.measure`): the measurement is its value plus the stage's own fresh mask, uniform in
`K^d` (`MaskScheme.Honest.uniform`), so the measurement is uniform at fixed challenges and pads of
the IP before.

`MaskedReduction.stage` is one stage as the C++ runs it on several claims: combination with fresh
coefficients (`MaskedReduction.combine`, error `1/|K|`), then the measurement; its errors sum to the masked
reduction's plus `1/|K|` (`sum_stageError`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking
open GKR.Schedule (one oneValue)
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι] {p m d e ng : ℕ} [ExpChar F p]

/-! ### The child's coordinates and claims on them -/

/-- **A coordinate of a packed child node**: position `pos` of group `group`, the `pos`-th
`B`-coordinate of the parent's word `group` (`tree_zk.h`, a region's `groups` of `d`
coordinates). -/
@[ext]
structure PackedCoord (ng d : ℕ) where
  /-- The group, the parent's word. -/
  group : Fin ng
  /-- The position in the group. -/
  pos : Fin d
  deriving DecidableEq

variable {Y : Type}

/-- **The part of a claim off the child's coordinates**, with its constant. -/
def restPart (c : AffineForm F (Y ⊕ PackedCoord ng d)) : AffineForm F Y :=
  c.filterMapTerms (fun t => t.2.elim (fun y => some (t.1, y)) fun _ => none) c.const

/-- **The claim's coefficient on child coordinate `(g, j)`**: the sum of its terms there. -/
def childCoeff (c : AffineForm F (Y ⊕ PackedCoord ng d)) (g : Fin ng) (j : Fin d) : F :=
  (c.terms.map fun t => t.2.elim (fun _ => 0) fun q => if q = ⟨g, j⟩ then t.1 else 0).sum

/-- **A claim splits** into its part off the child's coordinates and its coefficients on them. -/
theorem eval_split (c : AffineForm F (Y ⊕ PackedCoord ng d)) (z : Y ⊕ PackedCoord ng d → F) :
    c.eval z = (restPart c).eval (z ∘ Sum.inl) +
      ∑ g, ∑ j, childCoeff c g j * z (.inr ⟨g, j⟩) := by
  rw [restPart, AffineForm.eval_filterMapTerms]
  simp only [AffineForm.eval, childCoeff]
  suffices h : ∀ l : List (F × (Y ⊕ PackedCoord ng d)),
      (l.map fun t => t.1 * z t.2).sum =
        (l.map fun t => ((t.2.elim (fun y => some (t.1, y)) fun _ => none : Option (F × Y)).elim 0
          fun u => u.1 * (z ∘ Sum.inl) u.2)).sum +
        ∑ g, ∑ j, (l.map fun t => t.2.elim (fun _ => 0)
          fun q => if q = ⟨g, j⟩ then t.1 else 0).sum * z (.inr ⟨g, j⟩) by
    rw [h]; ring
  intro l
  induction l with
  | nil => simp
  | cons t l ih =>
    obtain ⟨a, y | ⟨g0, j0⟩⟩ := t
    · simp only [List.map_cons, List.sum_cons, ih, Sum.elim_inl, Option.elim, Function.comp_apply,
        zero_add]
      ring
    · simp only [List.map_cons, List.sum_cons, ih, Sum.elim_inr, Option.elim, add_mul,
        Finset.sum_add_distrib, PackedCoord.mk.injEq, ite_mul, zero_mul, ite_and,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, zero_add]
      ring

/-! ### Masks -/

/-- **How a stage's masks enter the rows** (`tree_zk.h:986-1016`, `mask_value`, `add_mask`,
`add_mask_power`): affine forms on the cells for each mask `σ_k` and for its twist `φ^k(σ_k)`, the
product triples that relate them, and the condition `Valid` outside the rows under which the twist
form is `φ^k` of the mask form (`twist_eval`). -/
structure MaskScheme (F ι : Type) [Field F] (p m d : ℕ) [ExpChar F p] where
  /-- The mask `σ_k`. -/
  sigma : Fin d → AffineForm F ι
  /-- The Frobenius twist `φ^k(σ_k)`. -/
  twist : Fin d → AffineForm F ι
  /-- The product triples' index. -/
  Q : Type
  [finQ : Fintype Q]
  /-- The product triples' encoding, which numbers them (`Encodable.fintypeEquivFin`). -/
  [encQ : Encodable Q]
  /-- The product triples. -/
  products : Ligero.Routing.ProductLayout ι Q
  /-- The condition outside the rows. -/
  Valid : (ι → F) → Prop
  /-- The twist form is the twist of the mask form. -/
  twist_eval : ∀ x, Ligero.Routing.SourceProducts products x → Valid x → ∀ k,
    (twist k).eval x = phi p m k ((sigma k).eval x)

attribute [instance] MaskScheme.finQ MaskScheme.encQ

/-- **The honest masks of a scheme**: pads `Pads`, the masks they give (`sigmaOf`), uniform in
`K^d` under uniform pads (`uniform`), and the committed cells that hold them (`Commits`), on which
the mask forms are the masks, the products hold and `Valid` holds. -/
structure MaskScheme.Honest [Fintype F] (Ms : MaskScheme F ι p m d) where
  /-- The pads. -/
  Pads : Type
  [fintype : Fintype Pads]
  [nonempty : Nonempty Pads]
  /-- The masks the pads give. -/
  sigmaOf : Pads → Fin d → F
  /-- The masks are uniform. -/
  uniform : Uniform sigmaOf
  /-- The cells hold the pads. -/
  Commits : Pads → (ι → F) → Prop
  /-- The mask forms are the masks. -/
  sigma_eval : ∀ π x, Commits π x → ∀ k, (Ms.sigma k).eval x = sigmaOf π k
  /-- The products hold. -/
  products : ∀ π x, Commits π x → Ligero.Routing.SourceProducts Ms.products x
  /-- `Valid` holds. -/
  valid : ∀ π x, Commits π x → Ms.Valid x

attribute [instance] MaskScheme.Honest.fintype MaskScheme.Honest.nonempty

/-! ### Squaring-chain masks -/

/-- **A cell of a squaring chain** (`stage.h:134-142`, `chain_cell(k, j)`): `s_{k, j + 1}`,
`j < k`, the `2^(j+1)`-th power of `σ_k`. -/
@[ext]
structure SquaringCell (d : ℕ) where
  /-- The measurement. -/
  k : Fin d
  /-- The step, one less than the C++ `j`. -/
  j : Fin k

/-- The squaring cells as a sigma type. -/
def SquaringCell.equivSigma (d : ℕ) : SquaringCell d ≃ Σ k : Fin d, Fin k where
  toFun c := ⟨c.k, c.j⟩
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (d : ℕ) : Fintype (SquaringCell d) := Fintype.ofEquiv _ (SquaringCell.equivSigma d).symm

/-- The squaring cells are encoded as the sigma type (`SquaringCell.equivSigma`). -/
instance (d : ℕ) : Encodable (SquaringCell d) := Encodable.ofEquiv _ (SquaringCell.equivSigma d)

/-- **The cells of a squaring-chain stage's masks** (`tree_zk.h:233-245`, root own: `σ_k`, then
`s_{k,j}`). -/
structure SquaringChainCells (ι : Type) (d : ℕ) where
  /-- The mask `σ_k`. -/
  sigma : Fin d → ι
  /-- The squaring cell. -/
  chain : SquaringCell d → ι

namespace SquaringChainCells

variable (C : SquaringChainCells ι d)

/-- The cell a squaring cell squares: `σ_k` for the first step, the previous squaring cell after
(`tree_zk.h:1075`: `x0 = j == 1 ? sigma(k) : chain_cell(k, j - 1)`). -/
def prev (c : SquaringCell d) : ι :=
  if h : (c.j : ℕ) = 0 then C.sigma c.k else C.chain ⟨c.k, ⟨c.j - 1, by omega⟩⟩

/-- The cell of the twist `φ^k(σ_k) = σ_k^(2^k)` (`stage.h:140-142`, `twist(k)`). -/
def twist (k : Fin d) : ι :=
  if h : (k : ℕ) = 0 then C.sigma k else C.chain ⟨k, ⟨k - 1, by omega⟩⟩

/-- The squaring triples `prev · prev = chain` (`tree_zk.h:1069-1078`). -/
def products : Ligero.Routing.ProductLayout ι (SquaringCell d) where
  source c := ![C.prev c, C.prev c, C.chain c]

omit [Fintype ι] in
/-- On cells where the squaring triples hold, squaring cell `(k, j)` is `σ_k^(2^(j+1))`. -/
theorem chain_eq_pow {x : ι → F} (h : Ligero.Routing.SourceProducts C.products x)
    (c : SquaringCell d) : x (C.chain c) = x (C.sigma c.k) ^ 2 ^ ((c.j : ℕ) + 1) := by
  obtain ⟨k, j, hj⟩ := c
  induction j with
  | zero =>
    have hq := h ⟨k, ⟨0, hj⟩⟩
    simp only [products, prev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ↓reduceDIte] at hq
    rw [← hq]
    ring
  | succ j ih =>
    have hq := h ⟨k, ⟨j + 1, hj⟩⟩
    simp only [products, prev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.add_one_ne_zero, ↓reduceDIte,
      Nat.add_sub_cancel] at hq
    rw [← hq, ih (by omega)]
    ring

omit [Fintype ι] in
/-- On cells where the squaring triples hold, the twist cell is `σ_k^(2^k)`. -/
theorem twist_eq_pow {x : ι → F} (h : Ligero.Routing.SourceProducts C.products x) (k : Fin d) :
    x (C.twist k) = x (C.sigma k) ^ 2 ^ (k : ℕ) := by
  unfold twist
  split_ifs with hk
  · rw [hk, pow_zero, pow_one]
  · rw [C.chain_eq_pow h]
    congr 2
    simp only
    omega

end SquaringChainCells

/-- **Squaring-chain masks** (`B = GF(2)`, `φ` the squaring; `stage.h:27-33`): `σ_k` and
`φ^k(σ_k)` are single cells in `K`, the squaring chain's triples relate them, and nothing is
needed outside the rows. -/
def MaskScheme.squaringChain [ExpChar F 2] (C : SquaringChainCells ι d) : MaskScheme F ι 2 1 d where
  sigma k := AffineForm.var (C.sigma k)
  twist k := AffineForm.var (C.twist k)
  Q := SquaringCell d
  products := C.products
  Valid _ := True
  twist_eval x h _ k := by
    simp only [AffineForm.eval_var, phi_def, one_mul]
    exact C.twist_eq_pow h k

/-- **The honest squaring-chain masks**: uniform `σ ∈ K^d`, the squaring cells its powers.

Running time of the generated cells: `d(d−1)/2` squarings. This running time is argued here, not
proved in Lean. -/
def MaskScheme.squaringChainHonest [Fintype F] [ExpChar F 2] (C : SquaringChainCells ι d) :
    (MaskScheme.squaringChain (F := F) C).Honest where
  Pads := Fin d → F
  sigmaOf σ := σ
  uniform := IdentDistrib.refl _
  Commits σ x := (∀ k, x (C.sigma k) = σ k) ∧ ∀ c : SquaringCell d,
    x (C.chain c) = σ c.k ^ 2 ^ ((c.j : ℕ) + 1)
  sigma_eval _ _ h k := by simp only [MaskScheme.squaringChain, AffineForm.eval_var, h.1 k]
  products σ x h := by
    intro q
    obtain ⟨k, j, hjk⟩ := q
    show x (C.prev ⟨k, ⟨j, hjk⟩⟩) * x (C.prev ⟨k, ⟨j, hjk⟩⟩) = x (C.chain ⟨k, ⟨j, hjk⟩⟩)
    rw [h.2 ⟨k, ⟨j, hjk⟩⟩]
    cases j with
    | zero =>
      simp only [SquaringChainCells.prev, ↓reduceDIte, h.1 k]
      ring
    | succ j =>
      simp only [SquaringChainCells.prev, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel,
        h.2 ⟨k, ⟨j, by omega⟩⟩]
      ring
  valid _ _ _ := trivial

/-! ### Squaring-chain masks over `GF(2^b)` -/

/-- **A cell of a squaring chain over `GF(2^b)`** (`stage.h`, `chain_cell(k, j)`): `s_{k, j + 1}`,
`j < b k`, the `2^(j+1)`-th power of `σ_k`. The twist `φ^k(σ_k) = σ_k^(2^(b k))` is the last
cell of chain `k`. -/
@[ext]
structure ChainCell (b d : ℕ) where
  /-- The measurement. -/
  k : Fin d
  /-- The step, one less than the C++ `j`. -/
  j : Fin (b * k)

/-- The chain cells as a sigma type. -/
def ChainCell.equivSigma (b d : ℕ) : ChainCell b d ≃ Σ k : Fin d, Fin (b * k) where
  toFun c := ⟨c.k, c.j⟩
  invFun c := ⟨c.1, c.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (b d : ℕ) : Fintype (ChainCell b d) := Fintype.ofEquiv _ (ChainCell.equivSigma b d).symm

/-- The chain cells are encoded as the sigma type (`ChainCell.equivSigma`). -/
instance (b d : ℕ) : Encodable (ChainCell b d) := Encodable.ofEquiv _ (ChainCell.equivSigma b d)

/-- **The cells of a squaring-chain stage over `GF(2^b)`** (`tree_zk.h`, root own: `σ_k`, then the
chain cells). -/
structure ChainCells (ι : Type) (b d : ℕ) where
  /-- The mask `σ_k`. -/
  sigma : Fin d → ι
  /-- The chain cell. -/
  chain : ChainCell b d → ι

namespace ChainCells

variable {b : ℕ} (C : ChainCells ι b d)

/-- The cell a chain cell squares: `σ_k` for the first step, the previous chain cell after. -/
def prev (c : ChainCell b d) : ι :=
  if h : (c.j : ℕ) = 0 then C.sigma c.k else C.chain ⟨c.k, ⟨c.j - 1, by omega⟩⟩

/-- The cell of the twist `φ^k(σ_k) = σ_k^(2^(b k))`: `σ_0` at `k = 0`, the last chain cell of
chain `k` otherwise. -/
def twist (k : Fin d) : ι :=
  if h : b * (k : ℕ) = 0 then C.sigma k else C.chain ⟨k, ⟨b * k - 1, by omega⟩⟩

/-- The squaring triples `prev · prev = chain`. -/
def products : Ligero.Routing.ProductLayout ι (ChainCell b d) where
  source c := ![C.prev c, C.prev c, C.chain c]

omit [Fintype ι] in
/-- On cells where the squaring triples hold, chain cell `(k, j)` is `σ_k^(2^(j+1))`. -/
theorem chain_eq_pow {x : ι → F} (h : Ligero.Routing.SourceProducts C.products x)
    (c : ChainCell b d) : x (C.chain c) = x (C.sigma c.k) ^ 2 ^ ((c.j : ℕ) + 1) := by
  obtain ⟨k, j, hj⟩ := c
  induction j with
  | zero =>
    have hq := h ⟨k, ⟨0, hj⟩⟩
    simp only [products, prev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, ↓reduceDIte] at hq
    rw [← hq]
    ring
  | succ j ih =>
    have hq := h ⟨k, ⟨j + 1, hj⟩⟩
    simp only [products, prev, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Nat.add_one_ne_zero, ↓reduceDIte,
      Nat.add_sub_cancel] at hq
    rw [← hq, ih (by omega)]
    ring

omit [Fintype ι] in
/-- On cells where the squaring triples hold, the twist cell is `σ_k^(2^(b k))`. -/
theorem twist_eq_pow {x : ι → F} (h : Ligero.Routing.SourceProducts C.products x) (k : Fin d) :
    x (C.twist k) = x (C.sigma k) ^ 2 ^ (b * k) := by
  unfold twist
  split_ifs with hk
  · rw [hk, pow_zero, pow_one]
  · rw [C.chain_eq_pow h]
    congr 2
    simp only
    omega

end ChainCells

/-- **Squaring-chain masks over `B = GF(2^b)`** (`stage.h`, `φ(y) = y^(2^b)`): `σ_k` and
`φ^k(σ_k) = σ_k^(2^(b k))` are single cells in `K`, the chain's `b k` squarings relate them, and
nothing is needed outside the rows. `MaskScheme.squaringChain` is the case `b = 1` with its own
cell type. -/
def MaskScheme.squaringChainOver [ExpChar F 2] {b : ℕ} (C : ChainCells ι b d) :
    MaskScheme F ι 2 b d where
  sigma k := AffineForm.var (C.sigma k)
  twist k := AffineForm.var (C.twist k)
  Q := ChainCell b d
  products := C.products
  Valid _ := True
  twist_eval x h _ k := by
    simp only [AffineForm.eval_var, phi_def]
    exact C.twist_eq_pow h k

/-- **The honest squaring-chain masks over `B = GF(2^b)`** (`lem:bits-sound`(2),(3)): uniform
`σ ∈ K^d`, the chain cell `(k, j)` the power `σ_k^(2^(j+1))`. `MaskScheme.squaringChainHonest` is
the case `b = 1` with its own cell type.

Running time of the generated cells: `b d(d−1)/2` squarings. This running time is argued here, not
proved in Lean. -/
def MaskScheme.squaringChainOverHonest [Fintype F] [ExpChar F 2] {b : ℕ} (C : ChainCells ι b d) :
    (MaskScheme.squaringChainOver (F := F) C).Honest where
  Pads := Fin d → F
  sigmaOf σ := σ
  uniform := IdentDistrib.refl _
  Commits σ x := (∀ k, x (C.sigma k) = σ k) ∧ ∀ c : ChainCell b d,
    x (C.chain c) = σ c.k ^ 2 ^ ((c.j : ℕ) + 1)
  sigma_eval _ _ h k := by simp only [MaskScheme.squaringChainOver, AffineForm.eval_var, h.1 k]
  products σ x h := by
    intro q
    obtain ⟨k, j, hjk⟩ := q
    show x (C.prev ⟨k, ⟨j, hjk⟩⟩) * x (C.prev ⟨k, ⟨j, hjk⟩⟩) = x (C.chain ⟨k, ⟨j, hjk⟩⟩)
    rw [h.2 ⟨k, ⟨j, hjk⟩⟩]
    cases j with
    | zero =>
      simp only [ChainCells.prev, ↓reduceDIte, h.1 k]
      ring
    | succ j =>
      simp only [ChainCells.prev, Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel,
        h.2 ⟨k, ⟨j, by omega⟩⟩]
      ring
  valid _ _ _ := trivial

omit [Fintype ι] in
/-- **Every committed data at which the squaring triples hold commits the honest squaring chain
over `GF(2^b)`** (`lem:bits-sound`(2)), at the masks the data holds: the honest prover's
completeness (`MaskedReduction.Honest.measure`) holds on all such data. -/
theorem MaskScheme.squaringChainOverHonest_commits [Fintype F] [ExpChar F 2] {b : ℕ}
    (C : ChainCells ι b d) {x : ι → F} (h : Ligero.Routing.SourceProducts C.products x) :
    (MaskScheme.squaringChainOverHonest (F := F) C).Commits (fun k => x (C.sigma k)) x :=
  ⟨fun _ => rfl, C.chain_eq_pow h⟩

/-! ### Subfield masks -/

/-- **The cells of a subfield-mask stage's masks** (`tree_zk.h:246-258`, the prefix: `s_{k,i}` at
`k m + i`) with the basis `γ` of `K` over the designated subfield `S0` (`ExtensionBasis`), and
`S0 ⊆ B` (`stage.h:91-92`, "a linear stage's base contains the designated subfield"). -/
structure SubfieldMasks (F ι : Type) [Field F] (p m d r : ℕ) [ExpChar F p] where
  /-- The cell `s_{k,i}`. -/
  cell : Fin d → Fin r → ι
  /-- The basis of `K` over `S0`. -/
  γ : Fin r → F
  /-- The designated subfield. -/
  S0 : Subfield F
  /-- `S0 ⊆ B`. -/
  S0_le : S0 ≤ fixedField F p m

/-- **Subfield masks** (`stage.h:34-40`): `σ_k = Σ_i γ_i s_{k,i}` and
`φ^k(σ_k) = Σ_i φ^k(γ_i) s_{k,i}`, no product triple, and the cells in `S0` as the condition
outside the rows (the prefix-row subfield test). -/
def MaskScheme.subfieldMasks {r : ℕ} (L : SubfieldMasks F ι p m d r) : MaskScheme F ι p m d where
  sigma k := AffineForm.sumFin fun i => L.γ i • AffineForm.var (L.cell k i)
  twist k := AffineForm.sumFin fun i => phi p m k (L.γ i) • AffineForm.var (L.cell k i)
  Q := Empty
  products := ⟨Empty.elim⟩
  Valid x := ∀ k i, x (L.cell k i) ∈ L.S0
  twist_eval x _ hx k := by
    simp only [AffineForm.eval_sumFin, AffineForm.eval_smul, AffineForm.eval_var, phi_sum,
      phi_mul, phi_of_mem (L.S0_le (hx k _))]

/-! ### The stage -/

/-- **A packing stage on logical coordinates** `Y`: the stage's basis (`B < T`, `d = [T : B]`),
the parent's words holding the child's `ng` groups (`word`, `tree_zk.h`, `rg.group_at`), and the
masks. `e` is the order of `φ` on `K` (`[K : B]`), which fixes the forms' inverse Frobenius. -/
structure Stage (F ι : Type) [Field F] (p m d e ng : ℕ) [ExpChar F p] (Y : Type) where
  /-- The stage's basis. -/
  basis : StageBasis F p m d
  /-- The parent's words. -/
  word : Fin ng → Y
  /-- The masks. -/
  masks : MaskScheme F ι p m d

namespace Stage

variable (S : Stage F ι p m d e ng Y)

/-- **The logical assignment of the child**: the words' decoded coordinates
(`StageBasis.coord`) beside the assignment of `Y`. -/
def extend (y : Y → F) : Y ⊕ PackedCoord ng d → F :=
  Sum.elim y fun c => S.basis.coord (y (S.word c.group)) c.pos

/-- **The level of the child's coordinates** over a level of `Y`. -/
def level (L : Level F ι Y) : Level F ι (Y ⊕ PackedCoord ng d) where
  view x := S.extend (L.view x)
  cell i := .inl (L.cell i)
  view_cell x i := L.view_cell x i

/-- **Measurement row `k`** (`tree_zk.h:750-762`): `Σ_g a_{k,g} W_g + σ_k − M_k`, the cells of the
mask renamed to `Y`. -/
def measureRow (cell : ι → Y) (c : AffineForm F (Y ⊕ PackedCoord ng d)) (M : Fin d → F)
    (k : Fin d) : AffineForm F Y :=
  AffineForm.sumFin (fun g => S.basis.form e (childCoeff c g) k • AffineForm.var (S.word g)) +
    (S.masks.sigma k).rename cell - AffineForm.ofConst (M k)

/-- **The remainder row** (`tree_zk.h:735-742`): `rest − Σ_k φ^k(σ_k) + Σ_k φ^k(M_k)`. -/
def remainderRow (cell : ι → Y) (c : AffineForm F (Y ⊕ PackedCoord ng d)) (M : Fin d → F) :
    AffineForm F Y :=
  restPart c - AffineForm.sumFin (fun k => (S.masks.twist k).rename cell) +
    AffineForm.ofConst (∑ k : Fin d, phi p m k (M k))

/-- **The stage's rows**, in the C++ order: the remainder first, then the `d` measurement rows
(`tree_zk.h:745-764`). -/
def rows (cell : ι → Y) (c : AffineForm F (Y ⊕ PackedCoord ng d)) (M : Fin d → F) :
    Fin (d + 1) → AffineForm F Y :=
  Fin.cases (S.remainderRow cell c M) (S.measureRow cell c M)

/-- **The masked measurement** of a claim on the words `W` with masks `σ`:
`M_k = Σ_g a_{k,g} W_g + σ_k` (`tree_zk.h:719-731`). -/
def measurement (c : AffineForm F (Y ⊕ PackedCoord ng d)) (W : Fin ng → F) (σ : Fin d → F)
    (k : Fin d) : F :=
  ∑ g, S.basis.form e (childCoeff c g) k * W g + σ k

omit [Fintype ι] in
/-- A form on the cells renamed to a level's coordinates reads the cells at the level's
assignment. -/
theorem _root_.GordieHowe.Level.eval_rename_cell (L : Level F ι Y) (a : AffineForm F ι) (x : ι → F) :
    (a.rename L.cell).eval (L.view x) = a.eval x := by
  rw [AffineForm.eval_rename]
  congr 1
  funext i
  exact L.view_cell x i

omit [Fintype ι] in
/-- **The measurement rows' values**: the measurement row `k` at the level's assignment is the
forms on the words plus the mask minus the measurement. -/
theorem eval_measureRow (L : Level F ι Y) (c : AffineForm F (Y ⊕ PackedCoord ng d))
    (M : Fin d → F) (x : ι → F) (k : Fin d) :
    (S.measureRow L.cell c M k).eval (L.view x) =
      ∑ g, S.basis.form e (childCoeff c g) k * L.view x (S.word g) +
        (S.masks.sigma k).eval x - M k := by
  simp only [measureRow, AffineForm.eval_sub, AffineForm.eval_add, AffineForm.eval_sumFin,
    AffineForm.eval_smul, AffineForm.eval_var, AffineForm.eval_ofConst, L.eval_rename_cell]

omit [Fintype ι] in
/-- **The remainder row's value** at the level's assignment. -/
theorem eval_remainderRow (L : Level F ι Y) (c : AffineForm F (Y ⊕ PackedCoord ng d))
    (M : Fin d → F) (x : ι → F) :
    (S.remainderRow L.cell c M).eval (L.view x) =
      (restPart c).eval (L.view x) - ∑ k, (S.masks.twist k).eval x +
        ∑ k : Fin d, phi p m k (M k) := by
  simp only [remainderRow, AffineForm.eval_sub, AffineForm.eval_add, AffineForm.eval_sumFin,
    AffineForm.eval_ofConst, L.eval_rename_cell]

variable [RelFrobeniusOrder F p m e]

omit [Fintype ι] in
/-- **A claim on the child at the level's assignment** through the stage's forms:
`rest + Σ_k φ^k(Σ_g a_{k,g} W_g)` (`eval_split`, `StageBasis.linear_identity`). -/
theorem eval_level (L : Level F ι Y) (c : AffineForm F (Y ⊕ PackedCoord ng d)) (x : ι → F) :
    c.eval ((S.level L).view x) = (restPart c).eval (L.view x) +
      ∑ k : Fin d, phi p m k (∑ g, S.basis.form e (childCoeff c g) k * L.view x (S.word g)) := by
  rw [S.basis.linear_identity (childCoeff c) fun g => L.view x (S.word g)]
  exact eval_split c _

omit [Fintype ι] in
/-- **The stage's soundness, exact**: if the stage's rows hold on the logical assignment of `Y`,
the masks' products and `Valid` hold on the cells, the claim holds on the child's logical
assignment. -/
theorem claim_of_rows (L : Level F ι Y) (c : AffineForm F (Y ⊕ PackedCoord ng d)) (M : Fin d → F)
    {x : ι → F} (hprod : Ligero.Routing.SourceProducts S.masks.products x)
    (hvalid : S.masks.Valid x) (hrows : ∀ i, (S.rows L.cell c M i).eval (L.view x) = 0) :
    c.eval ((S.level L).view x) = 0 := by
  have h0 := hrows 0
  simp only [rows, Fin.cases_zero, eval_remainderRow] at h0
  have hk : ∀ k, ∑ g, S.basis.form e (childCoeff c g) k * L.view x (S.word g) =
      M k - (S.masks.sigma k).eval x := fun k => by
    have h := hrows k.succ
    simp only [rows, Fin.cases_succ, eval_measureRow] at h
    linear_combination h
  rw [eval_level]
  simp only [hk, RelativePacking.phi_sub, ← S.masks.twist_eval x hprod hvalid,
    Finset.sum_sub_distrib]
  linear_combination h0

omit [Fintype ι] in
/-- **The stage's completeness**: on a claim that holds and the honest measurement with the mask
values, the stage's rows hold. -/
theorem rows_of_claim (L : Level F ι Y) (c : AffineForm F (Y ⊕ PackedCoord ng d)) {x : ι → F}
    (hprod : Ligero.Routing.SourceProducts S.masks.products x) (hvalid : S.masks.Valid x)
    (hc : c.eval ((S.level L).view x) = 0) (i : Fin (d + 1)) :
    (S.rows L.cell c (S.measurement c (fun g => L.view x (S.word g))
      fun k => (S.masks.sigma k).eval x) i).eval (L.view x) = 0 := by
  refine Fin.cases ?_ (fun k => ?_) i
  · rw [eval_level] at hc
    simp only [rows, Fin.cases_zero, eval_remainderRow, measurement, phi_add,
      S.masks.twist_eval x hprod hvalid, Finset.sum_add_distrib]
    linear_combination hc
  · simp only [rows, Fin.cases_succ, eval_measureRow, measurement]
    ring

end Stage

end GordieHowe

/-! ### The stage as a masked reduction -/

namespace GordieHowe.FieldProof.MaskedReduction

open IOP IOP.ProtocolSpec PackingStage RelativePacking 
open GKR.Schedule (one oneValue)
open scoped NNReal

variable {F ι : Type} [Field F] [Fintype ι] {p m d e ng : ℕ} [ExpChar F p] {Y : Type}

variable {Pub Wit : Type} {cells : Wit → ι → F}

/-- **The measurement of a stage** after a masked reduction with one claim on the child's level: the
prover sends `M ∈ K^d`; the claim is replaced by the stage's `d + 1` rows on `Y`, and the masks'
product triples join the rows on the cells. -/
def measure [Fintype F] [DecidableEq F] (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) : MaskedReduction F ι Pub Wit cells Y (d + 1) where
  n := M.n + 1
  spec := M.spec ++ one .P_to_V (Fin d → F)
  Lin := M.Lin
  linear p tr := M.linear p tr.left
  Q := M.Q ⊕ S.masks.Q
  products := M.products.sum S.masks.products
  claims p tr := S.rows L.cell (M.claims p tr.left 0) (oneValue tr.right)

/-- **The measurement's errors**: none at its rounds (a prover message only). -/
def measureError [Fintype F] [DecidableEq F]
    (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    (M.measure S L).spec.ChallengeIdx → ℝ≥0 :=
  appendError ε fun _ => 0

theorem sum_measureError [Fintype F] [DecidableEq F]
    (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    ∑ i, M.measureError S L ε i = ∑ i, ε i := by
  refine (sum_appendError (P₁ := M.spec) (P₂ := one .P_to_V (Fin d → F)) ε _).trans ?_
  simp

variable [RelFrobeniusOrder F p m e]

/-- **Soundness of a stage's measurement**: exact, so the errors are the masked reduction's; the relation
becomes "the masks' condition `Valid` on the cells implies the relation" (`ClaimReduction.imp`,
then a round with no challenge, whose output gives the claim by `Stage.claim_of_rows`). -/
noncomputable def Sound.measure [Fintype F] [DecidableEq F]
    {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1}
    {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {sat : Pub → Wit → Prop}
    {ε : M.spec.ChallengeIdx → ℝ≥0} (H : M.Sound (S.level L).view sat ε) :
    (M.measure S L).Sound L.view (fun p w => S.masks.Valid (cells w) → sat p w)
      (M.measureError S L ε) :=
  let R₂ : ClaimReduction (one .P_to_V (Fin d → F))
      (AppendContext (MaskedRowReduction.Instance Pub Wit) M.spec) (fun _ => 0) :=
    ChallengeEventReduction.reduction (one .P_to_V (Fin d → F)) (fun _ _ _ _ => False)
      (fun c => S.masks.Valid (cells c.ctx.wit) →
        M.OutHolds (S.level L).view c.ctx.pub c.transcript (cells c.ctx.wit))
      (fun c tr => RowsHold (M.linear c.ctx.pub c.transcript) (M.products.sum S.masks.products)
          (cells c.ctx.wit) ∧
        ∀ i, (S.rows L.cell (M.claims c.ctx.pub c.transcript 0) (oneValue tr) i).eval
          (L.view (cells c.ctx.wit)) = 0)
      (fun _ => 0)
      (fun _ _ _ => by simp)
      (fun c tr h => by
        refine Or.inl fun hv => ?_
        have hp := (Ligero.Routing.sourceProducts_sum _ _ _).mp h.1.products
        refine ⟨⟨h.1.linear, hp.1⟩, fun i => ?_⟩
        rw [Subsingleton.elim i 0]
        exact Stage.claim_of_rows S L _ _ hp.2 hv h.2)
  { reduction := (H.reduction.imp fun c => S.masks.Valid (cells c.wit)).seq R₂
      fun c tr h hv => (H.claimOut_iff c.pub c.wit tr).mpr (h hv)
    claim_iff := fun p w => imp_congr_right fun _ => H.claim_iff p w
    claimOut_iff := fun _ _ _ => by
      constructor
      · intro h
        exact ⟨h.1, h.2⟩
      · intro h
        exact ⟨h.rows, h.claims⟩ }

/-- **The simulator of a stage's measurement**: the masked reduction's simulator, then a uniform
measurement.

Running time: the masked reduction's simulator's and a copy of `d` field elements.
This running time is argued here, not proved in Lean. -/
def Sim.measure [Fintype F] [DecidableEq F]
    {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1}
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (SM : M.Sim) : (M.measure S L).Sim where
  SimCoins := SM.SimCoins × (Fin d → F)
  sim p ch s := Transcript.join (SM.sim p ch.left s.1)
    ((CausalTranscript.oneMessage (Msg := Fin d → F) s.2).transcript ch.right)

/-- **The honest prover of a stage's measurement**: the masked reduction's prover, then the masked
measurement of the claim on the words (`wordOf`, the words' values, which `hword` ties to the
committed cells) with the stage's fresh masks. It is simulated by `Sim.measure`, which sends uniform
measurements: at fixed challenges and pads before, the measurement is its value plus a uniform mask
(`MaskScheme.Honest.uniform`). -/
def Honest.measure [Fintype F] [DecidableEq F]
    {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) 1}
    {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {In : Type} {dom : Pub → In → Prop}
    {SM : M.Sim} (H : M.Honest (S.level L).view In dom SM) (MH : S.masks.Honest)
    (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g) :
    (M.measure S L).Honest L.view In dom (Sim.measure S L SM) where
  Pads := H.Pads × MH.Pads
  prover p x π := (H.prover p x π.1).append fun tr =>
    CausalTranscript.oneMessage (S.measurement (M.claims p tr 0) (wordOf p x π.1) (MH.sigmaOf π.2))
  Commits p x π w := H.Commits p x π.1 w ∧ MH.Commits π.2 (cells w)
  complete p x hx π w hw ch := by
    have e₁ := CausalTranscript.append_left (H.prover p x π.1) (fun tr =>
      CausalTranscript.oneMessage (S.measurement (M.claims p tr 0) (wordOf p x π.1)
        (MH.sigmaOf π.2))) ch
    have e₂ := CausalTranscript.append_right (H.prover p x π.1) (fun tr =>
      CausalTranscript.oneMessage (S.measurement (M.claims p tr 0) (wordOf p x π.1)
        (MH.sigmaOf π.2))) ch
    have h := (congrArg (fun tr => M.OutHolds (S.level L).view p tr (cells w)) e₁).mpr
      (H.complete p x hx π.1 w hw.1 ch.left)
    have hW : wordOf p x π.1 = fun g => L.view (cells w) (S.word g) :=
      funext fun g => (hword p x π.1 w hw.1 g).symm
    have hσ : MH.sigmaOf π.2 = fun k => (S.masks.sigma k).eval (cells w) :=
      funext fun k => (MH.sigma_eval π.2 _ hw.2 k).symm
    have hv := congrArg oneValue e₂
    refine ⟨⟨h.rows.linear, (Ligero.Routing.sourceProducts_sum _ _ _).mpr
      ⟨h.rows.products, MH.products _ _ hw.2⟩⟩, fun i => ?_⟩
    have key : ∀ i, (S.rows L.cell (M.claims p ((H.prover p x π.1).transcript ch.left) 0)
        (S.measurement (M.claims p ((H.prover p x π.1).transcript ch.left) 0) (wordOf p x π.1)
          (MH.sigmaOf π.2)) i).eval (L.view (cells w)) = 0 := by
      rw [hW, hσ]
      exact Stage.rows_of_claim S L _ (MH.products _ _ hw.2) (MH.valid _ _ hw.2)
        ((H.complete p x hx π.1 w hw.1 ch.left).claims 0)
    convert key i using 1
    exact congrArg₂ (fun a b => (S.rows L.cell (M.claims p a 0) b i).eval (L.view (cells w))) e₁ hv
  identDistrib p x ch := by
    refine (IdentDistrib.dependent (f₁ := fun π₁ => (H.prover p x π₁).transcript ch.left)
      (g₁ := SM.sim p ch.left)
      (f₂ := fun π₁ π₂ => (CausalTranscript.oneMessage (S.measurement
        (M.claims p ((H.prover p x π₁).transcript ch.left) 0) (wordOf p x π₁)
        (MH.sigmaOf π₂))).transcript ch.right)
      (g₂ := fun _ s => (CausalTranscript.oneMessage (Msg := Fin d → F) s).transcript ch.right)
      (H.identDistrib p x ch.left) fun π₁ => ?_).comp fun v => Transcript.join v.1 v.2
    let z : Fin d → F := fun k => ∑ g, S.basis.form e
      (childCoeff (M.claims p ((H.prover p x π₁).transcript ch.left) 0) g) k * wordOf p x π₁ g
    have hu : (fun π₂ => z + MH.sigmaOf π₂) =ᵈ (id : (Fin d → F) → Fin d → F) :=
      (MH.uniform.comp fun v => z + v).trans (Uniform.of_equiv (Equiv.addLeft z))
    exact hu.comp fun s => (CausalTranscript.oneMessage (Msg := Fin d → F) s).transcript ch.right

/-! ### One stage: combination, then measurement -/

variable [Fintype F] [DecidableEq F] {nc : ℕ}

/-- **One packing stage** on `nc` claims (`TreeRows::stage`): combination with one fresh
coefficient per claim (`MaskedReduction.combine`), then the measurement. The C++ skips the combination
when exactly one row touches the region (`tree_zk.h:568-569`); `MaskedReduction.measure` alone is that case. -/
def stage (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc) (S : Stage F ι p m d e ng Y)
    (L : Level F ι Y) : MaskedReduction F ι Pub Wit cells Y (d + 1) :=
  M.combine.measure S L

/-- **The stage's errors**: the masked reduction's, `1/|K|` at the combination, none at the
measurement. -/
noncomputable def stageError (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    (M.stage S L).spec.ChallengeIdx → ℝ≥0 :=
  M.combine.measureError S L (M.combineError ε)

omit [RelFrobeniusOrder F p m e] in
/-- **A stage adds `1/|K|`** to the errors of the masked reduction before it. -/
theorem sum_stageError (M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc)
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (ε : M.spec.ChallengeIdx → ℝ≥0) :
    ∑ i, M.stageError S L ε i = ∑ i, ε i + 1 / Fintype.card F := by
  exact (sum_measureError M.combine S L _).trans (sum_combineError M ε)

/-- **Soundness of one packing stage**: the claims hold on the child's level, or the combination
event occurred (`1/|K|`), given the masks' condition (`Sound.combine`, `Sound.measure`). -/
noncomputable def Sound.stage {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {sat : Pub → Wit → Prop}
    {ε : M.spec.ChallengeIdx → ℝ≥0} (H : M.Sound (S.level L).view sat ε) :
    (M.stage S L).Sound L.view (fun p w => S.masks.Valid (cells w) → sat p w)
      (M.stageError S L ε) :=
  H.combine.measure

/-- **The simulator of one packing stage**: the combination's, then the measurement's.

Running time: the masked reduction's simulator's, a copy of the challenge and of `d` field
elements. This running time is argued here, not proved in Lean. -/
def Sim.stage {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    (S : Stage F ι p m d e ng Y) (L : Level F ι Y) (SM : M.Sim) : (M.stage S L).Sim :=
  Sim.measure S L SM.combine

/-- **The honest prover of one packing stage**: the combination's, then the measurement's,
simulated by `Sim.stage`. -/
def Honest.stage {M : MaskedReduction F ι Pub Wit cells (Y ⊕ PackedCoord ng d) nc}
    {S : Stage F ι p m d e ng Y} {L : Level F ι Y} {In : Type} {dom : Pub → In → Prop}
    {SM : M.Sim} (H : M.Honest (S.level L).view In dom SM) (MH : S.masks.Honest)
    (wordOf : Pub → In → H.Pads → Fin ng → F)
    (hword : ∀ p x π w, H.Commits p x π w → ∀ g, L.view (cells w) (S.word g) = wordOf p x π g) :
    (M.stage S L).Honest L.view In dom (Sim.stage S L SM) :=
  H.combine.measure MH wordOf hword

end GordieHowe.FieldProof.MaskedReduction
