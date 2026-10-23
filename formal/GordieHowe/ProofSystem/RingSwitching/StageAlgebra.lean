-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Foundations.Algebra.RelativePacking
public import GordieHowe.ProofSystem.RingSwitching.PackedClaim

@[expose] public section

/-!
# One packing stage `B < T` inside a field `K`

GordieHowe packs a domain's values along a tree of subfields of the domain's field `K`
(`lib/gordiehowe/compiler/tree.h`). Each edge is one packing stage `B < T` (`lib/gordiehowe/compiler/stage.h`,
`PackingStage`): a `T`-value `p` holds `d = [T : B]` coordinates over `B` in a basis `β` of `T/B`,
`p = Σ_j β_j x_j`, decoded as `x_j = Tr_{T/B}(β*_j · p)` with the trace-dual basis `β*` and
`Tr_{T/B} y = Σ_{k<d} φ^k(y)`, where `φ(y) = y^|B|` is the Frobenius of `K` relative to `B`
(`RelativePacking.phi p m`, `|B| = p^m`).

`StageBasis K p m d` is the stage's data: the top field `T` as a subfield of `K`, fixed by `φ^d`
(`top_fixed`), containing `B` (`base_le`, with `B` the fixed field of `φ`), and a relative basis of
`T/B` with its trace-dual basis lying in `T` (it extends `RelativePacking.RelativeBasis`). The
facts are `field` facts, certified once for the concrete field. It covers both masking modes of the
C++:

* **squaring-chain masks** (`B = GF(2)`, `p = 2`, `m = 1`, `φ` the squaring):
  `PackedClaim.PackedBasis` (`PackedBasis.toStageBasis`, whose decode is `PackedClaim.decode`,
  `coord_toStageBasis`);
* **subfield masks**: any `B ⊇ S0`; for `T = K` this is `RelativePacking.RelativeBasis`
  (`RelativeBasis.toStageBasis`), the root stage of `lib/zk/zk_extension_packed.h`.

A claim `Σ_{g,j} c_{g,j} x_{g,j}` with coefficients in `K` on the coordinates of words `W_g` is
evaluated through `d` linear forms on the words, `a_{k,g} = φ^{-k}(Σ_j φ^k(β*_j) c_{g,j})`
(`form`; `φ^{-k}` is the inverse of `φ^k` on `K`, `phiInv`, which needs `φ^e = id` on `K`):
`Σ_k φ^k(Σ_g a_{k,g} W_g) = Σ_{g,j} c_{g,j} · coord W_g j` (`linear_identity`), for every vector
of words (no subfield hypothesis). Decoded coordinates of a word in `T` lie in `B`
(`coord_mem_fixedField`); over `B = GF(2)` they are bits (`coord_bool`).

Source: `lib/gordiehowe/compiler/stage.h` at `a9d05d59`'s C++ (header lines 1-31; `add_forms`, lines
119-145: `a[k][g] = phi_inv(Σ_j twisted_dual[k][j] · c[g d + j], k)` with
`twisted_dual[k][j] = phi(dual[j], k)`; `phi_inv(x, k) = frobenius_power(x, n - (b k) mod n)`,
lines 106-109, our `phiInv e k` with `e = n / b`; `coordinates`, lines 251-263:
`x_j = Σ_k twisted_dual[k][j] · phi^k(p)`, our `coord`; `pack`, lines 244-248).
-/

namespace GordieHowe.PackingStage

open RelativePacking
open scoped BigOperators

variable {K : Type*} [Field K] {p m d e : ℕ} [ExpChar K p]

/-! ### The inverse Frobenius power on `K` -/

/-- `φ^{-k}` on `K`: `φ^(e - k mod e)`, the inverse of `φ^k` when `φ^e` is the identity on `K`
(`phi_phiInv`). The C++ `phi_inv` (`stage.h:106-109`) with `e = [K : B]`. -/
def phiInv (p m e k : ℕ) [ExpChar K p] (x : K) : K := phi p m (e - k % e) x

variable [RelFrobeniusOrder K p m e]

/-- `φ^k` undoes `φ^{-k}`. -/
theorem phi_phiInv (k : ℕ) (x : K) : phi p m k (phiInv p m e k x) = x := by
  have he : 0 < e := RelFrobeniusOrder.pos (K := K) (p := p) (m := m)
  have hmod := Nat.mod_add_div k e
  have hlt := Nat.mod_lt k he
  have hk : k + (e - k % e) = e * (k / e + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [phiInv, phi_phi, hk, phi_mul_order e]

/-- `φ^{-k}` undoes `φ^k`. -/
theorem phiInv_phi (k : ℕ) (x : K) : phiInv p m e k (phi p m k x) = x := by
  have he : 0 < e := RelFrobeniusOrder.pos (K := K) (p := p) (m := m)
  have hmod := Nat.mod_add_div k e
  have hlt := Nat.mod_lt k he
  have hk : e - k % e + k = e * (k / e + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [phiInv, phi_phi, hk, phi_mul_order e]

omit [RelFrobeniusOrder K p m e] in
@[simp] theorem phiInv_add (k : ℕ) (x y : K) :
    phiInv p m e k (x + y) = phiInv p m e k x + phiInv p m e k y :=
  phi_add _ x y

omit [RelFrobeniusOrder K p m e] in
@[simp] theorem phiInv_mul (k : ℕ) (x y : K) :
    phiInv p m e k (x * y) = phiInv p m e k x * phiInv p m e k y :=
  phi_mul _ x y

/-! ### The stage basis -/

omit [RelFrobeniusOrder K p m e] in
variable (K p m d) in
/-- **A packing stage `B < T` inside `K`** (`stage.h`, `PackingStage`): `B` is the fixed field of
`φ = x ↦ x^(p^m)`; the top field `T` is a subfield of `K` fixed by `φ^d` and containing `B`; `β` is
a basis of `T/B` and `dual` its trace-dual basis (`trace_dual`, from `RelativeBasis`), both in
`T`. The fields are `field` facts, certified once for the concrete field. -/
structure StageBasis extends RelativeBasis K p m d where
  /-- The top field `T`. -/
  top : Subfield K
  /-- `φ^d` fixes `T`: `[T : B]` divides `d`. -/
  top_fixed : ∀ y ∈ top, phi p m d y = y
  /-- `B ≤ T`. -/
  base_le : fixedField K p m ≤ top
  /-- The basis lies in `T`. -/
  β_mem : ∀ j, β j ∈ top
  /-- The dual basis lies in `T`. -/
  dual_mem : ∀ j, dual j ∈ top

namespace StageBasis

omit [RelFrobeniusOrder K p m e]

variable (S : StageBasis K p m d)

/-- **Decoding coordinate `j` of a word** `W`: `Tr_{T/B}(β*_j · W)` (`stage.h:251-263`,
`coordinates`). -/
def coord (W : K) (j : Fin d) : K := RelativePacking.coord S.toRelativeBasis W j

/-- **Packing `d` coordinates into a word**: `Σ_j β_j · c_j` (`stage.h:244-248`, `pack`). -/
def pack (c : Fin d → K) : K := RelativePacking.pack S.toRelativeBasis c

/-- **Decoded coordinates of a word in `T` lie in `B`**: the trace of a `φ^d`-fixed element. -/
theorem coord_mem_fixedField {W : K} (hW : W ∈ S.top) (j : Fin d) :
    S.coord W j ∈ fixedField K p m :=
  relTrace_mem_of_fixed (S.top_fixed _ (S.top.mul_mem (S.dual_mem j) hW))

/-- Decoding a packed word returns its coordinates, when they lie in `B`. -/
theorem coord_pack {c : Fin d → K} (hc : ∀ j, c j ∈ fixedField K p m) (j : Fin d) :
    S.coord (S.pack c) j = c j :=
  RelativePacking.coord_pack S.toRelativeBasis hc j

/-- A packed word with coordinates in `B` lies in `T`. -/
theorem pack_mem {c : Fin d → K} (hc : ∀ j, c j ∈ fixedField K p m) : S.pack c ∈ S.top :=
  S.top.sum_mem (t := Finset.univ) fun j _ => S.top.mul_mem (S.β_mem j) (S.base_le (hc j))

/-- **The `k`-th form** of the coordinate coefficients `coeff` of one word:
`φ^{-k}(Σ_j φ^k(β*_j) · coeff_j)` (`stage.h:119-145`, `add_forms`). -/
def form (e : ℕ) (coeff : Fin d → K) (k : Fin d) : K :=
  phiInv p m e k (∑ j, phi p m k (S.dual j) * coeff j)

variable [RelFrobeniusOrder K p m e]

/-- `φ^k` undoes the outer `φ^{-k}` of the form. -/
theorem phi_form (coeff : Fin d → K) (k : Fin d) :
    phi p m k (S.form e coeff k) = ∑ j, phi p m k (S.dual j) * coeff j :=
  phi_phiInv _ _

/-- **The stage's linear identity.** For coordinate coefficients `coeff` and every vector of words
`W` (no subfield hypothesis), `Σ_k φ^k(Σ_y a_k[y] · W_y) = Σ_{y,j} coeff[y,j] · coord(W_y)_j` with
`a_k[y] = form e (coeff y) k`. -/
theorem linear_identity {ι : Type*} [Fintype ι] (coeff : ι → Fin d → K) (W : ι → K) :
    ∑ k : Fin d, phi p m k (∑ y, S.form e (coeff y) k * W y) =
      ∑ y, ∑ j, coeff y j * S.coord (W y) j := by
  simp only [phi_sum, phi_mul, phi_form, coord, RelativePacking.coord, relTrace, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

end StageBasis

/-! ### Base `GF(2)`: bits -/

omit [RelFrobeniusOrder K p m e] in
/-- **The fixed field of the squaring is `{0, 1}`**: over `B = GF(2)` the decoded coordinates of a
word in `T` are bits. -/
theorem eq_zero_or_one_of_mem_fixedField [ExpChar K 2] {x : K} (hx : x ∈ fixedField K 2 1) :
    x = 0 ∨ x = 1 := by
  rw [mem_fixedField_iff_pow, pow_one] at hx
  have h : x * (x - 1) = 0 := by rw [mul_sub, mul_one, ← sq, hx, sub_self]
  rcases mul_eq_zero.mp h with h | h
  · exact .inl h
  · exact .inr (sub_eq_zero.mp h)

omit [RelFrobeniusOrder K p m e] in
/-- **Coordinates over `GF(2)` are bits**: a word in `T` decodes to `0`s and `1`s. -/
theorem StageBasis.coord_bool [ExpChar K 2] (S : StageBasis K 2 1 d) {W : K} (hW : W ∈ S.top)
    (j : Fin d) : S.coord W j = 0 ∨ S.coord W j = 1 :=
  eq_zero_or_one_of_mem_fixedField (S.coord_mem_fixedField hW j)

/-! ### The bridges from `RelativePacking` and `PackedClaim` -/

omit [RelFrobeniusOrder K p m e] in
/-- **A relative basis is a root stage** `S0 < K` (`T = K`): `φ^D = id` on `K`
(`RelFrobeniusOrder K p m D`, a `field` fact) fixes `T`. -/
def _root_.GordieHowe.RelativePacking.RelativeBasis.toStageBasis {D : ℕ} [RelFrobeniusOrder K p m D]
    (B : RelativeBasis K p m D) : StageBasis K p m D where
  toRelativeBasis := B
  top := ⊤
  top_fixed y _ := phi_order y
  base_le := le_top
  β_mem _ := Subfield.mem_top _
  dual_mem _ := Subfield.mem_top _

omit [RelFrobeniusOrder K p m e] in
/-- The relative trace for the squaring over `2^a` terms is the packed trace
`PackedClaim.trace a`. -/
theorem relTrace_two_one_eq_trace [ExpChar K 2] (a : ℕ) (x : K) :
    relTrace 2 1 (2 ^ a) x = PackedClaim.trace a x := by
  simp only [relTrace, phi_def, one_mul, PackedClaim.trace]

omit [RelFrobeniusOrder K p m e] in
/-- **A packed basis is a stage** `GF(2) < E` (`p = 2`, `m = 1`, `d = 2^a`): the packing
subfield `E` is fixed by `x ↦ x^(2^(2^a))` (`PackedBasis.fixed`), contains `{0, 1}`, the fixed
field of the squaring, and the trace-dual condition is `PackedBasis.dual`. -/
def _root_.GordieHowe.PackedClaim.PackedBasis.toStageBasis [ExpChar K 2] {a : ℕ}
    (P : PackedClaim.PackedBasis K a) : StageBasis K 2 1 (2 ^ a) where
  β := P.β
  dual := P.βdual
  trace_dual i j := by rw [relTrace_two_one_eq_trace]; exact P.dual i j
  top := P.E
  top_fixed y hy := by rw [phi_def, one_mul]; exact P.fixed y hy
  base_le x hx := by
    rcases eq_zero_or_one_of_mem_fixedField hx with h | h
    · rw [h]; exact P.E.zero_mem
    · rw [h]; exact P.E.one_mem
  β_mem := P.β_mem
  dual_mem := P.βdual_mem

omit [RelFrobeniusOrder K p m e] in
/-- The stage of a packed basis decodes as `PackedClaim.decode`. -/
theorem coord_toStageBasis [ExpChar K 2] {a : ℕ} (P : PackedClaim.PackedBasis K a) (W : K)
    (i : Fin (2 ^ a)) : P.toStageBasis.coord W i = PackedClaim.decode P W i :=
  relTrace_two_one_eq_trace a _

end GordieHowe.PackingStage
