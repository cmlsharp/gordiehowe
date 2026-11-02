-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.Quantum.Interactive.SplitRestrict
public import GordieHowe.Model.Quantum.Interactive.ReqBridgeLogs

@[expose] public section

/-!
# Additions to a register, and Kraus maps that differ by a permutation after them

A register `Z` with a part `V` read and written through a lens (`RegLens`), and an addition
`v ↦ v + f z` to that part by a function `f` that does not read it (`RegAdd.perm`). A
permutation that neither reads nor writes the part, and keeps `f`, commutes with the addition
(`RegAdd.perm_comm`).

Two Kraus maps `K'` and `K` whose operators differ by a basis permutation `π` applied after them
(`KrausMap.LeftPerm π K' K`: `K'.op r (π a) b = K.op r a b`): `K' ρ` is `K ρ` relabelled by `π`
(`KrausMap.LeftPerm.apply`); the relation passes through reindexing, the identity on a second
factor, compositions on the right, permutations on the left (which conjugate `π`) and
projections that `π` keeps.

- `RegLens`, `RegLens.prod`, `RegLens.transport`, `RegLens.Indep`, `RegLens.self`, `RegLens.comp`,
  `RegLens.conj` (`conj_get`, `conj_set`, `indep_conj_iff`, `Indep.conj`), `fstLens`,
  `coordLens`; `RegAdd` (a part and the value added),
  `RegAdd.perm`, `RegAdd.perm_eq_refl`, `RegAdd.prod`, `RegAdd.perm_prod`, `RegAdd.transport`,
  `RegAdd.perm_transport`, `RegAdd.perm_comm`, `RegAdd.permCongr_perm`.
- `KrausMap.LeftPerm`, `KrausMap.LeftPerm.apply`, `.reindex`, `.tensorId`, `.comp_right`,
  `.ofPerm_comp`, `.restrict`, `.permConj_left`, `.trans`.

Permutations applied in sequence (`seqPerm`, `seqPerm_permCongr`), and the lists of additions
after each step (`StepAdds`, `StepAdds.perm`, `StepAdds.Keeps`, `StepAdds.Off`, `StepAdds.AllOn`,
`StepAdds.perm_comm`; conjugated by a permutation, `StepAdds.conj`, `StepAdds.add_conj`,
`StepAdds.perm_conj`), with a
part's independence (`RegLens.Indep`) and the additions on the coordinates of a tuple
(`RegAdd.coord`, `RegAdd.seqPerm_coord`). `KrausMap.LeftPerm.trans` composes permutations after
Kraus maps.

A permutation `π` of the adversary's registers that keeps the kind and the request register,
lifted to the adversary absorbed with a table (`AdaptiveIAlg.tabPerm`) and to its trace-preserving
form (`AdaptiveIAlg.tpPermOf`, `AdaptiveIAlg.cntPerm`): the permutations of the absorption
(`setAt`) and of the trace-preserving form (`tpShift`, `endSwap`, the budget test) commute with it,
so a step of `B.withStep st'` that is `B`'s step followed by `π` gives steps of the absorbed
adversary's trace-preserving form followed by the lifted permutation
(`AdaptiveIAlg.leftPerm_stepTab`, `AdaptiveIAlg.leftPerm_toTPKindAlg`,
`AdaptiveIAlg.leftPerm_absorbTab_toTP`). An addition's lifts (`AdaptiveIAlg.absAdd`,
`AdaptiveIAlg.tabAdd`, `AdaptiveIAlg.tpAdd`, `AdaptiveIAlg.cntAdd`) are its instances.

The local query of the restricted adversary (`basePerm`,
`GordieHowe/Model/Quantum/Interactive/SplitRestrict.lean`) is such an addition (`wsAdd`, `ysAdd`,
`basePerm_eq_ysAdd`, `basePerm_zero`), and the restricted adversary's step at the base part `ω`
is its step at the zero base part followed by it (`leftPerm_restrictAt_step`). As a list of
additions, one per query pair, it is `wsAdds` (`wsAdds_perm`).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace GordieHowe.Quantum

/-! ### A part of a register and additions to it -/

/-- **A part `V` of a register `Z`**, read by `get` and written by `set`, with the laws of a lens:
reading what was written, writing what was read, and the last write winning. -/
structure RegLens (Z V : Type*) where
  /-- The part of a basis state. -/
  get : Z → V
  /-- The basis state with its part replaced. -/
  set : Z → V → Z
  get_set : ∀ z v, get (set z v) = v
  set_get : ∀ z, set z (get z) = z
  set_set : ∀ z v v', set (set z v) v' = set z v'

namespace RegLens

attribute [simp] get_set set_get set_set

variable {Z Z' V : Type*} (L : RegLens Z V)

/-- **The part of the first factor**, on a product. -/
def prod (T : Type*) : RegLens (Z × T) V where
  get z := L.get z.1
  set z v := (L.set z.1 v, z.2)
  get_set z v := by simp
  set_get z := by simp
  set_set z v v' := by simp

/-- **The part read through an equivalence** `g : Z' ≃ Z`. -/
def transport (g : Z' ≃ Z) : RegLens Z' V where
  get z := L.get (g z)
  set z v := g.symm (L.set (g z) v)
  get_set z v := by simp
  set_get z := by simp
  set_set z v v' := by simp


variable (Z) in
/-- **The whole register**, as a part. -/
def self : RegLens Z Z where
  get z := z
  set _ v := v
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- **`g` does not read the part `L`**: writing the part leaves `g` unchanged. -/
def Indep {α : Type*} (g : Z → α) : Prop :=
  ∀ z v, g (L.set z v) = g z

/-- **The part conjugated by a permutation `C`**: read through `C⁻¹`, written back through `C`
(`transport` along `C⁻¹`). -/
def conj (C : Equiv.Perm Z) : RegLens Z V :=
  L.transport C.symm

theorem conj_get (C : Equiv.Perm Z) (z : Z) : (L.conj C).get z = L.get (C.symm z) :=
  rfl

theorem conj_set (C : Equiv.Perm Z) (z : Z) (v : V) :
    (L.conj C).set z v = C (L.set (C.symm z) v) :=
  rfl

/-- **The conjugated part's independence** is the part's independence of `g ∘ C`. -/
theorem indep_conj_iff {α : Type*} (C : Equiv.Perm Z) {g : Z → α} :
    (L.conj C).Indep g ↔ L.Indep (g ∘ C) := by
  constructor
  · intro h z v
    have := h (C z) v
    rwa [conj_set, Equiv.symm_apply_apply] at this
  · intro h z v
    have := h (C.symm z) v
    rwa [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply] at this

/-- **A function that does not read the part, read through `C⁻¹`, does not read the conjugated
part.** -/
theorem Indep.conj {L : RegLens Z V} {α : Type*} {g : Z → α} (h : L.Indep g)
    (C : Equiv.Perm Z) : (L.conj C).Indep (g ∘ C.symm) :=
  (L.indep_conj_iff C).2 fun z v => by
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    exact h z v

end RegLens

/-- **The first factor of a product**, as a part. -/
def fstLens (W V : Type*) : RegLens (W × V) W where
  get w := w.1
  set w v := (v, w.2)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- **A part of a part.** -/
def RegLens.comp {Z V U : Type*} (L : RegLens Z V) (L' : RegLens V U) : RegLens Z U where
  get z := L'.get (L.get z)
  set z u := L.set z (L'.set (L.get z) u)
  get_set _ _ := by simp [L.get_set, L'.get_set]
  set_get _ := by simp [L.set_get, L'.set_get]
  set_set _ _ _ := by simp [L.set_set, L.get_set, L'.set_set]

/-- **A coordinate of a tuple**, as a part. -/
def coordLens {n : ℕ} (V : Type*) (i : Fin n) : RegLens (Fin n → V) V where
  get v := v i
  set v y := Function.update v i y
  get_set _ _ := by simp
  set_get _ := by simp
  set_set _ _ _ := by simp


/-- **An addition to a part of a register**: a part (`RegLens`) and a function `f` of the basis
states that does not read the part (`f_set`); the permutation `perm` adds `f z` to the part of
`z`. -/
structure RegAdd (Z V : Type*) [AddGroup V] extends RegLens Z V where
  /-- The value added. -/
  f : Z → V
  f_set : ∀ z v, f (set z v) = f z

namespace RegAdd

variable {Z Z' V : Type*} [AddGroup V] (D : RegAdd Z V)

/-- **The addition**, a permutation of the register. -/
def perm : Equiv.Perm Z where
  toFun z := D.set z (D.get z + D.f z)
  invFun z := D.set z (D.get z - D.f z)
  left_inv z := by simp [D.f_set]
  right_inv z := by simp [D.f_set]

theorem perm_apply (z : Z) : D.perm z = D.set z (D.get z + D.f z) :=
  rfl

theorem perm_symm_apply (z : Z) : D.perm.symm z = D.set z (D.get z - D.f z) :=
  rfl

/-- **Adding zero is the identity.** -/
theorem perm_eq_refl (h : ∀ z, D.f z = 0) : D.perm = Equiv.refl Z :=
  Equiv.ext fun z => by simp [perm_apply, h]

/-- **Two additions on the same part, one after the other.** -/
theorem perm_perm (D₁ D₂ : RegAdd Z V) (hL : D₁.toRegLens = D₂.toRegLens) (z : Z) :
    D₁.perm (D₂.perm z) = D₂.set z (D₂.get z + D₂.f z + D₁.f z) := by
  obtain ⟨L₁, f₁, h₁⟩ := D₁
  obtain ⟨L₂, f₂, h₂⟩ := D₂
  obtain rfl : L₁ = L₂ := hL
  simp only [perm_apply, RegLens.get_set, RegLens.set_set, h₁]

/-- **The addition on the first factor of a product.** -/
def prod (T : Type*) : RegAdd (Z × T) V where
  toRegLens := D.toRegLens.prod T
  f z := D.f z.1
  f_set z v := D.f_set z.1 v

theorem perm_prod (T : Type*) : (D.prod T).perm = D.perm.prodCongr (Equiv.refl T) :=
  Equiv.ext fun _ => rfl

/-- **The addition read through an equivalence** `g : Z' ≃ Z`. -/
def transport (g : Z' ≃ Z) : RegAdd Z' V where
  toRegLens := D.toRegLens.transport g
  f z := D.f (g z)
  f_set z v := by simp [RegLens.transport, D.f_set]

/-- The addition read through an equivalence is the conjugate of the addition. -/
theorem perm_transport (g : Z' ≃ Z) : (D.transport g).perm = g.symm.permCongr D.perm :=
  Equiv.ext fun _ => rfl

/-- **A permutation that neither reads nor writes the part and keeps `f` commutes with the
addition**: `π` keeps the part (`hget`), commutes with writing it (`hset`), and `f ∘ π = f`
(`hf`). -/
theorem perm_comm (π : Equiv.Perm Z) (hget : ∀ z, D.get (π z) = D.get z)
    (hset : ∀ z v, π (D.set z v) = D.set (π z) v) (hf : ∀ z, D.f (π z) = D.f z) (z : Z) :
    π (D.perm z) = D.perm (π z) := by
  rw [perm_apply, perm_apply, hset, hget, hf]

/-- `perm_comm` as the conjugate of the addition by `π`. -/
theorem permCongr_perm (π : Equiv.Perm Z) (hget : ∀ z, D.get (π z) = D.get z)
    (hset : ∀ z v, π (D.set z v) = D.set (π z) v) (hf : ∀ z, D.f (π z) = D.f z) :
    π.permCongr D.perm = D.perm :=
  Equiv.ext fun z => by
    change π (D.perm (π.symm z)) = D.perm z
    rw [D.perm_comm π hget hset hf, Equiv.apply_symm_apply]

end RegAdd

/-! ### Permutations in sequence and lists of additions per step -/

/-- **Permutations applied in sequence**: `f 0` first, then `f 1`, …, `f (n - 1)`. -/
def seqPerm {Z : Type*} : (n : ℕ) → (Fin n → Equiv.Perm Z) → Equiv.Perm Z
  | 0, _ => 1
  | n + 1, f => f (Fin.last n) * seqPerm n fun i => f i.castSucc

section SeqPerm

variable {Z α : Type*}

/-- Permutations that keep a function keep it in sequence. -/
theorem seqPerm_comp_eq (g : Z → α) :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm Z), (∀ i z, g (f i z) = g z) →
      ∀ z, g (seqPerm n f z) = g z
  | 0, _, _, _ => rfl
  | n + 1, f, h, z => by
    change g (f (Fin.last n) (seqPerm n (fun i => f i.castSucc) z)) = g z
    rw [h, seqPerm_comp_eq g n _ (fun i => h i.castSucc)]

/-- Identities in sequence are the identity. -/
theorem seqPerm_one : ∀ (n : ℕ) (f : Fin n → Equiv.Perm Z), (∀ i, f i = 1) → seqPerm n f = 1
  | 0, _, _ => rfl
  | n + 1, f, h => by
    change f (Fin.last n) * seqPerm n (fun i => f i.castSucc) = 1
    rw [h, seqPerm_one n _ (fun i => h i.castSucc), one_mul]

/-- **Conjugates in sequence are the conjugate of the sequence.** -/
theorem seqPerm_permCongr (e : Z ≃ Z) :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm Z),
      seqPerm n (fun i => e.permCongr (f i)) = e.permCongr (seqPerm n f)
  | 0, _ => Equiv.ext fun z => by simp [seqPerm, Equiv.permCongr_apply]
  | n + 1, f => by
    change e.permCongr (f (Fin.last n)) * seqPerm n (fun i => e.permCongr (f i.castSucc)) = _
    rw [seqPerm_permCongr e n]
    exact Equiv.ext fun z => by simp [seqPerm, Equiv.permCongr_apply, Equiv.Perm.mul_apply]

/-- A permutation that commutes with each of them commutes with them in sequence. -/
theorem seqPerm_comm (π : Equiv.Perm Z) :
    ∀ (n : ℕ) (f : Fin n → Equiv.Perm Z), (∀ i z, π (f i z) = f i (π z)) →
      ∀ z, π (seqPerm n f z) = seqPerm n f (π z)
  | 0, _, _, _ => rfl
  | n + 1, f, h, z => by
    change π (f (Fin.last n) (seqPerm n (fun i => f i.castSucc) z)) =
      f (Fin.last n) (seqPerm n (fun i => f i.castSucc) (π z))
    rw [h, seqPerm_comm π n _ (fun i => h i.castSucc)]

end SeqPerm

namespace RegAdd

variable {Z V : Type*} [AddGroup V] {n : ℕ} (D : RegAdd Z (Fin n → V))

/-- **Coordinate `i` of an addition of tuples**, as an addition. -/
def coord (i : Fin n) : RegAdd Z V where
  toRegLens := D.toRegLens.comp (coordLens V i)
  f z := D.f z i
  f_set z v := by
    change D.f (D.set z _) i = D.f z i
    rw [D.f_set]

theorem update_add_ite {m : ℕ} (hm : m < n) (g a : Fin n → V) :
    Function.update (g + fun j : Fin n => if (j : ℕ) < m then a j else 0) ⟨m, hm⟩
        ((g + fun j : Fin n => if (j : ℕ) < m then a j else 0) ⟨m, hm⟩ + a ⟨m, hm⟩) =
      g + fun j : Fin n => if (j : ℕ) < m + 1 then a j else 0 := by
  funext j
  by_cases hj : (j : ℕ) = m
  · have : j = ⟨m, hm⟩ := Fin.ext hj
    subst this
    simp
  · rw [Function.update_of_ne (fun h => hj (congrArg Fin.val h))]
    simp only [Pi.add_apply]
    by_cases hl : (j : ℕ) < m
    · rw [if_pos hl, if_pos (by omega)]
    · rw [if_neg hl, if_neg (by omega)]

/-- The first `m` coordinates in sequence add the first `m` coordinates of `f`. -/
theorem seqPerm_coord_le :
    ∀ (m : ℕ) (hm : m ≤ n) (z : Z),
      seqPerm m (fun i => (D.coord (Fin.castLE hm i)).perm) z =
        D.set z (D.get z + fun j : Fin n => if (j : ℕ) < m then D.f z j else 0)
  | 0, _, z => by
    change z = D.set z (D.get z + fun j : Fin n => if (j : ℕ) < 0 then D.f z j else 0)
    simp only [Nat.not_lt_zero, ↓reduceIte]
    change z = D.set z (D.get z + 0)
    rw [add_zero, D.set_get]
  | m + 1, hm, z => by
    change (D.coord (Fin.castLE hm (Fin.last m))).perm
      (seqPerm m (fun i => (D.coord (Fin.castLE hm i.castSucc)).perm) z) = _
    have ih := seqPerm_coord_le m (Nat.le_of_succ_le hm) z
    have e : (fun i : Fin m => (D.coord (Fin.castLE hm i.castSucc)).perm) =
        fun i => (D.coord (Fin.castLE (Nat.le_of_succ_le hm) i)).perm := rfl
    rw [e, ih, perm_apply]
    change D.set (D.set z _) (Function.update (D.get (D.set z _)) _
      ((D.get (D.set z _)) _ + D.f (D.set z _) _)) = _
    rw [D.get_set, D.set_set, D.f_set]
    congr 1
    exact update_add_ite (by omega) _ _

/-- **Additions on the coordinates in sequence are the addition of tuples.** -/
theorem seqPerm_coord : seqPerm n (fun i => (D.coord i).perm) = D.perm :=
  Equiv.ext fun z => by
    rw [show (fun i => (D.coord i).perm) = fun i => (D.coord (Fin.castLE le_rfl i)).perm from rfl,
      seqPerm_coord_le D n le_rfl z, perm_apply]
    congr 2
    funext j
    simp [j.isLt]

end RegAdd

/-- **A list of additions after each step `k`**: `nb k` additions in sequence, addition `i` adding
`ω (x k i z)` to the part `L k i` on the branches `on k i z`. Its point is read from the registers
after the earlier additions, so the reads may be adaptive; neither the point nor the branches of
addition `i` read its part. Every encoding of step post-processing is such a list: the
restriction's `width` additions (one per query pair), side reads, query points, and the empty
list. -/
structure StepAdds (Z K X V : Type*) [AddGroup V] where
  /-- The number of additions after step `k`. -/
  nb : K → ℕ
  /-- The part of addition `i` after step `k`. -/
  L : ∀ k, Fin (nb k) → RegLens Z V
  /-- The branches of addition `i` after step `k`. -/
  on : ∀ k, Fin (nb k) → Z → Bool
  /-- The point of addition `i` after step `k`. -/
  x : ∀ k, Fin (nb k) → Z → X
  on_set : ∀ k i, (L k i).Indep (on k i)
  x_set : ∀ k i, (L k i).Indep (x k i)

namespace StepAdds

variable {Z K X V α : Type*} [AddGroup V] (P : StepAdds Z K X V) (ω : X → V)

/-- **Addition `i` after step `k` at `ω`.** -/
def add (k : K) (i : Fin (P.nb k)) : RegAdd Z V where
  toRegLens := P.L k i
  f z := if P.on k i z then ω (P.x k i z) else 0
  f_set z v := by rw [P.on_set k i z v, P.x_set k i z v]

/-- **The additions after step `k` at `ω`**, in sequence. -/
def perm (k : K) : Equiv.Perm Z :=
  seqPerm (P.nb k) fun i => (P.add ω k i).perm

/-- **Every addition keeps `g`.** -/
def Keeps (g : Z → α) : Prop :=
  ∀ k i, (P.L k i).Indep g

/-- **No addition after step `k`** on any branch. -/
def Off (k : K) : Prop :=
  ∀ i z, P.on k i z = false

/-- **Every addition on every branch.** -/
def AllOn : Prop :=
  ∀ k i z, P.on k i z = true

variable {P}

theorem comp_perm_eq {g : Z → α} (h : P.Keeps g) (k : K) (z : Z) : g (P.perm ω k z) = g z :=
  seqPerm_comp_eq g _ _ (fun i z => h k i z _) z

theorem add_of_allOn (h : P.AllOn) (k : K) (i : Fin (P.nb k)) (z : Z) :
    (P.add ω k i).f z = ω (P.x k i z) := by
  simp [add, h k i z]

theorem perm_of_off {k : K} (h : P.Off k) : P.perm ω k = 1 :=
  seqPerm_one _ _ fun i => RegAdd.perm_eq_refl _ fun z => by simp [add, h i z]

/-- **A permutation that neither reads nor writes the parts, and keeps the points and the
branches, commutes with the additions after step `k`.** -/
theorem perm_comm (π : Equiv.Perm Z) (k : K)
    (hget : ∀ i z, (P.L k i).get (π z) = (P.L k i).get z)
    (hset : ∀ i z v, π ((P.L k i).set z v) = (P.L k i).set (π z) v)
    (hon : ∀ i z, P.on k i (π z) = P.on k i z) (hx : ∀ i z, P.x k i (π z) = P.x k i z) (z : Z) :
    π (P.perm ω k z) = P.perm ω k (π z) :=
  seqPerm_comm π _ _ (fun i z => (P.add ω k i).perm_comm π (hget i) (hset i)
    (fun z => by simp only [add, hon, hx]) z) z

/-- **The additions conjugated by a permutation `C`**: the parts conjugated (`RegLens.conj`), the
branches and the points read through `C⁻¹`. -/
def conj (P : StepAdds Z K X V) (C : Equiv.Perm Z) : StepAdds Z K X V where
  nb := P.nb
  L k i := (P.L k i).conj C
  on k i := P.on k i ∘ C.symm
  x k i := P.x k i ∘ C.symm
  on_set k i := (P.on_set k i).conj C
  x_set k i := (P.x_set k i).conj C

/-- Addition `i` of the conjugated additions is addition `i` read through `C⁻¹`. -/
theorem add_conj (P : StepAdds Z K X V) (C : Equiv.Perm Z) (k : K) (i : Fin (P.nb k)) :
    (P.conj C).add ω k i = (P.add ω k i).transport C.symm :=
  rfl

/-- **The conjugated additions are the conjugate of the additions**:
`C ∘ P.perm ω k ∘ C⁻¹ = (P.conj C).perm ω k`. -/
theorem perm_conj (P : StepAdds Z K X V) (C : Equiv.Perm Z) (k : K) :
    C.permCongr (P.perm ω k) = (P.conj C).perm ω k := by
  change C.permCongr (seqPerm (P.nb k) fun i => (P.add ω k i).perm) =
    seqPerm (P.nb k) fun i => ((P.conj C).add ω k i).perm
  simp only [add_conj, RegAdd.perm_transport, Equiv.symm_symm]
  exact (seqPerm_permCongr C _ _).symm

end StepAdds

/-- **A permutation that commutes with `p` conjugates it to itself.** -/
theorem _root_.Equiv.permCongr_self_of_comm {Z : Type*} {π p : Equiv.Perm Z}
    (h : ∀ z, π (p z) = p (π z)) : π.permCongr p = p :=
  Equiv.ext fun z => by
    change π (p (π.symm z)) = p z
    rw [h, Equiv.apply_symm_apply]

/-! ### Kraus maps that differ by a permutation after them -/

namespace KrausMap

variable {R R' ι κ : Type*} [Fintype R] [Fintype R'] [Fintype ι] [DecidableEq ι] [Fintype κ]
  [DecidableEq κ]

/-- **`K'` is `K` followed by the basis permutation `π`**, operator by operator. -/
def LeftPerm (π : Equiv.Perm ι) (K' K : KrausMap R ι ι) : Prop :=
  ∀ r a b, K'.op r (π a) b = K.op r a b

namespace LeftPerm

variable {π : Equiv.Perm ι} {K' K : KrausMap R ι ι}

theorem op_apply (h : LeftPerm π K' K) (r : R) (a b : ι) : K'.op r a b = K.op r (π.symm a) b := by
  conv_lhs => rw [← π.apply_symm_apply a]
  exact h r _ b

/-- **`K'` applied to a matrix is `K` applied to it, relabelled by `π`.** -/
theorem apply (h : LeftPerm π K' K) (ρ : Matrix ι ι ℂ) :
    K' ρ = (K ρ).submatrix π.symm π.symm := by
  ext a b
  simp only [KrausMap.apply, Matrix.sum_apply, Matrix.submatrix_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, h.op_apply]

/-- **Along a reindexing**, the permutation is conjugated. -/
theorem reindex (h : LeftPerm π K' K) (e : ι ≃ κ) :
    LeftPerm (e.permCongr π) (K'.reindex e) (K.reindex e) := fun r a b => by
  change K'.op r (e.symm (e (π (e.symm a)))) (e.symm b) = K.op r (e.symm a) (e.symm b)
  rw [Equiv.symm_apply_apply]
  exact h r _ _

/-- **With the identity on a second factor.** -/
theorem tensorId (h : LeftPerm π K' K) (A : Type*) [Fintype A] [DecidableEq A] :
    LeftPerm (π.prodCongr (Equiv.refl A)) (K'.tensorId A) (K.tensorId A) := fun r a b => by
  change (K'.op r ⊗ₖ (1 : Matrix A A ℂ)) (π a.1, a.2) b = (K.op r ⊗ₖ (1 : Matrix A A ℂ)) a b
  simp only [Matrix.kroneckerMap_apply, h r]

/-- **A composition with a Kraus map on the right.** -/
theorem comp_right (h : LeftPerm π K' K) (L : KrausMap R' ι ι) :
    LeftPerm π (K'.comp L) (K.comp L) := fun r a b => by
  change (K'.op r.2 * L.op r.1) (π a) b = (K.op r.2 * L.op r.1) a b
  simp only [Matrix.mul_apply, h r.2]

theorem ofPerm_op_apply (σ : Equiv.Perm ι) (r : Unit) (a b : ι) :
    (KrausMap.ofPerm σ).op r a b = if a = σ b then 1 else 0 := by
  simp only [KrausMap.ofPerm, KrausMap.permConj, KrausMap.identity, Matrix.submatrix_apply,
    Equiv.refl_apply, Matrix.one_apply]
  exact if_congr (Equiv.symm_apply_eq σ) rfl rfl

theorem ofPerm_mul_apply (σ : Equiv.Perm ι) (r : Unit) (M : Matrix ι ι ℂ) (a b : ι) :
    ((KrausMap.ofPerm σ).op r * M) a b = M (σ.symm a) b := by
  rw [Matrix.mul_apply, Finset.sum_eq_single (σ.symm a)]
  · rw [ofPerm_op_apply, if_pos (σ.apply_symm_apply a).symm, one_mul]
  · intro c _ hc
    rw [ofPerm_op_apply, if_neg fun h => hc (by rw [h, Equiv.symm_apply_apply]), zero_mul]
  · simp

/-- **A basis permutation `σ` on the left** conjugates the permutation. -/
theorem ofPerm_comp (h : LeftPerm π K' K) (σ : Equiv.Perm ι) :
    LeftPerm (σ.permCongr π) ((KrausMap.ofPerm σ).comp K') ((KrausMap.ofPerm σ).comp K) :=
  fun r a b => by
    change ((KrausMap.ofPerm σ).op r.2 * K'.op r.1) (σ (π (σ.symm a))) b =
      ((KrausMap.ofPerm σ).op r.2 * K.op r.1) a b
    rw [ofPerm_mul_apply, ofPerm_mul_apply, Equiv.symm_apply_apply, h r.1]

/-- **A projection onto the basis states of `p`**, for `π` that keeps `p`. -/
theorem restrict (h : LeftPerm π K' K) {p : ι → Bool} (hp : ∀ a, p (π a) = p a) :
    LeftPerm π (K'.restrict p) (K.restrict p) := fun r a b => by
  change (Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) * K'.op r) (π a) b =
    (Matrix.diagonal (fun i => if p i then (1 : ℂ) else 0) * K.op r) a b
  rw [Matrix.diagonal_mul, Matrix.diagonal_mul, hp, h r]

/-- **A basis permutation `τ` after the map** (`permConj` with the identity before) conjugates the
permutation. -/
theorem permConj_left (h : LeftPerm π K' K) (τ : Equiv.Perm ι) :
    LeftPerm (τ.permCongr π) (K'.permConj (Equiv.refl ι) τ) (K.permConj (Equiv.refl ι) τ) :=
  fun r a b => by
    change (K'.op r).submatrix τ.symm (Equiv.refl ι) (τ (π (τ.symm a))) b =
      (K.op r).submatrix τ.symm (Equiv.refl ι) a b
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.refl_apply, h r]

/-- **`K₂` is `K₁` followed by `π₁` and `K₃` is `K₂` followed by `π₂`**: `K₃` is `K₁` followed by
both. -/
theorem trans {π₁ π₂ : Equiv.Perm ι} {K₁ K₂ K₃ : KrausMap R ι ι} (h₁ : LeftPerm π₁ K₂ K₁)
    (h₂ : LeftPerm π₂ K₃ K₂) : LeftPerm (π₁.trans π₂) K₃ K₁ :=
  fun r a b => (h₂ r (π₁ a) b).trans (h₁ r a b)

end LeftPerm

end KrausMap

/-! ### Additions through the absorption and the trace-preserving form -/

namespace AdaptiveIAlg

variable {X Y Req Resp O Req₁ Resp₁ Req₂ Resp₂ V : Type} [Fintype X] [DecidableEq X] [Fintype Y]
  [DecidableEq Y] [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp]
  [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁] [Inhabited Req₁]
  [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂] [AddGroup V]
  {shB : AlgShape X Y Req Resp} (B : AdaptiveIAlg shB O) (F : TwoRelay Req Resp Req₁ Resp₁ Req₂ Resp₂)
  (D : RegAdd (DReg B.W B.width X Y Req Resp) V)

/-- The addition `D` on the registers of the adversary absorbed through `F.base`. -/
def absAdd : RegAdd (DReg (B.AbsW (Resp' := Resp₁)) B.width X Y Req₁ Resp₁) V :=
  (D.prod (B.AbsRest (Req' := Req₁) (Resp' := Resp₁))).transport B.absSplit

/-- The addition `D` on the registers of the adversary absorbed with a table. -/
def tabAdd (tab : B.OuterTab Req₂ Resp₂) :
    RegAdd (DReg (B.absorbTab F tab).W B.width X Y Req₁ Resp₁) V :=
  ((B.absAdd D (Resp₁ := Resp₁) (Req₁ := Req₁)).prod (B.OuterTab Req₂ Resp₂)).transport
    ((B.absorb F.base).constSplit (B.OuterTab Req₂ Resp₂))

/-- The addition `D` on the registers of the trace-preserving form of the adversary absorbed with
a table. -/
def tpAdd (tab : B.OuterTab Req₂ Resp₂) : RegAdd (B.absorbTab F tab).CReg V :=
  ((B.tabAdd F D tab).prod (Fin ((B.absorbTab F tab).budget + 2))).transport
    (B.absorbTab F tab).cntSplit

variable {B F D}

/-- The permutation before slot `k` keeps the adversary's registers (in `absSplit`). -/
theorem absSplit_setAt_fst (F' : SideRelay Req Resp Req₁ Resp₁) (k : ℕ)
    (d : DReg (B.AbsW (Resp' := Resp₁)) B.width X Y Req₁ Resp₁) :
    (B.absSplit (B.setAt F' k d)).1 = (B.absSplit d).1 := by
  rw [AdaptiveIAlg.setAt_def]
  split_ifs
  · change (B.absSplit (if B.kind d.1.1.work then _ else d)).1 = _
    split_ifs <;> rfl
  · rfl

omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] in
/-- **The permutation before slot `k` changes the other registers as a function of the kind and
the request**: two basis states with the same kind, request and other registers keep the same
other registers. -/
theorem absSplit_setAt_snd_congr (F' : SideRelay Req Resp Req₁ Resp₁) (k : ℕ)
    {d d' : DReg (B.AbsW (Resp' := Resp₁)) B.width X Y Req₁ Resp₁}
    (h1 : B.kind (B.absSplit d).1.1.1 = B.kind (B.absSplit d').1.1.1)
    (h2 : (B.absSplit d).1.1.2.1 = (B.absSplit d').1.1.2.1)
    (h3 : (B.absSplit d).2 = (B.absSplit d').2) :
    (B.absSplit (B.setAt F' k d)).2 = (B.absSplit (B.setAt F' k d')).2 := by
  obtain ⟨⟨⟨w, rq, rs, lg, st⟩, mq, mr⟩, qs⟩ := d
  obtain ⟨⟨⟨w', rq', rs', lg', st'⟩, mq', mr'⟩, qs'⟩ := d'
  simp only [absSplit, AlgShape.absSplit, Equiv.coe_fn_mk, Prod.mk.injEq] at h1 h2 h3
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h3
  subst h2
  rw [AdaptiveIAlg.setAt_def]
  split_ifs
  · change (B.absSplit (if B.kind w then _ else _)).2 = (B.absSplit (if B.kind w' then _ else _)).2
    rw [h1]
    split_ifs <;> rfl
  · rfl


omit [Fintype Req₁] [Fintype Resp₁] [DecidableEq Resp₁] in
theorem absAdd_perm_eq :
    (B.absAdd D (Req₁ := Req₁) (Resp₁ := Resp₁)).perm =
      B.absSplit.symm.permCongr (D.perm.prodCongr (Equiv.refl _)) :=
  Equiv.ext fun _ => rfl

theorem tabAdd_perm_eq (tab : B.OuterTab Req₂ Resp₂) :
    (B.tabAdd F D tab).perm = ((B.absorb F.base).constSplit (B.OuterTab Req₂ Resp₂)).symm.permCongr
      ((B.absAdd D).perm.prodCongr (Equiv.refl _)) :=
  Equiv.ext fun _ => rfl

/-! #### The trace-preserving form -/

section TP

variable {shC : AlgShape X Y Req Resp} (C : AdaptiveIAlg shC O) (E : RegAdd (DReg C.W C.width X Y Req Resp) V)

/-- The addition `E` on the registers of the trace-preserving form (with the query counter). -/
def cntAdd : RegAdd C.CReg V :=
  (E.prod (Fin (C.budget + 2))).transport C.cntSplit

variable {C E}

theorem cntAdd_perm_apply (z : C.CReg) :
    (C.cntAdd E).perm z = C.cntSplit.symm (E.perm (C.cntSplit z).1, (C.cntSplit z).2) :=
  rfl

end TP


/-! #### Permutations of the adversary's registers through the absorption

Any permutation `π` of the adversary's registers that keeps the kind and the request register,
lifted through the absorption and the trace-preserving form (`absPerm`, `tabPerm`, `cntPerm`,
`tpPermOf`); the additions' lifts are its instances at `π = D.perm` (`absAdd_perm_eq`,
`tabAdd_perm_eq`, `tpAdd_perm_eq`). -/

section Perm

/-- **A permutation of the adversary's registers on the registers absorbed through `F.base`.** -/
def absPerm (π : Equiv.Perm (DReg B.W B.width X Y Req Resp)) :
    Equiv.Perm (DReg (B.AbsW (Resp' := Resp₁)) B.width X Y Req₁ Resp₁) :=
  B.absSplit.symm.permCongr (π.prodCongr (Equiv.refl _))

/-- **The permutation before slot `k` commutes with a permutation of the adversary's registers**
on the absorbed registers, for one that keeps the kind and the request register. -/
theorem setAt_absPerm {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (hkind : ∀ d, B.kind (π d).1.1 = B.kind d.1.1) (hreq : ∀ d, (π d).1.2.1 = d.1.2.1)
    (F' : SideRelay Req Resp Req₁ Resp₁) (k : ℕ)
    (d : DReg (B.AbsW (Resp' := Resp₁)) B.width X Y Req₁ Resp₁) :
    B.setAt F' k (absPerm π d) = absPerm π (B.setAt F' k d) := by
  set d₁ := absPerm π d
  have e1 : B.absSplit d₁ = (π (B.absSplit d).1, (B.absSplit d).2) := by
    simp [d₁, absPerm, Equiv.permCongr_apply]
    rfl
  have hs : (B.absSplit (B.setAt F' k d₁)).2 = (B.absSplit (B.setAt F' k d)).2 :=
    absSplit_setAt_snd_congr F' k (by rw [e1, hkind]) (by rw [e1, hreq]) (by rw [e1])
  apply B.absSplit.injective
  have e2 : B.absSplit (absPerm π (B.setAt F' k d)) =
      (π (B.absSplit (B.setAt F' k d)).1, (B.absSplit (B.setAt F' k d)).2) := by
    simp [absPerm, Equiv.permCongr_apply]
    rfl
  rw [e2]
  refine Prod.ext ?_ hs
  change (B.absSplit (B.setAt F' k d₁)).1 = π (B.absSplit (B.setAt F' k d)).1
  rw [absSplit_setAt_fst, absSplit_setAt_fst, e1]

variable (F) in
/-- **A permutation of the adversary's registers on the registers absorbed with a table.** -/
def tabPerm (tab : B.OuterTab Req₂ Resp₂) (π : Equiv.Perm (DReg B.W B.width X Y Req Resp)) :
    Equiv.Perm (DReg (B.absorbTab F tab).W B.width X Y Req₁ Resp₁) :=
  ((B.absorb F.base).constSplit (B.OuterTab Req₂ Resp₂)).symm.permCongr
    ((absPerm (Req₁ := Req₁) (Resp₁ := Resp₁) π).prodCongr (Equiv.refl _))

/-- **The table's register lift of a permutation that commutes with `absPerm π` commutes with
`tabPerm`.** -/
theorem tabLift_comm (tab : B.OuterTab Req₂ Resp₂)
    {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    {σ : Equiv.Perm (DReg (B.AbsW (Resp' := Resp₁)) B.width X Y Req₁ Resp₁)}
    (hσ : ∀ d, σ (absPerm π d) = absPerm π (σ d)) :
    (B.tabLift F σ).permCongr (tabPerm F tab π) = tabPerm F tab π := by
  refine Equiv.permCongr_self_of_comm fun z => ?_
  change ((B.absorb F.base).constSplit _).symm ((σ.prodCongr (Equiv.refl _))
      (((B.absorb F.base).constSplit _) (((B.absorb F.base).constSplit _).symm
        (((absPerm π).prodCongr (Equiv.refl _)) (((B.absorb F.base).constSplit _) z))))) =
    ((B.absorb F.base).constSplit _).symm (((absPerm π).prodCongr (Equiv.refl _))
      (((B.absorb F.base).constSplit _) (((B.absorb F.base).constSplit _).symm
        ((σ.prodCongr (Equiv.refl _)) (((B.absorb F.base).constSplit _) z)))))
  simp only [Equiv.apply_symm_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, hσ]

/-- **The steps of the adversary absorbed with a table are followed by the permutation** when the
adversary's are (`h`), for one that keeps the kind and the request register. -/
theorem leftPerm_stepTab
    (st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.LeftPerm π (st' k) (B.step k)) (hkind : ∀ d, B.kind (π d).1.1 = B.kind d.1.1)
    (hreq : ∀ d, (π d).1.2.1 = d.1.2.1) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.LeftPerm (tabPerm F tab π) ((B.withStep st').stepTab F k) (B.stepTab F k) := by
  have h1 := (h.tensorId (B.AbsRest (Req' := Req₁) (Resp' := Resp₁))).reindex B.absSplit.symm
  have h2 := (h1.tensorId (B.OuterTab Req₂ Resp₂)).reindex
    ((B.absorb F.base).constSplit (B.OuterTab Req₂ Resp₂)).symm
  have h3 := (h2.comp_right (KrausMap.ofPerm (B.afterAtTab F k))).ofPerm_comp
    (B.tabLift F (B.setAt F.base k))
  rw [show (B.absSplit.symm.permCongr (π.prodCongr (Equiv.refl _))) = absPerm π from rfl] at h3
  rw [show ((B.absorb F.base).constSplit (B.OuterTab Req₂ Resp₂)).symm.permCongr
      ((absPerm (Req₁ := Req₁) (Resp₁ := Resp₁) π).prodCongr (Equiv.refl _)) = tabPerm F tab π
      from rfl] at h3
  rw [tabLift_comm tab (setAt_absPerm hkind hreq F.base k)] at h3
  rw [stepTab_eq (B.withStep st') F k, stepTab_eq B F k]
  exact h3

variable {shC : AlgShape X Y Req Resp} (C : AdaptiveIAlg shC O)

/-- **A permutation of the adversary's registers on the registers of the trace-preserving form**
(with the query counter). -/
def cntPerm (π : Equiv.Perm (DReg C.W C.width X Y Req Resp)) : Equiv.Perm C.CReg :=
  C.cntSplit.symm.permCongr (π.prodCongr (Equiv.refl _))

variable {C}

theorem cntPerm_apply (π : Equiv.Perm (DReg C.W C.width X Y Req Resp)) (z : C.CReg) :
    C.cntPerm π z = C.cntSplit.symm (π (C.cntSplit z).1, (C.cntSplit z).2) :=
  rfl

@[simp] theorem cntPerm_mk (π : Equiv.Perm (DReg C.W C.width X Y Req Resp)) (w : C.W)
    (c : Fin (C.budget + 2)) (rr : Req × Option Resp) (qs : Fin C.width → X × Y) :
    C.cntPerm π (((AlgShape.CntW.mk w c), rr), qs) =
      (((AlgShape.CntW.mk (π ((w, rr), qs)).1.1 c), (π ((w, rr), qs)).1.2), (π ((w, rr), qs)).2) :=
  rfl

/-- **The counter's advance commutes with a permutation that keeps the kind.** -/
theorem tpShift_cntPerm {π : Equiv.Perm (DReg C.W C.width X Y Req Resp)}
    (hkind : ∀ d, C.kind (π d).1.1 = C.kind d.1.1) :
    C.tpShift.permCongr (C.cntPerm π) = C.cntPerm π := by
  refine Equiv.permCongr_self_of_comm fun z => ?_
  obtain ⟨⟨wc, rr⟩, qs⟩ := z
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc
  rw [cntPerm_mk, tpShift_apply, tpShift_apply, cntPerm_mk,
    show C.kind (π ((w, rr), qs)).1.1 = C.kind w from hkind _]

/-- **The exchange of the counter's last values commutes with a permutation.** -/
theorem endSwap_cntPerm (π : Equiv.Perm (DReg C.W C.width X Y Req Resp)) :
    C.endSwap.permCongr (C.cntPerm π) = C.cntPerm π := by
  refine Equiv.permCongr_self_of_comm fun z => ?_
  obtain ⟨⟨wc, rr⟩, qs⟩ := z
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc
  rw [cntPerm_mk, endSwap_apply, endSwap_apply, cntPerm_mk]

/-- **The budget test reads past a permutation that keeps the kind.** -/
theorem inBudget_cntPerm {π : Equiv.Perm (DReg C.W C.width X Y Req Resp)}
    (hkind : ∀ d, C.kind (π d).1.1 = C.kind d.1.1) (z : C.CReg) :
    C.inBudget (C.cntPerm π z) = C.inBudget z := by
  obtain ⟨⟨wc, rr⟩, qs⟩ := z
  obtain ⟨w, c, rfl⟩ := AlgShape.CntW.exists_eq_mk wc
  rw [cntPerm_mk, inBudget_mk, inBudget_mk,
    show C.kind (π ((w, rr), qs)).1.1 = C.kind w from hkind _]

theorem cntKraus_leftPerm
    {st' : StepIdx C.slots C.post → KrausMap C.R (DReg C.W C.width X Y Req Resp)
      (DReg C.W C.width X Y Req Resp)} {π : Equiv.Perm (DReg C.W C.width X Y Req Resp)}
    (k : StepIdx C.slots C.post) (h : KrausMap.LeftPerm π (st' k) (C.step k)) :
    KrausMap.LeftPerm (C.cntPerm π) ((C.withStep st').cntKraus k) (C.cntKraus k) :=
  (h.tensorId (Fin (C.budget + 2))).reindex C.cntSplit.symm

/-- **The trace-preserving form's steps are followed by the permutation** when the adversary's
are (`h`), for trace-preserving steps (`hTP'`, `hTP`) and a permutation that keeps the kind. -/
theorem leftPerm_toTPKindAlg
    {st' : StepIdx C.slots C.post → KrausMap C.R (DReg C.W C.width X Y Req Resp)
      (DReg C.W C.width X Y Req Resp)} {π : Equiv.Perm (DReg C.W C.width X Y Req Resp)}
    (k : StepIdx C.slots C.post) (h : KrausMap.LeftPerm π (st' k) (C.step k))
    (hkind : ∀ d, C.kind (π d).1.1 = C.kind d.1.1)
    (hTP' : (C.withStep st').TracePreserving) (hTP : C.TracePreserving) :
    KrausMap.LeftPerm (C.cntPerm π) ((C.withStep st').toTPKindAlg.step k)
      (C.toTPKindAlg.step k) := by
  intro z a b
  simp only [AdaptiveIAlg.toTPKindAlg_step_op, AlgShape.tpStep_op]
  change (C.withStep st').tpOp false k z (C.cntPerm π a) b = C.tpOp false k z a b
  rcases z with r | r | c
  · by_cases hk : (k : ℕ) < C.slots
    · have h1 := (((cntKraus_leftPerm k h).restrict (inBudget_cntPerm hkind)).permConj_left
        C.tpShift)
      rw [tpShift_cntPerm hkind] at h1
      simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte]
      rw [if_pos (show (k : ℕ) < (C.withStep st').slots from hk), if_pos hk]
      exact h1 r a b
    · simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte]
      rw [if_neg (show ¬ (k : ℕ) < (C.withStep st').slots from hk), if_neg hk]
      exact cntKraus_leftPerm k h r a b
  · by_cases hk : (k : ℕ) < C.slots
    · have hb : ∀ z, (fun d => !C.inBudget d) (C.cntPerm π z) = (fun d => !C.inBudget d) z :=
        fun z => by simp only [inBudget_cntPerm hkind]
      have h1 := (((cntKraus_leftPerm k h).restrict (p := fun d => !C.inBudget d)
        hb).permConj_left C.endSwap)
      rw [endSwap_cntPerm] at h1
      simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte]
      rw [if_pos (show (k : ℕ) < (C.withStep st').slots from hk), if_pos hk]
      exact h1 r a b
    · simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte]
      rw [if_neg (show ¬ (k : ℕ) < (C.withStep st').slots from hk), if_neg hk]
      rfl
  · simp only [tpOp_eq, tpRaw_inl, tpRaw_inr_inl, tpRaw_inr_inr, Bool.false_eq_true, ↓reduceIte,
      TracePreserving.haltOp_eq_zero hTP' k,
      TracePreserving.haltOp_eq_zero hTP k,
      Matrix.zero_kronecker]
    rfl

variable (F) in
/-- **A permutation of the adversary's registers on the trace-preserving form of the adversary
absorbed with a table.** -/
def tpPermOf (tab : B.OuterTab Req₂ Resp₂) (π : Equiv.Perm (DReg B.W B.width X Y Req Resp)) :
    Equiv.Perm (B.absorbTab F tab).CReg :=
  (B.absorbTab F tab).cntPerm (tabPerm F tab π)

theorem tpAdd_perm_eq (tab : B.OuterTab Req₂ Resp₂) :
    (B.tpAdd F D tab).perm = tpPermOf F tab D.perm :=
  Equiv.ext fun _ => rfl

/-- **The trace-preserving form of the adversary absorbed with a table is followed by the
permutation** when the adversary's step is (`h`), for trace-preserving adversaries and a
permutation that keeps the kind and the request register. -/
theorem leftPerm_absorbTab_toTP
    (st' : StepIdx B.slots B.post → KrausMap B.R (DReg B.W B.width X Y Req Resp)
      (DReg B.W B.width X Y Req Resp))
    (k : StepIdx B.slots B.post) {π : Equiv.Perm (DReg B.W B.width X Y Req Resp)}
    (h : KrausMap.LeftPerm π (st' k) (B.step k)) (hkind : ∀ d, B.kind (π d).1.1 = B.kind d.1.1)
    (hreq : ∀ d, (π d).1.2.1 = d.1.2.1) (hTP' : (B.withStep st').TracePreserving)
    (hTP : B.TracePreserving) (tab : B.OuterTab Req₂ Resp₂) :
    KrausMap.LeftPerm (tpPermOf F tab π)
      (((B.withStep st').absorbTab F tab).toTPKindAlg.step k)
      ((B.absorbTab F tab).toTPKindAlg.step k) :=
  leftPerm_toTPKindAlg (C := B.absorbTab F tab) (st' := (B.withStep st').stepTab F) k
    (leftPerm_stepTab st' k h hkind hreq tab)
    (fun _ => hkind _)
    (absorbTab_tracePreserving (B.withStep st') F hTP' tab)
    (absorbTab_tracePreserving B F hTP tab)

end Perm

end AdaptiveIAlg

/-! ### The local queries of the adversary at a fixed base part -/

section Restrict

variable {X Y Y₁ Y₂ Req Resp O Req₁ Resp₁ Req₂ Resp₂ : Type} [Fintype X] [DecidableEq X]
  [Fintype Y] [DecidableEq Y] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂]
  [Fintype Req] [DecidableEq Req] [Fintype Resp] [DecidableEq Resp] [AddGroup Y] [AddGroup Y₁]
  [AddGroup Y₂] [Fintype Req₁] [DecidableEq Req₁] [Fintype Resp₁] [DecidableEq Resp₁]
  [Inhabited Req₁] [Fintype Req₂] [DecidableEq Req₂] [Fintype Resp₂] [DecidableEq Resp₂]

/-- **The second factor of a product**, as a part. -/
def sndLens (W V : Type*) : RegLens (W × V) V where
  get w := w.2
  set w v := (w.1, v)
  get_set _ _ := rfl
  set_get _ := rfl
  set_set _ _ _ := rfl

/-- **A local query to the base part `H₁` on a part of the workspace**: on the branches of `on`
(which does not read the part, `hon`), the value `H₁ x` of pair `k`'s input `x` added to
coordinate `k` of the part `Lw` of the workspace. -/
def wsAdd {W : Type} {n : ℕ} (Lw : RegLens W (Fin n → Y₁)) (on : W → Bool)
    (hon : ∀ w v, on (Lw.set w v) = on w) (H₁ : X → Y₁) (Req Resp : Type) :
    RegAdd (DReg W n X Y₂ Req Resp) (Fin n → Y₁) where
  get d := Lw.get d.1.1
  set d v := ((Lw.set d.1.1 v, d.1.2), d.2)
  get_set _ _ := by simp
  set_get _ := by simp
  set_set _ _ _ := by simp
  f d k := if on d.1.1 then H₁ (d.2 k).1 else 0
  f_set d v := by simp only [hon]

/-- **The local queries to the base part as a list of additions**: after step `k`, one addition
per query pair `i`, coordinate `i` of the part `Lw` of the workspace receiving the value at pair
`i`'s input, on the branches of `on k`. -/
def wsAdds {W K : Type} {n : ℕ} (Lw : RegLens W (Fin n → Y₁)) (on : K → W → Bool)
    (hon : ∀ k w v, on k (Lw.set w v) = on k w) (Req Resp : Type) :
    StepAdds (DReg W n X Y₂ Req Resp) K X Y₁ where
  nb _ := n
  L k i := (wsAdd Lw (on k) (hon k) 0 Req Resp).toRegLens.comp (coordLens Y₁ i)
  on k _ d := on k d.1.1
  x _ i d := (d.2 i).1
  on_set k _ d v := hon k _ _
  x_set _ _ _ _ := rfl

omit [Fintype X] [DecidableEq X] [Fintype Y₁] [DecidableEq Y₁] [Fintype Y₂] [DecidableEq Y₂]
  [AddGroup Y₂] in
/-- **The list of local queries is the local query** of the tuple (`RegAdd.seqPerm_coord`). -/
theorem wsAdds_perm {W K : Type} {n : ℕ} (Lw : RegLens W (Fin n → Y₁)) (on : K → W → Bool)
    (hon : ∀ k w v, on k (Lw.set w v) = on k w) (H₁ : X → Y₁) (Req Resp : Type) (k : K) :
    (wsAdds (Y₂ := Y₂) Lw on hon Req Resp).perm H₁ k = (wsAdd Lw (on k) (hon k) H₁ Req Resp).perm :=
  (wsAdd Lw (on k) (hon k) H₁ Req Resp).seqPerm_coord

/-- **The local query `basePerm` as an addition**: the `Y₁`-parts of the query answers in the
workspace, the value `H₁ x` of pair `k`'s input `x` added on the branches of `on`. -/
abbrev ysAdd (H₁ : X → Y₁) {W : Type} (on : W → Bool) (n : ℕ) (Req Resp : Type) :
    RegAdd (DReg (W × (Fin n → Y₁)) n X Y₂ Req Resp) (Fin n → Y₁) :=
  wsAdd (sndLens W (Fin n → Y₁)) (fun w => on w.1) (fun _ _ => rfl) H₁ Req Resp

theorem basePerm_eq_ysAdd (H₁ : X → Y₁) {W : Type} (on : W → Bool) (n : ℕ) (Req Resp : Type) :
    basePerm (Y₂ := Y₂) H₁ on n Req Resp = (ysAdd H₁ on n Req Resp).perm := by
  refine Equiv.ext fun d => ?_
  obtain ⟨⟨⟨w, ys⟩, rest⟩, p⟩ := d
  change (((w, fun k => if on w then ys k + H₁ (p k).1 else ys k), rest), p) =
    (((w, ys + fun k => if on w then H₁ (p k).1 else 0), rest), p)
  by_cases h : on w
  · simp only [h, if_true]
    rfl
  · simp [h]
    rfl

/-- The local query to the zero base part is the identity. -/
theorem basePerm_zero {W : Type} (on : W → Bool) (n : ℕ) (Req Resp : Type) :
    basePerm (Y₂ := Y₂) (0 : X → Y₁) on n Req Resp = Equiv.refl _ := by
  rw [basePerm_eq_ysAdd]
  exact RegAdd.perm_eq_refl _ fun d => by
    funext k
    change (if on d.1.1.1 then (0 : X → Y₁) (d.2 k).1 else 0) = 0
    simp only [Pi.zero_apply, ite_self]

variable (sp : Y ≃+ Y₁ × Y₂) (ω : X → Y₁) {shA : AlgShape X Y Req Resp} (A : AdaptiveIAlg shA O)

/-- **The restricted adversary's step at the base part `ω` is its step at the zero base part
followed by the local query** (`ysAdd`). -/
theorem leftPerm_restrictAt_step (k : StepIdx A.slots A.post) :
    KrausMap.LeftPerm (ysAdd ω (A.stepOn k) A.width Req Resp).perm
      ((A.restrictAt sp ω).step k) ((A.restrictAt sp 0).step k) := fun r a b => by
  change ((((A.step k).reindex (splitReg sp A.W A.width X Req Resp).symm).op r).submatrix
      (basePerm ω (A.stepOn k) A.width Req Resp).symm (Equiv.refl _))
      ((ysAdd ω (A.stepOn k) A.width Req Resp).perm a) b =
    ((((A.step k).reindex (splitReg sp A.W A.width X Req Resp).symm).op r).submatrix
      (basePerm 0 (A.stepOn k) A.width Req Resp).symm (Equiv.refl _)) a b
  rw [Matrix.submatrix_apply, Matrix.submatrix_apply, ← basePerm_eq_ysAdd, Equiv.symm_apply_apply,
    basePerm_zero, Equiv.refl_symm]
  rfl

end Restrict

end GordieHowe.Quantum
