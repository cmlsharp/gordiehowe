-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.RingSwitching.TreePaper
public import GordieHowe.ProofSystem.RingSwitching.PlanTree
public import GordieHowe.Foundations.Algebra.PackingTower

@[expose] public section

/-!
# Ring switching for bits in characteristic 2, along the tower `K ⊃ S0 ⊃ GF(2)`

The paper's corollary `cor:tower` is `thm:tree` (`GordieHowe.RingSwitching.Tree.reduces`,
`complete`, `hvzk`, `GordieHowe/ProofSystem/RingSwitching/TreePaper.lean`) on the two-stage tree
`K ⊃ S0 ⊃ GF(2)` of a field `K` of characteristic 2 with evaluation subfield `S0 = F_{2^s}`,
`[K : S0] = r`. The committed words `U` (`TowerSetup.word`) pack bits through `S0`: the first stage
(`bitStage`, squaring-chain masks, `RS_sq(GF(2), S0)`) runs on the `S0`-coordinates
`unpack_{K/S0}(U)`, the second (`subStage`, subfield masks, `RS_sub(S0, K)`) on `U`; both combine
every outstanding claim (`Tree.cons`).

The claims of the corollary are on the value map `(unpack_{K/GF(2)}(U), V)` with the product basis
of `lem:unpack-tower` (`TowerSetup.product`, `StageBasis.tower`): a claim reads the bit coordinates
`TowerValue.bit` and the cells `TowerValue.cell` (`V`, and any other committed cell). The tree's
stage-by-stage decoding is the product-basis decoding (`level_view_rename`, from
`StageBasis.coord_tower`), so the tree's input relation is the corollary's (`claimsHold_iff`).

* `TowerSetup.reduces`: part (1), with the mask condition the membership claims
  `x (entry j) ∈ S0` (`masksValid_iff`) and soundness error `2/|K|`;
* `TowerSetup.complete`: part (2), on every committed data at which the input claims hold, every
  mask entry lies in `S0` and every product constraint of the squaring chains holds
  (`MasksHold`), the honest prover reading its masks from the data (`padsOf`);
* `TowerSetup.hvzk`: part (3), with the prover messages `Fin s → K` and `Fin r → K`
  (`spec_eq`), `s + r` elements of `K` (`r = w/s`).
-/

namespace GordieHowe

open IOP IOP.ProtocolSpec PackingStage RelativePacking FieldProof
open GKR.Schedule (one)
open scoped NNReal

namespace RingSwitching

/-- **A coordinate of the corollary's value map** `(unpack_{K/GF(2)}(U), V)`: a bit of a word,
decoded through the product basis (`bit`), or a committed cell (`cell`). -/
inductive TowerValue (ι : Type) (m D : ℕ) where
  /-- Position `c.pos` of `unpack_{K/GF(2)}` of the word `c.group`. -/
  | bit (c : PackedCoord m D)
  /-- A committed cell. -/
  | cell (i : ι)

/-- **The logical coordinates of the two-stage tree**: the cells, the `S0`-coordinates of the
words (`[K : S0] = r` each), and the bits of the `S0`-coordinates (`s` each). -/
abbrev TowerCoord (ι : Type) (m r s : ℕ) : Type :=
  (ι ⊕ PackedCoord m r) ⊕ PackedCoord (m * r) s

/-- **A coordinate of the value map as a coordinate of the tree** `K ⊃ S0 ⊃ GF(2)`
(`[K : S0] = r`, `[S0 : GF(2)] = s`): bit `finProdFinEquiv (j, i)` of word `g` is bit `i` of the
`S0`-coordinate `finProdFinEquiv (g, j)`. -/
def TowerValue.toCoord {ι : Type} {m : ℕ} (r s : ℕ) : TowerValue ι m (r * s) → TowerCoord ι m r s
  | .bit c => .inr ⟨finProdFinEquiv (c.group, (finProdFinEquiv.symm c.pos).1),
      (finProdFinEquiv.symm c.pos).2⟩
  | .cell i => .inl (.inl i)

/-- **Claims on the value map as claims on the tree's coordinates** (`TowerValue.toCoord`). -/
def towerClaims {K ι Pub : Type} {m nc : ℕ} (r s : ℕ)
    (claims : Pub → Fin nc → AffineForm K (TowerValue ι m (r * s))) (pub : Pub) (c : Fin nc) :
    AffineForm K (TowerCoord ι m r s) :=
  (claims pub c).rename (TowerValue.toCoord r s)

/-- **The data of the corollary**: a basis of `S0 = F_{2^s}` over `GF(2)` (`bits`) and a basis of
`K` over `S0` (`sub`), with their dual bases; the `m` committed words; the cells of the squaring
chains of the first stage (`chain`, `σ_k` then the chain cells, `MaskKit.chainCells`) and the mask
entries of the second (`entry`, entry `(k, i)` at `finProdFinEquiv (k, i)`); and the basis `γ` of
`K` over `S0` of the subfield masks (`γ_bijective`: combinations with coefficients in `S0` are
bijective onto `K`). -/
structure TowerSetup (K ι : Type) [Field K] [ExpChar K 2] (s r m : ℕ)
    [Fintype (fixedField K 2 s)] where
  /-- The basis of `S0` over `GF(2)`. -/
  bits : StageBasis K 2 1 s
  /-- The basis of `K` over `S0`. -/
  sub : StageBasis K 2 s r
  /-- The committed words `U`. -/
  word : Fin m → ι
  /-- The cells of the squaring chains. -/
  chain : Fin (s + ∑ k : Fin s, (k : ℕ)) → ι
  /-- The mask entries. -/
  entry : Fin (r * r) → ι
  /-- The basis of `K` over `S0` of the subfield masks. -/
  γ : Fin r → K
  /-- `γ` is a basis of `K` over `S0`. -/
  γ_bijective : Function.Bijective fun c : Fin r → fixedField K 2 s => ∑ i, γ i * (c i : K)

namespace TowerSetup

variable {K ι : Type} [Field K] [Fintype K] [DecidableEq K] [ExpChar K 2] [Fintype ι]
  {s r m : ℕ} [Fintype (fixedField K 2 s)] (T : TowerSetup K ι s r m)

/-- **The product basis of `K` over `GF(2)`** (`lem:unpack-tower`): `a_i b_j` at
`finProdFinEquiv (j, i)`, `a = bits`, `b = sub`. -/
def product : StageBasis K 2 1 (r * s) :=
  T.bits.tower T.sub (one_mul s).symm

/-- **The masks of the second stage**: subfield masks over `S0` (`MaskKit.subfield`). -/
def subKit : MaskKit K 2 s r (fixedField K 2 s) :=
  MaskKit.subfield T.γ le_rfl T.γ_bijective

/-- **The second stage** `S0 < K` on the words, with subfield masks (`RS_sub(S0, K)`). -/
def subStage : Stage K ι 2 s r r m ι where
  basis := T.sub
  word := T.word
  masks := T.subKit.scheme T.entry Fin.elim0

/-- **The first stage** `GF(2) < S0` on the `S0`-coordinates of the words, `finProdFinEquiv (g, j)`
the coordinate `j` of word `g`, with squaring-chain masks (`RS_sq(GF(2), S0)`). -/
def bitStage : Stage K ι 2 1 s (s * r) (m * r) (ι ⊕ PackedCoord m r) where
  basis := T.bits
  word g := .inr ⟨(finProdFinEquiv.symm g).1, (finProdFinEquiv.symm g).2⟩
  masks := (MaskKit.bitChain (S0 := fixedField K 2 s)).scheme Fin.elim0 T.chain

include T in
omit [DecidableEq K] [Fintype ι] in
/-- **`K` has `|S0|^r` elements**: `γ` is a basis of `K` over `S0`. -/
theorem card_eq_pow : Fintype.card K = Fintype.card (fixedField K 2 s) ^ r := by
  rw [← Fintype.card_congr (Equiv.ofBijective _ T.γ_bijective), Fintype.card_fun,
    Fintype.card_fin]

include T in
omit [DecidableEq K] [Fintype ι] in
/-- **`[K : S0] = w/s`**: for `|K| = 2^w`, `w ≠ 0` and `s ∣ w`, `r s = w`. -/
theorem mul_eq_of_card {w : ℕ} (hK : Fintype.card K = 2 ^ w) (hw : w ≠ 0) (hs : s ∣ w) :
    s * r = w := by
  have hS := card_fixedField_of_dvd hK hw hs one_lt_two
  rw [Nat.card_eq_fintype_card] at hS
  have h := T.card_eq_pow
  rw [hS, hK, ← pow_mul] at h
  exact (Nat.pow_right_injective le_rfl h).symm

variable [RelFrobeniusOrder K 2 1 (s * r)] [RelFrobeniusOrder K 2 s r]

/-- **The tree `K ⊃ S0 ⊃ GF(2)`** in processing order: the first stage, then the second, each
combining every outstanding claim. -/
def tree (nc : ℕ) : Tree K 2 ι (TowerCoord ι m r s) nc :=
  .cons T.bitStage (.cons T.subStage .nil)

/-- **The value map** `(unpack_{K/GF(2)}(U), V)` on the cells `x`, through the product basis. -/
def view (x : ι → K) : TowerValue ι m (r * s) → K
  | .bit c => T.product.coord (x (T.word c.group)) c.pos
  | .cell i => x i

omit [DecidableEq K] [Fintype ι] in
/-- **The tree decodes the value map** (`lem:unpack-tower`, `StageBasis.coord_tower`): the
stage-by-stage decoding of the tree at a renamed coordinate is the product-basis decoding. -/
theorem level_view_rename (nc : ℕ) (x : ι → K) (v : TowerValue ι m (r * s)) :
    (T.tree nc).level.view x (TowerValue.toCoord r s v) = T.view x v := by
  cases v with
  | cell i => rfl
  | bit c =>
    obtain ⟨g, k⟩ := c
    obtain ⟨⟨j, i⟩, rfl⟩ := finProdFinEquiv.surjective k
    simp only [tree, Tree.level, Stage.level, Stage.extend, TowerValue.toCoord, view, bitStage,
      subStage, Equiv.symm_apply_apply, Sum.elim_inr, Level.base_view, product, StageBasis.coord_tower]

omit [DecidableEq K] [Fintype ι] in
/-- **The tree's input relation is the corollary's**: the renamed claims hold on the tree's
decoding exactly when the claims hold on the value map. -/
theorem claimsHold_iff {Pub : Type} {nc : ℕ}
    (claims : Pub → Fin nc → AffineForm K (TowerValue ι m (r * s))) (pub : Pub) (x : ι → K) :
    (T.tree nc).ClaimsHold (towerClaims r s claims) pub x ↔ ∀ c, (claims pub c).eval (T.view x) = 0 := by
  have h : (T.tree nc).level.view x ∘ TowerValue.toCoord r s = T.view x :=
    funext (T.level_view_rename nc x)
  simp only [Tree.ClaimsHold, towerClaims, AffineForm.eval_rename, h]

omit [DecidableEq K] [Fintype ι] in
/-- **The mask condition of the tree is the membership claims** on the mask entries. -/
theorem masksValid_iff (nc : ℕ) (x : ι → K) :
    (T.tree nc).MasksValid x ↔ ∀ j, x (T.entry j) ∈ fixedField K 2 s := by
  change True ∧ ((∀ k i, x (T.entry (finProdFinEquiv (k, i))) ∈ fixedField K 2 s) ∧ True) ↔ _
  simp only [true_and, and_true]
  refine ⟨fun h j => ?_, fun h k i => h _⟩
  have hj := h (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2
  rwa [Prod.mk.eta, Equiv.apply_symm_apply] at hj

/-- **The tree has no routing obligation**: both stages combine every claim. -/
theorem routes {Pub Wit : Type} {cells : Wit → ι → K} {nc : ℕ}
    (M : MaskedReduction K ι Pub Wit cells (TowerCoord ι m r s) nc) : (T.tree nc).Routes M :=
  trivial

omit [DecidableEq K] [Fintype ι] in
/-- **Two combinations**, one per stage. -/
theorem combinations_tree (nc : ℕ) : (T.tree nc).combinations = 2 :=
  rfl

omit [DecidableEq K] [Fintype ι] in
/-- **Two stages.** -/
theorem stages_tree (nc : ℕ) : (T.tree nc).stages = 2 :=
  rfl

variable {Pub Wit : Type} {cells : Wit → ι → K} {nc : ℕ}
  (claims : Pub → Fin nc → AffineForm K (TowerValue ι m (r * s)))

/-- **The reduction of the corollary**: `thm:tree`'s reduction on the tree with the renamed
claims. -/
noncomputable abbrev reduction :
    ClaimReduction ((T.tree nc).ringSwitch (cells := cells) (towerClaims r s claims)).spec
      (MaskedRowReduction.Instance Pub Wit) ((T.tree nc).ringSwitchError (towerClaims r s claims)) :=
  (T.tree nc).ringSwitchReduction (towerClaims r s claims) (T.routes _)

/-- **The conclusions of part (1) of the paper's `cor:tower`**: those of `thm:tree` on the tree
(`tree`: round error at most `1/|K|` at each challenge, the output rows and claims on the cells and
the mask condition as output claim), with the input claim the claims on the value map
`(unpack_{K/GF(2)}(U), V)` (`claim_iff`), the mask condition the membership claims of the mask
entries in `S0` (`masksValid_iff`), and soundness error `2/|K|` (`sum_error`). -/
structure Reduces : Prop where
  /-- `thm:tree`, part (1), on the tree. -/
  tree : (T.tree nc).RingSwitchReduces (cells := cells) (towerClaims r s claims) (T.routes _)
  /-- The input claim: the claims on the value map. -/
  claim_iff : ∀ pub w, (T.reduction (cells := cells) claims).claim ⟨pub, w⟩ ↔
    ∀ c, (claims pub c).eval (T.view (cells w)) = 0
  /-- The mask condition: the mask entries lie in `S0`. -/
  masksValid_iff : ∀ x, (T.tree nc).MasksValid x ↔ ∀ j, x (T.entry j) ∈ fixedField K 2 s
  /-- The soundness error is `2/|K|`. -/
  sum_error : ∑ i, (T.tree nc).ringSwitchError (cells := cells) (towerClaims r s claims) i =
    2 / Fintype.card K

/-- **Paper `cor:tower`, part (1)**: ring switching along `K ⊃ S0 ⊃ GF(2)` is a round-by-round
reduction from the linear claims on `(unpack_{K/GF(2)}(U), V)`, with the product basis of
`lem:unpack-tower`, to the output rows and claims on the committed cells (linear claims, the
product constraints of the squaring chains) and the membership claims of the mask entries in `S0`,
with round error at most `1/|K|` at each of its two challenges and soundness error `2/|K|`. -/
@[headline]
theorem reduces : T.Reduces (cells := cells) claims where
  tree := (T.tree nc).reduces (towerClaims r s claims) (T.routes _)
  claim_iff pub w := T.claimsHold_iff claims pub (cells w)
  masksValid_iff := T.masksValid_iff nc
  sum_error := by
    rw [Tree.sum_ringSwitchError, combinations_tree]
    norm_num

/-! ### The honest prover -/

/-- **The honest prover of the corollary** (`thm:tree`'s honest run on the tree): on the committed
cells `x`, its honest input, in the domain where the claims hold on the value map, with the honest
masks of `prot:bits` and `prot:cells` (`MaskKit.bitChain`, `MaskKit.subfield`), reading the words'
values from `x`; simulated by `thm:tree`'s simulator (`Tree.ringSwitchSim`), which copies each of
the two combination challenges and sends uniform measurements in `K^s` and `K^r`. -/
def honest : ((T.tree nc).ringSwitch (cells := cells) (towerClaims r s claims)).Honest
    (Level.base (F := K)).view (ι → K) (fun pub x => ∀ c, (claims pub c).eval (T.view x) = 0)
    ((T.tree nc).ringSwitchSim (cells := cells) (towerClaims r s claims)) :=
  (T.tree nc).ringSwitchHonest (towerClaims r s claims) (T.routes _) (fun _ x w => cells w = x)
    (fun pub _ hx w hw => (T.claimsHold_iff claims pub (cells w)).mpr (hw ▸ hx))
    ((MaskKit.bitChain (S0 := fixedField K 2 s)).honest Fin.elim0 T.chain, T.subKit.honest T.entry Fin.elim0, PUnit.unit)
    (fun _ x z => (T.tree nc).level.view x z) fun _ _ _ hw _ _ => by rw [hw]

/-- **The masks condition of part (2)**: every mask entry lies in `S0` and every product
constraint of the squaring chains holds. -/
structure MasksHold (x : ι → K) : Prop where
  /-- The mask entries lie in `S0`. -/
  entry_mem : ∀ j, x (T.entry j) ∈ fixedField K 2 s
  /-- The squaring constraints hold. -/
  chain : Ligero.Routing.SourceProducts (MaskKit.chainCells T.chain).products x

/-- **The masks the honest prover reads from the committed data** `x`: the masks `σ_k` of the
first stage and the mask entries of the second. -/
def padsOf (x : ι → K) (h : ∀ j, x (T.entry j) ∈ fixedField K 2 s) :
    (T.honest (cells := cells) claims).Pads :=
  (((), fun k => x (T.chain (Fin.castAdd _ k))),
    fun k i => ⟨x (T.entry (finProdFinEquiv (k, i))), h _⟩)

omit [DecidableEq K] [ExpChar K 2] in
/-- **On cells where the squaring triples hold, the chain cells hold the chain values** of their
masks `σ_k` (`MaskKit.chainVal`). -/
theorem _root_.GordieHowe.MaskKit.chainVal_of_products {d : ℕ} {ι : Type}
    (co : Fin (d + ∑ k : Fin d, (k : ℕ)) → ι) {x : ι → K}
    (h : Ligero.Routing.SourceProducts (MaskKit.chainCells co).products x)
    (o : Fin (d + ∑ k : Fin d, (k : ℕ))) :
    x (co o) = MaskKit.chainVal (fun k => x (co (Fin.castAdd _ k))) o := by
  refine Fin.addCases (fun k => ?_) (fun j => ?_) o
  · rw [MaskKit.chainVal_sigma]
  · obtain ⟨c, rfl⟩ := ((SquaringCell.equivSigma d).trans finSigmaFinEquiv).surjective j
    rw [Equiv.trans_apply, MaskKit.chainVal_chain]
    exact (MaskKit.chainCells co).chain_eq_pow h c

/-- **Paper `cor:tower`, part (2)**: on every committed data `x` at which the claims hold on the
value map, every mask entry lies in `S0` and every product constraint holds, the honest prover
with the masks read from `x` (`padsOf`) makes the output rows and claims hold on `x`, at every
challenge. -/
@[headline]
theorem complete {pub : Pub} {x : ι → K} (hx : ∀ c, (claims pub c).eval (T.view x) = 0)
    (hm : T.MasksHold x) {w : Wit} (hw : cells w = x)
    (ch : ((T.tree nc).ringSwitch (cells := cells) (towerClaims r s claims)).spec.Challenges) :
    ((T.tree nc).ringSwitch (towerClaims r s claims)).OutHolds (Level.base (F := K)).view pub
      (((T.honest claims).prover pub x (T.padsOf claims x hm.entry_mem)).transcript ch)
      (cells w) := by
  subst hw
  refine (T.tree nc).complete (towerClaims r s claims) (T.routes _) _ _ _ _ _ hx
    (T.padsOf claims (cells w) hm.entry_mem) ⟨⟨rfl, fun j => j.elim0,
      MaskKit.chainVal_of_products T.chain hm.chain⟩,
      fun j => congrArg (fun k => cells w (T.entry k)) (finProdFinEquiv.apply_symm_apply j).symm,
      fun o => o.elim0⟩ ch

/-! ### Zero knowledge -/

/-- **The message schedule of the corollary**: the combination challenge of the first stage
(`nc` coefficients), its `s` sent elements of `K`, the combination challenge of the second
(`s + 1` coefficients) and its `r` sent elements. -/
theorem spec_eq : ((T.tree nc).ringSwitch (cells := cells) (towerClaims r s claims)).spec =
    MaskedRowReduction.noRounds ++ one .V_to_P (Fin nc → K) ++ one .P_to_V (Fin s → K) ++
      one .V_to_P (Fin (s + 1) → K) ++ one .P_to_V (Fin r → K) :=
  rfl

/-- **The conclusions of part (3) of the paper's `cor:tower`**: honest-verifier zero knowledge with
error `0` with respect to the uniform simulator (`uniformHVZK`, `thm:tree`, part (3), on the tree),
whose prover messages are `s` and `r` elements of `K` (`spec_eq`), with `r s = w` for
`|K| = 2^w` (`degree`). -/
structure Hvzk : Prop where
  /-- `thm:tree`, part (3), on the tree. -/
  uniformHVZK : (T.honest (cells := cells) (nc := nc) claims).UniformHVZK
  /-- The prover messages: `s`, then `r` elements of `K`. -/
  spec_eq : ((T.tree nc).ringSwitch (cells := cells) (towerClaims r s claims)).spec =
    MaskedRowReduction.noRounds ++ one .V_to_P (Fin nc → K) ++ one .P_to_V (Fin s → K) ++
      one .V_to_P (Fin (s + 1) → K) ++ one .P_to_V (Fin r → K)
  /-- `r = w/s`. -/
  degree : ∀ w, Fintype.card K = 2 ^ w → w ≠ 0 → s ∣ w → s * r = w

/-- **Paper `cor:tower`, part (3)**: when the prover draws the masks and chain elements of
`RS_sq(GF(2), S0)` and the mask entries of `RS_sub(S0, K)` from their honest distributions,
ring switching along `K ⊃ S0 ⊃ GF(2)` is honest-verifier zero knowledge with error `0` with respect
to the uniform simulator, whose prover messages are its `s + w/s` sent elements of `K`. -/
@[headline]
theorem hvzk : T.Hvzk (cells := cells) (nc := nc) claims where
  uniformHVZK := (T.tree nc).hvzk (towerClaims r s claims) (T.routes _) _ _ _ _ _
  spec_eq := T.spec_eq claims
  degree _ hK hw hs := T.mul_eq_of_card hK hw hs

end TowerSetup

end RingSwitching

end GordieHowe
