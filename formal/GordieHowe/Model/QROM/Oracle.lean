-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Model.QROM.Instability
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.DeriveFintype

@[expose] public section

/-!
# The domain-separated random oracle

The oracle of the Longfellow transcript in the model of Chiesa–Manohar–Spooner, "Succinct Arguments
in the Quantum Random Oracle Model" (CMS19, ePrint 2019/834; page numbers are the printed ones).
CMS19 uses one oracle `h : {0,1}^{2λ} → {0,1}^λ`; we use one oracle on a tagged query type, so the
four roles are disjoint by construction (domain separation). The quantum model is over the paper's
domain `{0,1}^m`, which `Query k kN kS L` enters through the injective encoding `Query.toBits`
(`GordieHowe/Model/QROM/QueryBits.lean`). The C++ separates the roles by tags (leaf `0x01`, node `0x02`,
transcript `0x00`; `kMerkleLeafTag` and `kMerkleNodeTag` in `lib/merkle/merkle_tree.h`) and expands
challenges with a customized cSHAKE256; matching the model is a correspondence obligation.

- `Byte` is `Fin 256` (Mathlib has no `Fintype UInt8`).
- `Digest k` is a `k`-byte string (`k = 48` at the QROM parameters, `k = 32` for SHA-256).
- `MerkleSalt kN` is a Merkle salt of `kN` bytes and `FiatShamirSalt kS` the per-proof Fiat–Shamir salt of `kS`
  bytes. The query type is generic in both lengths; the C++ has `kN = 2k` and `kS = k`
  (commit b90f5046).
- `Bytes L` is a byte string of length at most `L`, length-tagged, so the oracle domain
  is finite and the uniform oracle is a PMF.
- `Query k kN kS L` has the four roles: `leaf salt column` (a Merkle leaf, `H(salt ‖ column bytes)`,
  C++ `merkle_leaf_begin` and `BasicMerkleCommitment::commit` in `lib/merkle/merkle_commitment.h`,
  with a `2k`-byte salt), `node l r` (an inner Merkle node, `BasicDigest::hash2(L, R)` in
  `lib/merkle/merkle_tree.h`), `transcript prefix` (a Fiat–Shamir key) and `xof key salt` (a
  challenge stream from a key and the proof's Fiat–Shamir salt; `kS = 0` is the case without a salt:
  a salt of zero bytes carries no information).
- `Out k e` is the answer, a `k + e`-byte string stored as the pair (first `k` bytes,
  remaining `e` bytes). A hash-role answer is its first `k` bytes, `Out.digest`; an
  `xof` answer is the whole string, `Out.stream`. Storing the split as a product makes
  `n = k + e ≥ k` hold by construction and makes the digest marginal a projection.

Collisions for extraction are on digests: `collisionOn f` generalizes CMS19's
`P_col` (p. 32, `collision` in `GordieHowe/Model/QROM/Instability.lean`) to equality after a map
`f` of answers, and `digestCollision = collisionOn Out.digest`. Its instability is
at most `t / 2^(8k)` (`instab_digestCollision_le`), the analogue of Lemma 6.11.

`S(D)` (CMS19 Def 6.3, p. 31, the "half-preimages") becomes `halfPre digestsOf D`, the
digests occurring inside the recorded inputs: both children of a `node`, the `xof` key, and
`digestsOf prefix` for a `transcript` prefix, where the parse `digestsOf` is a parameter (fixed
with the transcript format). The Fiat–Shamir salt of an `xof` query is chosen by the prover, not
an oracle answer, and is not a half-preimage.
-/

namespace GordieHowe.QROM

open GordieHowe.IOP
open scoped ENNReal

/-- A byte. -/
abbrev Byte := Fin 256

/-- A `k`-byte digest. -/
abbrev Digest (k : ℕ) := Fin k → Byte

/-- A Merkle salt of `kN` bytes, hashed before the leaf's bytes (BCS16 p. 15 "salts"; CY24 `s_MT`).
The C++ salt has `kN = 2k` bytes, twice the digest length (`MerkleNonce::kLength = 2 · kDigestSize`,
`lib/merkle/merkle_commitment.h`, C++ b90f5046): 64 bytes at the ROM parameters (`k = 32`), 96 at
the QROM parameters (`k = 48`). -/
abbrev MerkleSalt (kN : ℕ) := Fin kN → Byte

/-- The Fiat–Shamir salt of `kS` bytes (CY24 Construction 25.1.1 p. 274, `τi`), chosen by the
prover, carried once in the proof, and part of every `xof` input. The C++ salt has `kS = k` bytes
(`λ = 8k` bits: 32 bytes at the ROM parameters, 48 at the QROM parameters; C++ b90f5046). `kS = 0` is the case without a salt
(`Fin 0 → Byte` has one element, and the transcript then has no salt write,
`TranscriptEncoding.saltBytes`). -/
abbrev FiatShamirSalt (kS : ℕ) := Fin kS → Byte

/-- **A byte string of length at most `L`**, tagged with its length. -/
@[ext]
structure Bytes (L : ℕ) where
  /-- The length. -/
  len : Fin (L + 1)
  /-- The bytes. -/
  data : Fin len → Byte

/-- A byte string is a dependent pair of its length and its bytes. -/
def Bytes.equivSigma (L : ℕ) : Bytes L ≃ Σ m : Fin (L + 1), Fin m → Byte where
  toFun b := ⟨b.len, b.data⟩
  invFun s := ⟨s.1, s.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance (L : ℕ) : DecidableEq (Bytes L) := (Bytes.equivSigma L).decidableEq

instance (L : ℕ) : Fintype (Bytes L) := Fintype.ofEquiv _ (Bytes.equivSigma L).symm

instance (L : ℕ) : Inhabited (Bytes L) := ⟨⟨0, Fin.elim0⟩⟩

/-- There are at most `256^(L + 1)` byte strings of length at most `L`. -/
theorem card_bytes_le (L : ℕ) : Fintype.card (Bytes L) ≤ 256 ^ (L + 1) := by
  rw [Fintype.card_congr (Bytes.equivSigma L)]
  have h : ∀ n, ∑ i ∈ Finset.range n, 256 ^ i ≤ 256 ^ n := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, pow_succ]
      omega
  simp only [Fintype.card_sigma, Fintype.card_fun, Fintype.card_fin]
  rw [Fin.sum_univ_eq_sum_range (fun i => 256 ^ i) (L + 1)]
  exact h _

/-- **A Merkle leaf**: a Merkle salt and the column bytes, hashed as `H(salt ‖ column)`
(`Query.leaf`). -/
@[ext]
structure MerkleLeaf (kN L : ℕ) where
  /-- The Merkle salt. -/
  salt : MerkleSalt kN
  /-- The column bytes. -/
  column : Bytes L
  deriving DecidableEq, Fintype

/-- **The children of an inner Merkle node**: its left and right child digests, hashed as
`H(left ‖ right)` (`Query.node`). -/
@[ext]
structure Children (k : ℕ) where
  /-- The left child's digest. -/
  left : Digest k
  /-- The right child's digest. -/
  right : Digest k
  deriving DecidableEq, Fintype

/-- The domain-separated oracle query, with `k`-byte digests,
`kN`-byte Merkle salts, `kS`-byte Fiat–Shamir salts and transcript inputs of at most `L` bytes. -/
inductive Query (k kN kS L : ℕ) where
  /-- A Merkle leaf `H(salt ‖ column)` with a Merkle salt (`merkle_leaf_begin` in
  `lib/merkle/merkle_commitment.h`). -/
  | leaf (salt : MerkleSalt kN) (column : Bytes L)
  /-- An inner Merkle node `H(l ‖ r)` (`BasicDigest::hash2` in `lib/merkle/merkle_tree.h`). -/
  | node (l r : Digest k)
  /-- A Fiat–Shamir key derivation from a transcript prefix. -/
  | transcript (pre : Bytes L)
  /-- A challenge stream expanded from a key and the proof's Fiat–Shamir salt. -/
  | xof (key : Digest k) (salt : FiatShamirSalt kS)
  deriving DecidableEq, Fintype

/-- **An oracle answer** of `k + e` bytes: its first `k` bytes, the digest of a hash-role answer,
and the remaining `e` bytes. -/
@[ext]
structure Out (k e : ℕ) where
  /-- The digest of a hash-role answer: the first `k` bytes. -/
  digest : Digest k
  /-- The remaining `e` bytes. -/
  rest : Fin e → Byte
  deriving DecidableEq, Fintype

namespace Out

variable {k e : ℕ}

instance : Inhabited (Out k e) := ⟨⟨fun _ => 0, fun _ => 0⟩⟩

/-- An answer is the pair of its digest and its remaining bytes. -/
def equivProd : Out k e ≃ Digest k × (Fin e → Byte) where
  toFun y := (y.digest, y.rest)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The whole `k + e`-byte answer, the challenge stream of an `xof` query. -/
def stream (y : Out k e) : Fin (k + e) → Byte := Fin.append y.digest y.rest

/-- An answer is its stream (`Fin.appendEquiv`). -/
def streamEquiv : Out k e ≃ (Fin (k + e) → Byte) := equivProd.trans (Fin.appendEquiv k e)

@[simp] theorem streamEquiv_apply (y : Out k e) : streamEquiv y = y.stream := rfl

theorem card_digest : Fintype.card (Digest k) = 2 ^ (8 * k) := by
  simp [pow_mul]

/-- An answer is `k + e` bytes: `|Out k e| = 2^(8(k + e))`, the range `{0,1}^n` of CMS19 at
`n = 8(k + e)`. -/
theorem card_eq_two_pow : Fintype.card (Out k e) = 2 ^ (8 * (k + e)) := by
  rw [Fintype.card_congr equivProd]
  simp [pow_mul, pow_add]

/-- `|Out k e| ≥ 2^(8k)`. -/
theorem two_pow_le_card (k e : ℕ) : 2 ^ (8 * k) ≤ Fintype.card (Out k e) := by
  rw [Fintype.card_congr equivProd, Fintype.card_prod, card_digest]
  exact Nat.le_mul_of_pos_right _ Fintype.card_pos

/-- The digest of a uniform answer is uniform: `Pr[digest y ∈ S] = |S| / 2^(8k)`. -/
theorem probUniform_digest_mem (S : Finset (Digest k)) :
    Pr[y ← Out k e : y.digest ∈ S] = S.card / 2 ^ (8 * k) := by
  classical
  rw [probUniform_eq_card_div]
  have hf : (Finset.univ.filter fun y : Out k e => y.digest ∈ S) =
      (S ×ˢ Finset.univ).map equivProd.symm.toEmbedding := by
    ext y
    rw [Finset.mem_filter, Finset.mem_map_equiv, Finset.mem_product]
    simp [equivProd]
  rw [hf, Finset.card_map, Finset.card_product, Fintype.card_congr equivProd, Fintype.card_prod,
    Finset.card_univ, Nat.cast_mul,
    Nat.cast_mul, ENNReal.mul_div_mul_right _ _ (by simp) (by simp), card_digest]
  norm_num

end Out

/-! ### Collisions after a map of answers -/

section CollisionOn

variable {X Y Z : Type*} [DecidableEq X] (f : Y → Z)

/-- Databases with two distinct inputs whose answers agree after `f`. `collisionOn id`
is CMS19's `P_col` (p. 32). -/
def collisionOn : Set (DB X Y) :=
  {D | ∃ x ∈ D, ∃ x' ∈ D, x ≠ x' ∧ (D.lookup x).map f = (D.lookup x').map f}

/-- The images under `f` of the answers of `D`. -/
def answerImages [DecidableEq Z] (D : DB X Y) : Finset Z :=
  D.keys.biUnion fun x => ((D.lookup x).map f).toFinset

variable {f}

theorem mem_answerImages [DecidableEq Z] {D : DB X Y} {z : Z} :
    z ∈ answerImages f D ↔ ∃ x ∈ D, (D.lookup x).map f = some z := by
  simp [answerImages, Finmap.mem_keys, Option.mem_toFinset, eq_comm]

theorem card_answerImages_le [DecidableEq Z] (D : DB X Y) : (answerImages f D).card ≤ D.size :=
  (Finset.card_biUnion_le).trans <| (Finset.sum_le_card_nsmul _ _ 1 fun x _ => by
    cases (D.lookup x).map f <;> simp).trans (by simp [DB.size])

theorem empty_notMem_collisionOn : (∅ : DB X Y) ∉ collisionOn f := by
  rintro ⟨x, hx, -⟩
  exact Finmap.notMem_empty hx

theorem extend_mem_collisionOn {D : DB X Y} (hD : D ∈ collisionOn f) {x : X} (hx : x ∉ D)
    (y : Y) : D.extend x y ∈ collisionOn f := by
  obtain ⟨a, ha, b, hb, hab, heq⟩ := hD
  refine ⟨a, DB.mem_extend.2 (Or.inr ha), b, DB.mem_extend.2 (Or.inr hb), hab, ?_⟩
  rw [DB.lookup_extend_of_ne (ne_of_mem_of_not_mem ha hx),
    DB.lookup_extend_of_ne (ne_of_mem_of_not_mem hb hx), heq]

/-- A database below a collision-free extension is collision-free. -/
theorem notMem_collisionOn_of_extend {D : DB X Y} {x : X} (hx : x ∉ D) {y : Y}
    (h : D.extend x y ∉ collisionOn f) : D ∉ collisionOn f :=
  fun hD => h (extend_mem_collisionOn hD hx y)

/-- A collision-free database extended at a new input has a collision after `f` only if
`f y` is already the image of an answer of `D`. -/
theorem mem_answerImages_of_extend_mem_collisionOn [DecidableEq Z] {D : DB X Y}
    (hD : D ∉ collisionOn f) {x : X} (hx : x ∉ D) {y : Y} (h : D.extend x y ∈ collisionOn f) :
    f y ∈ answerImages f D := by
  rw [mem_answerImages]
  obtain ⟨a, ha, b, hb, hab, heq⟩ := h
  rcases DB.mem_extend.1 ha with rfl | ha' <;> rcases DB.mem_extend.1 hb with rfl | hb'
  · exact absurd rfl hab
  · rw [DB.lookup_extend_self, DB.lookup_extend_of_ne (Ne.symm hab)] at heq
    exact ⟨b, hb', heq.symm⟩
  · rw [DB.lookup_extend_self, DB.lookup_extend_of_ne hab] at heq
    exact ⟨a, ha', heq⟩
  · rw [DB.lookup_extend_of_ne (ne_of_mem_of_not_mem ha' hx),
      DB.lookup_extend_of_ne (ne_of_mem_of_not_mem hb' hx)] at heq
    exact absurd ⟨a, ha', b, hb', hab, heq⟩ hD

variable [Fintype Y] [Nonempty Y] {t : ℕ} {c : ℝ≥0∞}

/-- If `f` of a uniform answer lands in any set `S` with probability at most `|S| / c`,
then `flip(P̄ → P, t) ≤ (t - 1) / c` for `P = collisionOn f` (CMS19 Lemma 6.11, p. 33). -/
theorem flipProb_compl_collisionOn_le
    (hf : ∀ S : Finset Z, Pr[y ← Y : f y ∈ S] ≤ S.card / c) :
    flipProb (collisionOn f : Set (DB X Y))ᶜ (collisionOn f) t ≤ ((t - 1 : ℕ) : ℝ≥0∞) / c := by
  classical
  refine flipProb_le fun D hD hs x hx => ?_
  calc Pr[y ← Y : D.extend x y ∈ collisionOn f]
      ≤ Pr[y ← Y : f y ∈ answerImages f D] :=
        probUniform_mono fun y hy => mem_answerImages_of_extend_mem_collisionOn hD hx hy
    _ ≤ (answerImages f D).card / c := hf _
    _ ≤ ((t - 1 : ℕ) : ℝ≥0∞) / c :=
        ENNReal.div_le_div_right (Nat.cast_le.2 ((card_answerImages_le D).trans (by omega))) _

theorem flipProb_collisionOn_compl :
    flipProb (collisionOn f : Set (DB X Y)) (collisionOn f)ᶜ t = 0 :=
  le_antisymm (flipProb_le fun _ hD _ _ hx =>
    (probUniform_eq_zero fun y hy => hy (extend_mem_collisionOn hD hx y)).le) bot_le

/-- The analogue of CMS19 Lemma 6.11 (p. 33) for collisions after `f`. -/
theorem instab_collisionOn_le (hf : ∀ S : Finset Z, Pr[y ← Y : f y ∈ S] ≤ S.card / c) :
    instab (collisionOn f : Set (DB X Y)) t ≤ ((t - 1 : ℕ) : ℝ≥0∞) / c :=
  max_le (flipProb_compl_collisionOn_le hf) (flipProb_collisionOn_compl.trans_le bot_le)

end CollisionOn

/-! ### Digest collisions -/

variable {k kN kS L e : ℕ}

/-- The oracle database of the domain-separated oracle. -/
abbrev ODB (k kN kS L e : ℕ) := DB (Query k kN kS L) (Out k e)

/-- Databases with two distinct recorded queries whose answers have the same digest. -/
def digestCollision : Set (ODB k kN kS L e) := collisionOn Out.digest

/-- CMS19 Lemma 6.11 (p. 33) for digest collisions: `I(P_col, t) ≤ (t - 1) / 2^(8k)`. -/
theorem instab_digestCollision_le' {t : ℕ} :
    instab (digestCollision : Set (ODB k kN kS L e)) t ≤ ((t - 1 : ℕ) : ℝ≥0∞) / 2 ^ (8 * k) :=
  instab_collisionOn_le fun S => (Out.probUniform_digest_mem S).le

/-- CMS19 Lemma 6.11 (p. 33) for digest collisions: `I(P_col, t) ≤ t / 2^(8k)`. -/
theorem instab_digestCollision_le {t : ℕ} :
    instab (digestCollision : Set (ODB k kN kS L e)) t ≤ (t : ℝ≥0∞) / 2 ^ (8 * k) :=
  instab_digestCollision_le'.trans (ENNReal.div_le_div_right (Nat.cast_le.2 (Nat.sub_le t 1)) _)

/-! ### Half-preimages -/

/-- The digests occurring inside a query: both children of a `node`, the key of an
`xof` (not its Fiat–Shamir salt), the parsed digests of a `transcript` prefix, and none for a `leaf`. -/
def Query.digests (digestsOf : Bytes L → Finset (Digest k)) : Query k kN kS L → Finset (Digest k)
  | .leaf _ _ => ∅
  | .node l r => {l, r}
  | .transcript p => digestsOf p
  | .xof key _ => {key}

/-- `S(D)` (CMS19 Def 6.3, p. 31), adapted to the tagged oracle: the digests occurring
inside the recorded inputs of `D`. -/
def halfPre (digestsOf : Bytes L → Finset (Digest k)) (D : ODB k kN kS L e) : Finset (Digest k) :=
  D.keys.biUnion (Query.digests digestsOf)

variable {digestsOf : Bytes L → Finset (Digest k)} {D : ODB k kN kS L e}

theorem mem_halfPre {u : Digest k} :
    u ∈ halfPre digestsOf D ↔ ∃ q ∈ D, u ∈ q.digests digestsOf := by
  simp [halfPre, Finmap.mem_keys]

theorem left_mem_halfPre {l r : Digest k} (h : Query.node l r ∈ D) :
    l ∈ halfPre digestsOf D := mem_halfPre.2 ⟨_, h, by simp [Query.digests]⟩

theorem right_mem_halfPre {l r : Digest k} (h : Query.node l r ∈ D) :
    r ∈ halfPre digestsOf D := mem_halfPre.2 ⟨_, h, by simp [Query.digests]⟩

theorem card_digests_le {c : ℕ} (hT : ∀ p, (digestsOf p).card ≤ c) (q : Query k kN kS L) :
    (q.digests digestsOf).card ≤ max 2 c := by
  cases q with
  | leaf => simp [Query.digests]
  | node l r => exact (Finset.card_le_two).trans (le_max_left _ _)
  | transcript p => exact (hT p).trans (le_max_right _ _)
  | xof => simp [Query.digests]

/-- `|S(D)| ≤ max 2 c · |D|`, where a transcript prefix contains at most `c` digests. -/
theorem card_halfPre_le {c : ℕ} (hT : ∀ p, (digestsOf p).card ≤ c) :
    (halfPre digestsOf D).card ≤ max 2 c * D.size :=
  Finset.card_biUnion_le.trans <|
    (Finset.sum_le_card_nsmul _ _ _ fun q _ => card_digests_le hT q).trans
      (by simp [DB.size, mul_comm])

section Extend

variable {q : Query k kN kS L} {y : Out k e}

/-- **Recording one entry adds at most the digests of its query to `S(D)`.** -/
theorem halfPre_extend_subset :
    halfPre digestsOf (D.extend q y) ⊆ halfPre digestsOf D ∪ q.digests digestsOf := by
  intro u hu
  obtain ⟨q', hq', hu'⟩ := mem_halfPre.1 hu
  rcases DB.mem_extend.1 hq' with rfl | hq''
  · exact Finset.mem_union_right _ hu'
  · exact Finset.mem_union_left _ (mem_halfPre.2 ⟨q', hq'', hu'⟩)

/-- `|S(D) ∪ digests(q)| ≤ max 2 c · (|D| + 1)`. -/
theorem card_halfPre_union_le {c : ℕ} (hT : ∀ p, (digestsOf p).card ≤ c) :
    (halfPre digestsOf D ∪ q.digests digestsOf).card ≤ max 2 c * (D.size + 1) :=
  (Finset.card_union_le _ _).trans (by
    have := card_halfPre_le (D := D) hT
    have := card_digests_le hT q
    rw [mul_add, mul_one]
    omega)

end Extend

/-! ### Merkle salts of `leaf` queries -/

/-- The Merkle salt of a `leaf` query, `none` for the other queries. -/
def Query.leafSalt : Query k kN kS L → Option (MerkleSalt kN)
  | .leaf ν _ => some ν
  | _ => none

/-! ### Recorded Fiat–Shamir salts -/

/-- The Fiat–Shamir salt of an `xof` query. -/
def Query.salt? : Query k kN kS L → Option (FiatShamirSalt kS)
  | .xof _ σ => some σ
  | _ => none

/-- The Fiat–Shamir salts of the recorded `xof` queries of `D`, one per query. -/
def recordedSalts (D : ODB k kN kS L e) : Multiset (FiatShamirSalt kS) := D.keys.val.filterMap Query.salt?

theorem mem_recordedSalts {D : ODB k kN kS L e} {σ : FiatShamirSalt kS} :
    σ ∈ recordedSalts D ↔ ∃ κ, Query.xof κ σ ∈ D := by
  constructor
  · intro h
    obtain ⟨q, hq, hσ⟩ := (Multiset.mem_filterMap _ _).1 h
    cases q with
    | xof κ σ' =>
      cases hσ
      exact ⟨κ, Finmap.mem_keys.1 hq⟩
    | _ => simp [Query.salt?] at hσ
  · rintro ⟨κ, hκ⟩
    exact (Multiset.mem_filterMap _ _).2 ⟨_, Finmap.mem_keys.2 hκ, rfl⟩

end GordieHowe.QROM
