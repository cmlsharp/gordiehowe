-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Sampler.Basic
public import GordieHowe.SPBCS.Sampler.Preimage

@[expose] public section

/-!
# Unranking the exact paths of a reader, and the preimage sampler of a reader's sampler

A `Reader.Unrank R` lists, for every length `j` and value `a`, the `j`-byte strings on which `R`
returns `a` having read exactly those bytes: `cnt j` of them (the same number for every value,
`exact_eq`), the `i`-th being `path j a i`. It is computable data with proofs, built along the
reader's combinators (`bytes`, `map` along an equivalence, `prod`, `pi`, `rej` with an unranking of
the accepted and rejected attempts, `limit`, `retry` with a list of the rejected values).

**The preimage sampler** (`Unrank.preimage`): the streams of `N` bytes on which `R` returns `a` are
an exact path of some length `j ≤ N` followed by `N - j` free bytes (`Reader.card_sampleOf_eq`).
They are numbered `0, …, F - 1` with `F = ∑ j ≤ N, cnt j · 256^(N - j)`: the number `i` falls in
the block of one length `j` (`pick`), its offset in the block is a path number and a number of
`N - j` little-endian bytes. The map from numbers to streams is injective and lands in the
fibre, which has `F` elements, so it is a bijection onto the fibre: uniform coins below `F` give
a uniform stream of the fibre.

Cost: the counts `cnt j` for `j ≤ N` are computed by the combinators' recursions (sums of products
of counts for sequencing); unranking one stream costs `O(N)` arithmetic operations on numbers below
`256^N` per combinator.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

namespace Reader

variable {α β : Type}

/-! ### Numbers as bytes and blocks -/

/-- The `m` little-endian bytes of `t` (base 256). -/
def bytesOfNat : ℕ → ℕ → List Byte
  | 0, _ => []
  | m + 1, t => (⟨t % 256, Nat.mod_lt _ (by norm_num)⟩ : Byte) :: bytesOfNat m (t / 256)

@[simp] theorem length_bytesOfNat (m t : ℕ) : (bytesOfNat m t).length = m := by
  induction m generalizing t with
  | zero => rfl
  | succ m ih => simp [bytesOfNat, ih]

theorem bytesOfNat_injective {m t t' : ℕ} (ht : t < 256 ^ m) (ht' : t' < 256 ^ m)
    (h : bytesOfNat m t = bytesOfNat m t') : t = t' := by
  induction m generalizing t t' with
  | zero =>
    simp only [pow_zero, Nat.lt_one_iff] at ht ht'
    rw [ht, ht']
  | succ m ih =>
    simp only [bytesOfNat, List.cons.injEq, Fin.mk.injEq] at h
    have hd := ih (Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact ht))
      (Nat.div_lt_of_lt_mul (by rw [← pow_succ']; exact ht')) h.2
    rw [← Nat.div_add_mod t 256, ← Nat.div_add_mod t' 256, hd, h.1]

/-- **The block of a number** among blocks of sizes `w j` for `j` in the list `l`, in order: the
first `j` whose block contains `i`, and the offset of `i` in it. -/
def pick (w : ℕ → ℕ) : List ℕ → ℕ → ℕ × ℕ
  | [], i => (0, i)
  | j :: js, i => if i < w j then (j, i) else pick w js (i - w j)

theorem pick_mem (w : ℕ → ℕ) : ∀ (l : List ℕ) (i : ℕ), i < (l.map w).sum →
    (pick w l i).1 ∈ l ∧ (pick w l i).2 < w (pick w l i).1
  | [], i, h => by simp at h
  | j :: js, i, h => by
    simp only [pick]
    split_ifs with hi
    · exact ⟨List.mem_cons_self .., hi⟩
    · simp only [List.map_cons, List.sum_cons] at h
      obtain ⟨h1, h2⟩ := pick_mem w js (i - w j) (by omega)
      exact ⟨List.mem_cons_of_mem _ h1, h2⟩

theorem pick_injective (w : ℕ → ℕ) : ∀ (l : List ℕ), l.Nodup → ∀ {i i' : ℕ},
    i < (l.map w).sum → i' < (l.map w).sum → pick w l i = pick w l i' → i = i'
  | [], _, _, _, h, _, _ => by simp at h
  | j :: js, hl, i, i', h, h', he => by
    simp only [List.map_cons, List.sum_cons] at h h'
    have hj : j ∉ js := (List.nodup_cons.1 hl).1
    simp only [pick] at he
    split_ifs at he with hi hi'
    · exact (Prod.mk.inj he).2
    · have := (pick_mem w js (i' - w j) (by omega)).1
      rw [← he] at this
      exact absurd this hj
    · have := (pick_mem w js (i - w j) (by omega)).1
      rw [he] at this
      exact absurd this hj
    · have := pick_injective w js (List.nodup_cons.1 hl).2 (by omega) (by omega) he
      omega


theorem sum_map_range (f : ℕ → ℕ) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

/-! ### Unranking -/

/-- **An unranking of the exact paths of a reader** (module docstring). -/
structure Unrank (R : Reader α) where
  /-- The number of exact paths of each length, for every value. -/
  cnt : ℕ → ℕ
  /-- The `i`-th exact path of length `j` returning `a`. -/
  path : ℕ → α → ℕ → List Byte
  length_path : ∀ j a i, i < cnt j → (path j a i).length = j
  run_path : ∀ j a i rest, i < cnt j → R.run (path j a i ++ rest) = some (a, rest)
  path_inj : ∀ j a i i', i < cnt j → i' < cnt j → path j a i = path j a i' → i = i'
  exact_eq : ∀ [DecidableEq α] j a, R.exact j a = cnt j

namespace Unrank

variable {R : Reader α} (U : R.Unrank)

/-- The length of the stream read by `R` is recovered from what it leaves unread. -/
theorem eq_of_run_eq {j j' : ℕ} {a : α} {i i' : ℕ} (hi : i < U.cnt j) (hi' : i' < U.cnt j')
    {rest rest' : List Byte} (h : U.path j a i ++ rest = U.path j' a i' ++ rest') :
    rest = rest' := by
  have h1 := U.run_path j a i rest hi
  have h2 := U.run_path j' a i' rest' hi'
  rw [h] at h1
  rw [h1] at h2
  exact (Prod.mk.inj (Option.some_inj.1 h2)).2

/-! #### The fibre of a stream length -/

variable (N : ℕ)

/-- The size of the block of exact paths of length `j` in the fibre of `N`-byte streams. -/
def blockSize (j : ℕ) : ℕ := U.cnt j * 256 ^ (N - j)

/-- **The number of `N`-byte streams on which `R` returns a given value**. -/
def fiberCnt : ℕ := ((List.range (N + 1)).map (U.blockSize N)).sum

/-- **The `i`-th stream of the fibre of `a`**, as a list of `N` bytes (module docstring). -/
def fiberList (a : α) (i : ℕ) : List Byte :=
  let p := pick (U.blockSize N) (List.range (N + 1)) i
  U.path p.1 a (p.2 / 256 ^ (N - p.1)) ++ bytesOfNat (N - p.1) (p.2 % 256 ^ (N - p.1))

/-- **The `i`-th stream of the fibre of `a`** as a stream. -/
def fiberStream (a : α) (i : ℕ) : Fin N → Byte := fun p => (U.fiberList N a i).getD p 0

variable {N}

theorem pick_spec {i : ℕ} (hi : i < U.fiberCnt N) :
    (pick (U.blockSize N) (List.range (N + 1)) i).1 ≤ N ∧
      (pick (U.blockSize N) (List.range (N + 1)) i).2 / 256 ^ (N - (pick (U.blockSize N)
        (List.range (N + 1)) i).1) < U.cnt (pick (U.blockSize N) (List.range (N + 1)) i).1 := by
  obtain ⟨h1, h2⟩ := pick_mem (U.blockSize N) (List.range (N + 1)) i hi
  refine ⟨Nat.lt_succ_iff.1 (List.mem_range.1 h1), ?_⟩
  exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2)

theorem length_fiberList (a : α) {i : ℕ} (hi : i < U.fiberCnt N) :
    (U.fiberList N a i).length = N := by
  obtain ⟨hj, hp⟩ := U.pick_spec hi
  simp only [fiberList, List.length_append, length_bytesOfNat, U.length_path _ _ _ hp]
  omega

theorem ofFn_fiberStream (a : α) {i : ℕ} (hi : i < U.fiberCnt N) :
    List.ofFn (U.fiberStream N a i) = U.fiberList N a i := by
  refine List.ext_getElem (by simp [U.length_fiberList a hi]) fun p h1 h2 => ?_
  simp [fiberStream, List.getElem?_eq_getElem h2]

theorem sampleOf_fiberStream (a : α) {i : ℕ} (hi : i < U.fiberCnt N) :
    R.sampleOf (U.fiberStream N a i) = some a := by
  obtain ⟨-, hp⟩ := U.pick_spec hi
  simp only [sampleOf, U.ofFn_fiberStream a hi, fiberList, U.run_path _ _ _ _ hp, Option.map_some]

theorem fiberStream_injective (a : α) {i i' : ℕ} (hi : i < U.fiberCnt N) (hi' : i' < U.fiberCnt N)
    (h : U.fiberStream N a i = U.fiberStream N a i') : i = i' := by
  have hl : U.fiberList N a i = U.fiberList N a i' := by
    rw [← U.ofFn_fiberStream a hi, ← U.ofFn_fiberStream a hi', h]
  have key : pick (U.blockSize N) (List.range (N + 1)) i =
      pick (U.blockSize N) (List.range (N + 1)) i' := by
    obtain ⟨hj, hp⟩ := U.pick_spec hi
    obtain ⟨hj', hp'⟩ := U.pick_spec hi'
    simp only [fiberList] at hl
    generalize pick (U.blockSize N) (List.range (N + 1)) i = P at hl hp hj ⊢
    generalize pick (U.blockSize N) (List.range (N + 1)) i' = P' at hl hp' hj' ⊢
    obtain ⟨j, r⟩ := P
    obtain ⟨j', r'⟩ := P'
    dsimp only at hl hp hp' hj hj' ⊢
    have htail := U.eq_of_run_eq hp hp' hl
    have hjj : j = j' := by
      have := congrArg List.length htail
      simp only [length_bytesOfNat] at this
      omega
    subst hjj
    have hpath := List.append_inj_left hl (by rw [U.length_path _ _ _ hp, U.length_path _ _ _ hp'])
    have hq := U.path_inj _ _ _ _ hp hp' hpath
    have hm := bytesOfNat_injective (Nat.mod_lt _ (by positivity)) (Nat.mod_lt _ (by positivity))
      htail
    have hrr : r = r' := by
      rw [← Nat.div_add_mod r (256 ^ (N - j)), ← Nat.div_add_mod r' (256 ^ (N - j)), hq, hm]
    rw [hrr]
  exact pick_injective (U.blockSize N) _ List.nodup_range hi hi' key

/-- **The fibre has `fiberCnt N` streams** (`Reader.card_sampleOf_eq`). -/
theorem card_fibre [DecidableEq α] (a : α) :
    (Finset.univ.filter fun s : Fin N → Byte => R.sampleOf s = some a).card = U.fiberCnt N := by
  rw [card_sampleOf_eq, fiberCnt, sum_map_range]
  exact Finset.sum_congr rfl fun j _ => by rw [U.exact_eq, blockSize]

end Unrank

/-- `exact` does not depend on the decidable equality used. -/
theorem exact_inst (R : Reader α) (i i' : DecidableEq α) : @exact α i R = @exact α i' R := by
  congr; exact Subsingleton.elim _ _

/-! ### Running on a prefix -/

theorem run_bytes_append (b : ℕ) (v : Fin b → Byte) (rest : List Byte) :
    (bytes b).run (List.ofFn v ++ rest) = some (v, rest) := by
  rw [run_bytes, dif_pos (by simp)]
  congr 2
  · funext i
    simp [List.getElem_append_left]
  · simp

/-- **A reader that returns `a` on `p` followed by anything returns it within a cut-off of at least
`p`'s length.** -/
theorem run_limit_append : ∀ (R : Reader α) (n : ℕ) (p rest : List Byte) (a : α), p.length ≤ n →
    (∀ rest', R.run (p ++ rest') = some (a, rest')) → (R.limit n).run (p ++ rest) = some (a, rest)
  | .done a', n, p, rest, a, _, h => by
    have h0 := h []
    simp only [run, List.append_nil, Option.some.injEq, Prod.mk.injEq] at h0
    obtain ⟨rfl, rfl⟩ := h0
    cases n <;> simpa [limit, run] using h rest
  | .fail, _, _, _, _, _, h => by simpa [run] using h []
  | .read f, n, [], rest, a, _, h => by simpa [run] using h []
  | .read f, 0, x :: p, rest, a, hp, _ => by simp at hp
  | .read f, n + 1, x :: p, rest, a, hp, h => by
    simp only [limit, List.cons_append, run]
    exact run_limit_append (f x) n p rest a (by simpa using hp) fun rest' => by
      simpa [run] using h rest'

namespace Unrank

/-! ### The combinators -/

/-- **A constant reader at a type with one element**: one path, the empty one. -/
def done [Subsingleton α] (a : α) : (Reader.done a).Unrank where
  cnt j := if j = 0 then 1 else 0
  path _ _ _ := []
  length_path j _ i hi := by split_ifs at hi with h <;> simp_all
  run_path j b i rest hi := by simp [run, Subsingleton.elim a b]
  path_inj j _ i i' hi hi' _ := by split_ifs at hi hi' <;> omega
  exact_eq j b := by cases j <;> simp [exact, Subsingleton.elim a b]

/-- **Reading `b` bytes**: one path, the bytes of the value. -/
def bytes (b : ℕ) : (Reader.bytes b).Unrank where
  cnt j := if j = b then 1 else 0
  path _ v _ := List.ofFn v
  length_path j v i hi := by
    split_ifs at hi with h
    · simp [h]
    · omega
  run_path j v i rest _ := run_bytes_append b v rest
  path_inj j _ i i' hi hi' _ := by split_ifs at hi hi' <;> omega
  exact_eq j v := by convert exact_bytes b j v

/-- **A reader read through an equivalence**: the paths of the preimage value. -/
def map [Fintype α] {R : Reader α} (U : R.Unrank) (e : α ≃ β) : (R.map e).Unrank where
  cnt := U.cnt
  path j c i := U.path j (e.symm c) i
  length_path j c i hi := U.length_path _ _ _ hi
  run_path j c i rest hi := by rw [run_map, U.run_path _ _ _ _ hi]; simp
  path_inj j c := U.path_inj j (e.symm c)
  exact_eq j c := by
    classical
    rw [exact_map_equiv, U.exact_eq]

/-- **A reader cut off after `n` bytes**: the paths of length at most `n`. -/
def limit {R : Reader α} (U : R.Unrank) (n : ℕ) : (R.limit n).Unrank where
  cnt j := if j ≤ n then U.cnt j else 0
  path := U.path
  length_path j a i hi := U.length_path j a i (by split_ifs at hi <;> omega)
  run_path j a i rest hi := by
    split_ifs at hi with hj
    · exact run_limit_append R n _ rest a (by rw [U.length_path _ _ _ hi]; exact hj)
        fun rest' => U.run_path j a i rest' hi
    · omega
  path_inj j a i i' hi hi' := U.path_inj j a i i' (by split_ifs at hi <;> omega)
    (by split_ifs at hi' <;> omega)
  exact_eq j a := by rw [exact_limit, U.exact_eq]

section Prod

variable {R : Reader α} {R' : Reader β} (U : R.Unrank) (U' : R'.Unrank)

/-- The block sizes of the paths of length `j` of two readers one after the other: the first
reads `i` bytes. -/
def prodBlock (j i : ℕ) : ℕ := U.cnt i * U'.cnt (j - i)

theorem prod_spec {j idx : ℕ} (h : idx < ((List.range (j + 1)).map (prodBlock U U' j)).sum) :
    (pick (prodBlock U U' j) (List.range (j + 1)) idx).1 ≤ j ∧
      (pick (prodBlock U U' j) (List.range (j + 1)) idx).2 /
        U'.cnt (j - (pick (prodBlock U U' j) (List.range (j + 1)) idx).1) <
          U.cnt (pick (prodBlock U U' j) (List.range (j + 1)) idx).1 ∧
      (pick (prodBlock U U' j) (List.range (j + 1)) idx).2 %
        U'.cnt (j - (pick (prodBlock U U' j) (List.range (j + 1)) idx).1) <
          U'.cnt (j - (pick (prodBlock U U' j) (List.range (j + 1)) idx).1) := by
  obtain ⟨h1, h2⟩ := pick_mem _ _ idx h
  simp only [prodBlock] at h2
  have hpos : 0 < U'.cnt (j - (pick (prodBlock U U' j) (List.range (j + 1)) idx).1) :=
    Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at h2; omega
  exact ⟨Nat.lt_succ_iff.1 (List.mem_range.1 h1),
    Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact h2), Nat.mod_lt _ hpos⟩

/-- **Two readers one after the other**: the paths of the first of some length, then of the
second for the rest. -/
def prod [Fintype α] [Fintype β] : (R.prod R').Unrank where
  cnt j := ((List.range (j + 1)).map (prodBlock U U' j)).sum
  path j ab idx :=
    let p := pick (prodBlock U U' j) (List.range (j + 1)) idx
    U.path p.1 ab.1 (p.2 / U'.cnt (j - p.1)) ++ U'.path (j - p.1) ab.2 (p.2 % U'.cnt (j - p.1))
  length_path j ab idx h := by
    obtain ⟨hj, h1, h2⟩ := prod_spec U U' h
    simp only [List.length_append, U.length_path _ _ _ h1, U'.length_path _ _ _ h2]
    omega
  run_path j ab idx rest h := by
    obtain ⟨hj, h1, h2⟩ := prod_spec U U' h
    simp only [Reader.prod, run_bind, List.append_assoc, U.run_path _ _ _ _ h1, Option.bind_some,
      run_map, U'.run_path _ _ _ _ h2, Option.map_some]
  path_inj j ab idx idx' h h' he := by
    obtain ⟨hj, h1, h2⟩ := prod_spec U U' h
    obtain ⟨hj', h1', h2'⟩ := prod_spec U U' h'
    refine pick_injective _ _ List.nodup_range h h' ?_
    simp only at he
    generalize pick (prodBlock U U' j) (List.range (j + 1)) idx = P at he h1 h2 hj ⊢
    generalize pick (prodBlock U U' j) (List.range (j + 1)) idx' = P' at he h1' h2' hj' ⊢
    obtain ⟨i, r⟩ := P
    obtain ⟨i', r'⟩ := P'
    dsimp only at he h1 h2 hj h1' h2' hj' ⊢
    have hsnd := U.eq_of_run_eq h1 h1' (by simpa using he)
    have hii : i = i' := by
      have := congrArg List.length hsnd
      rw [U'.length_path _ _ _ h2, U'.length_path _ _ _ h2'] at this
      omega
    subst hii
    have hfst := List.append_inj_left he (by rw [U.length_path _ _ _ h1, U.length_path _ _ _ h1'])
    have hq := U.path_inj _ _ _ _ h1 h1' hfst
    have hm := U'.path_inj _ _ _ _ h2 h2' hsnd
    rw [← Nat.div_add_mod r (U'.cnt (j - i)), ← Nat.div_add_mod r' (U'.cnt (j - i)), hq, hm]
  exact_eq j ab := by
    obtain ⟨a, b⟩ := ab
    classical
    calc (R.prod R').exact j (a, b) =
          ∑ i ∈ Finset.range (j + 1), R.exact i a * R'.exact (j - i) b := by
          convert exact_prod R R' j a b
      _ = _ := by
          rw [sum_map_range]
          exact Finset.sum_congr rfl fun i _ => by rw [U.exact_eq, U'.exact_eq]; rfl

end Prod


/-- **A tuple of readers one after the other** (`Reader.pi`): the empty path, or the first reader
followed by the rest, read through `Fin.consEquiv`. -/
def pi : {k : ℕ} → {β : Fin k → Type} → [∀ i, Fintype (β i)] → {R : (i : Fin k) → Reader (β i)} →
    (∀ i, (R i).Unrank) → (Reader.pi R).Unrank
  | 0, _, _, _, _ => done _
  | _ + 1, β, _, _, U => ((U 0).prod (pi fun i => U i.succ)).map (Fin.consEquiv β)

section Rej

variable {b : ℕ}

/-- **An unranking of the attempts of a rejection loop**: the `nRej` rejected attempts, and for
every value the `nAcc` attempts accepted with it. -/
structure ChunkUnrank (acc : (Fin b → Byte) → Option α) where
  /-- The number of rejected attempts. -/
  nRej : ℕ
  /-- The `i`-th rejected attempt. -/
  rejChunk : ℕ → Fin b → Byte
  rej_none : ∀ i, i < nRej → acc (rejChunk i) = none
  rej_inj : ∀ i i', i < nRej → i' < nRej → rejChunk i = rejChunk i' → i = i'
  card_rej : (Finset.univ.filter fun v => acc v = none).card = nRej
  /-- The number of attempts accepted with each value. -/
  nAcc : ℕ
  /-- The `i`-th attempt accepted with the value `a`. -/
  accChunk : α → ℕ → Fin b → Byte
  acc_some : ∀ a i, i < nAcc → acc (accChunk a i) = some a
  acc_inj : ∀ a i i', i < nAcc → i' < nAcc → accChunk a i = accChunk a i' → i = i'
  card_acc : ∀ [DecidableEq α] a, (Finset.univ.filter fun v => acc v = some a).card = nAcc

variable {acc : (Fin b → Byte) → Option α} (C : ChunkUnrank acc)

namespace ChunkUnrank

/-- The number of exact paths of length `j` of `rej acc t`. -/
def rejCnt : ℕ → ℕ → ℕ
  | 0, _ => 0
  | t + 1, j => if b ≤ j then C.nRej * rejCnt t (j - b) + (if j = b then C.nAcc else 0) else 0

/-- The `i`-th exact path of length `j` of `rej acc t` returning `a`: a rejected attempt and a path
of `rej acc (t - 1)`, or an accepted attempt. -/
def rejPath : ℕ → ℕ → α → ℕ → List Byte
  | 0, _, _, _ => []
  | t + 1, j, a, i =>
    if i < C.nRej * rejCnt C t (j - b) then
      List.ofFn (C.rejChunk (i / rejCnt C t (j - b))) ++ rejPath t (j - b) a (i % rejCnt C t (j - b))
    else List.ofFn (C.accChunk a (i - C.nRej * rejCnt C t (j - b)))

theorem rejCnt_succ_pos {t j i : ℕ} (h : i < rejCnt C (t + 1) j) : b ≤ j := by
  simp only [rejCnt] at h
  split_ifs at h with hb <;> first | assumption | exact absurd h (Nat.not_lt_zero _)

theorem rej_branch {t j i : ℕ} (h : i < rejCnt C (t + 1) j) (hi : i < C.nRej * rejCnt C t (j - b)) :
    i / rejCnt C t (j - b) < C.nRej ∧ i % rejCnt C t (j - b) < rejCnt C t (j - b) := by
  have hpos : 0 < rejCnt C t (j - b) := Nat.pos_of_ne_zero fun h0 => by
    rw [h0, mul_zero] at hi; omega
  exact ⟨Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact hi), Nat.mod_lt _ hpos⟩

theorem acc_branch {t j i : ℕ} (h : i < rejCnt C (t + 1) j)
    (hi : ¬ i < C.nRej * rejCnt C t (j - b)) :
    j = b ∧ i - C.nRej * rejCnt C t (j - b) < C.nAcc := by
  simp only [rejCnt] at h
  split_ifs at h with hb hj
  · exact ⟨hj, by omega⟩
  · omega
  · exact absurd h (Nat.not_lt_zero _)

theorem length_rejPath : ∀ (t j : ℕ) (a : α) (i : ℕ), i < rejCnt C t j →
    (rejPath C t j a i).length = j
  | 0, _, _, _, h => by simp [rejCnt] at h
  | t + 1, j, a, i, h => by
    have hb := C.rejCnt_succ_pos h
    simp only [rejPath]
    split_ifs with hi
    · obtain ⟨-, h2⟩ := C.rej_branch h hi
      simp only [List.length_append, List.length_ofFn, length_rejPath t _ a _ h2]
      omega
    · obtain ⟨hj, -⟩ := C.acc_branch h hi
      simp [hj]

theorem run_rejPath : ∀ (t j : ℕ) (a : α) (i : ℕ) (rest : List Byte), i < rejCnt C t j →
    (Reader.rej acc t).run (rejPath C t j a i ++ rest) = some (a, rest)
  | 0, _, _, _, _, h => by simp [rejCnt] at h
  | t + 1, j, a, i, rest, h => by
    simp only [rejPath, Reader.rej]
    split_ifs with hi
    · obtain ⟨h1, h2⟩ := C.rej_branch h hi
      rw [run_bind, List.append_assoc, run_bytes_append, Option.bind_some, C.rej_none _ h1]
      exact run_rejPath t _ a _ rest h2
    · obtain ⟨-, h2⟩ := C.acc_branch h hi
      rw [run_bind, run_bytes_append, Option.bind_some, C.acc_some _ _ h2]
      rfl

theorem rejPath_inj : ∀ (t j : ℕ) (a : α) (i i' : ℕ), i < rejCnt C t j → i' < rejCnt C t j →
    rejPath C t j a i = rejPath C t j a i' → i = i'
  | 0, _, _, _, _, h, _, _ => by simp [rejCnt] at h
  | t + 1, j, a, i, i', h, h', he => by
    have hrun := C.run_rejPath (t + 1) j a i [] h
    have hrun' := C.run_rejPath (t + 1) j a i' [] h'
    simp only [rejPath] at he
    by_cases hi : i < C.nRej * rejCnt C t (j - b) <;>
      by_cases hi' : i' < C.nRej * rejCnt C t (j - b) <;>
      simp only [hi, hi', if_true, if_false] at he
    · obtain ⟨h1, h2⟩ := C.rej_branch h hi
      obtain ⟨h1', h2'⟩ := C.rej_branch h' hi'
      have hc := List.append_inj he (by simp)
      have hq := C.rej_inj _ _ h1 h1' (List.ofFn_injective hc.1)
      have hm := rejPath_inj t _ a _ _ h2 h2' hc.2
      rw [← Nat.div_add_mod i (rejCnt C t (j - b)), ← Nat.div_add_mod i' (rejCnt C t (j - b)), hq, hm]
    · obtain ⟨h1, -⟩ := C.rej_branch h hi
      obtain ⟨hj, h2'⟩ := C.acc_branch h' hi'
      have hc : C.rejChunk (i / rejCnt C t (j - b)) =
          C.accChunk a (i' - C.nRej * rejCnt C t (j - b)) := by
        have := congrArg (List.take b) he
        rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp [hj])] at this
        rw [List.take_of_length_le (by simp)] at this
        exact List.ofFn_injective this
      have := C.rej_none _ h1
      rw [hc, C.acc_some _ _ h2'] at this
      exact absurd this (by simp)
    · obtain ⟨hj, h2⟩ := C.acc_branch h hi
      obtain ⟨h1', -⟩ := C.rej_branch h' hi'
      have hc : C.accChunk a (i - C.nRej * rejCnt C t (j - b)) =
          C.rejChunk (i' / rejCnt C t (j - b)) := by
        have := congrArg (List.take b) he
        rw [List.take_append_of_le_length (by simp), List.take_of_length_le (by simp [hj])] at this
        rw [List.take_of_length_le (by simp)] at this
        exact List.ofFn_injective this
      have := C.rej_none _ h1'
      rw [← hc, C.acc_some _ _ h2] at this
      exact absurd this (by simp)
    · obtain ⟨-, h2⟩ := C.acc_branch h hi
      obtain ⟨-, h2'⟩ := C.acc_branch h' hi'
      have := C.acc_inj a _ _ h2 h2' (List.ofFn_injective he)
      omega

theorem exact_rej [DecidableEq α] : ∀ (t j : ℕ) (a : α), (Reader.rej acc t).exact j a = rejCnt C t j
  | 0, j, a => by simp [Reader.rej, exact, rejCnt]
  | t + 1, j, a => by
    rw [exact_rej_succ, rejCnt, exact_rej t, C.card_rej, C.card_acc]

end ChunkUnrank

/-- **A rejection loop** with an unranking of its attempts: the rejected attempts, then an accepted
one. -/
def rej (t : ℕ) : (Reader.rej acc t).Unrank where
  cnt := C.rejCnt t
  path := C.rejPath t
  length_path := C.length_rejPath t
  run_path := C.run_rejPath t
  path_inj := C.rejPath_inj t
  exact_eq j a := C.exact_rej t j a

end Rej

end Unrank

end Reader


namespace Rejection

open Reader Reader.Unrank

/-- The `b` little-endian bytes of `x` modulo `256^b`. -/
def chunkOf (b x : ℕ) : Fin b → Byte :=
  finFunctionFinEquiv.symm ⟨x % 256 ^ b, Nat.mod_lt _ (by positivity)⟩

theorem leNat_chunkOf (b x : ℕ) : leNat (chunkOf b x) = x % 256 ^ b := by
  simp [leNat, chunkOf]

theorem chunkOf_injective {b x y : ℕ} (hx : x < 256 ^ b) (hy : y < 256 ^ b)
    (h : chunkOf b x = chunkOf b y) : x = y := by
  have := congrArg leNat h
  rwa [leNat_chunkOf, leNat_chunkOf, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem pow_split {b bits : ℕ} (hbits : bits ≤ 8 * b) :
    256 ^ b = 2 ^ bits * 2 ^ (8 * b - bits) := by
  rw [← pow_add, Nat.add_sub_cancel' hbits, pow_mul]; norm_num

/-- The `i`-th number whose low `bits` bits are at least `m`, below `256^b`: low part
`m + i mod (2^bits - m)`, high part `i / (2^bits - m)`. -/
def rejNum (bits m i : ℕ) : ℕ := m + i % (2 ^ bits - m) + i / (2 ^ bits - m) * 2 ^ bits

theorem rejNum_spec {b bits m i : ℕ} (hbits : bits ≤ 8 * b)
    (hi : i < (2 ^ bits - m) * 2 ^ (8 * b - bits)) :
    rejNum bits m i < 256 ^ b ∧ rejNum bits m i % 2 ^ bits = m + i % (2 ^ bits - m) ∧
      rejNum bits m i / 2 ^ bits = i / (2 ^ bits - m) ∧ m + i % (2 ^ bits - m) < 2 ^ bits := by
  have hpos : 0 < 2 ^ bits - m := Nat.pos_of_ne_zero fun h => by rw [h, zero_mul] at hi; omega
  have hr : i % (2 ^ bits - m) < 2 ^ bits - m := Nat.mod_lt _ hpos
  have hq : i / (2 ^ bits - m) < 2 ^ (8 * b - bits) := Nat.div_lt_of_lt_mul hi
  have hlow : m + i % (2 ^ bits - m) < 2 ^ bits := by omega
  refine ⟨?_, ?_, ?_, hlow⟩
  · rw [pow_split hbits, rejNum]
    calc m + i % (2 ^ bits - m) + i / (2 ^ bits - m) * 2 ^ bits
        < 2 ^ bits + i / (2 ^ bits - m) * 2 ^ bits := by omega
      _ = (i / (2 ^ bits - m) + 1) * 2 ^ bits := by ring
      _ ≤ 2 ^ (8 * b - bits) * 2 ^ bits := Nat.mul_le_mul_right _ hq
      _ = _ := mul_comm _ _
  · rw [rejNum, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlow]
  · rw [rejNum, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt hlow, zero_add]

theorem add_mul_lt_pow {b bits a q : ℕ} (hbits : bits ≤ 8 * b) (ha : a < 2 ^ bits)
    (hq : q < 2 ^ (8 * b - bits)) : a + q * 2 ^ bits < 256 ^ b := by
  rw [pow_split hbits]
  calc a + q * 2 ^ bits < 2 ^ bits + q * 2 ^ bits := by omega
    _ = (q + 1) * 2 ^ bits := by ring
    _ ≤ 2 ^ (8 * b - bits) * 2 ^ bits := Nat.mul_le_mul_right _ hq
    _ = _ := mul_comm _ _

/-- The value of an attempt `a + q · 2^bits`: its low `bits` bits are `a`, its high bits `q`. -/
theorem leNat_chunkOf_add_mul {b bits a q : ℕ} (hbits : bits ≤ 8 * b) (ha : a < 2 ^ bits)
    (hq : q < 2 ^ (8 * b - bits)) :
    leNat (chunkOf b (a + q * 2 ^ bits)) % 2 ^ bits = a ∧
      leNat (chunkOf b (a + q * 2 ^ bits)) / 2 ^ bits = q := by
  rw [leNat_chunkOf, Nat.mod_eq_of_lt (add_mul_lt_pow hbits ha hq), Nat.add_mul_mod_self_right,
    Nat.mod_eq_of_lt ha, Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt ha, zero_add]
  exact ⟨rfl, rfl⟩

/-- **The attempts of `nat`** (`acc b bits m`): the rejected attempts are the numbers whose low
`bits` bits are at least `m` (`rejNum`), the attempts accepted with `a` the numbers `a + i · 2^bits`.

Cost: one division and one multiplication on numbers below `256^b` per attempt. -/
def natChunk {b bits m : ℕ} (hbits : bits ≤ 8 * b) (hm : m ≤ 2 ^ bits) :
    ChunkUnrank (acc b bits m) where
  nRej := (2 ^ bits - m) * 2 ^ (8 * b - bits)
  rejChunk i := chunkOf b (rejNum bits m i)
  rej_none i hi := by
    obtain ⟨hlt, hmod, -, -⟩ := rejNum_spec hbits hi
    unfold acc
    rw [dif_neg]
    rw [leNat_chunkOf, Nat.mod_eq_of_lt hlt, hmod]
    omega
  rej_inj i i' hi hi' h := by
    obtain ⟨hlt, hmod, hdiv, -⟩ := rejNum_spec hbits hi
    obtain ⟨hlt', hmod', hdiv', -⟩ := rejNum_spec hbits hi'
    have he := chunkOf_injective hlt hlt' h
    have h1 : i % (2 ^ bits - m) = i' % (2 ^ bits - m) := by
      have := congrArg (· % 2 ^ bits) he
      simp only [hmod, hmod'] at this
      omega
    have h2 : i / (2 ^ bits - m) = i' / (2 ^ bits - m) := by
      rw [← hdiv, ← hdiv', he]
    rw [← Nat.div_add_mod i (2 ^ bits - m), ← Nat.div_add_mod i' (2 ^ bits - m), h1, h2]
  card_rej := by
    rw [card_acc_none hbits hm, pow_split hbits, Nat.sub_mul]
  nAcc := 2 ^ (8 * b - bits)
  accChunk a i := chunkOf b (a + i * 2 ^ bits)
  acc_some a i hi := by
    have hlow : (a : ℕ) < 2 ^ bits := lt_of_lt_of_le a.2 hm
    have hlt : (a : ℕ) + i * 2 ^ bits < 256 ^ b := by
      rw [pow_split hbits]
      calc (a : ℕ) + i * 2 ^ bits < 2 ^ bits + i * 2 ^ bits := by omega
        _ = (i + 1) * 2 ^ bits := by ring
        _ ≤ 2 ^ (8 * b - bits) * 2 ^ bits := Nat.mul_le_mul_right _ hi
        _ = _ := mul_comm _ _
    rw [acc_eq_some_iff, leNat_chunkOf, Nat.mod_eq_of_lt hlt, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt hlow]
  acc_inj a i i' hi hi' h := by
    have hlow : (a : ℕ) < 2 ^ bits := lt_of_lt_of_le a.2 hm
    have hb : ∀ i, i < 2 ^ (8 * b - bits) → (a : ℕ) + i * 2 ^ bits < 256 ^ b := fun i hi => by
      rw [pow_split hbits]
      calc (a : ℕ) + i * 2 ^ bits < 2 ^ bits + i * 2 ^ bits := by omega
        _ = (i + 1) * 2 ^ bits := by ring
        _ ≤ 2 ^ (8 * b - bits) * 2 ^ bits := Nat.mul_le_mul_right _ hi
        _ = _ := mul_comm _ _
    have he := congrArg (· / 2 ^ bits) (chunkOf_injective (hb i hi) (hb i' hi') h)
    simp only [Nat.add_mul_div_right _ _ (by positivity : 0 < 2 ^ bits),
      Nat.div_eq_of_lt hlow, zero_add] at he
    exact he
  card_acc a := by convert card_acc_eq hbits hm a

end Rejection

namespace Sampler

variable {k e : ℕ} {C : Type} [Fintype C] [DecidableEq C]

open Reader in
/-- **The preimage sampler of a reader's sampler** (module docstring of
`GordieHowe/SPBCS/Sampler/Unrank.lean`): coins below the fibre size `F`, the coin `i` giving the `i`-th
stream of the fibre (`Unrank.fiberStream`); one coin and an arbitrary stream when the fibres are
empty.

Cost: computing `F` and unranking one stream, polynomial in `k + e` and the reader's size. -/
def Preimage.ofUnrank {R : Reader C} (hR : R.Uniform) (U : R.Unrank) {d : C} :
    (Sampler.ofReader (k := k) (e := e) R hR d).Preimage where
  Coins := Fin (max (U.fiberCnt (k + e)) 1)
  nonempty := ⟨⟨0, lt_max_of_lt_right Nat.one_pos⟩⟩
  pre c r := U.fiberStream (k + e) c r
  sample_pre c r s hs := by
    have hpos : 0 < U.fiberCnt (k + e) := by
      rw [← U.card_fibre c]
      exact Finset.card_pos.2 ⟨s, by simpa [Sampler.ofReader] using hs⟩
    have hr : (r : ℕ) < U.fiberCnt (k + e) := r.2.trans_eq (max_eq_left hpos)
    exact U.sampleOf_fiberStream c hr
  card_eq c s s' hs hs' := by
    have hpos : 0 < U.fiberCnt (k + e) := by
      rw [← U.card_fibre c]
      exact Finset.card_pos.2 ⟨s, by simpa [Sampler.ofReader] using hs⟩
    have hmax : max (U.fiberCnt (k + e)) 1 = U.fiberCnt (k + e) := max_eq_left hpos
    have hlt : ∀ r : Fin (max (U.fiberCnt (k + e)) 1), (r : ℕ) < U.fiberCnt (k + e) :=
      fun r => r.2.trans_eq hmax
    -- the coins map injectively into the fibre, which has as many elements: a bijection
    have hone : ∀ t, R.sampleOf t = some c →
        (Finset.univ.filter fun r : Fin (max (U.fiberCnt (k + e)) 1) =>
          U.fiberStream (k + e) c r = t).card = 1 := by
      intro t ht
      have hinj : Function.Injective fun r : Fin (max (U.fiberCnt (k + e)) 1) =>
          (⟨U.fiberStream (k + e) c r, by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            exact U.sampleOf_fiberStream c (hlt r)⟩ :
            {t // t ∈ Finset.univ.filter fun s : Fin (k + e) → Byte => R.sampleOf s = some c}) :=
        fun r r' h => Fin.ext (U.fiberStream_injective c (hlt r) (hlt r')
          (congrArg Subtype.val h))
      have hbij := (Fintype.bijective_iff_injective_and_card _).2 ⟨hinj, by
        rw [Fintype.card_fin, Fintype.card_coe, U.card_fibre c, hmax]⟩
      obtain ⟨r, hr⟩ := hbij.2 ⟨t, by simpa using ht⟩
      rw [Finset.card_eq_one]
      refine ⟨r, Finset.eq_singleton_iff_unique_mem.2 ⟨by simpa using congrArg Subtype.val hr, ?_⟩⟩
      intro r' hr'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr'
      exact hinj (Subtype.ext (hr'.trans (congrArg Subtype.val hr).symm))
    rw [hone s hs, hone s' hs']

end Sampler

end GordieHowe.SPBCS
