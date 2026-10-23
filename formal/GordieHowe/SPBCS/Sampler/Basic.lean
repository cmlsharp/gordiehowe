-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Extraction.Transcript
public import Mathlib.Data.Fintype.CardEmbedding
public import Mathlib.Data.Nat.Size

@[expose] public section

/-!
# The challenge sampler

A model of the C++ `RandomEngine` (`third_party/longfellow/lib/random/random.h`, lines checked on main at `36753d9f`) and
of the field `sample` functions, reading from a finite byte stream, with the `Sampler` law
`card_eq` of `GordieHowe/SPBCS/Extraction/Transcript.lean` proved.

**Readers.** A `Reader α` is a finite decision tree over bytes: `done a` returns `a`,
`fail` fails, `read f` consumes one byte `x` and continues with `f x`. `run` executes it
on a byte list and returns the value and the unread bytes, or `none` when the tree fails
or the input is exhausted. A C++ loop `for (;;) { fill_bytes(b, buf); if (ok) return; }`
becomes `rej acc t`: at most `t` attempts of `b` bytes. Every attempt consumes at least one
byte, so on an input of fewer than `t` bytes the bound on attempts is never reached
(`run_rej_of_length_lt`): with `t` at least the stream length, `rej` is the unbounded C++
loop cut off at exhaustion.

**Uniformity.** `exact R j a` is the number of `j`-byte strings on which `R` returns `a`
having read exactly those `j` bytes. `R` is `Uniform` when this does not depend on `a`.
Then every value has the same number of preimages among `N`-byte streams
(`card_sampleOf_eq`), which is `Sampler.card_eq`. Uniformity is preserved by `prod`
(sequencing), `pi` (a tuple), `map` along an equivalence, and holds for `bytes` and for
rejection sampling `rej acc t` whose acceptance map `acc` has fibres of equal size.

**Exhaustion.** `failCount R N` counts the `N`-byte streams on which `R` returns `none`.
`failProb_bind_le` bounds sequencing, `failProb_rej_le` is the geometric bound
`ρ^t` for `t` attempts of `b` bytes within the stream, `ρ` the rejection probability.

**The Chernoff bound.** `pgf z R` is `E[z^S ; returns]` for `S` the bytes read on a uniform
unbounded stream, `pfail R` the probability of reaching `fail`. `failProb_le_ofReal`:
`failProb R N ≤ pgf z R / z^(N+1) + pfail R` for every `z ≥ 1` (Markov's inequality on `z^S`).
The generating functions multiply under sequencing and tuples (`pgf_bind_le`, `pgf_prod_le`,
`pgf_pi_le`; the failure probabilities add), and a rejection sampler whose attempts of `b` bytes
are accepted with probability at least `1/2` has `pgf z ≤ z^b / (2 - z^b)` (`pgf_rej_le`, the
`Geometric(1/2)` generating function) and `pfail ≤ 2^-t` (`pfail_rej_le`). This is the
computation of `experiments/pq-migration/fs_budget.py` behind the C++ budget `k + e`; bounding a
round's overrun numerically needs the round's reader (its sequence of C++ squeezes).

**The C++ samplers modelled.**
- `nat(n)` (`random.h` lines 56–89): `l = byteLen n` bytes, read little-endian, masked
  with `mask(n) = 2^(size n) - 1` (lines 107–115), rejected if `≥ n`: `natReader n`.
- `choose(res, n, k)` (lines 91–105): Fisher–Yates, `j = i + nat(n - i)`, swap `A[i]`,
  `A[j]`, `res[i] = A[i]`: `CReader.choose` (`GordieHowe/SPBCS/Sampler/ChallengeReader.lean`), a
  uniform `Fin k ↪ Fin n` through `FisherYates.equiv`.
- Prime field `sample`: `Fp64Goldilocks::sample` (`lib/algebra/fp_goldilocks.h`
  lines 167–174; 8 bytes, reject `≥ p`), `Fp14`/`Fp24::sample` (`lib/algebra/fp14.h`
  lines 292–305, `fp24.h` lines 286–299; `total_l = (exact_bits + 7) / 8` bytes, mask to
  `exact_bits`, reject `≥ m`), `FpGeneric::sample` (`lib/algebra/fp_generic.h`
  lines 392–403, the same). With `exact_bits = size m` these are all `natReader m`
  (Goldilocks: `size p = 64`, `byteLen p = 8`), followed by the representation
  `Fin m ≃ F` (`to_montgomery` of the integer read): `CReader.prime`.
- `GF2_128`/`GF2_256::sample` (`lib/gf2k/gf2_128.h` lines 197–205, `gf2_256.h`
  lines 195–203): `kBytes` raw bytes, every string a field element: `bytesReader`.
- Extension fields sample their coordinates in order: `Fp2::sample` (`lib/algebra/fp2.h` lines
  204–209, `re` then `im`), `Fp2Goldilocks::sample` (`fp_goldilocks.h` lines 344–349),
  `NativeWide::sample` (`lib/algebra/fp_native_wide.h` lines 372–379, `e[0], …, e[d-1]`):
  `CReader.ext`.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP
open scoped ENNReal

/-- A finite decision tree reading bytes. -/
inductive Reader (α : Type) where
  | done (a : α)
  | fail
  | read (f : Byte → Reader α)

namespace Reader

variable {α β γ : Type}

/-- Run a reader on a byte list: the value and the unread bytes. -/
def run : Reader α → List Byte → Option (α × List Byte)
  | done a, s => some (a, s)
  | fail, _ => none
  | read _, [] => none
  | read f, b :: s => run (f b) s

/-- Sequencing. -/
def bind : Reader α → (α → Reader β) → Reader β
  | done a, k => k a
  | fail, _ => fail
  | read f, k => read fun b => bind (f b) k

/-- Apply a function to the value. -/
def map (g : α → β) : Reader α → Reader β
  | done a => done (g a)
  | fail => fail
  | read f => read fun b => map g (f b)

theorem run_bind (R : Reader α) (k : α → Reader β) (s : List Byte) :
    (R.bind k).run s = (R.run s).bind fun p => (k p.1).run p.2 := by
  induction R generalizing s with
  | done a => rfl
  | fail => rfl
  | read f ih => cases s <;> simp [bind, run, ih]

theorem run_map (g : α → β) (R : Reader α) (s : List Byte) :
    (R.map g).run s = (R.run s).map fun p => (g p.1, p.2) := by
  induction R generalizing s with
  | done a => rfl
  | fail => rfl
  | read f ih => cases s <;> simp [map, run, ih]

theorem bind_map (g : α → β) (R : Reader α) (k : β → Reader γ) :
    (R.map g).bind k = R.bind (k ∘ g) := by
  induction R with
  | done a => rfl
  | fail => rfl
  | read f ih => simp [map, bind, ih]

theorem ofFn_cons {N : ℕ} (x : Byte) (t : Fin N → Byte) :
    List.ofFn (Fin.cons x t : Fin (N + 1) → Byte) = x :: List.ofFn t := by
  simp [List.ofFn_succ]

/-- The value a reader returns on a finite stream. -/
def sampleOf {N : ℕ} (R : Reader α) (s : Fin N → Byte) : Option α :=
  (R.run (List.ofFn s)).map Prod.fst

theorem sampleOf_read_cons {N : ℕ} (f : Byte → Reader α) (x : Byte) (t : Fin N → Byte) :
    (read f).sampleOf (Fin.cons x t : Fin (N + 1) → Byte) = (f x).sampleOf t := by
  simp only [sampleOf]
  rw [ofFn_cons]
  rfl

/-! ### Exact counts and uniformity -/

section Exact

variable [DecidableEq α] [DecidableEq β]

/-- The number of `j`-byte strings on which `R` returns `a` having read exactly `j`
bytes. -/
def exact : Reader α → ℕ → α → ℕ
  | done a', 0, a => if a' = a then 1 else 0
  | done _, _ + 1, _ => 0
  | fail, _, _ => 0
  | read _, 0, _ => 0
  | read f, j + 1, a => ∑ b, exact (f b) j a

/-- Every value is returned after exactly `j` bytes by the same number of strings. -/
def Uniform (R : Reader α) : Prop := ∀ j a a', R.exact j a = R.exact j a'

/-- The streams sampling `a` are counted by `exact`: a stream of `N` bytes sampling `a`
is a string of `j ≤ N` bytes read exactly, followed by `N - j` unread bytes. -/
theorem card_sampleOf_eq (R : Reader α) (N : ℕ) (a : α) :
    (Finset.univ.filter fun s : Fin N → Byte => R.sampleOf s = some a).card =
      ∑ j ∈ Finset.range (N + 1), R.exact j a * 256 ^ (N - j) := by
  induction R generalizing N with
  | done a' =>
    rw [Finset.sum_range_succ']
    simp only [exact, sampleOf, run, Option.map_some, Option.some_inj, zero_mul,
      Finset.sum_const_zero, zero_add, Nat.sub_zero]
    by_cases h : a' = a
    · simp [h]
    · simp [h]
  | fail => simp [sampleOf, run, exact]
  | read f ih =>
    cases N with
    | zero => simp [sampleOf, run, exact]
    | succ N =>
      rw [Finset.sum_range_succ']
      simp only [exact, zero_mul, add_zero, Nat.add_sub_add_right, Finset.sum_mul]
      rw [Finset.sum_comm, ← Finset.sum_congr rfl fun b _ => ih b N]
      rw [Finset.card_filter, ← (Fin.consEquiv fun _ => Byte).sum_comp,
        Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, sampleOf_read_cons]

theorem card_sampleOf_eq_of_uniform {R : Reader α} (hR : R.Uniform) (N : ℕ) (a a' : α) :
    (Finset.univ.filter fun s : Fin N → Byte => R.sampleOf s = some a).card =
      (Finset.univ.filter fun s : Fin N → Byte => R.sampleOf s = some a').card := by
  rw [card_sampleOf_eq, card_sampleOf_eq]
  exact Finset.sum_congr rfl fun j _ => by rw [hR j a a']

theorem exact_map (g : α → β) (R : Reader α) (j : ℕ) (c : β) [Fintype α] :
    (R.map g).exact j c = ∑ a, if g a = c then R.exact j a else 0 := by
  induction R generalizing j with
  | done a' =>
    cases j with
    | zero =>
      simp only [map, exact]
      rw [Finset.sum_eq_single a' (fun a _ ha => by simp [Ne.symm ha]) (by simp)]
      simp
    | succ j => simp [map, exact]
  | fail => simp [map, exact]
  | read f ih =>
    cases j with
    | zero => simp [map, exact]
    | succ j =>
      simp only [map, exact, ih]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      split_ifs <;> simp

theorem exact_map_equiv [Fintype α] (e : α ≃ β) (R : Reader α) (j : ℕ) (c : β) :
    (R.map e).exact j c = R.exact j (e.symm c) := by
  rw [exact_map, Finset.sum_eq_single (e.symm c) (fun a _ ha => by
    rw [if_neg]; exact fun h => ha (by rw [← h, Equiv.symm_apply_apply])) (by simp)]
  simp

theorem Uniform.map_equiv [Fintype α] {R : Reader α} (hR : R.Uniform) (e : α ≃ β) :
    (R.map e).Uniform := fun j c c' => by
  rw [exact_map_equiv, exact_map_equiv, hR]

theorem exact_bind [Fintype α] (R : Reader α) (k : α → Reader β) (j : ℕ) (c : β) :
    (R.bind k).exact j c =
      ∑ i ∈ Finset.range (j + 1), ∑ a, R.exact i a * (k a).exact (j - i) c := by
  induction R generalizing j with
  | done a' =>
    rw [Finset.sum_range_succ']
    simp only [bind, exact, Nat.sub_zero, zero_mul, Finset.sum_const_zero,
      Finset.sum_const_zero, zero_add, ite_mul, one_mul]
    rw [Finset.sum_ite_eq]
    simp
  | fail => simp [bind, exact]
  | read f ih =>
    cases j with
    | zero => simp [bind, exact]
    | succ j =>
      rw [Finset.sum_range_succ']
      simp only [bind, exact, ih, zero_mul, Finset.sum_const_zero, add_zero,
        Nat.add_sub_add_right, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]

/-- Two readers one after the other. -/
def prod (R : Reader α) (R' : Reader β) : Reader (α × β) :=
  R.bind fun a => R'.map (a, ·)

theorem exact_prod [Fintype α] [Fintype β] (R : Reader α) (R' : Reader β) (j : ℕ) (a : α)
    (b : β) : (R.prod R').exact j (a, b) =
      ∑ i ∈ Finset.range (j + 1), R.exact i a * R'.exact (j - i) b := by
  rw [prod, exact_bind]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single a (fun a' _ ha => by
    rw [exact_map, Finset.sum_eq_zero fun b' _ => by simp [ha], mul_zero]) (by simp)]
  rw [exact_map, Finset.sum_eq_single b (fun b' _ hb => by simp [hb]) (by simp)]
  simp

theorem Uniform.prod [Fintype α] [Fintype β] {R : Reader α} {R' : Reader β} (hR : R.Uniform)
    (hR' : R'.Uniform) : (R.prod R').Uniform := by
  rintro j ⟨a, b⟩ ⟨a', b'⟩
  rw [exact_prod, exact_prod]
  exact Finset.sum_congr rfl fun i _ => by rw [hR i a a', hR' (j - i) b b']

end Exact

/-! ### Tuples -/

/-- The readers `R 0, …, R (k-1)` one after the other. -/
def pi : {k : ℕ} → {β : Fin k → Type} → ((i : Fin k) → Reader (β i)) →
    Reader ((i : Fin k) → β i)
  | 0, _, _ => done fun i => i.elim0
  | _ + 1, β, R => ((R 0).prod (pi fun i => R i.succ)).map (Fin.consEquiv β)

theorem Uniform.pi : ∀ {k : ℕ} {β : Fin k → Type} [∀ i, Fintype (β i)] [∀ i, DecidableEq (β i)]
    {R : (i : Fin k) → Reader (β i)}, (∀ i, (R i).Uniform) → (Reader.pi R).Uniform
  | 0, _, _, _, _, _ => fun j a a' => by
    rw [Subsingleton.elim a a']
  | _ + 1, β, _, _, R, h => by
    have := Uniform.pi (R := fun i => R i.succ) fun i => h i.succ
    exact ((h 0).prod this).map_equiv (Fin.consEquiv β)

/-! ### Reading bytes -/

/-- Read `b` bytes, the first byte first. -/
def bytes : (b : ℕ) → Reader (Fin b → Byte)
  | 0 => done fun i => i.elim0
  | b + 1 => read fun x => (bytes b).map (Fin.cons x)

section ExactBytes

theorem exact_bytes (b j : ℕ) (v : Fin b → Byte) : (bytes b).exact j v = if j = b then 1 else 0 := by
  induction b generalizing j with
  | zero =>
    cases j with
    | zero => simp [bytes, exact, Subsingleton.elim (fun i : Fin 0 => i.elim0) v]
    | succ j => simp [bytes, exact]
  | succ b ih =>
    cases j with
    | zero => simp [bytes, exact]
    | succ j =>
      simp only [bytes, exact, exact_map, ih, Nat.add_right_cancel_iff]
      rw [Finset.sum_eq_single (v 0) (fun x _ hx => Finset.sum_eq_zero fun w _ => by
        rw [if_neg]; rintro rfl; exact hx (by simp)) (by simp)]
      rw [Finset.sum_eq_single (Fin.tail v) (fun w _ hw => by
        rw [if_neg]; intro h; exact hw (by rw [← h]; simp)) (by simp)]
      simp [Fin.cons_self_tail]

theorem uniform_bytes (b : ℕ) : (bytes b).Uniform := fun j v v' => by
  rw [exact_bytes, exact_bytes]

end ExactBytes

theorem run_bytes (b : ℕ) (s : List Byte) :
    (bytes b).run s = if h : b ≤ s.length then some (fun i => s[i.1]'(by omega), s.drop b)
      else none := by
  induction b generalizing s with
  | zero =>
    simp only [bytes, run, Nat.zero_le, dite_true, List.drop_zero, Option.some_inj,
      Prod.mk.injEq, and_true]
    funext i
    exact i.elim0
  | succ b ih =>
    cases s with
    | nil => simp [bytes, run]
    | cons x s =>
      simp only [bytes, run, run_map, ih, List.length_cons, Nat.add_le_add_iff_right]
      split_ifs with h
      · simp only [Option.map_some, List.drop_succ_cons, Option.some_inj, Prod.mk.injEq,
          and_true]
        funext i
        refine Fin.cases rfl (fun i => ?_) i
        simp
      · rfl

/-! ### Rejection sampling -/

variable {b : ℕ}

/-- At most `t` attempts: read `b` bytes, return `acc` of them if it is defined, else
try again. -/
def rej (acc : (Fin b → Byte) → Option α) : ℕ → Reader α
  | 0 => fail
  | t + 1 => (bytes b).bind fun v => (acc v).elim (rej acc t) done

section ExactRej

variable [DecidableEq α]

/-- `acc` has fibres of equal size. -/
def FibreUniform (acc : (Fin b → Byte) → Option α) : Prop :=
  ∀ a a', (Finset.univ.filter fun v => acc v = some a).card =
    (Finset.univ.filter fun v => acc v = some a').card

theorem sum_exact_elim (acc : (Fin b → Byte) → Option α) (R : Reader α) (m : ℕ) (a : α) :
    ∑ v, ((acc v).elim R done).exact m a =
      (Finset.univ.filter fun v => acc v = none).card * R.exact m a +
        if m = 0 then (Finset.univ.filter fun v => acc v = some a).card else 0 := by
  have hpt : ∀ v, ((acc v).elim R done).exact m a =
      (if acc v = none then R.exact m a else 0) +
        if m = 0 then (if acc v = some a then 1 else 0) else 0 := by
    intro v
    cases acc v with
    | none => simp
    | some a' => cases m <;> simp [exact]
  simp only [hpt, Finset.sum_add_distrib, Finset.card_filter, Finset.sum_mul, ite_mul,
    one_mul, zero_mul]
  split_ifs <;> simp

theorem exact_rej_succ (acc : (Fin b → Byte) → Option α) (t j : ℕ) (a : α) :
    (rej acc (t + 1)).exact j a =
      if b ≤ j then (Finset.univ.filter fun v => acc v = none).card * (rej acc t).exact (j - b) a +
        (if j = b then (Finset.univ.filter fun v => acc v = some a).card else 0)
      else 0 := by
  rw [rej, exact_bind]
  simp only [exact_bytes, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_range]
  by_cases hb : b ≤ j
  · simp only [if_pos (by omega : b < j + 1), if_pos hb]
    rw [sum_exact_elim]
    congr 1
    exact if_congr (by omega) rfl rfl
  · simp [hb]

theorem Uniform.rej {acc : (Fin b → Byte) → Option α} (hacc : FibreUniform acc) (t : ℕ) :
    (Reader.rej acc t).Uniform := by
  induction t with
  | zero => intro j a a'; simp [Reader.rej, exact]
  | succ t ih =>
    intro j a a'
    rw [exact_rej_succ, exact_rej_succ, ih (j - b) a a', hacc a a']

end ExactRej

/-- Every attempt consumes `b ≥ 1` bytes, so on fewer than `t` bytes the attempt bound `t`
is never reached: more attempts do not change the result. -/
theorem run_rej_of_length_lt (hb : 1 ≤ b) (acc : (Fin b → Byte) → Option α) :
    ∀ (t : ℕ) (s : List Byte), s.length < t → (rej acc (t + 1)).run s = (rej acc t).run s
  | 0, _, h => absurd h (Nat.not_lt_zero _)
  | t + 1, s, h => by
    rw [rej, rej, run_bind, run_bind, run_bytes]
    split_ifs with hs
    · simp only [Option.bind_some]
      cases acc _ with
      | none =>
        exact run_rej_of_length_lt hb acc t _ (by simp; omega)
      | some a => rfl
    · rfl

/-! ### Exhaustion -/

/-- The number of `N`-byte streams on which `R` returns `none`. -/
def failCount : Reader α → ℕ → ℕ
  | done _, _ => 0
  | fail, N => 256 ^ N
  | read _, 0 => 1
  | read f, N + 1 => ∑ x, failCount (f x) N

theorem card_sampleOf_none (R : Reader α) (N : ℕ) :
    (Finset.univ.filter fun s : Fin N → Byte => R.sampleOf s = none).card = R.failCount N := by
  induction R generalizing N with
  | done a => simp [sampleOf, run, failCount]
  | fail => simp [sampleOf, run, failCount]
  | read f ih =>
    cases N with
    | zero => simp [sampleOf, run, failCount]
    | succ N =>
      simp only [failCount, ← ih]
      rw [Finset.card_filter, ← (Fin.consEquiv fun _ => Byte).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.card_filter]
      refine Finset.sum_congr rfl fun t _ => ?_
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, sampleOf_read_cons]

theorem failCount_le (R : Reader α) (N : ℕ) : R.failCount N ≤ 256 ^ N := by
  rw [← card_sampleOf_none]
  exact (Finset.card_le_univ _).trans (by simp)

theorem failCount_succ_le (R : Reader α) (N : ℕ) : R.failCount (N + 1) ≤ 256 * R.failCount N := by
  induction R generalizing N with
  | done a => simp [failCount]
  | fail => simp [failCount, pow_succ, mul_comm]
  | read f ih =>
    cases N with
    | zero =>
      simp only [failCount, mul_one]
      calc ∑ x, (f x).failCount 0 ≤ ∑ _x : Byte, 1 :=
            Finset.sum_le_sum fun x _ => (failCount_le _ 0).trans (by simp)
        _ = 256 := by simp
    | succ N =>
      simp only [failCount, Finset.mul_sum]
      exact Finset.sum_le_sum fun x _ => ih x N

theorem failCount_add_le (R : Reader α) (N m : ℕ) :
    R.failCount (N + m) ≤ 256 ^ m * R.failCount N := by
  induction m with
  | zero => simp
  | succ m ih =>
    calc R.failCount (N + (m + 1)) ≤ 256 * R.failCount (N + m) := failCount_succ_le R _
      _ ≤ 256 * (256 ^ m * R.failCount N) := Nat.mul_le_mul_left _ ih
      _ = _ := by ring

/-- Sequencing: `R` fails within `N₁` bytes, or it succeeds and the continuation fails
within the next `N₂` bytes. -/
theorem failCount_bind_le (R : Reader α) (k : α → Reader β) {N₂ D : ℕ}
    (hk : ∀ a, (k a).failCount N₂ ≤ D) (N₁ : ℕ) :
    (R.bind k).failCount (N₁ + N₂) ≤ R.failCount N₁ * 256 ^ N₂ + 256 ^ N₁ * D := by
  induction R generalizing N₁ with
  | done a =>
    simp only [bind, failCount, zero_mul, zero_add]
    rw [Nat.add_comm]
    exact (failCount_add_le _ _ _).trans (Nat.mul_le_mul_left _ (hk a))
  | fail => simp [bind, failCount, pow_add]
  | read f ih =>
    cases N₁ with
    | zero =>
      simp only [zero_add, failCount, one_mul]
      exact (failCount_le _ _).trans (Nat.le_add_right _ _)
    | succ N₁ =>
      rw [Nat.add_right_comm]
      simp only [bind, failCount, Finset.sum_mul]
      calc ∑ x, ((f x).bind k).failCount (N₁ + N₂)
          ≤ ∑ x, ((f x).failCount N₁ * 256 ^ N₂ + 256 ^ N₁ * D) :=
            Finset.sum_le_sum fun x _ => ih x N₁
        _ = _ := by rw [Finset.sum_add_distrib]; simp [pow_succ]; ring

theorem failCount_map (g : α → β) (R : Reader α) (N : ℕ) : (R.map g).failCount N = R.failCount N := by
  induction R generalizing N with
  | done a => rfl
  | fail => rfl
  | read f ih => cases N <;> simp [map, failCount, ih]

theorem failCount_bytes_bind (k : (Fin b → Byte) → Reader β) (N : ℕ) :
    ((bytes b).bind k).failCount (b + N) = ∑ v, (k v).failCount N := by
  induction b generalizing N with
  | zero =>
    simp only [bytes, bind, zero_add]
    rw [Fintype.sum_unique]
    rfl
  | succ b ih =>
    rw [Nat.add_right_comm]
    simp only [bytes, bind, failCount, bind_map, Function.comp_def, ih]
    rw [← (Fin.consEquiv fun _ => Byte).sum_comp, Fintype.sum_prod_type]
    rfl

theorem bind_done (R : Reader α) : R.bind done = R := by
  induction R with
  | done a => rfl
  | fail => rfl
  | read f ih => simp [bind, ih]

theorem failCount_bytes_add (N : ℕ) : (bytes b).failCount (b + N) = 0 := by
  rw [← bind_done (bytes b), failCount_bytes_bind]
  simp [failCount]

theorem failCount_elim (acc : (Fin b → Byte) → Option α) (R : Reader α) (N : ℕ) :
    ∑ v, ((acc v).elim R done).failCount N =
      (Finset.univ.filter fun v => acc v = none).card * R.failCount N := by
  rw [Finset.card_filter, Finset.sum_mul]
  refine Finset.sum_congr rfl fun v _ => ?_
  cases acc v <;> simp [failCount]

theorem failCount_rej_succ (acc : (Fin b → Byte) → Option α) (t N : ℕ) :
    (rej acc (t + 1)).failCount (b + N) =
      (Finset.univ.filter fun v => acc v = none).card * (rej acc t).failCount N := by
  rw [rej, failCount_bytes_bind, failCount_elim]

/-! ### Failure probability -/

/-- The probability that `R` returns `none` on a uniform `N`-byte stream. -/
noncomputable def failProb (R : Reader α) (N : ℕ) : ℝ≥0∞ := R.failCount N / 256 ^ N

theorem prob_sampleOf_none (R : Reader α) (N : ℕ) :
    Pr[s ← (Fin N → Byte) : R.sampleOf s = none] = R.failProb N := by
  rw [probUniform_eq_card_div, card_sampleOf_none, failProb]
  simp

theorem failProb_le_one (R : Reader α) (N : ℕ) : R.failProb N ≤ 1 := by
  rw [← prob_sampleOf_none]
  exact GordieHowe.QROM.probUniform_le_one _

theorem failProb_read_succ (f : Byte → Reader α) (N : ℕ) :
    (read f).failProb (N + 1) = (∑ x, (f x).failProb N) * 256⁻¹ := by
  simp only [failProb, failCount, Nat.cast_sum, ENNReal.sum_div, Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [pow_succ, ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul,
    ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp))]
  ring

theorem failProb_succ_le (R : Reader α) (N : ℕ) : R.failProb (N + 1) ≤ R.failProb N := by
  have h := failCount_succ_le R N
  rw [failProb, failProb, pow_succ, mul_comm (256 ^ N : ℝ≥0∞)]
  calc (R.failCount (N + 1) : ℝ≥0∞) / (256 * 256 ^ N)
      ≤ ((256 * R.failCount N : ℕ) : ℝ≥0∞) / (256 * 256 ^ N) :=
        ENNReal.div_le_div_right (Nat.cast_le.2 h) _
    _ = _ := by
      rw [Nat.cast_mul, Nat.cast_ofNat, ENNReal.mul_div_mul_left _ _ (by simp) (by simp)]

theorem failProb_antitone (R : Reader α) {N N' : ℕ} (h : N ≤ N') :
    R.failProb N' ≤ R.failProb N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact le_rfl
  | succ d ih => exact (failProb_succ_le R _).trans (ih (Nat.le_add_right _ _))

/-! ### Reading at most `n` bytes -/

/-- **`R` cut off after `n` bytes**: the reader fails where `R` would read an `(n + 1)`-th byte
(the C++ transcript's per-point stream budget, `BasicTranscript::bytes`). -/
def limit : ℕ → Reader α → Reader α
  | _, done a => done a
  | _, fail => fail
  | 0, read _ => fail
  | n + 1, read f => read fun b => limit n (f b)

/-- On at most `n` bytes the cut-off reader runs as `R`. -/
theorem run_limit_of_length_le (R : Reader α) {n : ℕ} {l : List Byte} (h : l.length ≤ n) :
    (R.limit n).run l = R.run l := by
  induction R generalizing n l with
  | done a => cases n <;> rfl
  | fail => cases n <;> rfl
  | read f ih =>
    cases l with
    | nil => cases n <;> rfl
    | cons b l =>
      cases n with
      | zero => simp at h
      | succ n =>
        simp only [limit, run]
        exact ih b (by simpa using h)

/-- On an `n`-byte stream the cut-off reader samples as `R`. -/
theorem sampleOf_limit_self (R : Reader α) {n : ℕ} (s : Fin n → Byte) :
    (R.limit n).sampleOf s = R.sampleOf s := by
  simp only [sampleOf]
  rw [run_limit_of_length_le R (by simp)]

/-- The cut-off reader fails on `n + d` bytes exactly where `R` fails on the first `n`. -/
theorem failCount_limit (R : Reader α) (n d : ℕ) :
    (R.limit n).failCount (n + d) = R.failCount n * 256 ^ d := by
  induction R generalizing n with
  | done a => cases n <;> simp [limit, failCount]
  | fail => cases n <;> simp [limit, failCount, pow_add]
  | read f ih =>
    cases n with
    | zero => simp [limit, failCount]
    | succ n =>
      rw [Nat.add_right_comm]
      simp only [limit, failCount, Finset.sum_mul]
      exact Finset.sum_congr rfl fun b _ => ih b n

/-- **The failure probability of the cut-off reader** on a stream of at least `n` bytes is that
of `R` on `n` bytes. -/
theorem failProb_limit (R : Reader α) {n N : ℕ} (h : n ≤ N) :
    (R.limit n).failProb N = R.failProb n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [failProb, failProb, failCount_limit, Nat.cast_mul, pow_add, Nat.cast_pow, Nat.cast_ofNat,
    ENNReal.mul_div_mul_right _ _ (by simp) (by simp)]

section ExactLimit

variable [DecidableEq α]

/-- The cut-off reader returns after exactly `j` bytes as `R` does when `j ≤ n`, and never
otherwise. -/
theorem exact_limit (R : Reader α) (n j : ℕ) (a : α) :
    (R.limit n).exact j a = if j ≤ n then R.exact j a else 0 := by
  induction R generalizing n j with
  | done a' =>
    cases n <;> cases j <;> simp [limit, exact]
  | fail => cases n <;> simp [limit, exact]
  | read f ih =>
    cases n with
    | zero => cases j <;> simp [limit, exact]
    | succ n =>
      cases j with
      | zero => simp [limit, exact]
      | succ j =>
        simp only [limit, exact, ih, Nat.add_le_add_iff_right]
        split_ifs <;> simp

/-- Cutting a uniform reader off keeps it uniform. -/
theorem Uniform.limit {R : Reader α} (hR : R.Uniform) (n : ℕ) : (R.limit n).Uniform :=
  fun j a a' => by rw [exact_limit, exact_limit, hR j a a']

end ExactLimit

/-- Sequencing: `R` fails within `N₁` bytes, or the continuation fails within the next
`N₂` bytes. -/
theorem failProb_bind_le (R : Reader α) (k : α → Reader β) {N₂ : ℕ} {δ : ℝ≥0∞}
    (hk : ∀ a, (k a).failProb N₂ ≤ δ) (N₁ : ℕ) :
    (R.bind k).failProb (N₁ + N₂) ≤ R.failProb N₁ + δ := by
  induction R generalizing N₁ with
  | done a =>
    exact ((failProb_antitone _ (Nat.le_add_left _ _)).trans (hk a)).trans le_add_self
  | fail =>
    refine (failProb_le_one _ _).trans (le_add_right (le_of_eq ?_))
    simp [failProb, failCount, ENNReal.div_self]
  | read f ih =>
    cases N₁ with
    | zero =>
      exact (failProb_le_one _ _).trans (le_add_right (by simp [failProb, failCount]))
    | succ N₁ =>
      rw [Nat.add_right_comm]
      simp only [bind]
      rw [failProb_read_succ, failProb_read_succ]
      calc (∑ x, ((f x).bind k).failProb (N₁ + N₂)) * 256⁻¹
          ≤ (∑ x, ((f x).failProb N₁ + δ)) * 256⁻¹ := by
            gcongr with x; exact ih x N₁
        _ = (∑ x, (f x).failProb N₁) * 256⁻¹ + δ * (256 * 256⁻¹) := by
            rw [Finset.sum_add_distrib, add_mul]
            simp [mul_comm, mul_assoc]
        _ = _ := by rw [ENNReal.mul_inv_cancel (by simp) (by simp), mul_one]

theorem failProb_map (g : α → β) (R : Reader α) (N : ℕ) : (R.map g).failProb N = R.failProb N := by
  simp [failProb, failCount_map]

theorem failProb_prod_le (R : Reader α) (R' : Reader β) (N₁ N₂ : ℕ) :
    (R.prod R').failProb (N₁ + N₂) ≤ R.failProb N₁ + R'.failProb N₂ :=
  failProb_bind_le R _ (fun a => by rw [failProb_map]) N₁

/-- A tuple of readers, each given `M` bytes. -/
theorem failProb_pi_le : ∀ {k : ℕ} {β : Fin k → Type} (R : (i : Fin k) → Reader (β i)) (M : ℕ),
    (Reader.pi R).failProb (k * M) ≤ ∑ i, (R i).failProb M
  | 0, _, _, _ => by simp [Reader.pi, failProb, failCount]
  | k + 1, β, R, M => by
    rw [Reader.pi, failProb_map, Nat.succ_mul, Nat.add_comm (k * M) M, Fin.sum_univ_succ]
    refine (failProb_prod_le (R 0) (Reader.pi fun i => R i.succ) M (k * M)).trans ?_
    have := failProb_pi_le (fun i => R i.succ) M
    exact add_le_add le_rfl this

theorem failProb_rej_succ (acc : (Fin b → Byte) → Option α) (t N : ℕ) :
    (rej acc (t + 1)).failProb (b + N) =
      (Finset.univ.filter fun v => acc v = none).card / 256 ^ b * (rej acc t).failProb N := by
  rw [failProb, failCount_rej_succ, Nat.cast_mul, pow_add,
    ENNReal.mul_div_mul_comm (Or.inl (by simp)) (Or.inl (by simp)), failProb]

/-- The geometric tail bound: with at least `t` attempts and at least `t · b` bytes, the
rejection sampler fails with probability at most `ρ^t`, `ρ` the probability that one
attempt is rejected. -/
theorem failProb_rej_le (acc : (Fin b → Byte) → Option α) :
    ∀ {t T N : ℕ}, t ≤ T → t * b ≤ N →
      (rej acc T).failProb N ≤
        ((Finset.univ.filter fun v => acc v = none).card / 256 ^ b : ℝ≥0∞) ^ t
  | 0, _, _, _, _ => by simpa using failProb_le_one _ _
  | t + 1, T + 1, N, hT, hN => by
    obtain ⟨N', rfl⟩ : ∃ N', N = b + N' := ⟨N - b, by rw [Nat.succ_mul] at hN; omega⟩
    rw [failProb_rej_succ, pow_succ, mul_comm (_ ^ t)]
    gcongr
    exact failProb_rej_le acc (by omega) (by rw [Nat.succ_mul] at hN; omega)

theorem failProb_bytes (N : ℕ) (h : b ≤ N) : (bytes b).failProb N = 0 := by
  obtain ⟨N', rfl⟩ := Nat.exists_eq_add_of_le h
  simp [failProb, failCount_bytes_add]

/-! ### The Chernoff bound on the bytes read -/

section Chernoff

/-- **The generating function of the bytes read** at `z`: over a uniform unbounded byte stream,
the expected value of `z ^ (bytes read)` on the runs that return (`E[z^S ; returns]`, with `S`
the number of bytes read). -/
noncomputable def pgf (z : ℝ) : Reader α → ℝ
  | done _ => 1
  | fail => 0
  | read f => z / 256 * ∑ x, pgf z (f x)

/-- The probability that the reader reaches `fail` on a uniform unbounded byte stream. -/
noncomputable def pfail : Reader α → ℝ
  | done _ => 0
  | fail => 1
  | read f => (∑ x, pfail (f x)) / 256

theorem pgf_nonneg {z : ℝ} (hz : 0 ≤ z) : ∀ R : Reader α, 0 ≤ R.pgf z
  | done _ => zero_le_one
  | fail => le_rfl
  | read f => mul_nonneg (by positivity) (Finset.sum_nonneg fun x _ => pgf_nonneg hz (f x))

theorem pfail_nonneg : ∀ R : Reader α, 0 ≤ R.pfail
  | done _ => le_rfl
  | fail => zero_le_one
  | read f => div_nonneg (Finset.sum_nonneg fun x _ => pfail_nonneg (f x)) (by norm_num)

/-- The averaged children of a read node: if each child has total weight at least one, so does
their average. -/
theorem one_le_sum_div {z : ℝ} (f : Byte → Reader α)
    (ih : ∀ x, 1 ≤ (f x).pgf z + (f x).pfail) :
    1 ≤ (∑ x, (f x).pgf z) / 256 + (∑ x, (f x).pfail) / 256 := by
  have hs : (256 : ℝ) ≤ ∑ x, ((f x).pgf z + (f x).pfail) := by
    calc (256 : ℝ) = ∑ _x : Byte, (1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum fun x _ => ih x
  rw [Finset.sum_add_distrib] at hs
  rw [← add_div, le_div_iff₀ (by norm_num)]
  linarith

/-- At `z ≥ 1`, returning weighted by `z^S` and failing have total weight at least one. -/
theorem one_le_pgf_add_pfail {z : ℝ} (hz : 1 ≤ z) : ∀ R : Reader α, 1 ≤ R.pgf z + R.pfail
  | done _ => by simp [pgf, pfail]
  | fail => by simp [pgf, pfail]
  | read f => by
    have h2 := one_le_sum_div f fun x => one_le_pgf_add_pfail hz (f x)
    have hp : 0 ≤ ∑ x, pgf z (f x) := Finset.sum_nonneg fun x _ => pgf_nonneg (by linarith) (f x)
    have hle : (∑ x, pgf z (f x)) / 256 ≤ z / 256 * ∑ x, pgf z (f x) := by
      rw [div_mul_eq_mul_div]
      exact div_le_div_of_nonneg_right (le_mul_of_one_le_left hp hz) (by norm_num)
    simp only [pgf, pfail]
    linarith

/-- **Markov's inequality for the bytes read** (the Chernoff step): at `z ≥ 1`, the probability
that the reader does not return within `N` bytes is at most `E[z^S ; returns] / z^(N+1)` plus the
probability of reaching `fail`. -/
theorem failCount_div_le {z : ℝ} (hz : 1 ≤ z) :
    ∀ (R : Reader α) (N : ℕ), (R.failCount N : ℝ) / 256 ^ N ≤ R.pgf z / z ^ (N + 1) + R.pfail
  | done _, N => by
    simp only [failCount, Nat.cast_zero, zero_div, pgf, pfail, add_zero]
    positivity
  | fail, N => by simp [failCount, pgf, pfail]
  | read f, 0 => by
    have h2 := one_le_sum_div f fun x => one_le_pgf_add_pfail hz (f x)
    have hz0 : (0 : ℝ) < z := by linarith
    simp only [failCount, Nat.cast_one, pow_zero, div_one, zero_add, pow_one, pgf, pfail]
    have hdiv : z / 256 * (∑ x, pgf z (f x)) / z = (∑ x, pgf z (f x)) / 256 := by
      field_simp
    rw [hdiv]
    exact h2
  | read f, N + 1 => by
    have ih := fun x => failCount_div_le hz (f x) N
    have hz0 : (0 : ℝ) < z := by linarith
    simp only [failCount, Nat.cast_sum, pgf, pfail]
    calc (∑ x, ((f x).failCount N : ℝ)) / 256 ^ (N + 1)
        = (∑ x, ((f x).failCount N : ℝ) / 256 ^ N) / 256 := by
          rw [← Finset.sum_div, pow_succ, div_div]
      _ ≤ (∑ x, ((f x).pgf z / z ^ (N + 1) + (f x).pfail)) / 256 :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => ih x) (by norm_num)
      _ = z / 256 * (∑ x, (f x).pgf z) / z ^ (N + 1 + 1) + (∑ x, (f x).pfail) / 256 := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div, add_div, pow_succ z (N + 1)]
          field_simp

/-- Sequencing multiplies the generating functions. -/
theorem pgf_bind_le {z : ℝ} (hz : 0 ≤ z) (k : α → Reader β) {c : ℝ}
    (hk : ∀ a, (k a).pgf z ≤ c) : ∀ R : Reader α, (R.bind k).pgf z ≤ R.pgf z * c
  | done a => by simpa [bind, pgf] using hk a
  | fail => by simp [bind, pgf]
  | read f => by
    simp only [bind, pgf]
    rw [mul_assoc, Finset.sum_mul]
    exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => pgf_bind_le hz k hk (f x))
      (by positivity)

/-- Sequencing adds the failure probabilities. -/
theorem pfail_bind_le (k : α → Reader β) {c : ℝ} (hc : 0 ≤ c) (hk : ∀ a, (k a).pfail ≤ c) :
    ∀ R : Reader α, (R.bind k).pfail ≤ R.pfail + c
  | done a => by simpa [bind, pfail] using hk a
  | fail => by simp [bind, pfail, hc]
  | read f => by
    simp only [bind, pfail]
    calc (∑ x, ((f x).bind k).pfail) / 256 ≤ (∑ x, ((f x).pfail + c)) / 256 :=
          div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => pfail_bind_le k hc hk (f x))
            (by norm_num)
      _ = _ := by rw [Finset.sum_add_distrib, add_div]; simp

theorem pgf_map (g : α → β) (z : ℝ) : ∀ R : Reader α, (R.map g).pgf z = R.pgf z
  | done _ => rfl
  | fail => rfl
  | read f => by simp only [map, pgf, pgf_map g z (f _)]

theorem pfail_map (g : α → β) : ∀ R : Reader α, (R.map g).pfail = R.pfail
  | done _ => rfl
  | fail => rfl
  | read f => by simp only [map, pfail, pfail_map g (f _)]

theorem pgf_prod_le {z : ℝ} (hz : 0 ≤ z) (R : Reader α) (R' : Reader β) :
    (R.prod R').pgf z ≤ R.pgf z * R'.pgf z :=
  pgf_bind_le hz _ (fun a => by rw [pgf_map]) R

theorem pfail_prod_le (R : Reader α) (R' : Reader β) :
    (R.prod R').pfail ≤ R.pfail + R'.pfail :=
  pfail_bind_le _ (pfail_nonneg R') (fun a => by rw [pfail_map]) R

/-- A tuple of readers: the generating functions multiply. -/
theorem pgf_pi_le {z : ℝ} (hz : 0 ≤ z) : ∀ {k : ℕ} {β : Fin k → Type} (R : (i : Fin k) → Reader (β i)),
    (Reader.pi R).pgf z ≤ ∏ i, (R i).pgf z
  | 0, _, _ => by simp [Reader.pi, pgf]
  | k + 1, β, R => by
    rw [Reader.pi, pgf_map, Fin.prod_univ_succ]
    refine (pgf_prod_le hz (R 0) _).trans
      (mul_le_mul_of_nonneg_left (pgf_pi_le hz fun i => R i.succ) (pgf_nonneg hz _))

/-- A tuple of readers: the failure probabilities add. -/
theorem pfail_pi_le : ∀ {k : ℕ} {β : Fin k → Type} (R : (i : Fin k) → Reader (β i)),
    (Reader.pi R).pfail ≤ ∑ i, (R i).pfail
  | 0, _, _ => by simp [Reader.pi, pfail]
  | k + 1, β, R => by
    rw [Reader.pi, pfail_map, Fin.sum_univ_succ]
    exact (pfail_prod_le (R 0) _).trans (add_le_add le_rfl (pfail_pi_le fun i => R i.succ))

/-- Reading `b` bytes and continuing: the generating function is `(z/256)^b` times the sum over
the bytes read. -/
theorem pgf_bytes_bind (z : ℝ) (k : (Fin b → Byte) → Reader β) :
    ((bytes b).bind k).pgf z = (z / 256) ^ b * ∑ v, (k v).pgf z := by
  induction b with
  | zero =>
    simp only [bytes, bind, pow_zero, one_mul]
    rw [Fintype.sum_unique]
    rfl
  | succ b ih =>
    simp only [bytes, bind, pgf, bind_map, Function.comp_def, ih]
    rw [← (Fin.consEquiv fun _ => Byte).sum_comp, Fintype.sum_prod_type, pow_succ,
      Finset.mul_sum, Finset.mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun v _ => ?_
    simp only [Fin.consEquiv, Equiv.coe_fn_mk]
    ring

/-- Reading `b` bytes and continuing: the failure probability is the average over the bytes
read. -/
theorem pfail_bytes_bind (k : (Fin b → Byte) → Reader β) :
    ((bytes b).bind k).pfail = (∑ v, (k v).pfail) / 256 ^ b := by
  induction b with
  | zero =>
    simp only [bytes, bind, pow_zero, div_one]
    rw [Fintype.sum_unique]
    rfl
  | succ b ih =>
    simp only [bytes, bind, pfail, bind_map, Function.comp_def, ih]
    rw [← (Fin.consEquiv fun _ => Byte).sum_comp, Fintype.sum_prod_type, pow_succ,
      ← Finset.sum_div, div_div]
    rfl

/-- **The geometric bound for rejection sampling** (`Geometric(1/2)` domination): if an attempt
of `b` bytes is accepted with probability at least `1/2` (`2 · |rejected| ≤ 256^b`), then at
`1 ≤ z` with `z^b < 2` the generating function of `rej acc t` is at most `z^b / (2 - z^b)`,
`E[z^(b G)]` for `G ~ Geometric(1/2)` on `{1, 2, …}` (`fs_budget.py`, `log_mgf_geom_half`). -/
theorem pgf_rej_le (acc : (Fin b → Byte) → Option α) {z : ℝ} (hz : 1 ≤ z) (hzb : z ^ b < 2)
    (hacc : 2 * (Finset.univ.filter fun v => acc v = none).card ≤ 256 ^ b) :
    ∀ t, (rej acc t).pgf z ≤ z ^ b / (2 - z ^ b)
  | 0 => by
    simp only [rej, pgf]
    exact div_nonneg (pow_nonneg (by linarith) b) (by linarith)
  | t + 1 => by
    have ih := pgf_rej_le acc hz hzb hacc t
    set G := z ^ b / (2 - z ^ b)
    set Rc := (Finset.univ.filter fun v => acc v = none).card
    have hsplit : ∑ v, ((acc v).elim (rej acc t) done).pgf z =
        (256 ^ b - Rc : ℝ) * 1 + Rc * (rej acc t).pgf z := by
      have h1 : ∑ v, ((acc v).elim (rej acc t) done).pgf z =
          ∑ v, (if acc v = none then (rej acc t).pgf z else 1) :=
        Finset.sum_congr rfl fun v _ => by cases acc v <;> simp [pgf]
      rw [h1, Finset.sum_ite, Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul]
      have htot := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (fun v : Fin b → Byte => acc v = none)
      rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at htot
      have hc : (Finset.univ.filter fun v => ¬ acc v = none).card = 256 ^ b - Rc := by
        simp only [Rc]; omega
      rw [hc, Nat.cast_sub (by simp only [Rc]; omega)]
      push_cast
      ring
    rw [rej, pgf_bytes_bind, hsplit]
    have hw1 : 1 ≤ z ^ b := one_le_pow₀ hz
    have hG0 : 0 ≤ G := div_nonneg (by linarith) (by linarith)
    have hGe : G * (2 - z ^ b) = z ^ b := div_mul_cancel₀ _ (by linarith)
    have hRc : (2 * Rc : ℝ) ≤ 256 ^ b := by exact_mod_cast hacc
    have hRc0 : (0 : ℝ) ≤ Rc := Nat.cast_nonneg _
    have hN : (0 : ℝ) < 256 ^ b := by positivity
    have hzpow : (z / 256) ^ b = z ^ b / 256 ^ b := div_pow z 256 b
    rw [hzpow]
    rw [div_mul_eq_mul_div, div_le_iff₀ hN]
    -- `z^b ((N - R) + R pgf) ≤ G N` from `pgf ≤ G`, `G (2 - z^b) = z^b`, `2R ≤ N`, `z^b ≥ 1`
    have hpgf0 : 0 ≤ (rej acc t).pgf z := pgf_nonneg (by linarith) _
    nlinarith [mul_le_mul_of_nonneg_left ih (mul_nonneg (by linarith : (0:ℝ) ≤ z ^ b) hRc0),
      mul_nonneg (sub_nonneg.2 hw1) (sub_nonneg.2 hRc), mul_nonneg hG0 (sub_nonneg.2 hw1)]

/-- Rejection sampling with acceptance at least `1/2` reaches `fail` (after `t` rejected attempts)
with probability at most `2^-t`. -/
theorem pfail_rej_le (acc : (Fin b → Byte) → Option α)
    (hacc : 2 * (Finset.univ.filter fun v => acc v = none).card ≤ 256 ^ b) :
    ∀ t, (rej acc t).pfail ≤ (1 / 2) ^ t
  | 0 => by simp [rej, pfail]
  | t + 1 => by
    have ih := pfail_rej_le acc hacc t
    set Rc := (Finset.univ.filter fun v => acc v = none).card
    rw [rej, pfail_bytes_bind]
    have h1 : ∑ v, ((acc v).elim (rej acc t) done).pfail = Rc * (rej acc t).pfail := by
      rw [show ∑ v, ((acc v).elim (rej acc t) done).pfail =
          ∑ v, (if acc v = none then (rej acc t).pfail else 0) from
        Finset.sum_congr rfl fun v _ => by cases acc v <;> simp [pfail],
        Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
    rw [h1, pow_succ]
    have hN : (0 : ℝ) < 256 ^ b := by positivity
    have hRc : (2 * Rc : ℝ) ≤ 256 ^ b := by exact_mod_cast hacc
    have hp0 : 0 ≤ (rej acc t).pfail := pfail_nonneg _
    rw [div_le_iff₀ hN]
    nlinarith [mul_le_mul_of_nonneg_left ih (Nat.cast_nonneg Rc : (0 : ℝ) ≤ Rc),
      pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) t]

/-- **The Chernoff bound on exhaustion** in the form of the sampler's rejection bound `δ`: at every
`z ≥ 1`, the reader fails on a uniform `N`-byte stream with probability at most
`E[z^S ; returns] / z^(N+1)` plus the probability of reaching `fail`. -/
theorem failProb_le_ofReal {z : ℝ} (hz : 1 ≤ z) (R : Reader α) (N : ℕ) :
    R.failProb N ≤ ENNReal.ofReal (R.pgf z / z ^ (N + 1) + R.pfail) := by
  have h := failCount_div_le hz R N
  have he : R.failProb N = ENNReal.ofReal ((R.failCount N : ℝ) / 256 ^ N) := by
    rw [failProb, ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num)]
    norm_num
  rw [he]
  exact ENNReal.ofReal_le_ofReal h

end Chernoff

end Reader

/-! ### Rejection sampling of naturals -/

namespace Rejection

/-- The little-endian value of `b` bytes (`random.h` lines 78–82). -/
def leNat {b : ℕ} (v : Fin b → Byte) : ℕ := finFunctionFinEquiv v

/-- One attempt of `nat`/`sample`: the little-endian value of `b` bytes, masked to its
low `bits` bits, accepted if below `m`. -/
def acc (b bits m : ℕ) (v : Fin b → Byte) : Option (Fin m) :=
  if h : leNat v % 2 ^ bits < m then some ⟨_, h⟩ else none

theorem card_mod_eq (p q a : ℕ) (ha : a < q) :
    (Finset.univ.filter fun y : Fin (p * q) => (y : ℕ) % q = a).card = p := by
  rw [Finset.card_filter, ← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]
  have hq : ∀ (x : Fin p) (z : Fin q), ((finProdFinEquiv (x, z) : Fin (p * q)) : ℕ) % q = z := by
    intro x z
    rw [finProdFinEquiv_apply_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt z.2]
  simp only [hq]
  have : ∀ x : Fin p, (∑ z : Fin q, if (z : ℕ) = a then 1 else 0) = 1 := by
    intro _
    rw [Finset.sum_eq_single ⟨a, ha⟩ (fun z _ hz => if_neg fun h => hz (Fin.ext h)) (by simp)]
    simp
  rw [Finset.sum_congr rfl fun x _ => this x]
  simp

theorem card_leNat_mod_eq {b bits : ℕ} (hbits : bits ≤ 8 * b) {a : ℕ} (ha : a < 2 ^ bits) :
    (Finset.univ.filter fun v : Fin b → Byte => leNat v % 2 ^ bits = a).card =
      2 ^ (8 * b - bits) := by
  have hsplit : 256 ^ b = 2 ^ (8 * b - bits) * 2 ^ bits := by
    rw [← pow_add, Nat.sub_add_cancel hbits, pow_mul]; norm_num
  rw [← card_mod_eq (2 ^ (8 * b - bits)) (2 ^ bits) a ha, Finset.card_filter, Finset.card_filter,
    ← ((finFunctionFinEquiv.trans (finCongr hsplit)).symm).sum_comp]
  refine Finset.sum_congr rfl fun y _ => ?_
  simp [leNat]

theorem acc_eq_some_iff {b bits m : ℕ} {v : Fin b → Byte} {a : Fin m} :
    acc b bits m v = some a ↔ leNat v % 2 ^ bits = a := by
  unfold acc
  split_ifs with h
  · simp [Fin.ext_iff]
  · simp only [false_iff]
    intro he
    exact h (he ▸ a.2)

theorem card_acc_eq {b bits m : ℕ} (hbits : bits ≤ 8 * b) (hm : m ≤ 2 ^ bits) (a : Fin m) :
    (Finset.univ.filter fun v => acc b bits m v = some a).card = 2 ^ (8 * b - bits) := by
  simp only [acc_eq_some_iff]
  exact card_leNat_mod_eq hbits (lt_of_lt_of_le a.2 hm)

theorem fibreUniform_acc {b bits m : ℕ} (hbits : bits ≤ 8 * b) (hm : m ≤ 2 ^ bits) :
    Reader.FibreUniform (acc b bits m) := fun a a' => by
  rw [card_acc_eq hbits hm, card_acc_eq hbits hm]

/-- The number of rejected attempts: `256^b - m · 2^(8b - bits)`. -/
theorem card_acc_none {b bits m : ℕ} (hbits : bits ≤ 8 * b) (hm : m ≤ 2 ^ bits) :
    (Finset.univ.filter fun v => acc b bits m v = none).card = 256 ^ b - m * 2 ^ (8 * b - bits) := by
  have hsum : (Finset.univ.filter fun v => acc b bits m v = none).card +
      m * 2 ^ (8 * b - bits) = 256 ^ b := by
    have hdisj := Finset.card_eq_sum_card_fiberwise (f := acc b bits m)
      (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin] at hdisj
    rw [hdisj, Fintype.sum_option]
    simp only [card_acc_eq hbits hm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  omega

/-- `l` of `nat(n)` (`random.h` lines 60–66): the number of bytes of `n`. -/
def byteLen (n : ℕ) : ℕ := (Nat.size n + 7) / 8

/-- `byteLen n` is the least `l` with `n < 256^l`, the loop of `random.h` lines 62–66. -/
theorem lt_pow_iff_byteLen_le (n l : ℕ) : n < 256 ^ l ↔ byteLen n ≤ l := by
  rw [show (256 : ℕ) ^ l = 2 ^ (8 * l) by rw [pow_mul]; norm_num, ← Nat.size_le, byteLen]
  omega

/-- `mask(n)` (`random.h` lines 107–115) is `2^(size n) - 1`: the least `2^j - 1` with
`n &&& (2^j - 1) = n` is at `j = size n`, and masking is reduction mod `2^(size n)`. -/
theorem and_mask (x n : ℕ) : x &&& (2 ^ Nat.size n - 1) = x % 2 ^ Nat.size n :=
  Nat.and_two_pow_sub_one_eq_mod x _

theorem size_le_byteLen (n : ℕ) : Nat.size n ≤ 8 * byteLen n := by
  unfold byteLen; omega

theorem one_le_byteLen {n : ℕ} (hn : 0 < n) : 1 ≤ byteLen n := by
  have := Nat.size_pos.2 hn
  unfold byteLen; omega

end Rejection

open Rejection

/-- `nat(m)` (`random.h` lines 56–89), with at most `t` attempts: `byteLen m` bytes, read
little-endian, masked to `size m` bits, rejected if `≥ m`. -/
def natReader (m t : ℕ) : Reader (Fin m) := Reader.rej (acc (byteLen m) (Nat.size m) m) t

theorem uniform_natReader (m t : ℕ) : (natReader m t).Uniform :=
  Reader.Uniform.rej (fibreUniform_acc (size_le_byteLen m) (Nat.lt_size_self m).le) t

/-- The rejection probability of one attempt of `nat(m)`: `(2^(size m) - m) / 2^(size m)`
of the attempts, as a count over `256^(byteLen m)` strings. -/
theorem card_natReader_none (m : ℕ) :
    (Finset.univ.filter fun v => acc (byteLen m) (Nat.size m) m v = none).card =
      256 ^ byteLen m - m * 2 ^ (8 * byteLen m - Nat.size m) :=
  card_acc_none (size_le_byteLen m) (Nat.lt_size_self m).le

/-- On fewer than `t` bytes, `natReader m t` is the unbounded C++ loop cut off at
exhaustion: one more attempt changes nothing. -/
theorem run_natReader_of_length_lt {m : ℕ} (hm : 0 < m) {t : ℕ} {s : List Byte}
    (hs : s.length < t) : (natReader m (t + 1)).run s = (natReader m t).run s :=
  Reader.run_rej_of_length_lt (one_le_byteLen hm) _ t s hs

/-! ### Fisher–Yates -/

namespace FisherYates

variable {n k : ℕ}

theorem lt_of_fin {i : ℕ} (x : Fin (n - i)) : i < n := by have := x.2; omega

theorem add_lt {i : ℕ} (x : Fin (n - i)) : i + x < n := by have := x.2; omega

/-- The array `A` after the first `m` swaps of `choose` (`random.h` lines 96–104), as the
permutation `x ↦ A[x]`: step `m` swaps positions `m` and `m + r m`. -/
def state (r : (i : Fin k) → Fin (n - i)) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | m + 1 => if h : m < k then
      state r m * Equiv.swap ⟨m, lt_of_fin (r ⟨m, h⟩)⟩ ⟨m + r ⟨m, h⟩, add_lt (r ⟨m, h⟩)⟩
    else state r m

/-- A swap at step `m' ≥ m` does not move positions below `m`. -/
theorem state_apply_of_lt (r : (i : Fin k) → Fin (n - i)) {m : ℕ} {x : Fin n} (hx : (x : ℕ) < m) :
    ∀ m', m ≤ m' → state r m' x = state r m x := by
  intro m' hm
  induction m', hm using Nat.le_induction with
  | base => rfl
  | succ m' hm ih =>
    rw [state]
    split_ifs with h
    · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (fun he => by
          rw [Fin.ext_iff] at he; simp at he; omega) (fun he => by
          rw [Fin.ext_iff] at he; simp at he; omega), ih]
    · exact ih

/-- The output `res`: `res[i]` is `A[i]` after all `k` swaps, which is `A[i]` after swap
`i` (`state_apply_of_lt`), as the C++ writes it. -/
def res (r : (i : Fin k) → Fin (n - i)) (i : Fin k) : Fin n :=
  state r k ⟨i, lt_of_fin (r i)⟩

theorem res_eq_state_succ (r : (i : Fin k) → Fin (n - i)) (i : Fin k) :
    res r i = state r (i + 1) ⟨i, lt_of_fin (r i)⟩ :=
  state_apply_of_lt r (Nat.lt_succ_self _) k i.2

theorem res_injective (r : (i : Fin k) → Fin (n - i)) : Function.Injective (res r) :=
  fun i j h => Fin.ext (by simpa [res] using (state r k).injective h)

/-- The output as an embedding. -/
def emb (r : (i : Fin k) → Fin (n - i)) : Fin k ↪ Fin n := ⟨res r, res_injective r⟩

theorem state_succ_apply (r : (i : Fin k) → Fin (n - i)) {m : ℕ} (h : m < k) :
    state r (m + 1) ⟨m, lt_of_fin (r ⟨m, h⟩)⟩ =
      state r m ⟨m + r ⟨m, h⟩, add_lt (r ⟨m, h⟩)⟩ := by
  rw [state, dif_pos h, Equiv.Perm.mul_apply, Equiv.swap_apply_left]

theorem emb_injective : Function.Injective (emb : ((i : Fin k) → Fin (n - i)) → Fin k ↪ Fin n) := by
  intro r r' h
  have hres : ∀ i, res r i = res r' i := fun i => congrArg (fun e : Fin k ↪ Fin n => e i) h
  have key : ∀ m ≤ k, state r m = state r' m ∧ ∀ i : Fin k, (i : ℕ) < m → r i = r' i := by
    intro m
    induction m with
    | zero => exact fun _ => ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    | succ m ih =>
      intro hm
      obtain ⟨hs, hr⟩ := ih (by omega)
      have hmk : m < k := by omega
      have h1 := hres ⟨m, hmk⟩
      rw [res_eq_state_succ, res_eq_state_succ] at h1
      simp only at h1
      rw [state_succ_apply r hmk, state_succ_apply r' hmk, hs] at h1
      have hrm : r ⟨m, hmk⟩ = r' ⟨m, hmk⟩ := by
        have := (state r' m).injective h1
        rw [Fin.ext_iff] at this
        exact Fin.ext (by simpa using this)
      refine ⟨?_, fun i hi => ?_⟩
      · rw [state, state, dif_pos hmk, dif_pos hmk, hs]
        congr 3
        · rw [hrm]
      · rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | hi
        · exact hr i hi
        · have : i = ⟨m, hmk⟩ := Fin.ext hi
          rw [this, hrm]
  funext i
  exact (key k le_rfl).2 i i.2

theorem card_pi : Fintype.card ((i : Fin k) → Fin (n - i)) = Fintype.card (Fin k ↪ Fin n) := by
  rw [Fintype.card_pi, Fintype.card_embedding_eq, Fintype.card_fin, Fintype.card_fin,
    Nat.descFactorial_eq_prod_range, ← Fin.prod_univ_eq_prod_range]
  simp

/-- Fisher–Yates is a bijection from the `nat` draws onto the injective `k`-tuples. -/
theorem emb_bijective : Function.Bijective (emb : ((i : Fin k) → Fin (n - i)) → Fin k ↪ Fin n) :=
  (Fintype.bijective_iff_injective_and_card _).2 ⟨emb_injective, card_pi⟩

theorem le_of_emb (y : Fin k ↪ Fin n) : k ≤ n := by
  simpa using Fintype.card_le_of_embedding y

/-- **The array of the inverse run**: the permutation after the first `m` swaps when the targets
are the values `y`, each step swapping position `m` with the current position of `y m`. -/
def invState (y : Fin k ↪ Fin n) : ℕ → Equiv.Perm (Fin n)
  | 0 => 1
  | m + 1 => if h : m < k then
      invState y m * Equiv.swap ⟨m, lt_of_lt_of_le h (le_of_emb y)⟩ ((invState y m).symm (y ⟨m, h⟩))
    else invState y m

/-- **Fisher–Yates inverted**: the draws `r i`, the offset of the current position of `y i` from
`i`.

Cost: `k` steps, each a permutation inverse and a swap on `Fin n`. -/
def inv (y : Fin k ↪ Fin n) (i : Fin k) : Fin (n - i) :=
  ⟨((invState y i).symm (y i) : ℕ) - i, by
    have := ((invState y i).symm (y i)).2
    have := lt_of_lt_of_le i.2 (le_of_emb y)
    omega⟩

theorem invState_apply_of_lt (y : Fin k ↪ Fin n) : ∀ m, m ≤ k → ∀ j : Fin k, (j : ℕ) < m →
    invState y m ⟨j, lt_of_lt_of_le j.2 (le_of_emb y)⟩ = y j
  | 0, _, j, hj => absurd hj (Nat.not_lt_zero _)
  | m + 1, hm, j, hj => by
    have hmk : m < k := by omega
    have ih := invState_apply_of_lt y m (by omega)
    set v := (invState y m).symm (y ⟨m, hmk⟩)
    have hv : m ≤ (v : ℕ) := by
      by_contra hlt
      push Not at hlt
      have h1 := ih ⟨v, by omega⟩ hlt
      have h2 : invState y m v = y ⟨m, hmk⟩ := by simp [v]
      have : (⟨(v : ℕ), lt_of_lt_of_le (show (v : ℕ) < k by omega) (le_of_emb y)⟩ : Fin n) = v :=
        rfl
      rw [this, h2] at h1
      have := congrArg Fin.val (y.injective h1)
      simp at this
      omega
    rw [invState, dif_pos hmk, Equiv.Perm.mul_apply]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [Equiv.swap_apply_of_ne_of_ne (fun h => by simp [Fin.ext_iff] at h; omega)
        (fun h => by rw [Fin.ext_iff] at h; simp at h; omega)]
      exact ih j hj
    · have hjm : j = ⟨m, hmk⟩ := Fin.ext hj
      subst hjm
      rw [show (⟨m, _⟩ : Fin n) = ⟨m, lt_of_lt_of_le hmk (le_of_emb y)⟩ from rfl,
        Equiv.swap_apply_left]
      simp [v]

theorem inv_add (y : Fin k ↪ Fin n) (m : ℕ) (h : m < k) :
    m + (inv y ⟨m, h⟩ : ℕ) = ((invState y m).symm (y ⟨m, h⟩) : ℕ) := by
  simp only [inv]
  have : m ≤ (((invState y m).symm (y ⟨m, h⟩)) : ℕ) := by
    by_contra hlt
    push Not at hlt
    set v := (invState y m).symm (y ⟨m, h⟩)
    have h1 := invState_apply_of_lt y m h.le ⟨v, by omega⟩ hlt
    have h2 : invState y m v = y ⟨m, h⟩ := by simp [v]
    rw [show (⟨(v : ℕ), _⟩ : Fin n) = v from rfl, h2] at h1
    have := congrArg Fin.val (y.injective h1)
    simp at this
    omega
  omega

theorem state_inv (y : Fin k ↪ Fin n) : ∀ m, state (inv y) m = invState y m
  | 0 => rfl
  | m + 1 => by
    rw [state, invState]
    split_ifs with h
    · rw [state_inv y m]
      congr 2
      exact Fin.ext (inv_add y m h)
    · exact state_inv y m

theorem emb_inv (y : Fin k ↪ Fin n) : emb (inv y) = y := by
  refine DFunLike.ext _ _ fun i => ?_
  change res (inv y) i = y i
  rw [res_eq_state_succ, state_inv]
  exact invState_apply_of_lt y (i + 1) i.2 i (Nat.lt_succ_self _)

/-- **Fisher–Yates as an equivalence**, with its inverse `inv`. -/
def equiv : ((i : Fin k) → Fin (n - i)) ≃ (Fin k ↪ Fin n) where
  toFun := emb
  invFun := inv
  left_inv r := emb_injective (emb_inv _)
  right_inv := emb_inv

end FisherYates

/-! ### Field elements -/

/-- A binary-field `sample` (`gf2_128.h` lines 197–205, `gf2_256.h` lines 195–203): `b` raw
bytes, every string an element (`e`, `of_bytes_field`). -/
def bytesReader {F : Type} {b : ℕ} (e : (Fin b → Byte) ≃ F) : Reader F := (Reader.bytes b).map e

theorem uniform_bytesReader {F : Type} [Fintype F] [DecidableEq F] {b : ℕ} (e : (Fin b → Byte) ≃ F) :
    (bytesReader e).Uniform :=
  (Reader.uniform_bytes b).map_equiv e

/-! ### Tail bounds for the concrete readers -/

/-- `nat(m)` with at least `t` attempts fails on `N ≥ t · byteLen m` bytes with probability
at most `ρ^t`, `ρ` the rejection probability of one attempt. -/
theorem failProb_natReader_le (m : ℕ) {t T N : ℕ} (hT : t ≤ T) (hN : t * byteLen m ≤ N) :
    (natReader m T).failProb N ≤
      (((256 ^ byteLen m - m * 2 ^ (8 * byteLen m - Nat.size m) : ℕ) : ℝ≥0∞) /
        256 ^ byteLen m) ^ t := by
  rw [← card_natReader_none]
  exact Reader.failProb_rej_le _ hT hN

theorem failProb_bytesReader {F : Type} {b : ℕ} (e : (Fin b → Byte) ≃ F) {N : ℕ} (h : b ≤ N) :
    (bytesReader e).failProb N = 0 := by
  rw [bytesReader, Reader.failProb_map, Reader.failProb_bytes N h]

/-! ### The samplers -/

namespace Sampler

variable {k e : ℕ}

/-- The sampler of a uniform reader on the `k + e`-byte stream, reading `d` where it rejects. -/
def ofReader {C : Type} [Fintype C] [DecidableEq C] (R : Reader C) (hR : R.Uniform) (d : C) :
    Sampler k e C where
  sample := R.sampleOf
  default := d
  card_eq := Reader.card_sampleOf_eq_of_uniform hR _

/-- The rejection probability of a reader's sampler is the reader's probability of exhaustion,
bounded by the `failProb_*_le` lemmas. -/
theorem ofReader_rejectionProb {C : Type} [Fintype C] [DecidableEq C] (R : Reader C) (hR : R.Uniform)
    (d : C) : (ofReader (k := k) (e := e) R hR d).rejectionProb = R.failProb (k + e) :=
  Reader.prob_sampleOf_none R _

end Sampler

end GordieHowe.SPBCS
