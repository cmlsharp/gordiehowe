-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Sampler.Basic
public import GordieHowe.SPBCS.Sampler.Unrank
public import GordieHowe.Model.IOP.Append
public import GordieHowe.Model.IOP.Completeness
public import GordieHowe.Model.IOP.AppendN
public import GordieHowe.Model.IOP.DropMessage
public import GordieHowe.ProofSystem.GKR.Schedule

@[expose] public section

/-!
# Challenge readers

A challenge round of the C++ protocol reads its challenge from one challenge point of the
transcript (`lib/random/transcript.h` lines 36–52): a run of `RandomEngine` draws, each a field
`sample`, a `nat` or a `choose`, reading consecutive bytes of the point's stream. A
`CReader C` is that run as a `Reader` (`GordieHowe/SPBCS/Sampler/Basic.lean`) at an attempt bound `t` for every
rejection loop, with

- `uniform`: the challenge is uniform on success (`Reader.Uniform`, which gives the `Sampler`
  law `card_eq`);
- `load`: the number of draws and a bound on the bytes of one attempt, with the Chernoff data of
  `Reader.failProb_le_ofReal`: every attempt reads at most `load.bytes` bytes and is accepted with
  probability at least `1/2` (every C++ rejection sampler masks to the bit length of its bound),
  so the generating function of the bytes read is at most `geomPgf z load.bytes ^ load.draws`
  (`pgf_rej_le`) and the probability of exhausting the attempt bound is at most
  `load.draws · 2^-t` (`pfail_rej_le`).

The combinators follow the C++ calls: `prime`, `binary`, `ext` (a field `sample`), `nat`,
`choose`, `prod` (two runs one after the other), `pi` (`RandomEngine::elt(e, n, F)`, `n` draws in
order) and `map` along an equivalence. Each reader carries an unranking of its exact paths
(`unrank`, `Reader.Unrank`), from which `SpecReaders.preimage` builds the preimage sampler of each
round's sampler (`Sampler.Preimage`, used by the zero-knowledge simulator).

`SpecReaders P` is a reader for every challenge round of a protocol `P`, with the combinators of
the protocol constructions: `one`, `oneP`, `empty`, `append`, `appendN`, `dropMsg`. `SpecReaders.sampler` is the
challenge sampler of every round on the `k + e`-byte stream (`Sampler.ofReader` at attempt bound
`k + e`, where the bound is never reached: `run_rej_of_length_lt`), and `sum_δ_le` bounds the sum
of the rejection probabilities by the number of rounds times the per-round Chernoff bound.
-/

namespace GordieHowe.SPBCS
open GordieHowe.QROM

open GordieHowe.IOP IOP.ProtocolSpec
open scoped ENNReal

/-! ### The geometric generating function -/

/-- `E[z^(b G)]` for `G ~ Geometric(1/2)` on `{1, 2, …}`: `z^b / (2 - z^b)` (`fs_budget.py`,
`log_mgf_geom_half`). -/
noncomputable def geomPgf (z : ℝ) (b : ℕ) : ℝ := z ^ b / (2 - z ^ b)

theorem one_le_geomPgf {z : ℝ} (hz : 1 ≤ z) {b : ℕ} (hzb : z ^ b < 2) : 1 ≤ geomPgf z b := by
  have h1 : 1 ≤ z ^ b := one_le_pow₀ hz
  rw [geomPgf, le_div_iff₀ (by linarith)]
  linarith

theorem geomPgf_nonneg {z : ℝ} (hz : 1 ≤ z) {b : ℕ} (hzb : z ^ b < 2) : 0 ≤ geomPgf z b :=
  zero_le_one.trans (one_le_geomPgf hz hzb)

/-- `geomPgf z` is monotone in the byte count below the bound `z^b < 2`. -/
theorem geomPgf_mono {z : ℝ} (hz : 1 ≤ z) {b b' : ℕ} (hbb : b ≤ b') (hzb : z ^ b' < 2) :
    geomPgf z b ≤ geomPgf z b' := by
  have hp : z ^ b ≤ z ^ b' := pow_le_pow_right₀ hz hbb
  have h1 : 1 ≤ z ^ b := one_le_pow₀ hz
  unfold geomPgf
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- Reading `b` bytes with no rejection is dominated by the geometric bound. -/
theorem pow_le_geomPgf {z : ℝ} (hz : 1 ≤ z) {b : ℕ} (hzb : z ^ b < 2) : z ^ b ≤ geomPgf z b := by
  have h1 : 1 ≤ z ^ b := one_le_pow₀ hz
  rw [geomPgf, le_div_iff₀ (by linarith)]
  nlinarith

/-! ### Loads -/

/-- The load of a run of draws: the number of draws and a bound on the bytes of one attempt. -/
structure Load where
  draws : ℕ
  bytes : ℕ

namespace Load

/-- The per-round Chernoff bound of a load at `z` on an `N`-byte stream with attempt bound `t`:
`geomPgf z bytes ^ draws / z^(N+1) + draws · 2^-t`. -/
noncomputable def bound (z : ℝ) (N t : ℕ) (L : Load) : ℝ :=
  geomPgf z L.bytes ^ L.draws / z ^ (N + 1) + L.draws * (1 / 2) ^ t

/-- Two runs one after the other. -/
def add (L L' : Load) : Load := ⟨L.draws + L'.draws, max L.bytes L'.bytes⟩

/-- `n` runs one after the other. -/
def nsmul (n : ℕ) (L : Load) : Load := ⟨n * L.draws, L.bytes⟩

/-- **The componentwise order of loads**: at most as many draws, and attempts of at most as many
bytes. -/
structure Le (L L' : Load) : Prop where
  /-- At most as many draws. -/
  draws : L.draws ≤ L'.draws
  /-- Attempts of at most as many bytes. -/
  bytes : L.bytes ≤ L'.bytes

instance : Preorder Load where
  le := Le
  le_refl _ := ⟨le_rfl, le_rfl⟩
  le_trans _ _ _ h h' := ⟨h.draws.trans h'.draws, h.bytes.trans h'.bytes⟩

theorem le_iff {L L' : Load} : L ≤ L' ↔ L.draws ≤ L'.draws ∧ L.bytes ≤ L'.bytes :=
  ⟨fun h => ⟨h.draws, h.bytes⟩, fun h => ⟨h.1, h.2⟩⟩

/-- Componentwise maximum. -/
def max (L L' : Load) : Load := ⟨Max.max L.draws L'.draws, Max.max L.bytes L'.bytes⟩

theorem le_max_left (L L' : Load) : L ≤ L.max L' := ⟨Nat.le_max_left _ _, Nat.le_max_left _ _⟩

theorem le_max_right (L L' : Load) : L' ≤ L.max L' :=
  ⟨Nat.le_max_right _ _, Nat.le_max_right _ _⟩

theorem nsmul_le_nsmul (L : Load) {n n' : ℕ} (h : n ≤ n') : L.nsmul n ≤ L.nsmul n' :=
  ⟨Nat.mul_le_mul_right _ h, le_rfl⟩

theorem bound_mono {z : ℝ} (hz : 1 ≤ z) {N t : ℕ} {L L' : Load} (h : L ≤ L')
    (hzb : z ^ L'.bytes < 2) : L.bound z N t ≤ L'.bound z N t := by
  have hzb' : z ^ L.bytes < 2 := (pow_le_pow_right₀ hz h.bytes).trans_lt hzb
  have h1 : 1 ≤ geomPgf z L'.bytes := one_le_geomPgf hz hzb
  have hp : geomPgf z L.bytes ^ L.draws ≤ geomPgf z L'.bytes ^ L'.draws :=
    (pow_le_pow_left₀ (geomPgf_nonneg hz hzb') (geomPgf_mono hz h.bytes hzb) _).trans
      (pow_le_pow_right₀ h1 h.draws)
  unfold bound
  gcongr
  exact_mod_cast h.draws

/-- The Chernoff bound decreases in the stream length and in the attempt bound. -/
theorem bound_anti {z : ℝ} (hz : 1 ≤ z) {L : Load} (hzb : z ^ L.bytes < 2) {N N' t t' : ℕ}
    (hN : N ≤ N') (ht : t ≤ t') : L.bound z N' t' ≤ L.bound z N t := by
  unfold bound
  have hg : 0 ≤ geomPgf z L.bytes ^ L.draws := pow_nonneg (geomPgf_nonneg hz hzb) _
  refine add_le_add (div_le_div_of_nonneg_left hg (by positivity)
    (pow_le_pow_right₀ hz (by omega))) (mul_le_mul_of_nonneg_left
    (pow_le_pow_of_le_one (by norm_num) (by norm_num) ht) (Nat.cast_nonneg _))

end Load

/-! ### Uniformity through a map with fibres of equal size -/

namespace Reader

variable {α β : Type}

/-- **The fibres of `g` have equal size.** -/
def EqualFibres [Fintype α] [DecidableEq β] (g : α → β) : Prop :=
  ∀ c c', (Finset.univ.filter fun a => g a = c).card = (Finset.univ.filter fun a => g a = c').card

theorem equalFibres_iff [Fintype α] [DecidableEq β] {g : α → β} :
    EqualFibres g ↔
      ∀ c c', (Finset.univ.filter fun a => g a = c).card =
        (Finset.univ.filter fun a => g a = c').card :=
  Iff.rfl

/-- Mapping a uniform reader along a map whose fibres have equal size keeps it uniform (a
projection of a product forgets draws without biasing the rest). -/
theorem Uniform.map_of_card_fibre [Fintype α] [DecidableEq α] [DecidableEq β] {R : Reader α}
    (hR : R.Uniform) (g : α → β) (hg : EqualFibres g) :
    (R.map g).Uniform := by
  intro j c c'
  by_cases hα : Nonempty α
  · obtain ⟨a₀⟩ := hα
    have hconst : ∀ a, R.exact j a = R.exact j a₀ := fun a => hR j a a₀
    rw [exact_map, exact_map]
    simp only [hconst]
    rw [← Finset.sum_filter, ← Finset.sum_filter, Finset.sum_const, Finset.sum_const, hg c c']
  · rw [not_nonempty_iff] at hα
    rw [exact_map, exact_map]
    simp

/-- The first projection of a product has fibres of equal size. -/
theorem equalFibres_fst {γ δ : Type} [Fintype γ] [Fintype δ] [DecidableEq γ] :
    EqualFibres (Prod.fst : γ × δ → γ) := by
  intro c c'
  have h : ∀ c : γ, (Finset.univ.filter fun a : γ × δ => a.1 = c).card = Fintype.card δ := by
    intro c
    have he : (Finset.univ.filter fun a : γ × δ => a.1 = c) =
        ({c} : Finset γ) ×ˢ (Finset.univ : Finset δ) := by
      ext ⟨x, y⟩
      simp [eq_comm]
    rw [he, Finset.card_product]
    simp
  rw [h, h]

/-- Uniformity does not depend on the decidable equality used to count. -/
theorem uniform_congr {R : Reader α} (i i' : DecidableEq α) :
    @Uniform α i R ↔ @Uniform α i' R := by
  rw [Subsingleton.elim i i']

end Reader

/-! ### Challenge readers -/

/-- **A challenge reader**: the C++ draws of one challenge round as a reader at every attempt
bound `t`, uniform on success, with its load and the Chernoff data of the load, and the stream
bytes the C++ grants the round's point beyond the transcript's default budget. -/
structure CReader (C : Type) where
  /-- The reader at attempt bound `t` for every rejection loop. -/
  R : ℕ → Reader C
  /-- The challenge is uniform on success. -/
  uniform : ∀ t, @Reader.Uniform C (Classical.decEq C) (R t)
  /-- The draws and the bytes of one attempt. -/
  load : Load
  /-- The generating function of the bytes read is at most the geometric bound. -/
  pgf_le : ∀ {z : ℝ}, 1 ≤ z → z ^ load.bytes < 2 → ∀ t, (R t).pgf z ≤ geomPgf z load.bytes ^ load.draws
  /-- The probability of exhausting an attempt bound is at most `draws · 2^-t`. -/
  pfail_le : ∀ t, (R t).pfail ≤ load.draws * (1 / 2) ^ t
  /-- An unranking of the exact paths of the reader at every attempt bound (`Reader.Unrank`), from
  which the preimage sampler of the round's sampler is built (`SpecReaders.preimage`). -/
  unrank : ∀ t, (R t).Unrank
  /-- The value read where the reader rejects (the verifier rejects there), so that the challenges
  of a transcript are a total function. -/
  default : C
  /-- The stream bytes the C++ grants the point beyond the default budget `k + e`
  (`BasicTranscript::extend_point_budget`, `lib/random/transcript.h`); `0` for a point that is not
  extended. -/
  grant : ℕ := 0

namespace CReader

variable {C D E : Type}

theorem uniform' [DecidableEq C] (r : CReader C) (t : ℕ) : (r.R t).Uniform :=
  (Reader.uniform_congr _ _).mp (r.uniform t)

/-- **The rejection probability of a challenge reader** on an `N`-byte stream at attempt
bound `t`: at most the load's Chernoff bound (`Reader.failProb_le_ofReal`). -/
theorem failProb_le (r : CReader C) {z : ℝ} (hz : 1 ≤ z) (hzb : z ^ r.load.bytes < 2)
    (N t : ℕ) : (r.R t).failProb N ≤ ENNReal.ofReal (r.load.bound z N t) := by
  refine (Reader.failProb_le_ofReal hz (r.R t) N).trans (ENNReal.ofReal_le_ofReal ?_)
  unfold Load.bound
  gcongr
  · exact r.pgf_le hz hzb t
  · exact r.pfail_le t

/-- A uniform reader, counted with the classical decidable equality. -/
theorem uniform_classical [DecidableEq C] {R : Reader C} (h : R.Uniform) :
    @Reader.Uniform C (Classical.decEq C) R :=
  (Reader.uniform_congr _ _).mp h

/-- The reader read through an equivalence of challenge types. -/
def map [Fintype C] (r : CReader C) (e : C ≃ D) : CReader D where
  R t := (r.R t).map e
  uniform t := by
    classical
    exact uniform_classical ((r.uniform' t).map_equiv e)
  load := r.load
  pgf_le hz hzb t := by rw [Reader.pgf_map]; exact r.pgf_le hz hzb t
  pfail_le t := by rw [Reader.pfail_map]; exact r.pfail_le t
  unrank t := (r.unrank t).map e
  default := e r.default
  grant := r.grant

@[simp] theorem map_load [Fintype C] (r : CReader C) (e : C ≃ D) : (r.map e).load = r.load := rfl

/-- The reader at a type equal to its challenge type. -/
def cast (r : CReader C) (h : C = D) : CReader D := h ▸ r

@[simp] theorem cast_load (r : CReader C) (h : C = D) : (r.cast h).load = r.load := by
  subst h
  rfl

/-- Two runs one after the other (`RandomEngine` draws in sequence within one point). -/
def prod [Fintype C] [Fintype D] (r : CReader C) (r' : CReader D) : CReader (C × D) where
  R t := (r.R t).prod (r'.R t)
  uniform t := by
    classical
    exact uniform_classical ((r.uniform' t).prod (r'.uniform' t))
  load := r.load.add r'.load
  pgf_le {z} hz hzb t := by
    have hb : z ^ r.load.bytes < 2 :=
      (pow_le_pow_right₀ hz (le_max_left _ _)).trans_lt hzb
    have hb' : z ^ r'.load.bytes < 2 :=
      (pow_le_pow_right₀ hz (le_max_right _ _)).trans_lt hzb
    have hg := one_le_geomPgf hz hzb
    refine (Reader.pgf_prod_le (by linarith) _ _).trans ?_
    simp only [Load.add, pow_add]
    exact mul_le_mul
      ((r.pgf_le hz hb t).trans (pow_le_pow_left₀ (geomPgf_nonneg hz hb)
        (geomPgf_mono hz (le_max_left _ _) hzb) _))
      ((r'.pgf_le hz hb' t).trans (pow_le_pow_left₀ (geomPgf_nonneg hz hb')
        (geomPgf_mono hz (le_max_right _ _) hzb) _))
      (Reader.pgf_nonneg (by linarith) _)
      (pow_nonneg (geomPgf_nonneg hz (by simpa [Load.add] using hzb)) _)
  pfail_le t := by
    refine (Reader.pfail_prod_le _ _).trans ?_
    simp only [Load.add, Nat.cast_add, add_mul]
    exact add_le_add (r.pfail_le t) (r'.pfail_le t)
  unrank t := (r.unrank t).prod (r'.unrank t)
  default := (r.default, r'.default)
  grant := r.grant + r'.grant

@[simp] theorem prod_load [Fintype C] [Fintype D] (r : CReader C) (r' : CReader D) :
    (r.prod r').load = r.load.add r'.load := rfl

/-- A tuple of runs, each with load at most `L`, one after the other. -/
def piDep {n : ℕ} {β : Fin n → Type} [∀ i, Fintype (β i)] (r : ∀ i, CReader (β i)) (L : Load)
    (hL : ∀ i, (r i).load ≤ L) : CReader (∀ i, β i) where
  R t := Reader.pi fun i => (r i).R t
  uniform t := by
    classical
    exact uniform_classical (Reader.Uniform.pi fun i => (r i).uniform' t)
  load := L.nsmul n
  pgf_le {z} hz hzb t := by
    refine (Reader.pgf_pi_le (by linarith) _).trans ?_
    have hg := one_le_geomPgf hz hzb
    have hi : ∀ i, ((r i).R t).pgf z ≤ geomPgf z L.bytes ^ L.draws := fun i => by
      have hb : z ^ (r i).load.bytes < 2 := (pow_le_pow_right₀ hz (hL i).2).trans_lt hzb
      exact ((r i).pgf_le hz hb t).trans ((pow_le_pow_left₀ (geomPgf_nonneg hz hb)
        (geomPgf_mono hz (hL i).2 hzb) _).trans (pow_le_pow_right₀ hg (hL i).1))
    calc ∏ i, ((r i).R t).pgf z ≤ ∏ _i : Fin n, geomPgf z L.bytes ^ L.draws :=
          Finset.prod_le_prod₀ (fun i _ => Reader.pgf_nonneg (by linarith) _) fun i _ => hi i
      _ = geomPgf z (L.nsmul n).bytes ^ (L.nsmul n).draws := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Load.nsmul]
          rw [← pow_mul, mul_comm]
  pfail_le t := by
    refine (Reader.pfail_pi_le _).trans ?_
    calc ∑ i, ((r i).R t).pfail ≤ ∑ _i : Fin n, (L.draws : ℝ) * (1 / 2) ^ t :=
          Finset.sum_le_sum fun i _ => ((r i).pfail_le t).trans
            (mul_le_mul_of_nonneg_right (by exact_mod_cast (hL i).1) (by positivity))
      _ = _ := by simp [Load.nsmul, mul_assoc]
  unrank t := Reader.Unrank.pi fun i => (r i).unrank t
  default i := (r i).default
  grant := ∑ i, (r i).grant

@[simp] theorem piDep_load {n : ℕ} {β : Fin n → Type} [∀ i, Fintype (β i)]
    (r : ∀ i, CReader (β i)) (L : Load) (hL : ∀ i, (r i).load ≤ L) :
    (piDep r L hL).load = L.nsmul n := rfl

/-- `n` draws in order (`RandomEngine::elt(e, n, F)`, `third_party/longfellow/lib/random/random.h` lines 50–54). -/
def pi [Fintype C] (n : ℕ) (r : CReader C) : CReader (Fin n → C) :=
  piDep (fun _ => r) r.load fun _ => ⟨le_rfl, le_rfl⟩

@[simp] theorem pi_load [Fintype C] (n : ℕ) (r : CReader C) : (pi n r).load = r.load.nsmul n :=
  rfl

/-- **`n` tuples of `m` runs** load `n · m` runs. -/
theorem pi_pi_load [Fintype C] (n m : ℕ) (r : CReader C) :
    (pi n (pi m r)).load = r.load.nsmul (n * m) := by
  simp only [pi_load, Load.nsmul, Load.mk.injEq, and_true]
  ring

/-- **Two tuples of runs of one reader** load at most `a + (b + c)` runs of it, for any `a`. -/
theorem prod_pi_load_le [Fintype C] (r : CReader C) (a b c : ℕ) :
    ((pi b r).prod (pi c r)).load ≤ r.load.nsmul (a + (b + c)) := by
  simp only [prod_load, pi_load, Load.add, Load.nsmul, Load.le_iff]
  constructor
  · ring_nf
    omega
  · simp

/-- **The reader with its point granted `g` more stream bytes** (`extend_point_budget`, which adds
to the point's grant until the point closes); the draws are unchanged. -/
def extend (r : CReader C) (g : ℕ) : CReader C := { r with grant := r.grant + g }

@[simp] theorem extend_load (r : CReader C) (g : ℕ) : (r.extend g).load = r.load := rfl

@[simp] theorem extend_grant (r : CReader C) (g : ℕ) : (r.extend g).grant = r.grant + g := rfl

@[simp] theorem cast_grant (r : CReader C) (h : C = D) : (r.cast h).grant = r.grant := by
  subst h
  rfl

/-! ### Field elements, `nat` and `choose` -/

open Rejection in
/-- An attempt of `nat(m)`, `m > 0`, is accepted with probability at least `1/2`: it masks to the
bit length of `m`. -/
theorem two_mul_card_natReader_none_le {m : ℕ} (hm : 0 < m) :
    2 * (Finset.univ.filter fun v => acc (byteLen m) (Nat.size m) m v = none).card ≤
      256 ^ byteLen m := by
  rw [card_natReader_none]
  have hs := size_le_byteLen m
  have hpos := Nat.size_pos.2 hm
  have hlow : 2 ^ (Nat.size m - 1) ≤ m := by
    by_contra h
    have := (Nat.size_le (m := m) (n := Nat.size m - 1)).2 (by omega)
    omega
  have h256 : (256 : ℕ) ^ byteLen m = 2 ^ (8 * byteLen m) := by rw [pow_mul]; norm_num
  have hprod : 2 ^ (8 * byteLen m - 1) ≤ m * 2 ^ (8 * byteLen m - Nat.size m) := by
    calc 2 ^ (8 * byteLen m - 1) = 2 ^ (Nat.size m - 1) * 2 ^ (8 * byteLen m - Nat.size m) := by
          rw [← pow_add]; congr 1; omega
      _ ≤ _ := Nat.mul_le_mul_right _ hlow
  have htwo : 2 * 2 ^ (8 * byteLen m - 1) = 2 ^ (8 * byteLen m) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- `nat(m)` for `m > 0` (`third_party/longfellow/lib/random/random.h` lines 56–89): `byteLen m` bytes, little-endian,
masked to `size m` bits, rejected if `≥ m`. -/
def nat (m : ℕ) (hm : 0 < m) : CReader (Fin m) where
  R t := natReader m t
  uniform t := uniform_classical (uniform_natReader m t)
  load := ⟨1, Rejection.byteLen m⟩
  pgf_le hz hzb t := by
    rw [pow_one]
    exact Reader.pgf_rej_le _ hz hzb (two_mul_card_natReader_none_le hm) t
  pfail_le t := by
    rw [Nat.cast_one, one_mul]
    exact Reader.pfail_rej_le _ (two_mul_card_natReader_none_le hm) t
  unrank t := Reader.Unrank.rej
    (Rejection.natChunk (Rejection.size_le_byteLen m) (Nat.lt_size_self m).le) t
  default := ⟨0, hm⟩

@[simp] theorem nat_load (m : ℕ) (hm : 0 < m) : (nat m hm).load = ⟨1, Rejection.byteLen m⟩ := rfl

/-- A prime-field `sample` (`fp14.h` lines 292–305, `fp24.h` lines 286–299,
`fp_goldilocks.h` lines 167–174): `nat(m)`, then the element represented by the integer read
(`to_montgomery`, the residue of the integer). -/
def prime {F : Type} {m : ℕ} (hm : 0 < m) (e : Fin m ≃ F) : CReader F := (nat m hm).map e

@[simp] theorem prime_load {F : Type} {m : ℕ} (hm : 0 < m) (e : Fin m ≃ F) :
    (prime hm e).load = ⟨1, Rejection.byteLen m⟩ := rfl

theorem pgf_bytes (z : ℝ) (b : ℕ) : (Reader.bytes b).pgf z = z ^ b := by
  have h := Reader.pgf_bytes_bind z (b := b) Reader.done
  rw [Reader.bind_done] at h
  rw [h]
  simp only [Reader.pgf, Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  rw [div_pow]
  push_cast
  field_simp

theorem pfail_bytes (b : ℕ) : (Reader.bytes b).pfail = 0 := by
  have h := Reader.pfail_bytes_bind (b := b) Reader.done
  rw [Reader.bind_done] at h
  rw [h]
  simp [Reader.pfail]

/-- A binary-field `sample` (`gf2_128.h` lines 197–205, `gf2_256.h` lines 195–203): `b` raw
bytes, every string an element (`e`). -/
def binary {F : Type} [Fintype F] {b : ℕ} (e : (Fin b → Byte) ≃ F) : CReader F where
  R _ := bytesReader e
  uniform _ := by
    classical
    exact uniform_classical (uniform_bytesReader e)
  load := ⟨1, b⟩
  pgf_le hz hzb _ := by
    rw [bytesReader, Reader.pgf_map, pgf_bytes, pow_one]
    exact pow_le_geomPgf hz hzb
  pfail_le t := by
    rw [bytesReader, Reader.pfail_map, pfail_bytes]
    positivity
  unrank _ := (Reader.Unrank.bytes b).map e
  default := e fun _ => 0

@[simp] theorem binary_load {F : Type} [Fintype F] {b : ℕ} (e : (Fin b → Byte) ≃ F) :
    (binary e).load = ⟨1, b⟩ := rfl

/-- An extension-field `sample` (`fp2.h` lines 204–209, `fp_goldilocks.h` lines 344–349,
`fp_native_wide.h` lines 372–379): the `d` coordinates in order, each by `r`, then the element with
those coordinates (`e`). -/
def ext {F E : Type} [Fintype F] {d : ℕ} (r : CReader F) (e : (Fin d → F) ≃ E) : CReader E :=
  (pi d r).map e

@[simp] theorem ext_load {F E : Type} [Fintype F] {d : ℕ} (r : CReader F) (e : (Fin d → F) ≃ E) :
    (ext r e).load = r.load.nsmul d := rfl

theorem byteLen_mono {m n : ℕ} (h : m ≤ n) : Rejection.byteLen m ≤ Rejection.byteLen n := by
  unfold Rejection.byteLen
  have := Nat.size_le_size h
  omega

/-- `choose(res, n, k)` for `k ≤ n` (`third_party/longfellow/lib/random/random.h` lines 91–105): `k` draws
`nat(n - i)`, then Fisher–Yates: a uniform `Fin k ↪ Fin n`. -/
def choose (n k : ℕ) (hk : k ≤ n) : CReader (Fin k ↪ Fin n) :=
  (piDep (fun i : Fin k => nat (n - i) (by omega)) ⟨1, Rejection.byteLen n⟩
    fun i => ⟨le_rfl, byteLen_mono (Nat.sub_le n i)⟩).map FisherYates.equiv

@[simp] theorem choose_load (n k : ℕ) (hk : k ≤ n) :
    (choose n k hk).load = ⟨k * 1, Rejection.byteLen n⟩ := rfl

end CReader

/-! ### A reader for every challenge round -/

variable {n n₁ n₂ m : ℕ}

/-- **A challenge reader for every challenge round** of `P`. -/
abbrev SpecReaders (P : ProtocolSpec n) := ∀ i : P.ChallengeIdx, CReader (P.Challenge i)

namespace SpecReaders

/-- Every round's load satisfies `good`. -/
def AllLoads {P : ProtocolSpec n} (rd : SpecReaders P) (good : Load → Prop) : Prop :=
  ∀ i, good (rd i).load

theorem AllLoads.mono {P : ProtocolSpec n} {rd : SpecReaders P} {good good' : Load → Prop}
    (h : rd.AllLoads good) (hg : ∀ L, good L → good' L) : rd.AllLoads good' := fun i => hg _ (h i)

/-- A challenge round of one message. -/
def one (C : Type) (r : CReader C) : SpecReaders (GKR.Schedule.one .V_to_P C) := fun _ => r

theorem one_allLoads {C : Type} (r : CReader C) {good : Load → Prop} (h : good r.load) :
    (one C r).AllLoads good := fun _ => h

/-- A prover round of one message has no challenge round. -/
def oneP (M : Type) : SpecReaders (GKR.Schedule.one .P_to_V M) :=
  fun i => absurd i.2 (by simp [GKR.Schedule.one])

theorem oneP_allLoads (M : Type) (good : Load → Prop) : (oneP M).AllLoads good :=
  fun i => absurd i.2 (by simp [GKR.Schedule.one])

/-- The empty protocol. -/
def empty : SpecReaders GKR.Schedule.empty := fun i => i.1.elim0

theorem empty_allLoads (good : Load → Prop) : empty.AllLoads good := fun i => i.1.elim0

variable {P₁ : ProtocolSpec n₁} {P₂ : ProtocolSpec n₂}

/-- Two protocols one after the other. -/
def append (r₁ : SpecReaders P₁) (r₂ : SpecReaders P₂) : SpecReaders (P₁ ++ P₂) := fun i =>
  match h : challengeIdxEquiv i with
  | .inl j => (r₁ j).cast (append_Challenge_of_inl h).symm
  | .inr j => (r₂ j).cast (append_Challenge_of_inr h).symm

/-- `r₁ ++ r₂` is `r₁.append r₂`. -/
instance : HAppend (SpecReaders P₁) (SpecReaders P₂) (SpecReaders (P₁ ++ P₂)) := ⟨append⟩

theorem append_allLoads {r₁ : SpecReaders P₁} {r₂ : SpecReaders P₂} {good : Load → Prop}
    (h₁ : r₁.AllLoads good) (h₂ : r₂.AllLoads good) : (r₁ ++ r₂).AllLoads good := by
  change (r₁.append r₂).AllLoads good
  intro i
  unfold append
  split
  · rw [CReader.cast_load]; exact h₁ _
  · rw [CReader.cast_load]; exact h₂ _

/-- **The second part's loads** of an append satisfy what the append's do. -/
theorem allLoads_of_append_right {r₁ : SpecReaders P₁} {r₂ : SpecReaders P₂} {good : Load → Prop}
    (h : (r₁ ++ r₂).AllLoads good) : r₂.AllLoads good := by
  intro j
  have hj := h (ChallengeIdx.inr (P₁ := P₁) j)
  change good ((r₁.append r₂) _).load at hj
  unfold append at hj
  split at hj
  · rename_i _ h'
    rw [challengeIdxEquiv_inr] at h'
    exact absurd h' (by simp)
  · rename_i j' h'
    rw [challengeIdxEquiv_inr] at h'
    obtain rfl := Sum.inr_injective h'
    rwa [CReader.cast_load] at hj

/-- **The first part's loads** of an append satisfy what the append's do. -/
theorem allLoads_of_append_left {r₁ : SpecReaders P₁} {r₂ : SpecReaders P₂} {good : Load → Prop}
    (h : (r₁ ++ r₂).AllLoads good) : r₁.AllLoads good := by
  intro j
  have hj := h (ChallengeIdx.inl (P₂ := P₂) j)
  change good ((r₁.append r₂) _).load at hj
  unfold append at hj
  split at hj
  · rename_i j' h'
    rw [challengeIdxEquiv_inl] at h'
    obtain rfl := Sum.inl_injective h'
    rwa [CReader.cast_load] at hj
  · rename_i _ h'
    rw [challengeIdxEquiv_inl] at h'
    exact absurd h' (by simp)

/-- **The readers of an `m`-fold append** (`ProtocolSpec.appendN`): each round's reader is its
part's, by the recursion of `appendN`. -/
def appendN : (m : ℕ) → {n : Fin m → ℕ} → {P : (i : Fin m) → ProtocolSpec (n i)} →
    (∀ i, SpecReaders (P i)) → SpecReaders (ProtocolSpec.appendN m P)
  | 0, _, _, _ => fun i => i.1.elim0
  | 1, _, _, r => r 0
  | m + 2, _, _, r => r 0 ++ appendN (m + 1) fun i => r i.succ

theorem appendN_allLoads {good : Load → Prop} : (m : ℕ) → {n : Fin m → ℕ} →
    {P : (i : Fin m) → ProtocolSpec (n i)} → {r : ∀ i, SpecReaders (P i)} →
    (∀ i, (r i).AllLoads good) → (appendN m r).AllLoads good
  | 0, _, _, _, _ => fun i => i.1.elim0
  | 1, _, _, _, h => h 0
  | m + 2, _, _, _, h => append_allLoads (h 0) (appendN_allLoads (m + 1) fun i => h i.succ)

/-- **The readers of a protocol with a prover round removed** (`ProtocolSpec.dropMsg`): each
challenge round keeps its reader. -/
def dropMsg {Q : ProtocolSpec n} (r : SpecReaders Q) (s : Fin n) : SpecReaders (Q.dropMsg s) :=
  fun i => r (dropChallengeIdx i)

theorem dropMsg_allLoads {Q : ProtocolSpec n} {r : SpecReaders Q} (s : Fin n) {good : Load → Prop}
    (hr : r.AllLoads good) : (r.dropMsg s).AllLoads good := fun _ => hr _

variable {P : ProtocolSpec n}

/-- **The stream length of every round** at the default budget `base`: the default and the round's
grant (`CReader.grant`), the C++ `N_i = k + e + grant_i`. -/
def streamLength (rd : SpecReaders P) (base : ℕ) (i : P.ChallengeIdx) : ℕ := base + (rd i).grant

theorem le_streamLength (rd : SpecReaders P) (base : ℕ) (i : P.ChallengeIdx) :
    base ≤ rd.streamLength base i :=
  Nat.le_add_right _ _

/-- **The largest grant** of a round. -/
def maxGrant [Fintype P.ChallengeIdx] (rd : SpecReaders P) : ℕ :=
  Finset.univ.sup fun i => (rd i).grant

theorem streamLength_le_maxGrant [Fintype P.ChallengeIdx] (rd : SpecReaders P) (base : ℕ)
    (i : P.ChallengeIdx) : rd.streamLength base i ≤ base + rd.maxGrant :=
  Nat.add_le_add_left (Finset.le_sup (f := fun i => (rd i).grant) (Finset.mem_univ i)) _

/-- **The challenge samplers** of the rounds on the `k + e`-byte stream, round `i` reading at most
`N i` bytes: each round's reader at attempt bound `N i` (never reached on `N i` bytes,
`run_rej_of_length_lt`, so this is the unbounded C++ loop), cut off after `N i` bytes
(`Reader.limit`, the C++ per-point budget check). -/
def sampler [∀ i, Fintype (P.Challenge i)] [∀ i, DecidableEq (P.Challenge i)]
    (rd : SpecReaders P) (k e : ℕ) (N : P.ChallengeIdx → ℕ) (i : P.ChallengeIdx) :
    Sampler k e (P.Challenge i) :=
  Sampler.ofReader (((rd i).R (N i)).limit (N i)) (((rd i).uniform' _).limit _) (rd i).default

/-- **The preimage samplers of the rounds' samplers** (`Sampler.Preimage.ofUnrank` at the
round's unranking cut off after `N i` bytes): coins below the fibre size, each giving one stream
of the fibre.

Cost: the fibre size and one unranking, polynomial in `k + e` and the round's draws. -/
def preimage [∀ i, Fintype (P.Challenge i)] [∀ i, DecidableEq (P.Challenge i)]
    (rd : SpecReaders P) (k e : ℕ) (N : P.ChallengeIdx → ℕ) (i : P.ChallengeIdx) :
    (rd.sampler k e N i).Preimage :=
  Sampler.Preimage.ofUnrank _ (((rd i).unrank (N i)).limit (N i))

/-- **The rejection probability of a round's sampler** within the stream (`N i ≤ k + e`) is that of
its reader on `N i` bytes (`Reader.failProb_limit`). -/
theorem sampler_rejectionProb [∀ i, Fintype (P.Challenge i)] [∀ i, DecidableEq (P.Challenge i)]
    (rd : SpecReaders P) {k e : ℕ} {N : P.ChallengeIdx → ℕ} {i : P.ChallengeIdx}
    (hN : N i ≤ k + e) : (rd.sampler k e N i).rejectionProb = ((rd i).R (N i)).failProb (N i) := by
  rw [sampler, Sampler.ofReader_rejectionProb, Reader.failProb_limit _ hN]

/-- **The sum of the rejection probabilities** of the samplers is at most the number of rounds
times `ε`, when every round's stream fits in the `k + e` bytes and every round's load has Chernoff
bound at most `ε` at some `z` on its own stream length (`CReader.failProb_le`). -/
theorem sum_δ_le [∀ i, Fintype (P.Challenge i)] [∀ i, DecidableEq (P.Challenge i)]
    (rd : SpecReaders P) {k e : ℕ} {N : P.ChallengeIdx → ℕ} (hN : ∀ i, N i ≤ k + e) {z ε : ℝ}
    (hz : 1 ≤ z) (hb : ∀ i, z ^ (rd i).load.bytes < 2)
    (h : ∀ i, (rd i).load.bound z (N i) (N i) ≤ ε) :
    ∑ i, (rd.sampler k e N i).rejectionProb ≤ Fintype.card P.ChallengeIdx * ENNReal.ofReal ε := by
  calc ∑ i, (rd.sampler k e N i).rejectionProb ≤ ∑ _i : P.ChallengeIdx, ENNReal.ofReal ε := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [sampler_rejectionProb rd (hN i)]
        exact ((rd i).failProb_le hz (hb i) _ _).trans (ENNReal.ofReal_le_ofReal (h i))
    _ = _ := by simp

end SpecReaders

end GordieHowe.SPBCS
