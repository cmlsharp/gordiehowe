-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import GordieHowe.Foundations.Algebra.PowMod
public import GordieHowe.Applications.Spec.Rq
public import LatticeCrypto.Falcon.ConcretePrimitives

@[expose] public section

/-!
# Falcon public-key decoding: the mod-`q` negacyclic NTT and its inverse

The Falcon emulated relation (`falcon_key` and `decode_key` in
`lib/gordiehowe/examples/falcon/falcon_emulated.h`) passes the public key in Falcon's mod-`12289` NTT
domain (`key_hat`). The verifier's preprocessing `decode_key` decodes it with
`emulated_ntt::decode(key_hat, qzetas, q)` (`lib/circuits/ntt/emulated_signature.h:82-88`): check
every entry is below `q`, then apply `falcon_intt_ref`. The signature rows use the decoded
coefficient vector. This preprocessing fixes the checked statement, so it is modelled here.

This file transcribes `falcon_ntt_zetas`, `falcon_ntt_ref` and `falcon_intt_ref`
(`lib/schemes/falcon/falcon_ntt.h`) and proves that decoding inverts the
forward transform in both directions.

## Transcription

* The loops are recursions on their iteration counts. The C++ loop bounds are
  `for (len = n/2; len >= 1; len >>= 1)` (forward, `log2 n` stages),
  `for (len = 1; len < n; len <<= 1)` (inverse, `log2 n` stages) and
  `for (start = 0; start < n; start += 2*len)` (`n / (2*len)` blocks); these counts are
  exact when `n` is a power of two, the only case the harness uses (`n = 512`).
* The forward block loop's counter `k` is threaded through the stages as in C++; after a
  stage of `n / (2*len)` blocks it has advanced by `n / (2*len)`, which the stage recursion
  adds explicitly. The inverse is symmetric.
* The in-place array is a function `ℕ → R`; each butterfly reads `a[j]` and `a[j+len]`
  before writing `a[j]`, then `a[j+len]`, as in C++. Indices at or above `n` are never read
  or written by the loops.
* The arithmetic is over `ZMod q`. Every C++ assignment stores `x % q` of an integer
  expression whose operands are below `q`: `t = z*a[j+len] % q`, `(u + t) % q`,
  `(u + q - t) % q` (forward), `(u + v) % q`, `z*((u + q - v) % q) % q` with
  `z = q - zetas[k]` (inverse), and `a[j]*ninv % q`. For operands below `q` these are
  `u + t`, `u - t`, `u + v`, `-zeta * (u - v)` and `a[j] * ninv` in `ZMod q`, so the natural
  number the C++ stores is the `ZMod.val` of the `ZMod q` value. The entries are below `q`
  on entry because `decode` checks it; the harness applies `falcon_ntt_ref` only to
  vectors reduced mod `q`.
* `falcon_powmod` is `GordieHowe.powMod`: both compute `b ^ e % q`
  (`powMod_eq_mod`).

## Results

`intt_ntt` and `ntt_intt` are the round trip for any commutative ring, any power of two
`n = 2 ^ L`, any twiddle table with the bit-reversal pairing `Paired`, and `ninv` with
`2 ^ L * ninv = 1`. The proof is stage by stage: the inverse stage at `len` undoes the forward
stage at `len` up to a factor `2` (`invStage_fwdStage`). The only fact about the root it uses
is `ψ ^ n = -1`, from which `falconZeta_paired` derives the pairing of the bit-reversed table
(`falconBrv_pair`). `falconDecode_eq_some_iff` states decoding for `ZMod q` with those two
`param` hypotheses; `falconDecode_512_eq_some_iff` discharges them at `n = 512`, `q = 12289`
(`falconRoot2n_512_pow`, `falconNinv_512`, each a `decide` on one `powMod` value), and
`falconDecode_eq_keyCoeffs_iff` / `falconDecode_keyHat` are the forms the signature rows'
instantiation uses. `falconRoot2n_512_isPrimitiveRoot` certifies that the C++ root has order
exactly `1024`.

In the Falcon emulated relation, `key_hat` is the public input `hhat`, which `falcon_key` checks
is canonical below `q`, and `qzetas` is `falcon_ntt_zetas(512, q)` (`decode_key`).

The vendored `Falcon.Concrete.ntt` (`Vendor/LatticeCrypto/Falcon/Concrete/NTT.lean`) uses the
same generator `11` and root `11 ^ 12`, but it proves no round trip and is written with
imperative `while` loops, so it is not reused.
-/

namespace GordieHowe.Falcon512.KeyNTT

/-! ## Host helpers on `ℕ` -/

/-- The loop of `falcon_log2` (`falcon_ntt.h:39-43`): `while ((1 << l) < n) ++l`, with a fuel
argument that bounds the iterations. -/
def log2Loop (n : ℕ) : ℕ → ℕ → ℕ
  | 0, l => l
  | fuel + 1, l => if 1 <<< l < n then log2Loop n fuel (l + 1) else l

/-- `falcon_log2` (`falcon_ntt.h:39-43`), starting at `l = 0` with fuel `n`. -/
def falconLog2 (n : ℕ) : ℕ := log2Loop n n 0

theorem log2Loop_two_pow (L : ℕ) :
    ∀ fuel l, l ≤ L → L - l ≤ fuel → log2Loop (2 ^ L) fuel l = L
  | 0, l, h1, h2 => by
    simp only [log2Loop]
    omega
  | fuel + 1, l, h1, h2 => by
    simp only [log2Loop, Nat.one_shiftLeft]
    by_cases h : l < L
    · rw [ite_eq_left (Nat.pow_lt_pow_right (by norm_num) h)]
      exact log2Loop_two_pow L fuel (l + 1) (by omega) (by omega)
    · have : 2 ^ L ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [ite_eq_right (by omega)]
      omega

theorem falconLog2_two_pow (L : ℕ) : falconLog2 (2 ^ L) = L :=
  log2Loop_two_pow L _ 0 (Nat.zero_le _) (by have := @Nat.lt_two_pow_self L; omega)

/-- The value of `r` in `falcon_brv` (`falcon_ntt.h:45-49`) after the first `i` iterations
of `for (i = 0; i < bits; ++i) r |= ((x >> i) & 1) << (bits - 1 - i)`. -/
def brvAcc (x bits : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => brvAcc x bits i ||| (((x >>> i) &&& 1) <<< (bits - 1 - i))

/-- `falcon_brv` (`falcon_ntt.h:45-49`): the low `bits` bits of `x`, reversed. -/
def falconBrv (x bits : ℕ) : ℕ := brvAcc x bits bits

/-- Setting bit `p` of a multiple of `2 ^ (p + 1)` adds `2 ^ p`. -/
theorem or_shiftLeft_eq_add {c t : ℕ} (p : ℕ) (ht : t < 2) :
    2 ^ (p + 1) * c ||| t <<< p = 2 ^ (p + 1) * c + t * 2 ^ p := by
  have h1 : 2 ^ (p + 1) * c = (2 ^ 1 * c) <<< p := by
    rw [Nat.shiftLeft_eq]
    ring
  rw [h1, ← Nat.shiftLeft_or_distrib, ← Nat.two_pow_add_eq_or_of_lt (by simpa using ht),
    Nat.shiftLeft_eq, Nat.shiftLeft_eq]
  ring

/-- `brvAcc` is the sum of the reversed bits read so far, and it is a multiple of the
smallest bit position written so far. -/
theorem brvAcc_eq (x bits : ℕ) : ∀ i, i ≤ bits →
    brvAcc x bits i = ∑ j ∈ Finset.range i, x / 2 ^ j % 2 * 2 ^ (bits - 1 - j) ∧
      2 ^ (bits - i) ∣ brvAcc x bits i
  | 0, _ => by simp [brvAcc]
  | i + 1, hi => by
    obtain ⟨ih, hdvd⟩ := brvAcc_eq x bits i (by omega)
    have hp : bits - i = (bits - 1 - i) + 1 := by omega
    rw [hp] at hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hbit : (x >>> i) &&& 1 = x / 2 ^ i % 2 := by
      rw [Nat.and_one_is_mod, Nat.shiftRight_eq_div_pow]
    have hstep : brvAcc x bits (i + 1) =
        brvAcc x bits i + x / 2 ^ i % 2 * 2 ^ (bits - 1 - i) := by
      rw [brvAcc, hbit, hc, or_shiftLeft_eq_add _ (Nat.mod_lt _ (by norm_num))]
    refine ⟨by rw [hstep, ih, Finset.sum_range_succ], ?_⟩
    rw [hstep, show bits - (i + 1) = bits - 1 - i by omega, hc]
    exact Nat.dvd_add (Dvd.dvd.mul_right (pow_dvd_pow 2 (by omega)) c)
      (Dvd.intro_left _ rfl)

theorem falconBrv_eq_sum (x bits : ℕ) :
    falconBrv x bits = ∑ j ∈ Finset.range bits, x / 2 ^ j % 2 * 2 ^ (bits - 1 - j) :=
  (brvAcc_eq x bits bits le_rfl).1

/-- Reversing `L + 1` bits puts the lowest bit on top and reverses the remaining `L`. -/
theorem falconBrv_succ (x L : ℕ) :
    falconBrv x (L + 1) = x % 2 * 2 ^ L + falconBrv (x / 2) L := by
  rw [falconBrv_eq_sum, falconBrv_eq_sum, Finset.sum_range_succ', add_comm]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_range] at hj
    rw [Nat.div_div_eq_div_mul, ← pow_succ', show L + 1 - 1 - (j + 1) = L - 1 - j by omega]

theorem falconBrv_zero (L : ℕ) : falconBrv 0 L = 0 := by
  simp [falconBrv_eq_sum]

/-- The bit-reversal pairing: the twiddle index of block `b` in a forward stage with
`2 ^ s` blocks (`2 ^ s + b`) and the index the inverse uses for the same block
(`2 ^ (s + 1) - 1 - b`) have bit reversals summing to `2 ^ L`. -/
theorem falconBrv_pair {s L : ℕ} (hs : s < L) {b : ℕ} (hb : b < 2 ^ s) :
    falconBrv (2 ^ s + b) L + falconBrv (2 ^ (s + 1) - 1 - b) L = 2 ^ L := by
  induction s generalizing L b with
  | zero =>
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    obtain rfl : b = 0 := by simpa using hb
    show falconBrv 1 (L + 1) + falconBrv 1 (L + 1) = 2 ^ (L + 1)
    rw [falconBrv_succ, show 1 / 2 = 0 from rfl, falconBrv_zero, pow_succ]
    omega
  | succ s ih =>
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    have hP := pow_succ 2 s
    have hP2 := pow_succ 2 (s + 1)
    rw [falconBrv_succ, falconBrv_succ,
      show (2 ^ (s + 1) + b) / 2 = 2 ^ s + b / 2 by omega,
      show (2 ^ (s + 1 + 1) - 1 - b) / 2 = 2 ^ (s + 1) - 1 - b / 2 by omega]
    have hih := ih (L := L) (b := b / 2) (by omega) (by omega)
    have hbits : (2 ^ (s + 1) + b) % 2 + (2 ^ (s + 1 + 1) - 1 - b) % 2 = 1 := by omega
    calc (2 ^ (s + 1) + b) % 2 * 2 ^ L + falconBrv (2 ^ s + b / 2) L +
          ((2 ^ (s + 1 + 1) - 1 - b) % 2 * 2 ^ L + falconBrv (2 ^ (s + 1) - 1 - b / 2) L)
        = ((2 ^ (s + 1) + b) % 2 + (2 ^ (s + 1 + 1) - 1 - b) % 2) * 2 ^ L +
          (falconBrv (2 ^ s + b / 2) L + falconBrv (2 ^ (s + 1) - 1 - b / 2) L) := by ring
      _ = 2 ^ (L + 1) := by rw [hbits, hih]; ring

/-- The generator test of `falcon_root_2n` (`falcon_ntt.h:55-58`). -/
def isGen (q g : ℕ) : Bool :=
  powMod g ((q - 1) / 2) q != 1 && powMod g ((q - 1) / 3) q != 1

/-- The search `g = 2; while (!is_gen(g)) ++g` of `falcon_root_2n` (`falcon_ntt.h:59-60`),
with a fuel argument that bounds the iterations. -/
def findGen (q : ℕ) : ℕ → ℕ → ℕ
  | 0, g => g
  | fuel + 1, g => if isGen q g then g else findGen q fuel (g + 1)

/-- `falcon_root_2n` (`falcon_ntt.h:52-62`): `g ^ ((q - 1) / (2n)) % q` for the smallest
`g ≥ 2` passing the generator test (fuel `q`). -/
def falconRoot2n (n q : ℕ) : ℕ :=
  powMod (findGen q q 2) ((q - 1) / (2 * n)) q

/-- `falcon_ntt_zetas` (`falcon_ntt.h:65-71`): `zetas[i] = psi ^ brv(i) % q`. The C++ vector
has `n` entries; the transforms read indices `1` to `n - 1` only. -/
def falconNttZetas (n q i : ℕ) : ℕ :=
  powMod (falconRoot2n n q) (falconBrv i (falconLog2 n)) q

/-- `ninv = falcon_powmod(n % q, q - 2, q)` (`falcon_ntt.h:108`). -/
def falconNinv (n q : ℕ) : ℕ := powMod (n % q) (q - 2) q

/-! ## The transforms over a commutative ring -/

section Transform

variable {R : Type*} [CommRing R]

/-- The innermost loop `for (j = start; j < start + len; ++j)` of both transforms
(`falcon_ntt.h:81-86` and `:100-105`), run for `c` iterations from `j`. Each iteration reads
`u = a[j]`, `v = a[j+len]`, then writes `a[j] = f u v` and `a[j+len] = g u v`. -/
def butterflyLoop (f g : R → R → R) (len : ℕ) : ℕ → ℕ → (ℕ → R) → ℕ → R
  | _, 0, a => a
  | j, c + 1, a =>
    butterflyLoop f g len (j + 1) c
      (Function.update (Function.update a j (f (a j) (a (j + len)))) (j + len)
        (g (a j) (a (j + len))))

/-- The block loop `for (start = ...; start < n; start += 2*len)` of both transforms, run for
`c` iterations. `zAt k` is the twiddle read with counter value `k` and `next` the counter
update: `z = zetas[k++]` (`falcon_ntt.h:80`) or `z = q - zetas[--k]` (`falcon_ntt.h:99`). -/
def blockLoop (zAt : ℕ → R) (next : ℕ → ℕ) (f g : R → R → R → R) (len : ℕ) :
    ℕ → ℕ → ℕ → (ℕ → R) → ℕ → R
  | _, _, 0, a => a
  | k, start, c + 1, a =>
    blockLoop zAt next f g len (next k) (start + 2 * len) c
      (butterflyLoop (f (zAt k)) (g (zAt k)) len start len a)

/-- Forward butterfly, first output: `a[j] = (u + t) % q` with `t = z * a[j+len] % q`
(`falcon_ntt.h:82-84`). -/
def fwdF (z u v : R) : R := u + z * v

/-- Forward butterfly, second output: `a[j+len] = (u + q - t) % q` (`falcon_ntt.h:85`). -/
def fwdG (z u v : R) : R := u - z * v

/-- Inverse butterfly, first output: `a[j] = (u + v) % q` (`falcon_ntt.h:103`). -/
def invF (_z u v : R) : R := u + v

/-- Inverse butterfly, second output: `a[j+len] = z * ((u + q - v) % q) % q`
(`falcon_ntt.h:104`), where `z` is already `-zeta`. -/
def invG (z u v : R) : R := z * (u - v)

/-- The stage loop of `falcon_ntt_ref` (`falcon_ntt.h:78-89`), run for `c` iterations from
`len` with counter `k`; each stage runs `n / (2*len)` blocks and advances `k` by as much. -/
def fwdStages (ζ : ℕ → R) (n : ℕ) : ℕ → ℕ → ℕ → (ℕ → R) → ℕ → R
  | _, _, 0, a => a
  | len, k, c + 1, a =>
    fwdStages ζ n (len / 2) (k + n / (2 * len)) c
      (blockLoop ζ (· + 1) fwdF fwdG len k 0 (n / (2 * len)) a)

/-- `falcon_ntt_ref` (`falcon_ntt.h:74-90`): `k = 1`, `len` from `n / 2` down to `1`. -/
def ntt (ζ : ℕ → R) (n : ℕ) (a : ℕ → R) : ℕ → R :=
  fwdStages ζ n (n / 2) 1 (falconLog2 n) a

/-- The stage loop of `falcon_intt_ref` (`falcon_ntt.h:97-107`), run for `c` iterations from
`len` with counter `k`; the counter is decremented before each read, and `z = q - zetas[k]`
is `-ζ` in `ZMod q`. -/
def invStages (ζ : ℕ → R) (n : ℕ) : ℕ → ℕ → ℕ → (ℕ → R) → ℕ → R
  | _, _, 0, a => a
  | len, k, c + 1, a =>
    invStages ζ n (2 * len) (k - n / (2 * len)) c
      (blockLoop (fun k => -ζ (k - 1)) (· - 1) invF invG len k 0 (n / (2 * len)) a)

/-- The final loop `for (j = 0; j < n; ++j) a[j] = a[j] * ninv % q` (`falcon_ntt.h:109`),
run for `c` iterations from `j`. -/
def scaleLoop (s : R) : ℕ → ℕ → (ℕ → R) → ℕ → R
  | _, 0, a => a
  | j, c + 1, a => scaleLoop s (j + 1) c (Function.update a j (a j * s))

/-- `falcon_intt_ref` (`falcon_ntt.h:93-110`): `k = n`, `len` from `1` up to `n / 2`, then
multiplication by `ninv`. -/
def intt (ζ : ℕ → R) (ninv : R) (n : ℕ) (a : ℕ → R) : ℕ → R :=
  scaleLoop ninv 0 n (invStages ζ n 1 n (falconLog2 n) a)

/-! ### The loops, entry by entry -/

section Loops

variable {f g : R → R → R} {len : ℕ}

omit [CommRing R] in
theorem butterflyLoop_of_notMem {c j : ℕ} {a : ℕ → R} {i : ℕ} (h1 : i < j ∨ j + c ≤ i)
    (h2 : i < j + len ∨ j + len + c ≤ i) : butterflyLoop f g len j c a i = a i := by
  induction c generalizing j a with
  | zero => rfl
  | succ c ih =>
    rw [butterflyLoop, ih (by omega) (by omega), Function.update_of_ne (by omega),
      Function.update_of_ne (by omega)]

omit [CommRing R] in
theorem butterflyLoop_low {c j : ℕ} {a : ℕ → R} {r : ℕ} (hc : c ≤ len) (hr : r < c) :
    butterflyLoop f g len j c a (j + r) = f (a (j + r)) (a (j + r + len)) := by
  induction c generalizing j a r with
  | zero => omega
  | succ c ih =>
    rcases r with _ | r
    · simp only [Nat.add_zero]
      rw [butterflyLoop, butterflyLoop_of_notMem (by omega) (by omega),
        Function.update_of_ne (by omega), Function.update_self]
    · rw [butterflyLoop, show j + (r + 1) = j + 1 + r by omega, ih (by omega) (by omega)]
      simp only [Function.update_apply]
      split_ifs <;> first | omega | rfl

omit [CommRing R] in
theorem butterflyLoop_high {c j : ℕ} {a : ℕ → R} {r : ℕ} (hc : c ≤ len) (hr : r < c) :
    butterflyLoop f g len j c a (j + r + len) = g (a (j + r)) (a (j + r + len)) := by
  induction c generalizing j a r with
  | zero => omega
  | succ c ih =>
    rcases r with _ | r
    · simp only [Nat.add_zero]
      rw [butterflyLoop, butterflyLoop_of_notMem (by omega) (by omega), Function.update_self]
    · rw [butterflyLoop, show j + (r + 1) = j + 1 + r by omega, ih (by omega) (by omega)]
      simp only [Function.update_apply]
      split_ifs <;> first | omega | rfl

end Loops

section Blocks

variable {zAt : ℕ → R} {next : ℕ → ℕ} {f g : R → R → R → R} {len : ℕ}

omit [CommRing R] in
theorem blockLoop_of_notMem {c k start : ℕ} {a : ℕ → R} {i : ℕ}
    (h : i < start ∨ start + 2 * len * c ≤ i) :
    blockLoop zAt next f g len k start c a i = a i := by
  induction c generalizing k start a with
  | zero => rfl
  | succ c ih =>
    have : 2 * len * (c + 1) = 2 * len * c + 2 * len := by ring
    rw [blockLoop, ih (by omega), butterflyLoop_of_notMem (by omega) (by omega)]

omit [CommRing R] in
theorem blockLoop_low {c k start : ℕ} {a : ℕ → R} {b r : ℕ} (hb : b < c) (hr : r < len) :
    blockLoop zAt next f g len k start c a (start + 2 * len * b + r) =
      f (zAt (next^[b] k)) (a (start + 2 * len * b + r)) (a (start + 2 * len * b + r + len)) := by
  induction c generalizing k start a b with
  | zero => omega
  | succ c ih =>
    rcases b with _ | b
    · simp only [Nat.mul_zero, Nat.add_zero, Function.iterate_zero, id]
      rw [blockLoop, blockLoop_of_notMem (by omega), butterflyLoop_low le_rfl hr]
    · have hi : start + 2 * len * (b + 1) = start + 2 * len + 2 * len * b := by ring
      rw [blockLoop, hi, ih (by omega), Function.iterate_succ_apply,
        butterflyLoop_of_notMem (by omega) (by omega),
        butterflyLoop_of_notMem (by omega) (by omega)]

omit [CommRing R] in
theorem blockLoop_high {c k start : ℕ} {a : ℕ → R} {b r : ℕ} (hb : b < c) (hr : r < len) :
    blockLoop zAt next f g len k start c a (start + 2 * len * b + r + len) =
      g (zAt (next^[b] k)) (a (start + 2 * len * b + r)) (a (start + 2 * len * b + r + len)) := by
  induction c generalizing k start a b with
  | zero => omega
  | succ c ih =>
    rcases b with _ | b
    · simp only [Nat.mul_zero, Nat.add_zero, Function.iterate_zero, id]
      rw [blockLoop, blockLoop_of_notMem (by omega), butterflyLoop_high le_rfl hr]
    · have hi : start + 2 * len * (b + 1) = start + 2 * len + 2 * len * b := by ring
      rw [blockLoop, hi, ih (by omega), Function.iterate_succ_apply,
        butterflyLoop_of_notMem (by omega) (by omega),
        butterflyLoop_of_notMem (by omega) (by omega)]

omit [CommRing R] in
/-- `blockLoop_low` for a stage that starts at index `0`. -/
theorem blockLoop_low_zero {m k : ℕ} {a : ℕ → R} {b r : ℕ} (hb : b < m) (hr : r < len) :
    blockLoop zAt next f g len k 0 m a (2 * len * b + r) =
      f (zAt (next^[b] k)) (a (2 * len * b + r)) (a (2 * len * b + r + len)) := by
  simpa using blockLoop_low (zAt := zAt) (next := next) (f := f) (g := g) (start := 0) (k := k)
    (a := a) hb hr

omit [CommRing R] in
/-- `blockLoop_high` for a stage that starts at index `0`. -/
theorem blockLoop_high_zero {m k : ℕ} {a : ℕ → R} {b r : ℕ} (hb : b < m) (hr : r < len) :
    blockLoop zAt next f g len k 0 m a (2 * len * b + r + len) =
      g (zAt (next^[b] k)) (a (2 * len * b + r)) (a (2 * len * b + r + len)) := by
  simpa using blockLoop_high (zAt := zAt) (next := next) (f := f) (g := g) (start := 0) (k := k)
    (a := a) hb hr

end Blocks

theorem iterate_add_one (b k : ℕ) : (· + 1)^[b] k = k + b := by
  induction b generalizing k with
  | zero => rfl
  | succ b ih => rw [Function.iterate_succ_apply, ih]; omega

theorem iterate_sub_one (b k : ℕ) : (· - 1)^[b] k = k - b := by
  induction b generalizing k with
  | zero => rfl
  | succ b ih => rw [Function.iterate_succ_apply, ih]; omega

/-- Every index below `2 * len * m` is the low or the high entry of a butterfly. -/
theorem exists_block {len m i : ℕ} (hlen : 0 < len) (hi : i < 2 * len * m) :
    ∃ b r, b < m ∧ r < len ∧ (i = 2 * len * b + r ∨ i = 2 * len * b + r + len) := by
  have hdm := Nat.div_add_mod i (2 * len)
  have hmod := Nat.mod_lt i (show 0 < 2 * len by omega)
  have hb : i / (2 * len) < m := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]
    linarith
  by_cases hr : i % (2 * len) < len
  · exact ⟨i / (2 * len), i % (2 * len), hb, hr, Or.inl (by omega)⟩
  · exact ⟨i / (2 * len), i % (2 * len) - len, hb, by omega, Or.inr (by omega)⟩

theorem block_lt {len m b r : ℕ} (hb : b < m) (hr : r < len) :
    2 * len * b + r + len < 2 * len * m := by
  have h1 : 2 * len * (b + 1) ≤ 2 * len * m := Nat.mul_le_mul_left _ hb
  have h2 : 2 * len * (b + 1) = 2 * len * b + 2 * len := by ring
  omega

/-- Multiplication of the entries below `N` by `s`. -/
def scaleBelow (s : R) (N : ℕ) (a : ℕ → R) : ℕ → R := fun i => if i < N then a i * s else a i

theorem scaleBelow_scaleBelow (s t : R) (N : ℕ) (a : ℕ → R) :
    scaleBelow s N (scaleBelow t N a) = scaleBelow (t * s) N a := by
  funext i
  unfold scaleBelow
  split_ifs <;> ring

theorem scaleBelow_one (N : ℕ) (a : ℕ → R) : scaleBelow 1 N a = a := by
  funext i
  unfold scaleBelow
  split_ifs <;> simp

theorem scaleLoop_eq (s : R) (c j : ℕ) (a : ℕ → R) :
    scaleLoop s j c a = fun i => if j ≤ i ∧ i < j + c then a i * s else a i := by
  induction c generalizing j a with
  | zero =>
    funext i
    simp only [scaleLoop]
    split_ifs <;> first | omega | rfl
  | succ c ih =>
    funext i
    rw [scaleLoop, ih]
    simp only [Function.update_apply]
    split_ifs <;> first | omega | rfl | (subst_vars; rfl)

theorem scaleLoop_zero (s : R) (N : ℕ) (a : ℕ → R) : scaleLoop s 0 N a = scaleBelow s N a := by
  rw [scaleLoop_eq]
  funext i
  simp [scaleBelow]

/-! ### One stage -/

section Stage

variable {zAt : ℕ → R} {next : ℕ → ℕ} {f g : R → R → R → R} {len : ℕ}

/-- A stage commutes with multiplying the entries it touches by `s`, when its butterflies
are homogeneous. -/
theorem blockLoop_scaleBelow (hlen : 0 < len) {s : R}
    (hf : ∀ z u v, f z (u * s) (v * s) = f z u v * s)
    (hg : ∀ z u v, g z (u * s) (v * s) = g z u v * s) (k m : ℕ) (a : ℕ → R) :
    blockLoop zAt next f g len k 0 m (scaleBelow s (2 * len * m) a) =
      scaleBelow s (2 * len * m) (blockLoop zAt next f g len k 0 m a) := by
  funext i
  by_cases hi : i < 2 * len * m
  · obtain ⟨b, r, hb, hr, rfl | rfl⟩ := exists_block hlen hi
    · have := block_lt hb hr
      have hlow : 2 * len * b + r < 2 * len * m := by omega
      rw [blockLoop_low_zero hb hr]
      simp only [scaleBelow, this, hlow, ite_true]
      rw [blockLoop_low_zero hb hr]
      exact hf _ _ _
    · have := block_lt hb hr
      have hlow : 2 * len * b + r < 2 * len * m := by omega
      rw [blockLoop_high_zero hb hr]
      simp only [scaleBelow, this, hlow, ite_true]
      rw [blockLoop_high_zero hb hr]
      exact hg _ _ _
  · rw [blockLoop_of_notMem (by omega), scaleBelow, ite_eq_right hi, scaleBelow, ite_eq_right hi,
      blockLoop_of_notMem (by omega)]

end Stage

/-- The inverse stage undoes the forward stage at the same `len`, up to a factor `2`,
when each block's forward twiddle times the negated inverse twiddle is `1`. -/
theorem invStage_fwdStage {ζ : ℕ → R} {len m k k' : ℕ} (hlen : 0 < len)
    (hpair : ∀ b < m, -ζ (k' - 1 - b) * ζ (k + b) = 1) (a : ℕ → R) :
    blockLoop (fun k => -ζ (k - 1)) (· - 1) invF invG len k' 0 m
        (blockLoop ζ (· + 1) fwdF fwdG len k 0 m a) =
      scaleBelow 2 (2 * len * m) a := by
  funext i
  by_cases hi : i < 2 * len * m
  · obtain ⟨b, r, hb, hr, rfl | rfl⟩ := exists_block hlen hi
    · rw [blockLoop_low_zero hb hr, blockLoop_low_zero hb hr, blockLoop_high_zero hb hr,
        scaleBelow, ite_eq_left hi]
      simp only [invF, fwdF, fwdG]
      ring
    · rw [blockLoop_high_zero hb hr, blockLoop_low_zero hb hr, blockLoop_high_zero hb hr,
        scaleBelow, ite_eq_left hi, iterate_add_one, iterate_sub_one,
        show k' - b - 1 = k' - 1 - b by omega]
      simp only [invG, fwdF, fwdG]
      linear_combination (2 * a (2 * len * b + r + len)) * hpair b hb
  · rw [blockLoop_of_notMem (by omega), scaleBelow, ite_eq_right hi, blockLoop_of_notMem (by omega)]

/-- The forward stage undoes the inverse stage at the same `len`, up to a factor `2`. -/
theorem fwdStage_invStage {ζ : ℕ → R} {len m k k' : ℕ} (hlen : 0 < len)
    (hpair : ∀ b < m, -ζ (k' - 1 - b) * ζ (k + b) = 1) (a : ℕ → R) :
    blockLoop ζ (· + 1) fwdF fwdG len k 0 m
        (blockLoop (fun k => -ζ (k - 1)) (· - 1) invF invG len k' 0 m a) =
      scaleBelow 2 (2 * len * m) a := by
  funext i
  by_cases hi : i < 2 * len * m
  · obtain ⟨b, r, hb, hr, rfl | rfl⟩ := exists_block hlen hi
    · rw [blockLoop_low_zero hb hr, blockLoop_low_zero hb hr, blockLoop_high_zero hb hr,
        scaleBelow, ite_eq_left hi, iterate_add_one, iterate_sub_one,
        show k' - b - 1 = k' - 1 - b by omega]
      simp only [invF, invG, fwdF]
      linear_combination (a (2 * len * b + r) - a (2 * len * b + r + len)) * hpair b hb
    · rw [blockLoop_high_zero hb hr, blockLoop_low_zero hb hr, blockLoop_high_zero hb hr,
        scaleBelow, ite_eq_left hi, iterate_add_one, iterate_sub_one,
        show k' - b - 1 = k' - 1 - b by omega]
      simp only [invF, invG, fwdG]
      linear_combination (a (2 * len * b + r + len) - a (2 * len * b + r)) * hpair b hb
  · rw [blockLoop_of_notMem (by omega), scaleBelow, ite_eq_right hi, blockLoop_of_notMem (by omega)]

/-! ### All stages, for `n = 2 ^ L` -/

section Stages

variable (ζ : ℕ → R) (L : ℕ)

/-- The forward stage with `len = 2 ^ e`: `2 ^ (L - 1 - e)` blocks, counter from
`2 ^ (L - 1 - e)`. -/
def fwdStage (e : ℕ) : (ℕ → R) → ℕ → R :=
  blockLoop ζ (· + 1) fwdF fwdG (2 ^ e) (2 ^ (L - 1 - e)) 0 (2 ^ (L - 1 - e))

/-- The inverse stage with `len = 2 ^ e`: `2 ^ (L - 1 - e)` blocks, counter from
`2 ^ (L - e)` downwards. -/
def invStage (e : ℕ) : (ℕ → R) → ℕ → R :=
  blockLoop (fun k => -ζ (k - 1)) (· - 1) invF invG (2 ^ e) (2 ^ (L - e)) 0 (2 ^ (L - 1 - e))

/-- Forward stages `e + c - 1` down to `e`, in the order the forward loop runs them. -/
def fwdRange : ℕ → ℕ → (ℕ → R) → ℕ → R
  | _, 0, a => a
  | e, c + 1, a => fwdRange e c (fwdStage ζ L (e + c) a)

/-- Inverse stages `e` up to `e + c - 1`, in the order the inverse loop runs them. -/
def invRange : ℕ → ℕ → (ℕ → R) → ℕ → R
  | _, 0, a => a
  | e, c + 1, a => invRange (e + 1) c (invStage ζ L e a)

variable {ζ L}

theorem fwdRange_succ' (c e : ℕ) (a : ℕ → R) :
    fwdRange ζ L e (c + 1) a = fwdStage ζ L e (fwdRange ζ L (e + 1) c a) := by
  induction c generalizing a with
  | zero => simp [fwdRange]
  | succ c ih =>
    rw [fwdRange, ih]
    conv_rhs => rw [fwdRange]
    rw [show e + 1 + c = e + (c + 1) by omega]

theorem invRange_succ' (c e : ℕ) (a : ℕ → R) :
    invRange ζ L e (c + 1) a = invStage ζ L (e + c) (invRange ζ L e c a) := by
  induction c generalizing e a with
  | zero => simp [invRange]
  | succ c ih =>
    rw [invRange, ih]
    conv_rhs => rw [invRange]
    rw [show e + 1 + c = e + (c + 1) by omega]

theorem two_mul_pow_mul_pow {e : ℕ} (he : e < L) : 2 * 2 ^ e * 2 ^ (L - 1 - e) = 2 ^ L := by
  rw [← pow_succ', ← pow_add]
  congr 1
  omega

theorem pow_div_two_mul_pow {e : ℕ} (he : e < L) : 2 ^ L / (2 * 2 ^ e) = 2 ^ (L - 1 - e) := by
  rw [← pow_succ', Nat.pow_div (by omega) (by norm_num)]
  congr 1
  omega

theorem fwdStage_scaleBelow {e : ℕ} (he : e < L) (s : R) (a : ℕ → R) :
    fwdStage ζ L e (scaleBelow s (2 ^ L) a) = scaleBelow s (2 ^ L) (fwdStage ζ L e a) := by
  have h := blockLoop_scaleBelow (zAt := ζ) (next := (· + 1)) (f := fwdF) (g := fwdG) (s := s) (by positivity : 0 < 2 ^ e)
    (fun z u v => by simp only [fwdF]; ring) (fun z u v => by simp only [fwdG]; ring)
    (2 ^ (L - 1 - e)) (2 ^ (L - 1 - e)) a
  rwa [two_mul_pow_mul_pow he] at h

theorem invStage_scaleBelow {e : ℕ} (he : e < L) (s : R) (a : ℕ → R) :
    invStage ζ L e (scaleBelow s (2 ^ L) a) = scaleBelow s (2 ^ L) (invStage ζ L e a) := by
  have h := blockLoop_scaleBelow (zAt := fun k => -ζ (k - 1)) (next := (· - 1)) (f := invF)
    (g := invG) (s := s)
    (by positivity : 0 < 2 ^ e)
    (fun z u v => by simp only [invF]; ring) (fun z u v => by simp only [invG]; ring)
    (2 ^ (L - e)) (2 ^ (L - 1 - e)) a
  rwa [two_mul_pow_mul_pow he] at h

theorem fwdStage_of_le {e : ℕ} (he : e < L) (a : ℕ → R) {i : ℕ} (hi : 2 ^ L ≤ i) :
    fwdStage ζ L e a i = a i :=
  blockLoop_of_notMem (Or.inr (by rw [Nat.zero_add, two_mul_pow_mul_pow he]; exact hi))

theorem invStage_of_le {e : ℕ} (he : e < L) (a : ℕ → R) {i : ℕ} (hi : 2 ^ L ≤ i) :
    invStage ζ L e a i = a i :=
  blockLoop_of_notMem (Or.inr (by rw [Nat.zero_add, two_mul_pow_mul_pow he]; exact hi))

theorem fwdRange_scaleBelow (s : R) {c e : ℕ} (h : e + c ≤ L) (a : ℕ → R) :
    fwdRange ζ L e c (scaleBelow s (2 ^ L) a) = scaleBelow s (2 ^ L) (fwdRange ζ L e c a) := by
  induction c generalizing a with
  | zero => rfl
  | succ c ih => rw [fwdRange, fwdRange, fwdStage_scaleBelow (by omega), ih (by omega)]

theorem invRange_scaleBelow (s : R) {c e : ℕ} (h : e + c ≤ L) (a : ℕ → R) :
    invRange ζ L e c (scaleBelow s (2 ^ L) a) = scaleBelow s (2 ^ L) (invRange ζ L e c a) := by
  induction c generalizing e a with
  | zero => rfl
  | succ c ih => rw [invRange, invRange, invStage_scaleBelow (by omega), ih (by omega)]

theorem fwdRange_of_le {c e : ℕ} (h : e + c ≤ L) (a : ℕ → R) {i : ℕ} (hi : 2 ^ L ≤ i) :
    fwdRange ζ L e c a i = a i := by
  induction c generalizing a with
  | zero => rfl
  | succ c ih => rw [fwdRange, ih (by omega), fwdStage_of_le (by omega) a hi]

theorem invRange_of_le {c e : ℕ} (h : e + c ≤ L) (a : ℕ → R) {i : ℕ} (hi : 2 ^ L ≤ i) :
    invRange ζ L e c a i = a i := by
  induction c generalizing e a with
  | zero => rfl
  | succ c ih => rw [invRange, ih (by omega), invStage_of_le (by omega) a hi]

/-- The forward stage loop from `len = 2 ^ e` runs the forward stages `e` down to `0`. -/
theorem fwdStages_eq {e : ℕ} (hL : e < L) (a : ℕ → R) :
    fwdStages ζ (2 ^ L) (2 ^ e) (2 ^ (L - 1 - e)) (e + 1) a = fwdRange ζ L 0 (e + 1) a := by
  induction e generalizing a with
  | zero =>
    rw [fwdStages, pow_div_two_mul_pow hL]
    rfl
  | succ e ih =>
    rw [fwdStages, pow_div_two_mul_pow hL, pow_succ, Nat.mul_div_cancel _ (by norm_num),
      show 2 ^ (L - 1 - (e + 1)) + 2 ^ (L - 1 - (e + 1)) = 2 ^ (L - 1 - e) by
        rw [← two_mul, ← pow_succ']
        congr 1
        omega,
      ih (by omega)]
    conv_rhs => rw [fwdRange, Nat.zero_add]
    rfl

/-- The inverse stage loop from `len = 2 ^ e` runs the inverse stages `e` up to `L - 1`. -/
theorem invStages_eq {c e : ℕ} (hL : e + c = L) (a : ℕ → R) :
    invStages ζ (2 ^ L) (2 ^ e) (2 ^ (L - e)) c a = invRange ζ L e c a := by
  induction c generalizing e a with
  | zero => rfl
  | succ c ih =>
    rw [invStages, pow_div_two_mul_pow (by omega), ← pow_succ',
      show 2 ^ (L - e) - 2 ^ (L - 1 - e) = 2 ^ (L - (e + 1)) by
        rw [show L - e = (L - 1 - e) + 1 by omega, pow_succ,
          show L - (e + 1) = L - 1 - e by omega]
        omega,
      ih (by omega), invRange]
    rfl

theorem ntt_eq (a : ℕ → R) : ntt ζ (2 ^ L) a = fwdRange ζ L 0 L a := by
  rcases L with _ | L
  · rfl
  · have h := fwdStages_eq (ζ := ζ) (L := L + 1) (show L < L + 1 by omega) a
    rw [show L + 1 - 1 - L = 0 by omega, pow_zero] at h
    rw [ntt, falconLog2_two_pow, show 2 ^ (L + 1) / 2 = 2 ^ L by rw [pow_succ]; simp]
    exact h

theorem intt_eq (ninv : R) (a : ℕ → R) :
    intt ζ ninv (2 ^ L) a = scaleBelow ninv (2 ^ L) (invRange ζ L 0 L a) := by
  have h := invStages_eq (ζ := ζ) (L := L) (c := L) (e := 0) (by omega) a
  simp only [pow_zero, Nat.sub_zero] at h
  rw [intt, falconLog2_two_pow, scaleLoop_zero, h]

/-- The bit-reversal pairing of a twiddle table for `n = 2 ^ L`: in the forward stage with
`2 ^ s` blocks, block `b` uses `ζ (2 ^ s + b)` and the inverse stage uses
`-ζ (2 ^ (s + 1) - 1 - b)`; their product must be `-1`. -/
def Paired (ζ : ℕ → R) (L : ℕ) : Prop :=
  ∀ s < L, ∀ b < 2 ^ s, ζ (2 ^ s + b) * ζ (2 ^ (s + 1) - 1 - b) = -1

theorem Paired.stage (hζ : Paired ζ L) {e : ℕ} (he : e < L) :
    ∀ b < 2 ^ (L - 1 - e), -ζ (2 ^ (L - e) - 1 - b) * ζ (2 ^ (L - 1 - e) + b) = 1 := by
  intro b hb
  have h := hζ (L - 1 - e) (by omega) b hb
  rw [show L - 1 - e + 1 = L - e by omega] at h
  linear_combination -h

theorem Paired.invStage_fwdStage (hζ : Paired ζ L) {e : ℕ} (he : e < L) (a : ℕ → R) :
    invStage ζ L e (fwdStage ζ L e a) = scaleBelow 2 (2 ^ L) a := by
  rw [invStage, fwdStage, _root_.GordieHowe.Falcon512.KeyNTT.invStage_fwdStage (by positivity)
    (hζ.stage he), two_mul_pow_mul_pow he]

theorem Paired.fwdStage_invStage (hζ : Paired ζ L) {e : ℕ} (he : e < L) (a : ℕ → R) :
    fwdStage ζ L e (invStage ζ L e a) = scaleBelow 2 (2 ^ L) a := by
  rw [invStage, fwdStage, _root_.GordieHowe.Falcon512.KeyNTT.fwdStage_invStage (by positivity)
    (hζ.stage he), two_mul_pow_mul_pow he]

theorem Paired.invRange_fwdRange (hζ : Paired ζ L) {c e : ℕ} (h : e + c ≤ L) (a : ℕ → R) :
    invRange ζ L e c (fwdRange ζ L e c a) = scaleBelow (2 ^ c) (2 ^ L) a := by
  induction c generalizing e a with
  | zero => rw [pow_zero, scaleBelow_one]; rfl
  | succ c ih =>
    rw [fwdRange_succ', invRange, hζ.invStage_fwdStage (by omega),
      invRange_scaleBelow _ (by omega), ih (by omega), scaleBelow_scaleBelow, pow_succ]

theorem Paired.fwdRange_invRange (hζ : Paired ζ L) {c e : ℕ} (h : e + c ≤ L) (a : ℕ → R) :
    fwdRange ζ L e c (invRange ζ L e c a) = scaleBelow (2 ^ c) (2 ^ L) a := by
  induction c generalizing a with
  | zero => rw [pow_zero, scaleBelow_one]; rfl
  | succ c ih =>
    rw [invRange_succ', fwdRange, hζ.fwdStage_invStage (by omega),
      fwdRange_scaleBelow _ (by omega), ih (by omega), scaleBelow_scaleBelow, pow_succ]

/-- Decoding inverts the forward transform: `falcon_intt_ref` after `falcon_ntt_ref` is the
identity, for any power of two `n = 2 ^ L`, any twiddle table with the bit-reversal pairing,
and `ninv` inverse to `2 ^ L`. -/
theorem intt_ntt (hζ : Paired ζ L) {ninv : R} (hninv : 2 ^ L * ninv = 1) (a : ℕ → R) :
    intt ζ ninv (2 ^ L) (ntt ζ (2 ^ L) a) = a := by
  rw [intt_eq, ntt_eq, hζ.invRange_fwdRange (by omega), scaleBelow_scaleBelow, hninv,
    scaleBelow_one]

/-- The forward transform inverts decoding. -/
theorem ntt_intt (hζ : Paired ζ L) {ninv : R} (hninv : 2 ^ L * ninv = 1) (a : ℕ → R) :
    ntt ζ (2 ^ L) (intt ζ ninv (2 ^ L) a) = a := by
  rw [intt_eq, ntt_eq, fwdRange_scaleBelow _ (by omega), hζ.fwdRange_invRange (by omega),
    scaleBelow_scaleBelow, hninv, scaleBelow_one]

/-- The forward transform leaves the entries at or above `n` alone. -/
theorem ntt_of_le (a : ℕ → R) {i : ℕ} (hi : 2 ^ L ≤ i) : ntt ζ (2 ^ L) a i = a i := by
  rw [ntt_eq, fwdRange_of_le (by omega) a hi]

/-- The inverse transform leaves the entries at or above `n` alone. -/
theorem intt_of_le (ninv : R) (a : ℕ → R) {i : ℕ} (hi : 2 ^ L ≤ i) :
    intt ζ ninv (2 ^ L) a i = a i := by
  rw [intt_eq, scaleBelow, ite_eq_right (by omega), invRange_of_le (by omega) a hi]

end Stages

end Transform

/-- A root with `ψ ^ (2 ^ L) = -1`, in a ring where `-1 ≠ 1`, is a primitive `2 ^ (L + 1)`-th
root of unity. -/
theorem isPrimitiveRoot_of_pow_two_pow_eq_neg_one {R : Type*} [CommRing R] {ψ : R} {L : ℕ}
    (h1 : (-1 : R) ≠ 1) (h : ψ ^ 2 ^ L = -1) : IsPrimitiveRoot ψ (2 ^ (L + 1)) := by
  rw [IsPrimitiveRoot.iff_orderOf]
  refine orderOf_eq_prime_pow (p := 2) ?_ ?_
  · rw [h]
    exact h1
  · rw [pow_succ, pow_mul, h]
    norm_num

/-! ## The Falcon instance -/

/-- The twiddle table `falcon_ntt_zetas(n, q)` (`falcon_ntt.h:65-71`) read in `ZMod q`. -/
def falconZeta (n q i : ℕ) : ZMod q := (falconNttZetas n q i : ZMod q)

theorem falconZeta_eq (n q i : ℕ) :
    falconZeta n q i = (falconRoot2n n q : ZMod q) ^ falconBrv i (falconLog2 n) := by
  rw [falconZeta, falconNttZetas, powMod_eq_pow]

/-- The bit-reversed table of a root `ψ` with `ψ ^ n = -1` has the pairing the round trip
needs. -/
theorem falconZeta_paired {L q : ℕ} (hψ : (falconRoot2n (2 ^ L) q : ZMod q) ^ 2 ^ L = -1) :
    Paired (falconZeta (2 ^ L) q) L := by
  intro s hs b hb
  rw [falconZeta_eq, falconZeta_eq, falconLog2_two_pow, ← pow_add, falconBrv_pair hs hb,
    hψ]

/-- The C++ input vector as the working array: entry `i` below `n` is `a i` read in `ZMod q`;
the loops never touch the entries at or above `n`. -/
def extend {n : ℕ} (q : ℕ) (a : Fin n → ℕ) : ℕ → ZMod q :=
  fun i => if h : i < n then (a ⟨i, h⟩ : ZMod q) else 0

theorem extend_of_le {n q : ℕ} (a : Fin n → ℕ) {i : ℕ} (hi : n ≤ i) : extend q a i = 0 := by
  rw [extend, dite_eq_right (by omega)]

/-- Reading back the values of a working array that is zero at and above `n`. -/
theorem extend_val {n q : ℕ} [NeZero q] {v : ℕ → ZMod q} (hv : ∀ i, n ≤ i → v i = 0) :
    extend q (fun i : Fin n => (v i).val) = v := by
  funext i
  by_cases hi : i < n
  · rw [extend, dite_eq_left hi, ZMod.natCast_zmod_val]
  · rw [extend_of_le _ (by omega), hv i (by omega)]

/-- `falcon_ntt_ref(a, falcon_ntt_zetas(n, q), q)` (`falcon_ntt.h:74-90`) on a vector of
naturals below `q`, returning the naturals the C++ stores. -/
def falconNttRef (n q : ℕ) (a : Fin n → ℕ) : Fin n → ℕ :=
  fun i => (ntt (falconZeta n q) n (extend q a) i).val

/-- The forward transform returns reduced values, as the C++ stores `x % q`. -/
theorem falconNttRef_lt {n q : ℕ} [NeZero q] (a : Fin n → ℕ) (i : Fin n) :
    falconNttRef n q a i < q :=
  ZMod.val_lt _

/-- `falcon_intt_ref(a, falcon_ntt_zetas(n, q), q)` (`falcon_ntt.h:93-110`) on a vector of
naturals below `q`, returning the naturals the C++ stores. -/
def falconInttRef (n q : ℕ) (a : Fin n → ℕ) : Fin n → ℕ :=
  fun i => (intt (falconZeta n q) (falconNinv n q : ZMod q) n (extend q a) i).val

/-- `emulated_ntt::decode(a, zetas, q)` (`lib/circuits/ntt/emulated_signature.h:82-88`): reject
(`none`, where the C++ `check` aborts) unless every entry is below `q`, then apply
`falcon_intt_ref`. `decode_key` (`lib/gordiehowe/examples/falcon/falcon_emulated.h`) calls it with
`qzetas = falcon_ntt_zetas(n, q)`. -/
def falconDecode (n q : ℕ) (a : Fin n → ℕ) : Option (Fin n → ℕ) :=
  if ∀ i, a i < q then some (falconInttRef n q a) else none

section Decode

variable {L q : ℕ} [NeZero q]

theorem extend_falconNttRef (c : Fin (2 ^ L) → ℕ) :
    extend q (falconNttRef (2 ^ L) q c) = ntt (falconZeta (2 ^ L) q) (2 ^ L) (extend q c) :=
  extend_val fun _ hi => by rw [ntt_of_le _ hi, extend_of_le _ hi]

theorem extend_falconInttRef (a : Fin (2 ^ L) → ℕ) :
    extend q (falconInttRef (2 ^ L) q a) =
      intt (falconZeta (2 ^ L) q) (falconNinv (2 ^ L) q : ZMod q) (2 ^ L) (extend q a) :=
  extend_val fun _ hi => by rw [intt_of_le _ _ hi, extend_of_le _ hi]

omit [NeZero q] in
theorem val_extend {n : ℕ} {a : Fin n → ℕ} (ha : ∀ i, a i < q) (i : Fin n) :
    (extend q a i).val = a i := by
  rw [extend, dite_eq_left i.isLt, ZMod.val_natCast_of_lt (ha i)]

/-- Decoding succeeds with result `c` exactly when `c` has entries below `q` and its forward
transform is the input, for `n = 2 ^ L`, a root `ψ` with `ψ ^ n = -1` (`param`) and
`ninv * n = 1` in `ZMod q` (`param`). -/
theorem falconDecode_eq_some_iff
    (hψ : (falconRoot2n (2 ^ L) q : ZMod q) ^ 2 ^ L = -1)
    (hninv : 2 ^ L * (falconNinv (2 ^ L) q : ZMod q) = 1) (a c : Fin (2 ^ L) → ℕ) :
    falconDecode (2 ^ L) q a = some c ↔ (∀ i, c i < q) ∧ falconNttRef (2 ^ L) q c = a := by
  have hζ := falconZeta_paired hψ
  constructor
  · intro h
    unfold falconDecode at h
    split_ifs at h with ha
    cases h
    refine ⟨fun i => ZMod.val_lt _, funext fun i => ?_⟩
    rw [falconNttRef, extend_falconInttRef, ntt_intt hζ hninv, val_extend ha]
  · rintro ⟨hc, rfl⟩
    rw [falconDecode, ite_eq_left (falconNttRef_lt c)]
    congr 1
    funext i
    rw [falconInttRef, extend_falconNttRef, intt_ntt hζ hninv, val_extend hc]

end Decode

/-- `falcon_root_2n(512, 12289)` finds the generator `11` and returns `11 ^ 12 % 12289`. -/
theorem falconRoot2n_512 : falconRoot2n 512 12289 = 10302 := by decide

/-- `ψ ^ 512 = -1` for the flagship root (`param`). -/
theorem falconRoot2n_512_pow : (falconRoot2n (2 ^ 9) 12289 : ZMod 12289) ^ 2 ^ 9 = -1 := by
  rw [← powMod_eq_pow]
  decide

/-- The flagship root is a primitive `1024`-th root of unity mod `12289`. -/
theorem falconRoot2n_512_isPrimitiveRoot :
    IsPrimitiveRoot (falconRoot2n 512 12289 : ZMod 12289) 1024 :=
  isPrimitiveRoot_of_pow_two_pow_eq_neg_one (L := 9) (by decide) falconRoot2n_512_pow

/-- `ninv * 512 = 1` mod `12289` for the flagship `ninv` (`param`). -/
theorem falconNinv_512 : 2 ^ 9 * (falconNinv (2 ^ 9) 12289 : ZMod 12289) = 1 := by
  decide

/-- Decoding at the flagship parameters `n = 512`, `q = 12289`. -/
theorem falconDecode_512_eq_some_iff (a c : Fin 512 → ℕ) :
    falconDecode 512 12289 a = some c ↔ (∀ i, c i < 12289) ∧ falconNttRef 512 12289 c = a :=
  falconDecode_eq_some_iff (L := 9) falconRoot2n_512_pow falconNinv_512 a c

/-- The NTT-domain vector the flagship passes as `key_hat` for the key `pk`: the forward
transform of the key's coefficient vector. -/
def keyHat (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512) : Fin 512 → ℕ :=
  falconNttRef 512 12289 fun i : Fin 512 => (Falcon512.coeff pk.h i).val

theorem keyHat_lt (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512) (i : Fin 512) :
    keyHat pk i < 12289 :=
  falconNttRef_lt _ i

/-- Decoding a `key_hat` yields the coefficient vector `(Falcon.coeff pk.h i).val`
(`GordieHowe.Falcon512.EmulatedAlgebraCircuit.keyCoeffs pk.h`, by definition) exactly when `key_hat` is `keyHat pk`. -/
theorem falconDecode_eq_keyCoeffs_iff
    (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512) (keyHatIn : Fin 512 → ℕ) :
    falconDecode 512 12289 keyHatIn = some (fun i : Fin 512 => (Falcon512.coeff pk.h i).val) ↔
      keyHatIn = keyHat pk := by
  rw [falconDecode_512_eq_some_iff, eq_comm (a := keyHatIn)]
  exact and_iff_right fun i => ZMod.val_lt _

/-- The coefficient vector the signature rows use, `decode(key_hat)`, is the key's
coefficient vector when `key_hat = keyHat pk`. -/
theorem falconDecode_keyHat (pk : _root_.Falcon.PublicKey _root_.Falcon.Concrete.params512) :
    falconDecode 512 12289 (keyHat pk) = some (fun i : Fin 512 => (Falcon512.coeff pk.h i).val) :=
  (falconDecode_eq_keyCoeffs_iff pk _).2 rfl

end GordieHowe.Falcon512.KeyNTT
