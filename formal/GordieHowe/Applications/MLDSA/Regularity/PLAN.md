# HighBits regularity with the accept bit: Lean plan (working document)

Target (for `ringRegGap`, RingSigner.lean, and `regError`, Flatten.lean). Fix `s1, s2` in the
η-box and `c` on the τ-ball; `A` uniform; `t = A s1 + s2`, `t0` its low part, `a = c s2`,
`b = c t0`. With `x = z - c s1`, `z` uniform on the accepted z-box (`box_shift_card`),

    p_θ(v) = Pr_z[HighBits(A x) = v ∧ r0, ct0, hint checks pass]       (real, per key)
    s_θ(v) = Pr_w[HighBits(w)   = v ∧ r0, ct0, hint checks pass]       (stand-in)

Goal: `E_A Σ_v |p_θ(v) - s_θ(v)| ≤ ρ · ε` for every `(s1, s2, c)`, `ρ = (mL/q)^N`.

## Route A (recommended): ℓ2 on the unnormalized difference, A averaged on cosets

1. `l1_le_sqrt_card_mul_l2` (ToMathlib, Finset): `Σ_v |f v| ≤ √(|V| · Σ_v f v ^ 2)`.
   Replaces the note's χ² identities (1)-(2); no first moment `B1` is needed, because the
   ξ = 0 Fourier mode of `p_θ(v)` is exactly `s_θ(v)` and cancels.
2. `perKey_tv_le` (ToMathlib/PMFTV): for sub-probability masses `p, s` with `Σ s = σ > 0`,
   `Σ p > 0`: `tvDist (p/Σp) (s/σ) ≤ Σ |p - s| / σ`. This is the per-key bridge (ii): the
   per-key conditional laws need no global conditioning; with r0 only `σ = ρ` for every key, and
   with the hint check `σ_θ = ρ · acceptWeight b v` summed over `v` (`card_acceptSet`), so the
   bound divides by `min_θ σ_θ` (or by the `memberWeight` normalization of `ringRegGap`).
3. Accept-bit expansion (new, Regularity/HintExpansion.lean): with `ζ = e^{2πi/(N+1)}`,
   `1[#fires ≤ ω] = Σ_k c_k ∏_i (1_{A_i∖F_i} + ζ^k 1_{F_i})`, `Σ_k |c_k| = Λ`,
   `Λ = 2.77, 2.62, 2.74` at 44/65/87 (numeric, N = 256k). `F_i ⊂ A_i` is the hint
   sub-interval of `bucket_hint_card`; both pieces are intervals, so each factor has
   `|ĝ(a)| ≤ q/|a|` (twice the single-interval bound) and `|ĝ(0)| ≤ L`.
4. Coset averaging (new, general, ToMathlib/UniformFunction or a new Fourier file): for a
   linear map `φ` on a finite vector space and `G` any function,
   `|E_A[G(φ A) ψ(A)]| ≤ 1[ψ trivial on ker φ] · sup |G|` for a character `ψ`. Applied with
   `φ A = A s1` (the cells depend on `A` only through `t0`), condition (4) of the note becomes
   "the slot-j vector `ξ x̂(j) - η x̂'(j)` is parallel to `ŝ1(j)`": `ℓ - 1` equations per slot,
   so `Pr ≤ G^{-(ℓ-1)|T|}` instead of the note's `G^{-ℓ|T|}`.
5. Small supports (`|T| ≤ 5`): the note's §4, with `f̃ ≤ min(1, q/(L|a|))`. Needs Lemma 2
   (`Determinant.lean`, below) and the integer checks (`IntegerChecks.lean`, done).
6. Medium supports (`6 ≤ |T| ≤ 128`): two disjoint windows, `S2 = T2 ≤ q²/(mL²) < 45`
   (Parseval on the pair kernel `Σ_v g_v ⊗ ḡ_v`, unchanged by the hint split).
7. Large supports (`|T| > 128`): the annihilator route below.

Numbers (scratchpad script `num/hint.py`; log2 of the per-`r` term of (5), worst `r`):

| set | note (no hint, `ℓ`) | hint, `ℓ` | hint, `ℓ-1` (Route A) |
|----|----|----|----|
| 44 | TV ≤ 2^-129.8 | fails at r ≥ 240 | r ≤ 160 fine (r=5: 2^-128); fails r ≥ 200 |
| 65 | 2^-207.4 | 2^-36.6 (r=256 dominant) | fails r ≥ 240 |
| 87 | 2^-303.3 | 2^-302.5 | fails r ≥ 240 |

So Route A is sound for `|T| ≤ ~160` at all sets; the failure is only the overlapping-window
bound (6) with `S1 = (Σ f̃)²`, whose ℓ1-Fourier cost `Ũ^k` per slot (`2^78` at 44) exceeds
`G^{ℓ-1}` (`2^54`). Even the note has thin margin there at 44 (`U^4 = 2^70` vs `G^4 = 2^72`).
Proposed fix, to be checked before any Lean: at a slot where two rows are non-parallel the
system has rank `2(ℓ-1)`, not `ℓ-1`; for large supports almost every slot is such, giving
`G^{-2(ℓ-1)}` (`2^108` at 44) per slot. This needs a grouping by "rank-1 slots" in place of
`(1 + K)^k - 1`; its count is not yet worked out.

## Large supports: the annihilator route (worked out 2026-10-23)

Swap the order of the `(ξ, η)` sum and the `(x, x')` average. For fixed `(x, x')` the pairs
satisfying the coset constraint form `Ann(x, x')^k`, where `Ann` is a product over slots `j` of a
subspace `D_j ⊂ F_q²` (the same for every row): `0`; the `ξ`-line (`η(j) = 0`, needs
`x̂(j) ∈ span ŝ1(j)`, prob `≤ G^{-(ℓ-1)}`); the `η`-line (same with `x'`); a diagonal line
`η(j) = λ_j ξ(j)` (needs `x̂' ∈ span(x̂, ŝ1)` or `x̂ ∈ span ŝ1`, prob `≤ 2G^{-(ℓ-2)}`); or all of
`F_q²` (prob `≤ G^{-2(ℓ-1)}`). Slot conditions multiply: condition on `x` first (linear, rank
`(ℓ-1)` per slot), then on `x'` given `x` (linear). Per row, the subspace is fibred: `ξ` ranges
over `C_{Tξ}` (`Tξ` = ξ-lines, diagonals, full slots) and, given `ξ`, `η` over a coset of
`C_{Tη}` (`Tη` = η-lines, full slots), so the row sum is `≤ M_f(|Tξ|) · M_f(|Tη|)` with the
single-coefficient window bound `M_f` (`S1 = Σ f̃`, `S2 = Σ f̃² = q/L` by Parseval; window bounds
hold on cosets). Lemmas: `slotType_prob_le` (rank-box bound, two stages), `fibre_window_le`.

Each `r = |T|` takes the smaller of Route A (`ℓ-1`) and this route (both bound the same
`r`-indexed sum). Result, `log2 (Λ √B̃2)` (scripts `num/hintRA.py`, `num/annJ.py`):

| set | covered `r` | worst term | `log2(Λ √B̃2)` |
|----|----|----|----|
| 65 | all 1..256 | `r = 6` (Route A), `2^-297.5` | **-147.4** |
| 87 | all 1..256 | `r = 6` (Route A), `2^-489.5` | **-243.3** |
| 44 | `r ≤ 215` (worst `r = 5`, `2^-128`) | `r ∈ [216, 256]` open | open |

The per-key relative error is this times `ρ / min_θ σ_θ` (hint acceptance of the stand-in).
At 44 the open terms are dominated by patterns with almost all slots diagonal: the fibre bound
pays `S1` (ℓ1 Fourier mass, `4·(2 S1 - S2) ≈ 63` bits per slot) against `2G^{-2} ≈ 2^-35`.
For purely diagonal patterns, Cauchy–Schwarz on the graph `λ ↦ (ξ, η)` gives `(Σ f̃²)^{n_d}`
(`4 · 5.46 ≈ 22` bits per slot) and closes them; patterns with one non-diagonal slot then
dominate (`r = 256`: `2^403`). Needed: a hybrid lemma bounding `Σ_{W_D ⊕ W_O} F(ξ) G(η)` by
`(Σ f̃²)^{n_d} · M_f(...) M_f(...)` without the `q^{dim}` kernel loss of a global
Cauchy–Schwarz. Not yet found.

## Fixed key versus averaged over A

`ringRegGap` is per fixed `sk` and `aHat`; this bound averages over `A` (for every `s1, s2, c`).
- Restate (recommended): put `𝔼_{keygen} ringRegGap` in the ring theorem. BKM06 Def. 4 averages
  the anonymity advantage over honest key generation, the advantage bound is linear in the
  per-member gap, so the average is exact and costs nothing in bits; the cost is a restated
  headline term and a keygen-averaging step in the reduction (ExpandA modelled as uniform `A`).
- Markov: `Pr_A[gap > ε/δ] ≤ δ`; the theorem then holds outside a `δ`-fraction of keys with
  error `ε/δ + δ`, best `δ = √ε`: halves the bits (65: ~2^-73, 87: ~2^-121) and needs a
  good-key event in the statement.

## Route B (rejected): χ² on the finer partition (HighBits, fire pattern)

Data processing from the product partition into cells of lengths `ℓ_i` and `L - ℓ_i`. The χ²
weighting `1/|cell|` makes the short sub-cells' kernel decay as `|a|^{-1/2}` (`f̃ = √f`), so
budgets halve: `D4 > 1` at 44, `T2` doubles to 90, and `(Σ√f)^2 ≈ 2^28.5` per slot: large
supports fail at every set by thousands of bits. Small supports alone survive.

## Lemma 2 (determinant bound), Regularity/Determinant.lean (general parts to ToMathlib)

- `negacyclicMatrix v : Matrix (Fin a) (Fin a) ℤ` (`M i j = v (i - j)` with sign `-1` on wrap).
- `negacyclic_det_ne_zero`: `v ≠ 0`, `a = 2^e` → `det ≠ 0`. Route: kernel vector `u` over ℚ
  gives `X^a + 1 ∣ u · v` in `ℚ[X]`; `X^(2^e) + 1 = cyclotomic (2^(e+1)) ℚ`
  (`cyclotomic_prime_pow_eq_geom_sum`), irreducible (`cyclotomic.irreducible_rat`), no Eisenstein
  needed; degrees `< a` contradict.
- `pow_dvd_det_of_rank_le` (ToMathlib/Matrix): `p` prime, `rank (M.map (Int.castRingHom (ZMod p)))
  ≤ r` → `(p:ℤ)^(n - r) ∣ det M` (lift an invertible mod-p matrix whose first `n - r` columns span
  the kernel; factor `p` from those columns of `M U`; `det U` coprime to `p`). Not in Mathlib.
- `rank_negacyclic_le`: if `v ≡ Σ_{t∈T} λ_t (ρ_t^b)_b (mod p)` with `ρ_t^a = -1`, the columns
  `X^j v` lie in `span {w_t}` because `X · w_t = ρ_t^{-1} w_t`; so rank `≤ |T|`. (Simpler than the
  note's "primal transform is a permutation of aλ".)
- `abs_det_le` two forms: Leibniz `|det M| ≤ a! ‖v‖∞^a` (weak, enough for (10)-(14)); Hadamard
  form `|det M|² ≤ ‖v‖₂^{2a}` from AM-GM on the eigenvalues of `M Mᵀ` (all rows of a negacyclic
  matrix have norm `‖v‖₂`), needed for (14a). Mathlib has no Hadamard inequality.
- `centered_lift_norm_ge`: `q^(a - r) ≤ a^(a/2) ‖v‖∞^a`, instantiated at `q = 8380417`.

## Remaining (estimates, agent-hours)

Lemma 2: ~1 day. Fourier/coset machinery (items 3, 4, characters on `ZMod q`, Parseval on the
pair kernel, rank-box bound): 1-2 days. §4 recursion (11)-(13) as a recursion on `(r, a, s)` with
the information-set bijections (Vandermonde minors): 1-2 days. Medium-support windows and tails:
~1 day. Large supports: open (Route A item 7). The note's §5 first moment is not needed.

## Note checks

All of (10), the (14a) endpoints, the (14a) collision values, (13), the `δ_r`, `κ_r`, the table
`56r + 10a_r`, `T2 < 45`, the log checks of (18), `U`, both ratio tests and the final envelope
(log2 TV ≤ -131.4, -182.4, -259.3) recompute correctly. Minor: in §5 `k r x_r < 1/256` is an
equality at `k = 8, r = 64` (harmless: `ε < 2^-10` is strict); two-pair collision at `r = 4` is
`9/16`, printed as `5/8` (an upper bound). Lemma 2 needs `q` prime (implicit).
