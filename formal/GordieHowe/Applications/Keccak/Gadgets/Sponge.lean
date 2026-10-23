-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.Applications.Keccak.Gadgets.Batch
public import GordieHowe.Applications.Keccak.Gadgets.Hook

@[expose] public section

/-!
# The Keccak sponge over a batch of Keccak-f chains (`lib/circuits/keccak/keccak_sponge.h`)

`KeccakSponge::hash` (`keccak_sponge.h` lines 83-122 at `e5daf0a`) runs the sponge in the
circuit over a `KeccakBatch` (`GordieHowe.KeccakBatch`): it pads the message and XORs each rate block
into the state (lines 91-102), hooks the result as a committed permutation input (`start`,
line 103), reads the whole output of an absorb permutation that a later block absorbs into
(`output(p)`, line 104), chains the squeeze permutations inside the trace (`chain`, line 109),
and reads the output bytes off the squeeze permutations' output words (`output(p, q)`, lines
111-113). An output word is sixteen packed private inputs aliased onto the committed round-23
trace word (`keccak_batch.h` lines 139-162 and 199-207), so the circuit reads the bits of the
trace word itself.

* `Call`: a hash call placed at the consecutive permutations from `first` of a batch whose
  shape hooks its absorb permutations and chains its squeezes; `Call.perm` is the permutation of
  a block. Several calls share one batch, each placed at its own `first`.
* `laneBit_zChunk_zBit`: lane bit `z` is bit `zBit z` of packed word `zChunk z`, the indexing of
  the aliased output words.
* `spongeStart_succ_of_le`: a squeeze permutation's honest input (`KeccakTrace.spongeStart`) is
  Keccak-f of the previous one.

The word-level absorb of a call and its soundness are `KeccakSponge.WordAbsorb` and
`KeccakSponge.wordAbsorb_sound`.

Generic in the sponge configuration `SpongeSpec` (rate and domain suffix, `keccak_sponge.h`
lines 43-51); Falcon and ML-DSA call it at `SpongeSpec.shake256` (`kShake256{136, 0x1f}`).
-/

namespace GordieHowe.KeccakSponge

open GordieHowe.Bits GordieHowe.Keccak GordieHowe.Shake256 GordieHowe.KeccakTrace GordieHowe.KeccakBatch GordieHowe.KeccakHook GordieHowe.PackedClaim

variable {np a : ℕ}

theorem absorbBlocks_le_numBlocks (sp : SpongeSpec) (len outLen : ℕ) : absorbBlocks sp len ≤ numBlocks sp len outLen :=
  Nat.le_add_right _ _

/-! ### Calls -/

/-- **A sponge call over a batch**, with configuration `sp`, of shape `sh`: `len` input bytes, `outLen` output bytes,
at the `numBlocks sp len outLen` consecutive permutations from `first` (`KeccakSponge::hash`: its
absorb permutations are `start`s, its squeezes `chain`s, so its permutations are contiguous in
the batch). The shape hooks the absorb permutations and chains the squeezes (a parameter
condition). -/
structure Call (sp : SpongeSpec) (sh : Shape np a) (len outLen : ℕ) where
  first : ℕ
  fits : first + numBlocks sp len outLen ≤ np
  hooked : ∀ (k : ℕ) (hk : k < absorbBlocks sp len),
    sh.Hooked ⟨first + k, by have := absorbBlocks_le_numBlocks sp len outLen; omega⟩
  chained : ∀ (k : ℕ) (hk : k < numBlocks sp len outLen), absorbBlocks sp len ≤ k →
    ¬ sh.Hooked ⟨first + k, by omega⟩

namespace Call

variable {sp : SpongeSpec} {sh : Shape np a} {len outLen : ℕ} (c : Call sp sh len outLen)

/-- The permutation of block `k`. -/
def perm (k : Fin (numBlocks sp len outLen)) : Fin np := ⟨c.first + k, by have := c.fits; omega⟩

end Call

/-! ### The aliased outputs -/

/-- Lane bit `z` is bit `zBit z` of packed word `zChunk z`. -/
theorem laneBit_zChunk_zBit (z : Fin 64) : KeccakHook.laneBit (zChunk z) (zBit z) = z :=
  Fin.ext (by simp only [KeccakHook.laneBit, zChunk, zBit]; omega)

variable {K : Type*} [Field K] [DecidableEq K]

/-! ### The honest call -/

section Complete

variable [CharP K 2] {B : PackedBasis K 4} {sp : SpongeSpec} {sh : Shape np a} {len outLen : ℕ}
  {c : Call sp sh len outLen} {input : Fin len → BitWires K 8}

omit [DecidableEq K] [CharP K 2] in
/-- A squeeze permutation's honest input is Keccak-f of the previous one. -/
theorem spongeStart_succ_of_le {k : ℕ} (hk : absorbBlocks sp len ≤ k + 1) :
    spongeStart sp input (k + 1) = keccakF (spongeStart sp input k) := by
  have hab : absorbBlocks sp len = len / sp.rate + 1 := rfl
  rw [spongeStart, if_neg (by omega)]
  rfl

end Complete

end GordieHowe.KeccakSponge
