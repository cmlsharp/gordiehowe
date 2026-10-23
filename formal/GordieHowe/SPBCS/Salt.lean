-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Basic
public import GordieHowe.Model.QROM.QueryBits

@[expose] public section

/-!
# The salt slot of the spBCS compiler

The Fiat–Shamir salt a query of the spBCS compiler (`GordieHowe/SPBCS/Basic.lean`) reads:
`querySalt` on the classical oracle's queries (the salt of a `transcript` input's decoded content,
the salt of an `xof` query, none otherwise) and `saltOfBits` on the quantum oracle's bit strings,
which agree through the query encoding (`saltOfBits_toBits`). The fresh-slice arguments of
completeness, zero knowledge and witness indistinguishability replace the oracle on the inputs of
one salt.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP IOP.SPTerm

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι}

section

variable {Mg : Merges t} {n : ι → ℕ} {P : (j : ι) → ProtocolSpec (n j)}
  [∀ j i, Fintype ((P j).Challenge i)] [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}
  (M : SPBCS Mg P X k kN kS L e)

/-- **The salt a query reads**: the salt of the salted statement of a `transcript` input's
content with merges, the salt of an `xof` query, none for a `leaf` or `node` query. -/
def querySalt : Query k kN kS L → Option (FiatShamirSalt kS)
  | .transcript b => (M.senc.decode b).map fun c => c.stmt.salt
  | .xof _ σ => some σ
  | _ => none

theorem querySalt_transcript_encode {c : M.MContent} (hc : c.WF n fun j => chainWF (P j)) :
    M.querySalt (.transcript (M.senc.encode c)) = some c.stmt.salt := by
  simp [querySalt, M.senc.decode_encode _ hc]

theorem querySalt_of_not_isChainQuery {q : Query k kN kS L} (hq : ¬ SPBCS.IsChainQuery q) :
    M.querySalt q = none := by
  cases q <;> simp_all [SPBCS.IsChainQuery, querySalt]

open Classical in
/-- The salt in the slot of a quantum-oracle input. -/
noncomputable def saltOfBits (b : Bits (queryBits k kN kS L)) : Option (FiatShamirSalt kS) :=
  (Function.partialInv Query.toBits b).bind M.querySalt

theorem saltOfBits_toBits (q : Query k kN kS L) :
    M.saltOfBits (Query.toBits q) = M.querySalt q := by
  classical
  simp only [saltOfBits]
  rw [Function.partialInv_left Query.toBits.injective]
  rfl

end

end GordieHowe.SPBCS
