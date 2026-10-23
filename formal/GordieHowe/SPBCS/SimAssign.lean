-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.SPBCS.Basic
public import GordieHowe.Model.QROM.NIZK
public import GordieHowe.Model.NARG.OracleProg

@[expose] public section

/-!
# Where a simulator program of the spBCS compiler programs the oracle

The property of a classical simulator program of the spBCS compiler
(`GordieHowe/SPBCS/Basic.lean`) that the simulation-sound extractability argument uses: every assignment
it makes programs the `xof` point, at the proof query's Fiat–Shamir salt, at the digest of the oracle's
answer to a `transcript` input that the program queried and whose content holds the proof query's salted
statement (paper `def:bcs-base-game`, third condition). A verifier run for a statement of no proof query
then reaches a programmed point only through a digest collision.
-/

namespace GordieHowe.SPBCS

open GordieHowe.QROM GordieHowe.IOP GordieHowe.Quantum GordieHowe.QROM

variable {ι : Type} {k kN kS L e : ℕ} {t : SPTerm ι} {Mg : Merges t} {n : ι → ℕ}
  {P : (j : ι) → IOP.ProtocolSpec (n j)} [∀ j i, Fintype ((P j).Challenge i)]
  [∀ j i, DecidableEq ((P j).Challenge i)] {X : Type}

section

variable (M : SPBCS Mg P X k kN kS L e)

/-- **The program assigns only at the keys of its chain inputs for the salted statement `ss`**
(module docstring): under every oracle `O`, each assignment of the run programs the `xof` point
at the salt of `ss` and the digest of `O` at a queried `transcript` input whose content holds
`ss`. -/
def AssignsAtKeys {R : Type}
    (prog : OracleProg (Query k kN kS L) (Out k e) (NARG.SimOutput (Query k kN kS L) (Out k e) R))
    (ss : SaltedStatement kS X) : Prop :=
  ∀ (O : Query k kN kS L → Out k e) (qa : Assignment (Query k kN kS L) (Out k e)),
    qa ∈ (prog.run O).assignments →
      ∃ (bT : Bytes L) (cnt : M.MContent), Query.transcript bT ∈ prog.trace O ∧
        M.senc.decode bT = some cnt ∧ cnt.stmt = ss ∧
        qa.input = .xof (O (.transcript bT)).digest ss.salt

end

end GordieHowe.SPBCS
