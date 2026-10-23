-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe.ProofSystem.Program.ForkJoinZK
public import GordieHowe.ProofSystem.Program.Comap

@[expose] public section

/-!
# A multi-circuit IOP with forked domains at another statement type

A multi-circuit IOP with forked domains reads its statement only
through its application phase, so composing the phase with a map `f : Stmt' → Stmt`
(`GordieHowe.RealizedProgram.ProofSystem.PhaseStep.comap`, with a statement check `GordieHowe.RealizedProgram.ProofSystem.PhaseStep.comapWith`) gives the same composite over the
statements `Stmt'`; the soundness data and the honest prover carry over unchanged
(`GordieHowe.RealizedProgram.ProofSystem.IOP.Sound.comap`, `GordieHowe.RealizedProgram.ProofSystem.IOP.Honest.comap`).
-/

namespace GordieHowe

namespace RealizedProgram.ProofSystem.IOP

variable {Stmt Stmt' W : Type} {rel : Set (Stmt × W)}

/-- **A multi-circuit IOP with forked domains at the statements `Stmt'`**: the same domains, the
application phase read through `f`, for the relation `{(x', w) | (f x', w) ∈ rel}`. -/
def comap (C : IOP Stmt W rel) (f : Stmt' → Stmt) :
    IOP Stmt' W {p | (f p.1, p.2) ∈ rel} where
  m := C.m
  neZero := C.neZero
  Pub := C.Pub
  Wit := C.Wit
  holds := C.holds
  circuit := C.circuit
  oracle := C.oracle
  app := C.app.comap f

/-- **The soundness data carry over** to the statements `Stmt'`. -/
def Sound.comap {C : IOP Stmt W rel} (S : C.Sound) (f : Stmt' → Stmt) :
    (C.comap f).Sound where
  circuit := S.circuit
  εapp := S.εapp
  eventBound := S.eventBound.comap f

/-- **A multi-circuit IOP with forked domains at the statements `Stmt'` with a statement check**:
the application phase read through `f` and checking `chk`. -/
def comapWith (C : IOP Stmt W rel) (f : Stmt' → Stmt) (chk : Stmt' → Bool) :
    IOP Stmt' W {p | chk p.1 = true ∧ (f p.1, p.2) ∈ rel} where
  m := C.m
  neZero := C.neZero
  Pub := C.Pub
  Wit := C.Wit
  holds := C.holds
  circuit := C.circuit
  oracle := C.oracle
  app := C.app.comapWith f chk

/-- **The soundness data carry over** with a statement check. -/
def Sound.comapWith {C : IOP Stmt W rel} (S : C.Sound) (f : Stmt' → Stmt)
    (chk : Stmt' → Bool) : (C.comapWith f chk).Sound where
  circuit := S.circuit
  εapp := S.εapp
  eventBound := S.eventBound.comapWith f chk

variable {I : Type} {relI : Set (Stmt × I)}

/-- **The simulator data at the statements `Stmt'`**: the application phase's simulator read through
`f` (`PhaseStep.Sim.comap`), the domains' simulators. -/
def SimData.comap {C : IOP Stmt W rel} (S : C.SimData) (f : Stmt' → Stmt) : (C.comap f).SimData where
  app := S.app.comap f
  sim := S.sim

/-- **The simulator data with a statement check** (`PhaseStep.Sim.comapWith`). -/
def SimData.comapWith {C : IOP Stmt W rel} (S : C.SimData) (f : Stmt' → Stmt) (chk : Stmt' → Bool) :
    (C.comapWith f chk).SimData where
  app := S.app.comapWith f chk
  sim := S.sim

/-- **The honest prover at the statements `Stmt'`**, on the honest inputs
`{(x', y) | (f x', y) ∈ relI}`, simulated by `SimData.comap`. -/
def Honest.comap {C : IOP Stmt W rel} {S : C.SimData} (Hc : C.Honest S I relI) (f : Stmt' → Stmt) :
    (C.comap f).Honest (S.comap f) I {p | (f p.1, p.2) ∈ relI} where
  In := Hc.In
  dom := Hc.dom
  app := Hc.app.comap f
  circuit := Hc.circuit
  accepts := Hc.accepts
  perfect := Hc.perfect

/-- **The honest prover with a statement check**, on the honest inputs whose statements pass it,
simulated by `SimData.comapWith`. -/
def Honest.comapWith {C : IOP Stmt W rel} {S : C.SimData} (Hc : C.Honest S I relI) (f : Stmt' → Stmt)
    (chk : Stmt' → Bool) :
    (C.comapWith f chk).Honest (S.comapWith f chk) I {p | chk p.1 = true ∧ (f p.1, p.2) ∈ relI} where
  In := Hc.In
  dom := Hc.dom
  app := Hc.app.comapWith f chk
  circuit := Hc.circuit
  accepts := Hc.accepts
  perfect := Hc.perfect

end RealizedProgram.ProofSystem.IOP

end GordieHowe
