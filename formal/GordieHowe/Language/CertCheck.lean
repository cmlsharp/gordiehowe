-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public meta import Lean.Elab.Tactic.ElabTerm

public meta section

/-!
# The tactic that decides the GKR circuit certificates

Every check of the GKR circuit certificates in `GordieHowe/Generated/` is a `Bool` checker applied
to exported data, closed by `gh_cert_check`, which the GKR certificates' generator emits. (The plan
and program certificates are closed by `decide +kernel` directly.)

`gh_cert_check` runs `decide +kernel` (the kernel evaluates the checker, adding no axiom) unless
`GordieHowe.certCheckNative` below is `true`, in which case it runs `gh_native_check`
(`Realizations/Circuit/LoadNative.lean`): the checker is compiled and evaluated on the certificate
data read from its file at run time, and the result is trusted through an axiom added for each use
(`<theorem>._native.native_decide.ax_<i>_<j>`, as `native_decide` names it in Lean v4.34).

The switch is this one definition for the whole build, set by `scripts/cert_mode.sh
kernel|native`. Every module that uses the tactic imports this one, so Lake rebuilds those
modules, and every module downstream of one, after a switch.

`native_decide` is for development builds only: the published check runs in kernel mode, and
`scripts/check.sh` fails in native mode unless given `--dev`, and reports every headline theorem
whose axioms include such an axiom.
-/

namespace GordieHowe

open Lean Elab Tactic

/-- **The GKR certificate check mode**: `false` (the default, and the mode of every published
check) decides the certificates by `decide +kernel`, `true` by `native_decide`. Set by
`scripts/cert_mode.sh`. -/
def certCheckNative : Bool := false

/-- `gh_cert_check`: closes a decidable goal by `decide +kernel`, or by `native_decide` when
`GordieHowe.certCheckNative` is `true`. -/
syntax (name := ghCertCheck) "gh_cert_check" : tactic

/-- `gh_native_check`: native mode's check; its elaborator is in `LoadNative.lean`. -/
syntax (name := ghNativeCheck) "gh_native_check" : tactic

/-- The elaborator of `gh_cert_check`. -/
@[tactic ghCertCheck]
def evalGhCertCheck : Tactic := fun _ => do
  if certCheckNative then
    evalTactic (← `(tactic| gh_native_check))
  else
    evalTactic (← `(tactic| decide +kernel))

end GordieHowe
