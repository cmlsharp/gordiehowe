-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

import GordieHoweTest.GKRCertificate
import GordieHowe.Language.Realizations.Circuit.RelEntry

/-!
# The certificate loader on the C++ exporter's small certificates

The `.ghc` files the C++ test `lib/circuits/compiler/cert_export_test.cc` writes
(`GKRRelData/cert_<name>.ghc`), loaded by `load_ghc`: for the circuits of `GKRCertificate.lean`
the decoded DAG, layered circuit and schedule are its literals (`rfl`, checked by the kernel), and
every loaded schedule passes the checker.
-/

namespace GordieHoweTest.GKRRelLoad

open GordieHowe.GKR.Certificate

namespace Add

load_ghc "GKRRelData/cert_add.ghc" "566deec2de2eca5d"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.Add.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.Add.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.Add.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Add

namespace Mul

load_ghc "GKRRelData/cert_mul.ghc" "8744e2d68a54d37a"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.Mul.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.Mul.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.Mul.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Mul

namespace Scale

load_ghc "GKRRelData/cert_scale.ghc" "e766cd58badc85e1"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.Scale.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.Scale.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.Scale.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Scale

namespace Copies

load_ghc "GKRRelData/cert_copies.ghc" "dac45b18e3e6bbb0"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.Copies.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.Copies.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.Copies.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Copies

namespace Cse

load_ghc "GKRRelData/cert_cse.ghc" "92b8f3121a6b299f"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.Cse.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.Cse.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.Cse.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Cse

namespace LastLayer

load_ghc "GKRRelData/cert_lastlayer.ghc" "74f5b4b736f6a206"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.LastLayer.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.LastLayer.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.LastLayer.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end LastLayer

namespace OutputAnInput

load_ghc "GKRRelData/cert_output_an_input.ghc" "e63ffb3474e96c56"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.OutputAnInput.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.OutputAnInput.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.OutputAnInput.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end OutputAnInput

namespace AliasLinearCopy

load_ghc "GKRRelData/cert_alias_linear_copy.ghc" "7ef289dcf9fecfc7"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.AliasLinearCopy.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.AliasLinearCopy.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.AliasLinearCopy.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end AliasLinearCopy

namespace Assert0

load_ghc "GKRRelData/cert_assert0.ghc" "566deec2de2eca5d"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.Assert0.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.Assert0.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.Assert0.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Assert0

namespace Canonicalization

load_ghc "GKRRelData/cert_canonicalization.ghc" "135dbe394dbdc18b"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.Canonicalization.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.Canonicalization.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.Canonicalization.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Canonicalization

namespace MatMul

load_ghc "GKRRelData/cert_matmul.ghc" "e3c5ecbee3b1cd64"

/-- The decoded DAG is the literal. -/
example : cert.dag = GKRCertificate.MatMul.dag := rfl

/-- The decoded layered circuit is the literal. -/
example : cert.layered = GKRCertificate.MatMul.circuit := rfl

/-- The decoded schedule is the literal. -/
example : cert.sched = GKRCertificate.MatMul.cert := rfl

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end MatMul

namespace Folds

load_ghc "GKRRelData/cert_folds.ghc" "e35e0691b8551348"

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Folds

namespace Ladder1k

load_ghc "GKRRelData/cert_ladder1k.ghc" "86b2858093fbda37"

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Ladder1k

namespace Ladder5k

load_ghc "GKRRelData/cert_ladder5k.ghc" "33a161c0905319dd"

/-- The loaded schedule passes the checker. -/
example : check cert.dag cert.layered cert.sched = true := by decide +kernel

end Ladder5k

end GordieHoweTest.GKRRelLoad
