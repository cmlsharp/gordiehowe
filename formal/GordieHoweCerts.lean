-- Copyright 2026 Chad Sharp and Paul Grubbs
-- SPDX-License-Identifier: Apache-2.0

module

public import GordieHowe
public import GordieHowe.Applications.Falcon512.Emulated.QROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Emulated.ROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Native.QROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Native.ROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.RingForger
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.RingScheme
public import GordieHowe.Applications.Falcon512.Ring.Carrier.QROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.RingForger
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.RingScheme
public import GordieHowe.Applications.Falcon512.Ring.Carrier.ROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.RingForger
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.RingProgram
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.RingScheme
public import GordieHowe.Applications.Falcon512.Ring.Native.QROMParams.Theorem
public import GordieHowe.Applications.Falcon512.Ring.Native.ROMParams.RingForger
public import GordieHowe.Applications.Falcon512.Ring.Native.ROMParams.RingScheme
public import GordieHowe.Applications.Falcon512.Ring.Native.ROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Emulated.QROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Emulated.ROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Native.QROMParams
public import GordieHowe.Applications.MLDSA44.Native.QROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Native.ROMParams
public import GordieHowe.Applications.MLDSA44.Native.ROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.QROMParams.RingForger
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.QROMParams.RingScheme
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.QROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.ROMParams.RingForger
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.ROMParams.RingScheme
public import GordieHowe.Applications.MLDSA44.Ring.Carrier.ROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.RingForger
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.RingScheme
public import GordieHowe.Applications.MLDSA44.Ring.Native.QROMParams.Theorem
public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.RingForger
public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.RingScheme
public import GordieHowe.Applications.MLDSA44.Ring.Native.ROMParams.Theorem
public import GordieHowe.Applications.ZKFigures
public import GordieHowe.Generated.Falcon512.Emulated.QROMParams.Certified
public import GordieHowe.Generated.Falcon512.Emulated.ROMParams.Certified
public import GordieHowe.Generated.Falcon512.Native.QROMParams.Certified
public import GordieHowe.Generated.Falcon512.Native.ROMParams.Certified
public import GordieHowe.Generated.Falcon512.Ring.Carrier.QROMParams.Certified
public import GordieHowe.Generated.Falcon512.Ring.Carrier.ROMParams.Certified
public import GordieHowe.Generated.Falcon512.Ring.Native.QROMParams.Certified
public import GordieHowe.Generated.Falcon512.Ring.Native.ROMParams.Certified
public import GordieHowe.Generated.MDL.ECDSA.ROMParams.Certified
public import GordieHowe.Generated.MDL.MLDSA44.Attrs1.QROMParams.Certified
public import GordieHowe.Generated.MDL.MLDSA44.Attrs1.ROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Emulated.QROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Emulated.ROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Native.QROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Native.ROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.QROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Ring.Carrier.ROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Ring.Native.QROMParams.Certified
public import GordieHowe.Generated.MLDSA44.Ring.Native.ROMParams.Certified
public import GordieHowe.Generated.RSA2048.Goldilocks2.Msg2KiB.ROMParams.Certified
public import GordieHowe.Generated.SHA256.Batched1KiB.ROMParams.Certified
public import GordieHowe.Generated.SHA256.Batched2KiB.ROMParams.Certified
public import GordieHowe.Generated.SHA256.Batched32KiB.ROMParams.Certified
public import GordieHowe.Generated.SHA256.Batched64B.ROMParams.Certified
public import GordieHowe.Generated.SHA256.Batched8Blocks.QROMParams.Certified
public import GordieHowe.Generated.SHA256.Batched8Blocks.ROMParams.Certified
public import GordieHowe.Generated.SHA256.Batched8KiB.QROMParams.Certified
public import GordieHowe.Generated.SHA256.Batched8KiB.ROMParams.Certified
public import GordieHowe.Generated.SHA3.Batched1KiB.QROMParams.Certified
public import GordieHowe.Generated.SHA3.Batched1KiB.ROMParams.Certified
public import GordieHowe.Generated.SHA3.Batched32KiB.ROMParams.Certified
public import GordieHowe.Generated.SHA3.Batched8KiB.ROMParams.Certified
public import GordieHowe.PaperManifest

@[expose] public section

/-!
# GordieHowe: the certificate library

The exported programs, plans and certificates (`GordieHowe/Generated/`) and every module that
imports one, directly or through another. The root imports every program's proof system from its
certificates (`GordieHowe/Generated/<program>/Certified.lean`, which imports the program's facts,
its validity, realization and completion certificates and its GKR circuits' certificates), the
modules with the applications' headline theorems, and the paper manifest.

`lake build` (the default target `GordieHowe`) checks no certificate; `lake build GordieHoweCerts`
and `scripts/check.sh --certs` check them. `GordieHowe` imports no module of this library
(`scripts/cert_boundary.py`).
-/
