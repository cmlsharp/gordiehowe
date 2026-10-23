# XKCP subset

cSHAKE256 of NIST SP 800-185 (`cSHAKE256_Initialize` / `_Update` / `_Final` / `_Squeeze`), for the
Fiat–Shamir challenge stream of `lib/random/transcript.h`, from the eXtended Keccak Code Package.

- Upstream: <https://github.com/XKCP/XKCP>, commit `4affab454735d54e78156880b3b44e38dcbf765c`
  (2026-09-25).
- `upstream/` holds the vendored files verbatim, at their upstream paths under `lib/`.
- `config/` and `select/` are ours (Apache-2.0). They contain no hash code:
  - `config/xkcp-target.h` chooses the Keccak-p[1600] implementation from compiler-predefined
    macros, so a cross build picks the target's implementation;
  - `config/KeccakP-1600-SnP.h` includes the chosen implementation's SnP header;
  - `config/config.h` replaces the `config.h` that XKCP's build generates;
  - `config/brg_endian.h` replaces XKCP's `lib/common/brg_endian.h`, which is not CC0; it defines
    the byte-order macros from `__BYTE_ORDER__`;
  - `select/keccakp1600.c`, `select/keccakp1600-avx2.S` and `select/keccakp1600-armv7a-neon.S`
    compile the chosen implementation and nothing else; each `.S` wrapper is empty unless
    `xkcp-target.h` picks its core.

## License

XKCP's `LICENSE` names the files it does not release under CC0: `lib/common/brg_endian.h`
(Gladman), the AVX2 and AVX-512 assembler cores (`KeccakP-1600-AVX2.s`, `KeccakP-1600-AVX512.s`,
CRYPTOGAMS license) and the AArch64 ARMv8-A SHA3 cores (Apache-2.0 OR ISC OR MIT). Of these,
only the AVX2 core is vendored:

- `upstream/lib/low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.s` is under the CRYPTOGAMS license
  (BSD-style, three clauses, with a GPL alternative). `LICENSE.CRYPTOGAMS` holds its text,
  copied verbatim from XKCP's `LICENSE`; redistribution in source or binary form must reproduce
  it.

Every other vendored file carries the CC0 waiver ("To the extent possible under law, the
implementer has waived all copyright ... http://creativecommons.org/publicdomain/zero/1.0/") in
its header; checked file by file:

| File (under `upstream/lib/`) | Role |
|---|---|
| `common/align.h`, `common/SnP-common.h`, `common/load-store.h` | common macros |
| `low/common/SnP-Relaned.h` | SnP helpers |
| `low/KeccakP-1600/common/KeccakP-1600-64.macros`, `KeccakP-1600-unrolling.macros` | round macros of opt64 |
| `low/KeccakP-1600/plain-64bits/KeccakP-1600-opt64.c`, `KeccakP-1600-plain64.h`, `SnP/KeccakP-1600-SnP.h` | opt64 |
| `low/KeccakP-1600/AVX512/C/KeccakP-1600-AVX512.c`, `KeccakP-1600-SnP.h` | AVX-512 (C intrinsics) |
| `low/KeccakP-1600/AVX2/KeccakP-1600-AVX2.h`, `SnP/KeccakP-1600-SnP.h` | AVX2 interface (the `.s` is CRYPTOGAMS, above) |
| `low/KeccakP-1600/ARMv7A-NEON/KeccakP-1600-armv7a-le-neon-gcc.s`, `KeccakP-1600-SnP.h` | ARMv7-A NEON |
| `low/KeccakP-1600/plain-32bits-inplace/KeccakP-1600-inplace32BI.c`, `KeccakP-1600-SnP.h` | 32-bit bit-interleaved |
| `high/Keccak/KeccakSponge.c`, `.h`, `.inc` | the sponge |
| `high/Keccak/SP800-185/SP800-185.c`, `.h`, `.inc`, `high/common/Phases.h` | SP 800-185 |

## Keccak-p[1600] per target

Chosen in `config/xkcp-target.h`, first match wins. The C and assembler sources are compiled
with the C++ flags (`CMAKE_CXX_FLAGS`, e.g. `-march=native`) and the architecture flags of
`lib/CMakeLists.txt`, so the library and the C++ headers choose alike.

| Target | Condition | Implementation | Status (2026-09-30) |
|---|---|---|---|
| x86-64 with AVX-512 | `__x86_64__`, `__AVX512F__`, `__AVX512VL__` | `AVX512/C` | compiled (`-march=znver4`); not run: the Core Ultra 5 125H test machine has no AVX-512 and qemu-user lacks it |
| x86-64 ELF with AVX2, opt-in via `LONGFELLOW_XKCP_USE_AVX2` (off by default: 14–21% more cycles than `plain-64bits` on the Core Ultra 5 125H) | `LONGFELLOW_XKCP_USE_AVX2`, `__x86_64__`, `__AVX2__`, `__ELF__` | `AVX2` (CRYPTOGAMS assembler) | Core Ultra 5 125H, `-march=native`: NIST cSHAKE256 samples, `transcript_test`, `ligero_test`, `zk_test`, `falcon_skip_e2e_test`, `ml_dsa_split_e2e_test` in both field profiles |
| ARMv7-A with NEON | `__arm__`, `__ARM_NEON`, `__ARM_ARCH >= 7`, little endian, ARM state | `ARMv7A-NEON` | cross-compiled (gcc 15, `-march=armv7-a -mfpu=neon-vfpv4 -mfloat-abi=hard`); NIST cSHAKE256 samples 3 and 4 pass under qemu-arm |
| other 64-bit, including AArch64 | `__SIZEOF_POINTER__ == 8` | `plain-64bits`, all rounds unrolled | x86-64 (Core Ultra 5 125H): full test suite; AArch64: cross-compiled (gcc 15, `-march=armv8-a+crypto`), NIST samples pass under qemu-aarch64 |
| other 32-bit | otherwise | `plain-32bits-inplace` | cross-compiled for ARMv7-A without NEON; NIST samples pass under qemu-arm |

On the Core Ultra 5 125H (clang 21, `-O3 -march=native`), one challenge point (cSHAKE256 with a
48-byte key, squeezing 64 B, 1 KiB or 97,248 B) costs the AVX2 core 14–21% more user cycles than
opt64 on a P-core (2,510 against 2,200; 10,580 against 8,890; 821,000 against 681,500) and
2.2–2.5 times the time on an E-core.

The AVX2 core requires ELF because it assembles its `.type`/`.size` directives unless the
assembler symbol `old_gas_syntax` is defined, which XKCP's build defines for macOS; x86-64
Mach-O and PE targets use opt64. `select/keccakp1600-avx2.S` includes the `.s` through the C
preprocessor, which leaves its code unchanged and only cuts short the `#` comment lines that
contain `//`. AArch64 uses opt64 as XKCP's
`ARMv8A` target does (`LowLevel.build` marks its NEON assembler core obsolete, slower than plain
C); the faster ARMv8.4-A SHA3 core is not CC0.
