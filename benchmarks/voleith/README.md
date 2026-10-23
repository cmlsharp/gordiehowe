# VOLE-in-the-head ML-DSA-44 proofs against our proof of possession

The comparison with Baum and Beckmann's ML-DSA-44 proof (ePrint 2026/2473),
run by `repro.sh`'s `voleith` stage.

## Sources

- The proof system, their fork of swanky's schmivitz:
  `anonymous.4open.science/r/swanky-0321`.
- The circuits and protocol: `anonymous.4open.science/r/blind_mldsa-800C`.

Both were downloaded on 2026-10-17 through the repository API's zip endpoint
(`https://anonymous.4open.science/api/repo/<id>/zip`) and unpacked side by
side (`swanky/`, `blind_mldsa/`), as their Appendix B requires.
`repro.sh --voleith-zips` checks the two archives against these digests:

| Archive | sha256 | Files |
| --- | --- | ---: |
| `blind_mldsa-800C` zip | `72b34f9e3faee87928daf75da4ae7e5e1ecd9b525811f838d0f465edd3cf54be` | 39 |
| `swanky-0321` zip | `3d5a74f61b1aa766fd7d027f771de6ddf6cab8dcfa651cdf62b3335fe61a2231` | 765 |

`provenance/` holds the sha256 of every unpacked file and the API's listing.

## Files

- `scripts/patches/bb-private-message.patch`: their statement with the
  message private, as in our proof of possession.
- `scripts/pop_bench.rs`: the driver of their proof.
- `scripts/bb_build.sh`, `scripts/bb_check.sh`: the build and a correctness run.
- `scripts/time.sh`: the timing session, ours and theirs interleaved in
  blocks, 1 and 4 threads; `scripts/summarize.py`: its tables.
- `scripts/patches/vm-*.patch`, `scripts/vm_*`: Cloudflare's vole-mole
  variants, for reference only; the paper does not report them.
- `fixture/`: the key, message and signature both proofs use.
