#!/usr/bin/env python3
# Copyright 2026 Chad Sharp and Paul Grubbs
# SPDX-License-Identifier: Apache-2.0

"""Convert C++ ML-DSA reference test vectors into Lean data files.

Reads from lib/circuits/tests/pq/ml_dsa/ under the repo root (the parent
of formal/) and writes Lean source under
formal/Test/GordieHoweTest/Data/.

Run from anywhere; paths are resolved relative to this script's location. Most of these source
files are in the original longfellow-zk repository, not in this one.

  python3 Test/scripts/gen_vectors.py

Source files read (all under lib/circuits/tests/pq/ml_dsa/):
  - ml_dsa_ref_test.cc                  ExpandA seed for ML-DSA-44
  - ml_dsa_ref_test_vectors.inc         kExpectedExpandAVectors (44),
                                        GetSampleInBallTests (44)
  - ml_dsa_44_benchmark.inc             full (msg, pk, ctx, mu, sig) example
  - ml_dsa_65_ref_test_vectors.inc      kExpectedExpandAVectors (65)
  - ml_dsa_65_examples.cc               GetMlDsa65Examples first entry
"""
import re
import pathlib

HERE = pathlib.Path(__file__).resolve().parent
REPO_ROOT = HERE.parents[2]  # formal/Test/scripts -> repo root
ML_DSA_DIR = REPO_ROOT / "lib" / "circuits" / "tests" / "pq" / "ml_dsa"
OUT_DIR = HERE.parent / "GordieHoweTest" / "Data"
LICENSE_HEADER = [
    "-- Copyright 2026 Chad Sharp and Paul Grubbs",
    "-- SPDX-License-Identifier: Apache-2.0",
    "",
]


def read(name: str) -> str:
    return (ML_DSA_DIR / name).read_text()


def extract_hex_blocks(text: str) -> list[str]:
    """Return the hex strings inside each hexToBytes(...) call, in order."""
    blocks = re.findall(r'hexToBytes\(\s*((?:"[0-9a-fA-F]*"\s*)+)\)', text)
    return ["".join(re.findall(r'"([0-9a-fA-F]*)"', b)) for b in blocks]


def extract_ints(text: str) -> list[int]:
    return [int(x) for x in re.findall(r'\d+', text)]


def slice_between(text: str, start_marker: str, end_marker: str) -> str:
    i = text.index(start_marker)
    j = text.index(end_marker, i + len(start_marker))
    return text[i + len(start_marker):j]


def slice_braced(text: str, decl: str) -> str:
    """decl ends in '{'; return the text strictly between that '{' and its
    matching '}', by brace-depth counting (robust to formatting)."""
    i = text.index(decl)
    open_pos = i + len(decl) - 1
    assert text[open_pos] == '{'
    depth = 1
    j = open_pos + 1
    while depth > 0:
        if text[j] == '{':
            depth += 1
        elif text[j] == '}':
            depth -= 1
        j += 1
    return text[open_pos + 1:j - 1]


def gen_expand_a(varname: str, text: str, decl: str, k: int, l: int, n: int) -> list[list[list[int]]]:
    body = slice_braced(text, decl)
    nums = extract_ints(body)
    assert len(nums) == k * l * n, f"{varname}: expected {k*l*n} numbers, got {len(nums)}"
    out = []
    idx = 0
    for _r in range(k):
        row = []
        for _s in range(l):
            row.append(nums[idx:idx + n])
            idx += n
        out.append(row)
    return out


def lean_nat_array_1d(name: str, xs: list[int]) -> str:
    body = ", ".join(str(x) for x in xs)
    return f"def {name} : Array Nat := #[{body}]\n"


def lean_expand_a_def(name: str, table: list[list[list[int]]]) -> str:
    """Flatten a k x l x 256 table into one Array Nat, row-major (r, s, i).

    Prefixed with `set_option maxRecDepth`: elaborating a `#[...]` literal with
    thousands of entries exceeds Lean's default recursion depth otherwise.
    """
    flat = [v for row in table for col in row for v in col]
    return "set_option maxRecDepth 100000 in\n" + lean_nat_array_1d(name, flat)


def gen_sample_in_ball(text: str) -> list[tuple[list[int], list[int]]]:
    """Parse the ten test cases in GetSampleInBallTests's return list."""
    body = slice_between(
        text,
        "std::vector<MlDsa44ByteInputOutput> GetSampleInBallTests() {\n  return {",
        "\n}",
    )
    # Walk brace depth to split into the ten top-level `{ {in...}, {out...} }`
    # entries.
    entries = []
    depth = 0
    cur_start = None
    for i, ch in enumerate(body):
        if ch == '{':
            if depth == 0:
                cur_start = i
            depth += 1
        elif ch == '}':
            depth -= 1
            if depth == 0 and cur_start is not None:
                entries.append(body[cur_start:i + 1])
                cur_start = None
    assert len(entries) == 10, f"expected 10 SampleInBall entries, got {len(entries)}"
    tests = []
    for e in entries:
        # e is `{ {in bytes}, { out values } }`; split at top level (depth 1)
        inner = e[1:-1]
        depth = 0
        parts = []
        cur = []
        for ch in inner:
            if ch == '{':
                depth += 1
                if depth == 1:
                    cur = []
                    continue
            if ch == '}':
                depth -= 1
                if depth == 0:
                    parts.append("".join(cur))
                    continue
            if depth >= 1:
                cur.append(ch)
        assert len(parts) == 2, f"expected 2 parts (in, out), got {len(parts)}"
        in_bytes = extract_ints(parts[0])
        out_vals = extract_ints(parts[1])
        assert len(in_bytes) == 32, len(in_bytes)
        assert len(out_vals) == 256, len(out_vals)
        tests.append((in_bytes, out_vals))
    return tests


def hex_of_bytes(bs: list[int]) -> str:
    return "".join(f"{b:02x}" for b in bs)


def main():
    OUT_DIR.mkdir(parents=True, exist_ok=True)

    # ---- ML-DSA-44 ExpandA ----
    ref_test_cc = read("ml_dsa_ref_test.cc")
    seed_match = re.search(
        r"static std::vector<uint8_t> ExpandASeed\(\) \{\s*return \{([^}]*)\};",
        ref_test_cc,
    )
    seed44 = [int(x, 16) for x in re.findall(r'0x[0-9a-fA-F]+', seed_match.group(1))]
    assert len(seed44) == 32, len(seed44)

    ref_vectors = read("ml_dsa_ref_test_vectors.inc")
    table44 = gen_expand_a(
        "kExpectedExpandAVectors44", ref_vectors,
        "extern const uint64_t kExpectedExpandAVectors[4][4][256] = {",
        4, 4, 256,
    )

    out = list(LICENSE_HEADER)
    out.append("-- Generated by Test/scripts/gen_vectors.py from")
    out.append("-- lib/circuits/tests/pq/ml_dsa/ml_dsa_ref_test.cc (ExpandASeed for MLDsa44Params)")
    out.append("-- and lib/circuits/tests/pq/ml_dsa/ml_dsa_ref_test_vectors.inc")
    out.append("-- (kExpectedExpandAVectors[4][4][256]). DO NOT EDIT BY HAND; rerun the script.")
    out.append("")
    out.append("namespace GordieHoweTest")
    out.append("")
    out.append(f"def expandASeed44Hex : String := \"{hex_of_bytes(seed44)}\"")
    out.append("")
    out.append("-- Flattened (r, s, i) row-major: index r * 4 * 256 + s * 256 + i, r s : Fin 4.")
    out.append(lean_expand_a_def("expandA44Expected", table44))
    out.append("")
    out.append("end GordieHoweTest")
    (OUT_DIR / "ExpandA44.lean").write_text("\n".join(out) + "\n")

    # ---- ML-DSA-44 SampleInBall ----
    sib_tests = gen_sample_in_ball(ref_vectors)
    out = list(LICENSE_HEADER)
    out.append("-- Generated by Test/scripts/gen_vectors.py from")
    out.append("-- lib/circuits/tests/pq/ml_dsa/ml_dsa_ref_test_vectors.inc")
    out.append("-- (GetSampleInBallTests(), kNumSampleInBallTests = 10). DO NOT EDIT BY HAND.")
    out.append("")
    out.append("namespace GordieHoweTest")
    out.append("")
    out.append("-- Each entry: (32-byte c-tilde-style input hex, 256 expected coefficients")
    out.append("-- as naturals mod q, i.e. 0, 1, or q - 1).")
    out.append("def sampleInBall44Tests : Array (String × Array Nat) := #[")
    for i, (inb, outv) in enumerate(sib_tests):
        comma = "," if i < len(sib_tests) - 1 else ""
        out.append(f"  (\"{hex_of_bytes(inb)}\", #[{', '.join(str(v) for v in outv)}]){comma}")
    out.append("]")
    out.append("")
    out.append("end GordieHoweTest")
    (OUT_DIR / "SampleInBall44.lean").write_text("\n".join(out) + "\n")

    # ---- ML-DSA-44 benchmark (msg, pk, ctx, sig) ----
    bench = read("ml_dsa_44_benchmark.inc")
    blocks = extract_hex_blocks(bench)
    assert len(blocks) == 5, len(blocks)
    msg_hex, pk_hex, ctx_hex, mu_hex, sig_hex = blocks
    assert len(msg_hex) // 2 == 32
    assert len(pk_hex) // 2 == 1312
    assert len(ctx_hex) // 2 == 0
    assert len(sig_hex) // 2 == 2420
    out = list(LICENSE_HEADER)
    out.append("-- Generated by Test/scripts/gen_vectors.py from")
    out.append("-- lib/circuits/tests/pq/ml_dsa/ml_dsa_44_benchmark.inc")
    out.append("-- (OpenSSL 3.6.4-signed ML-DSA-44 example; message bytes 00..1f, empty context).")
    out.append("-- DO NOT EDIT BY HAND.")
    out.append("")
    out.append("namespace GordieHoweTest")
    out.append("")
    out.append(f"def bench44MsgHex : String := \"{msg_hex}\"")
    out.append(f"def bench44PkHex : String := \"{pk_hex}\"")
    out.append(f"def bench44CtxHex : String := \"{ctx_hex}\"")
    out.append(f"def bench44SigHex : String := \"{sig_hex}\"")
    out.append("")
    out.append("end GordieHoweTest")
    (OUT_DIR / "Benchmark44.lean").write_text("\n".join(out) + "\n")

    # ---- ML-DSA-65 ExpandA ----
    seed65 = list(range(32))
    ref65 = read("ml_dsa_65_ref_test_vectors.inc")
    table65 = gen_expand_a(
        "kExpectedExpandAVectors65", ref65,
        "extern const uint64_t kExpectedExpandAVectors[6][5][256] = {",
        6, 5, 256,
    )
    out = list(LICENSE_HEADER)
    out.append("-- Generated by Test/scripts/gen_vectors.py from")
    out.append("-- lib/circuits/tests/pq/ml_dsa/ml_dsa_ref_test.cc (ExpandASeed for MLDsa65Params:")
    out.append("-- bytes 0..31) and lib/circuits/tests/pq/ml_dsa/ml_dsa_65_ref_test_vectors.inc")
    out.append("-- (kExpectedExpandAVectors[6][5][256]). DO NOT EDIT BY HAND.")
    out.append("")
    out.append("namespace GordieHoweTest")
    out.append("")
    out.append(f"def expandASeed65Hex : String := \"{hex_of_bytes(seed65)}\"")
    out.append("")
    out.append("-- Flattened (r, s, i) row-major: index r * 5 * 256 + s * 256 + i, r : Fin 6, s : Fin 5.")
    out.append(lean_expand_a_def("expandA65Expected", table65))
    out.append("")
    out.append("end GordieHoweTest")
    (OUT_DIR / "ExpandA65.lean").write_text("\n".join(out) + "\n")

    # ---- ML-DSA-65 example 0 (msg, pk, ctx, sig) ----
    ex65 = read("ml_dsa_65_examples.cc")
    start = ex65.index("GetMlDsa65Examples() {")
    end = ex65.index("GetMlDsa65FailExamples")
    body = ex65[start:end]
    blocks65 = extract_hex_blocks(body)
    assert len(blocks65) >= 5, len(blocks65)
    msg65_hex, pk65_hex, ctx65_hex, mu65_hex, sig65_hex = blocks65[:5]
    out = list(LICENSE_HEADER)
    out.append("-- Generated by Test/scripts/gen_vectors.py from")
    out.append("-- lib/circuits/tests/pq/ml_dsa/ml_dsa_65_examples.cc")
    out.append("-- (first entry of GetMlDsa65Examples()). DO NOT EDIT BY HAND.")
    out.append("")
    out.append("namespace GordieHoweTest")
    out.append("")
    out.append(f"def example65MsgHex : String := \"{msg65_hex}\"")
    out.append(f"def example65PkHex : String := \"{pk65_hex}\"")
    out.append(f"def example65CtxHex : String := \"{ctx65_hex}\"")
    out.append(f"def example65SigHex : String := \"{sig65_hex}\"")
    out.append("")
    out.append("end GordieHoweTest")
    (OUT_DIR / "Example65.lean").write_text("\n".join(out) + "\n")

    print("wrote:")
    for f in sorted(OUT_DIR.glob("*.lean")):
        print(" ", f, f.stat().st_size, "bytes")


if __name__ == "__main__":
    main()
