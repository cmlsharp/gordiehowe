// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// The Falcon split baseline's gadget audit: each case evaluates a gadget on
// a fixed assignment with upstream's EvaluationBackend and prints whether
// its constraints accept it.
//
// usage: falcon_split_audit
//
//   ptr-past-stream     the routing of falcon_h2p_ptr.h before its bound
//                       pos[n-1] < S accepts a stream with n - 1 accepted
//                       chunks, a pointer past the stream and a free c[n-1];
//                       the bounded gadget rejects it, and accepts the
//                       honest routing
//   budget-one-group    Falcon-1024's encoding budget as one F_q sum (the
//                       Falcon-512 form) accepts high parts summing to
//                       J + q (an s2 that does not fit sbytelen); the
//                       grouped form rejects it, and accepts sum J
//   shake-private-len   shake256_private_length.h against upstream's
//                       Sha3Reference at lengths 0, 1, 7, 31 and 32 with
//                       Falcon's 40-byte prefix: the honest digest verifies,
//                       a digest of another length and a changed message
//                       byte are rejected
// Each line reads "LFB_AUDIT case=NAME accepted=0|1 want=0|1 ok|FAIL"; the
// exit status is 0 when every case behaves as wanted.
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <string>
#include <vector>

#include "circuits/logic/evaluation_backend.h"
#include "circuits/logic/logic.h"
#include "circuits/tests/sha3/sha3_circuit.h"
#include "circuits/tests/sha3/sha3_reference.h"
#include "circuits/tests/sha3/sha3_witness.h"
#include "falcon_encoding.h"
#include "falcon_h2p_ptr.h"
#include "falcon_hash_to_point.h"
#include "falcon_norm.h"
#include "falcon_set.h"
#include "fp14.h"
#include "fp14_n.h"
#include "gf2k/gf2_128.h"
#include "shake256_private_length.h"

namespace proofs {
namespace {

bool all_ok = true;
void report(const std::string& name, bool accepted, bool want) {
  const bool ok = accepted == want;
  std::printf("LFB_AUDIT case=%s accepted=%d want=%d %s\n", name.c_str(),
              accepted ? 1 : 0, want ? 1 : 0, ok ? "ok" : "FAIL");
  all_ok &= ok;
}

// falcon_h2p_ptr before the bound pos[n-1] < S (the baseline at 18d5878d).
template <class Logic>
void h2p_ptr_unbounded(const Logic& lc,
                       const std::vector<typename Logic::v16>& stream,
                       const std::vector<typename Logic::v16>& c,
                       const std::vector<typename Logic::v16>& pos,
                       uint64_t cutoff, uint64_t n) {
  using BitW = typename Logic::BitW;
  const size_t S = stream.size();
  const BitW btrue = lc.bit(1);
  for (size_t j = 0; j < n; ++j) {
    if (j > 0) lc.assert1(lc.vlt(pos[j - 1], pos[j]));
    for (size_t k = 0; k < S; ++k) {
      BitW is_at = lc.veq(pos[j], (uint64_t)k);
      BitW is_rej = lc.lnot(lc.vlt(stream[k], cutoff));
      lc.assert_implies(is_at, lc.veq(c[j], stream[k]));
      lc.assert_implies(is_at, lc.lnot(is_rej));
      BitW after_prev = (j > 0) ? lc.vlt(pos[j - 1], (uint64_t)k) : btrue;
      BitW before_cur = lc.vlt((uint64_t)k, pos[j]);
      lc.assert_implies(lc.land(after_prev, before_cur), is_rej);
    }
  }
}

void ptr_cases() {
  using F = GF2_128<>;
  using EB = EvaluationBackend<F>;
  using L = Logic<F, EB>;
  const F f;
  EB bk(f, false);
  const L lc(&bk, f);
  // S = 6 chunks, n = 4: three accepted (below 5q), three rejected.
  const std::vector<uint64_t> stream = {100, kFalconCutoff + 5, 200, 300,
                                        65000, 65001};
  auto v16s = [&](const std::vector<uint64_t>& v) {
    std::vector<typename L::v16> out;
    for (uint64_t x : v) out.push_back(lc.template vbit<16>(x));
    return out;
  };
  const auto st = v16s(stream);
  // The fourth pointer past the stream, its c free.
  const auto pos_bad = v16s({0, 2, 3, 6});
  const auto c_bad = v16s({100, 200, 300, 12345});
  h2p_ptr_unbounded(lc, st, c_bad, pos_bad, kFalconCutoff, 4);
  report("ptr-past-stream/before", !bk.assertion_failed(), true);
  falcon_h2p_ptr(lc, st, c_bad, pos_bad, kFalconCutoff, 4);
  report("ptr-past-stream/after", !bk.assertion_failed(), false);
  // The honest routing of n = 3 (the first three accepted).
  const auto pos_ok = v16s({0, 2, 3});
  const auto c_ok = v16s({100, 200, 300});
  falcon_h2p_ptr(lc, st, c_ok, pos_ok, kFalconCutoff, 3);
  report("ptr-honest/after", !bk.assertion_failed(), true);
}

// falcon_encoding_native_bits at Falcon-512's single group, for any n (the
// baseline at 18d5878d; its static_assert kept it from Falcon-1024).
template <class Logic>
void encoding_one_group(const Logic& lc,
                        const std::vector<FalconCoeffWires<Logic>>& cw,
                        size_t first, size_t count,
                        const typename Logic::EltW& slack,
                        const FalconNormParams& p, uint64_t budget) {
  using EltW = typename Logic::EltW;
  EltW sum = lc.konst(uint64_t{0});
  for (size_t i = first; i < first + count; ++i) {
    const EltW& a1 = cw[i].a_lo[1];
    const EltW& h = cw[i].a_lo[p.La - 1];
    EltW b = lc.sub(a1, lc.mul(lc.elt(uint64_t{2}), h));
    lc.assert0(lc.mul(b, lc.sub(b, lc.konst(uint64_t{1}))));
    sum = lc.add(sum, h);
  }
  lc.assert_eq(lc.add(sum, slack), lc.konst(budget));
}

void budget_cases() {
  using S = falcon_baseline::Falcon1024;
  using AF = Fp14_9;
  using EB = EvaluationBackend<AF>;
  using L = Logic<AF, EB>;
  const uint64_t q = falcon_baseline::kFalconQ, J = S::kHighBudget;
  const Fp14 base{q};
  const AF af{base, AF::beta_};
  EB bk(af, false);
  const L lc(&bk, af);
  FalconNormParams p = falcon_norm_params(q, 64, 2 * S::kN, S::kBetaSq);
  p.high_from = S::kN;
  // High parts h_i (a1 = 2 h_i, a0 = 0) summing to TOTAL over s2's n
  // coefficients, 15 per coefficient from the first on.
  auto rows = [&](uint64_t total) {
    std::vector<FalconCoeffWires<L>> cw(2 * S::kN);
    for (size_t i = 0; i < 2 * S::kN; ++i) {
      uint64_t h = 0;
      if (i >= S::kN) {
        h = total < 15 ? total : 15;
        total -= h;
      }
      cw[i].a_lo = {lc.konst(uint64_t{0}), lc.konst(2 * h), lc.konst(h)};
    }
    return cw;
  };
  const uint64_t over = J + q;
  {
    const auto cw = rows(over);
    encoding_one_group(lc, cw, S::kN, S::kN, lc.konst(uint64_t{0}), p, J);
    report("budget-one-group/before", !bk.assertion_failed(), true);
  }
  {
    // The grouped form (two groups of 512) with every first slack: the
    // first group's equation, which the second slack does not enter, fails
    // for each of them.
    const auto cw = rows(over);
    bool any = false;
    check(falcon_encoding_native_groups(S::kN, J, q) == 2, "two groups");
    const uint64_t smax = uint64_t{1} << falcon_bit_width(J);
    for (uint64_t s0 = 0; s0 < smax; ++s0) {
      falcon_encoding_native_bits(lc, cw, S::kN, S::kN,
                                  {lc.konst(s0), lc.konst(uint64_t{0})}, p, J);
      any |= !bk.assertion_failed();
    }
    report("budget-grouped/after", any, false);
  }
  {
    // The honest sum J: its slacks are J - (high parts up to each group's
    // end).
    const auto cw = rows(J);
    FalconEncodingAdvice e;
    uint64_t left = J;
    for (size_t i = 0; i < S::kN; ++i) {
      const uint64_t h = left < 15 ? left : 15;
      left -= h;
      e.high.push_back(h);
    }
    const auto slack = falcon_encoding_group_slacks(
        e, falcon_encoding_native_groups(S::kN, J, q), J);
    std::vector<typename L::EltW> sw;
    for (uint64_t x : slack) sw.push_back(lc.konst(x));
    falcon_encoding_native_bits(lc, cw, S::kN, S::kN, sw, p, J);
    report("budget-honest/after", !bk.assertion_failed(), true);
  }
}

void shake_cases() {
  using F = GF2_128<>;
  using EB = EvaluationBackend<F>;
  using L = Logic<F, EB>;
  const F f;
  EB bk(f, false);
  const L lc(&bk, f);
  constexpr size_t kPrefix = falcon_baseline::kNonceBytes;
  constexpr size_t kMax = falcon_baseline::kMaxMessageBytes;
  constexpr size_t kOut = falcon_baseline::Falcon512::kOutBytes;
  std::vector<uint8_t> prefix(kPrefix);
  for (size_t i = 0; i < kPrefix; ++i) prefix[i] = uint8_t(3 * i + 1);
  auto bytes = [&](const std::vector<uint8_t>& v) {
    std::vector<typename L::v8> out;
    for (uint8_t b : v) out.push_back(lc.template vbit<8>(b));
    return out;
  };
  auto witness_wires = [&](const std::vector<Sha3Witness::BlockWitness>& h) {
    std::vector<typename Sha3Circuit<L>::BlockWitness> out(h.size());
    for (size_t b = 0; b < h.size(); ++b)
      for (size_t r = 0; r < 24; ++r)
        for (size_t x = 0; x < 5; ++x)
          for (size_t y = 0; y < 5; ++y)
            out[b].a_intermediate[r][x][y] =
                lc.template vbit<64>(h[b].a_intermediate[r][x][y]);
    return out;
  };
  // The gadget on message bytes MSG (padded) with LENGTH's flags and the
  // block witnesses of WITNESS_MSG, its output compared with DIGEST.
  auto run = [&](const std::vector<uint8_t>& msg, size_t length,
                 const std::vector<uint8_t>& witness_msg,
                 const std::vector<uint8_t>& digest) {
    std::vector<Sha3Witness::BlockWitness> hbw;
    lfb::shake256_private_length_witness(prefix, witness_msg, kMax, kOut, hbw);
    const auto bws = witness_wires(hbw);
    std::vector<typename L::BitW> flags;
    for (uint8_t b : lfb::shake256_in_message(length, kMax))
      flags.push_back(lc.bit(b));
    std::vector<typename L::v8> out;
    lfb::assert_shake256_private_length(
        lc, bytes(prefix), bytes(lfb::shake256_padded_message(msg, kMax)),
        flags, kOut, out, bws);
    for (size_t i = 0; i < kOut; ++i)
      lc.vassert_eq(out[i], lc.template vbit<8>(digest[i]));
    return !bk.assertion_failed();
  };
  auto shake = [&](const std::vector<uint8_t>& msg) {
    std::vector<uint8_t> in = prefix;
    in.insert(in.end(), msg.begin(), msg.end());
    std::vector<uint8_t> d(kOut);
    Sha3Reference::shake256Hash(in.data(), in.size(), d.data(), d.size());
    return d;
  };
  for (size_t len : {size_t{0}, size_t{1}, size_t{7}, size_t{31}, size_t{32}}) {
    std::vector<uint8_t> msg(len);
    for (size_t i = 0; i < len; ++i) msg[i] = uint8_t(7 * i + 5);
    const std::string tag = "shake-private-len/" + std::to_string(len);
    report(tag + "/honest", run(msg, len, msg, shake(msg)), true);
    // A digest of the message one byte longer (or shorter), with the
    // flags of LEN and the honest block witnesses.
    std::vector<uint8_t> other = msg;
    if (len < kMax) {
      other.push_back(0);
    } else {
      other.pop_back();
    }
    report(tag + "/other-length", run(msg, len, msg, shake(other)), false);
    if (len > 0) {
      std::vector<uint8_t> changed = msg;
      changed[len - 1] ^= 0x40;
      report(tag + "/changed-byte", run(changed, len, msg, shake(msg)),
             false);
    }
  }
}

}  // namespace
}  // namespace proofs

int main() {
  proofs::ptr_cases();
  proofs::budget_cases();
  proofs::shake_cases();
  std::printf("LFB_AUDIT_RESULT %s\n", proofs::all_ok ? "pass" : "FAIL");
  return proofs::all_ok ? 0 : 1;
}
