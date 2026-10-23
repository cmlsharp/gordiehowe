// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
// Native signature relations against the same commitment as the circuit and
// MAC.
#ifndef PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_NATIVE_LINEAR_H_
#define PRIVACY_PROOFS_ZK_LIB_CIRCUITS_NTT_NATIVE_LINEAR_H_
#include "circuits/mac/linear_mac.h"
#include <cstddef>
#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <vector>

namespace proofs::native_linear {
// Coefficient equations over F[X]/(X^n + 1). A term is either a witness
// polynomial itself or its negacyclic product with a public polynomial.
template <class F> class Relation {
public:
  using E = typename F::Elt;
  using EC = typename ZkCommon<F>::ExtraConstraints;
  using Map = std::vector<std::pair<size_t, E>>;
  using Poly = std::vector<Map>;
  // NTT inputs are evaluations at root^(2*bitreverse(k)+1), matching the
  // negacyclic plan. Their ordering and root are part of the public interface.
  enum class PublicForm { kCoefficients, kNtt };
  struct Term {
    size_t row, poly;
    E sign;
    std::vector<size_t> coefficients;
    PublicForm form;
  };
  const F &f;
  size_t npub, n, groups;
  E root;
  std::vector<Poly> polys;
  std::vector<Term> terms;
  Relation(const F &field, size_t pub, size_t g, size_t count, E psi)
      : f(field), npub(pub), n(count), groups(g), root(psi) {}
  template <class Wires>
  size_t poly(const InputLayoutBackend<F> &bk, const Wires &wires) {
    Poly p;
    for (auto w : wires)
      p.push_back({{bk.input_index(w), f.one()}});
    return poly(std::move(p));
  }
  size_t poly(Poly p) {
    check(p.size() == n, "polynomial size");
    for (const auto &m : p)
      for (const auto &[i, a] : m) {
        (void)a;
        check(i >= npub, "relation operand must be committed");
      }
    polys.push_back(std::move(p));
    return polys.size() - 1;
  }
  void term(size_t row, size_t p, E sign, std::vector<size_t> d = {},
            PublicForm form = PublicForm::kCoefficients) {
    check(row < groups && p < polys.size(), "term dimensions");
    check(d.empty() || d.size() == n, "coefficients dimensions");
    check(!d.empty() || form == PublicForm::kCoefficients,
          "NTT form requires a public polynomial");
    for (auto i : d)
      check(i < npub, "coefficients must be public");
    terms.push_back({row, p, sign, std::move(d), form});
  }
  // The rows' description: the operand maps and every term, with the value
  // of each public coefficient. Those coefficients are statement inputs, so
  // the tag is fixed before the protocol starts.
  std::vector<uint8_t> tag(const Dense<F> &pub) const {
    std::vector<uint8_t> tg;
    const char domain[] = "native-signature-convolution-v2";
    tg.assign(domain, domain + sizeof(domain));
    auto putn = [&](uint64_t v) {
      for (size_t b = 0; b < 8; ++b)
        tg.push_back((v >> (8 * b)) & 255);
    };
    auto pute = [&](E v) {
      uint8_t bytes[F::kBytes];
      f.to_bytes_field(bytes, v);
      tg.insert(tg.end(), bytes, bytes + sizeof(bytes));
    };
    putn(npub);
    putn(n);
    putn(groups);
    pute(root);
    putn(polys.size());
    for (const auto &p : polys)
      for (const auto &m : p) {
        putn(m.size());
        for (auto [i, a] : m) {
          putn(i);
          pute(a);
        }
      }
    putn(terms.size());
    for (const auto &t : terms) {
      putn(t.row);
      putn(t.poly);
      pute(t.sign);
      putn(static_cast<uint64_t>(t.form));
      putn(t.coefficients.size());
      for (auto i : t.coefficients) {
        putn(i);
        pute(pub.v_[i]);
      }
    }
    return tg;
  }
  EC extra(const Dense<F> &pub) const {
    EC ec;
    ec.tag = tag(pub);
    auto plan = std::make_shared<host_ntt::NegacyclicPlan<F>>(f, n, root);
    std::vector<std::vector<E>> spectra;
    for (const auto &t : terms) {
      std::vector<E> d;
      for (auto i : t.coefficients)
        d.push_back(pub.v_[i]);
      if (!d.empty()) {
        // C_a^T = C_{a*}, where a* = [a0, -a[n-1], ..., -a1].
        std::vector<E> star(n);
        if (t.form == PublicForm::kNtt) {
          // a*(x) = a(x^-1). In bit-reversed odd-root order, inversion
          // sends frequency k to n-1-k. No inverse/forward NTT is needed.
          for (size_t k = 0; k < n; ++k)
            star[k] = d[n - 1 - k];
        } else {
          star[0] = d[0];
          for (size_t k = 1; k < n; ++k)
            star[k] = f.negf(d[n - k]);
          plan->transform(star, false);
        }
        spectra.push_back(std::move(star));
      } else {
        spectra.emplace_back();
      }
    }
    ec.gen = [this](auto &a, auto &b, size_t &ci) {
      (void)a;
      for (size_t i = 0; i < groups * n; ++i) {
        b.push_back(f.zero());
        ++ci;
      }
    };
    ec.accumulate = [this, plan, spectra = std::move(spectra)](
                        E *A, const E *lambda, size_t base) {
      auto add = [&](size_t p, size_t k, E v) {
        for (auto [i, a] : polys[p][k])
          f.add(A[i - npub], f.mulf(a, v));
      };
      // Share forward transforms across terms in the same equation, and
      // inverse transforms across products using the same witness operand.
      std::vector<std::vector<E>> freq(groups), weights(polys.size());
      for (size_t j = 0; j < terms.size(); ++j) {
        const auto &t = terms[j];
        if (spectra[j].empty()) {
          for (size_t k = 0; k < n; ++k)
            add(t.poly, k, f.mulf(t.sign, lambda[base + t.row * n + k]));
          continue;
        }
        if (freq[t.row].empty()) {
          freq[t.row].assign(lambda + base + t.row * n,
                             lambda + base + (t.row + 1) * n);
          plan->transform(freq[t.row], false);
        }
        auto &v = weights[t.poly];
        if (v.empty())
          v.assign(n, f.zero());
        for (size_t k = 0; k < n; ++k)
          f.add(v[k], f.mulf(t.sign, f.mulf(freq[t.row][k], spectra[j][k])));
      }
      for (size_t p = 0; p < weights.size(); ++p)
        if (!weights[p].empty()) {
          plan->transform(weights[p], true);
          for (size_t k = 0; k < n; ++k)
            add(p, k, weights[p][k]);
        }
    };
    return ec;
  }
};

// The digest of the MAC rows followed by the signature rows, as prove and
// verify below build them. Absorbed with the statement.
template <class Hash, class M, class S, class W>
auto digest(const M &mac, const S &sig, const W &pub) {
  using F = std::remove_cv_t<std::remove_reference_t<decltype(sig.f)>>;
  const auto t = sig.tag(pub);
  return ZkCommon<F>::template hash_of_constraints<Hash>(mac.tag(&t), false,
                                                         "native-linear");
}
template <class M, class S, class P, class Z, class W, class T>
bool prove(M &mac, S &sig, P &p, Z &z, W &w, T &t) {
  auto ec = sig.extra(w);
  return linear_mac::prove(mac, p, z, w, t, &ec);
}
template <class M, class S, class V, class Z, class W, class T>
bool verify(M &mac, S &sig, V &v, Z &z, W &w, T &t) {
  auto ec = sig.extra(w);
  return linear_mac::verify(mac, v, z, w, t, &ec);
}
} // namespace proofs::native_linear
#endif
