// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the compiled plan as a Lean data file.
//
// export_lean_plan(cs, meta) writes one module of the schema
// formal/GordieHowe/Language/Export.lean (schemaVersion 3): a single
// `def plan : GordieHowe.RealizedProgram.Export.Plan` in the namespace
// GordieHowe.Generated.<lean_name>.Plan. Every value is read from the
// compiled system: the nodes and phases, each domain's compilation
// (DomainPlan: the Ligero tableau LigeroParam laid out, the packing tree,
// the circuit, the inputs, the batches), the range requests with their
// realizations and tables, the lowerings' records (PlanRecords: the MACs,
// the assert_mod gadgets, the selections, the filtered permutations of
// byte windows, the charged degrees) and the late messages. Each domain
// also records the bound its no-wrap conditions use (characteristicFloor,
// the characteristic itself)
// and, without relative packing, where its Bit cells' Boolean checks are
// placed. A characteristic is written in full, of any width (F_p256). The exporter is the correspondence point between the C++
// and the Lean instance files, so it computes nothing the C++ does not.
//
// Conventions of the output:
//   - lists are in C++ order: domains in declaration order, requests per
//     domain in declaration order, challenges in node-id order, messages
//     in message order;
//   - names are the C++ node and constraint names;
//   - phases are the C++'s (0 committed, 1..phases the challenge rounds);
//   - a coordinate range is a node's circuit inputs (input 0 is the
//     constant one): its first input and length, its cell type, its storage
//     (`committed`, `pad`, `public`, `message` for a late value's masked
//     message, `view` for a bit view a circuit reads) and phase;
//   - an expression's terms are `.node x`, `.sum x` (the sum operator
//     on x) or `.op "o(...(x))"` for any other operator chain, its
//     operators' names innermost first;
//   - a packing edge's mode is `squaringChain` or `subfieldMasks`
//     (stage.h);
//   - a message's `subfieldMessage` says that it lies in a proper subfield
//     (its masking space is not the field), which the verifier's decoding
//     enforces, and `padSpace` names the packing-tree node of its pad as a
//     packing edge's `child` does (`GF(2^16)`, `GF(2^32)`, `bit`,
//     `GF(p^1)`), or the field's own name for a pad committed in K.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_EXPORT_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_EXPORT_H_

#include <algorithm>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <filesystem>
#include <fstream>
#include <map>
#include <memory>
#include <optional>
#include <tuple>
#include <stdexcept>
#include <string>
#include <type_traits>
#include <utility>
#include <vector>

#include "algebra/fp_goldilocks.h"
#include "gordiehowe/core.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/compiler/range.h"
#include "gordiehowe/system.h"
#include "util/crypto.h"

namespace proofs::gordiehowe::compiler {

// The license header every exported Lean module opens with, before
// `module`.
inline constexpr char kLeanLicenseHeader[] =
    "-- Copyright 2026 Chad Sharp and Paul Grubbs\n"
    "-- SPDX-License-Identifier: Apache-2.0\n\n";

// The options every exported Lean module sets after its docstring: the
// elaborator's recursion depth for the long list literals of the data
// modules (the SHA-256 programs need 100000), and no heartbeat budget, for
// the elaborator or the kernel (the SHA3 32 KiB and post-quantum mDL
// programs, and the kernel checks of the proof modules, exceed the
// default). A check's time and memory are bounded by the build, not by
// heartbeats.
inline constexpr char kLeanModuleOptions[] =
    "set_option maxHeartbeats 0\n"
    "set_option maxRecDepth 100000\n\n";

// What the export records beside the compiled system: the configuration
// (kebab case, `falcon-emulated`) and profile (`wide`), the C++ commit of
// the binary, the bench run id and the message length in bytes. LEAN_NAME
// is the Lean configuration name without the root
// (`MLDSA44.Native.ROMParams`); empty, it is lean_config_name(config,
// profile). It names the modules only: the plan's contents and digest do
// not read it.
struct ExportMeta {
  std::string config, profile, cpp_commit, run_id;
  size_t msg_len = 0, ctx_len = 0;
  std::string lean_name;
};

namespace plan_export_internal {
// falcon-emulated -> FalconEmulated.
inline std::string camel(const std::string &kebab) {
  std::string s;
  bool up = true;
  for (char c : kebab) {
    if (c == '-' || c == '_' || c == ' ') {
      up = true;
      continue;
    }
    s += up && c >= 'a' && c <= 'z' ? char(c - 'a' + 'A') : c;
    up = false;
  }
  return s;
}
}  // namespace plan_export_internal

// The Lean parameter set of PROFILE: ROMParams for the classical profiles
// (narrow, narrow-fp128), QROMParams for the post-quantum one (wide), and
// <Profile>Params for a test's own profile (`test`: TestParams).
inline std::string lean_param_set(const std::string &profile) {
  if (profile == "narrow" || profile == "narrow-fp128") return "ROMParams";
  if (profile == "wide") return "QROMParams";
  return plan_export_internal::camel(profile) + "Params";
}

namespace plan_export_internal {
// A message length as a name component: 1KiB for 1024 bytes, 503B
// otherwise.
inline std::string size_name(const std::string &bytes) {
  const unsigned long n = std::stoul(bytes);
  return n % 1024 == 0 ? std::to_string(n / 1024) + "KiB"
                       : std::to_string(n) + "B";
}
// The hash comparisons' size label: <n>B a message length, <n> a count of
// UNIT (Blocks, Perms).
inline std::string hash_size_name(const std::string &label,
                                  const std::string &unit) {
  return label.back() == 'B' ? size_name(label.substr(0, label.size() - 1))
                             : label + unit;
}
inline bool starts_with(const std::string &s, const std::string &p) {
  return s.compare(0, p.size(), p) == 0;
}
}  // namespace plan_export_internal

// The Lean configuration name of CONFIG at PROFILE, without the root:
// <application>[.<program>].<parameter set> (lean_param_set). The
// configurations the Lean names by a fixed application (MLDSA44.Native,
// Falcon512.Ring.Carrier, MDL.ECDSA, Composite, ...) take it as they are;
// the families with several exports insert the part that tells them apart
// before the parameter set:
//   pq-mdoc-<arm>-<n>            MDL.MLDSA44.Attrs<n> (goldilocks),
//                                MDL.MLDSA44Fq.Attrs<n> (fq)
//   rsa-[fp128_]<key>            RSA2048.<Goldilocks2|Fp128>.Msg<size>, with
//                                .<Variant>T<t>M<m> outside the bench's
//                                auto t9 m2 (Goldilocks2) and auto t11 m3
//                                (Fp128)
//   sha256-<mode>-<n|nB>         SHA256.<Mode><n>Blocks, SHA256.<Mode><size>
//   sha3-256-<mode>-<n|nB>       SHA3.<Mode><n>Perms, SHA3.<Mode><size>
//   keccak-perms-<mode>-<n>      KeccakPerms.<Mode><n>
// (<size> 1KiB or 503B). Any other configuration is <Config> in camel case
// (a test's `toy` is Toy.QROMParams).
inline std::string lean_config_name(const std::string &config,
                                    const std::string &profile) {
  using plan_export_internal::camel;
  using plan_export_internal::hash_size_name;
  using plan_export_internal::size_name;
  using plan_export_internal::starts_with;
  static const std::map<std::string, std::string> kFixed = {
      {"mldsa-emulated", "MLDSA44.Emulated"},
      {"mldsa-native", "MLDSA44.Native"},
      {"mldsa-ring-native", "MLDSA44.Ring.Native"},
      {"mldsa-ring-carrier", "MLDSA44.Ring.Carrier"},
      {"falcon-emulated", "Falcon512.Emulated"},
      {"falcon-native", "Falcon512.Native"},
      {"falcon-ring-native", "Falcon512.Ring.Native"},
      {"falcon-ring-carrier", "Falcon512.Ring.Carrier"},
      {"mdoc", "MDL.ECDSA"},
      {"composite", "Composite"},
  };
  const std::string set = "." + lean_param_set(profile);
  const auto it = kFixed.find(config);
  if (it != kFixed.end()) return it->second + set;
  // The parts of CONFIG after PREFIX, split at '-'.
  auto parts = [&](const std::string &prefix) {
    std::vector<std::string> out;
    std::string cur;
    for (char c : config.substr(prefix.size())) {
      if (c == '-') {
        out.push_back(cur);
        cur.clear();
      } else {
        cur += c;
      }
    }
    out.push_back(cur);
    return out;
  };
  auto bad = [&]() -> std::string {
    throw std::runtime_error("plan export: no Lean name for " + config);
  };
  if (starts_with(config, "pq-mdoc-")) {
    const auto p = parts("pq-mdoc-");
    if (p.size() != 2 || (p[0] != "goldilocks" && p[0] != "fq")) return bad();
    return std::string(p[0] == "fq" ? "MDL.MLDSA44Fq" : "MDL.MLDSA44") +
           ".Attrs" + p[1] + set;
  }
  if (starts_with(config, "rsa-")) {
    // rsa_pkcs1_bench.cc's config_key: [fp128_]<variant>_t<t>[_m<m>]_
    // <bytes>_batched.
    std::string key = config.substr(4);
    const bool fp128 = starts_with(key, "fp128_");
    if (fp128) key = key.substr(6);
    std::vector<std::string> f;
    std::string cur;
    for (char c : key + "_") {
      if (c == '_') {
        f.push_back(cur);
        cur.clear();
      } else {
        cur += c;
      }
    }
    if (f.size() < 4 || f.size() > 5 || f.back() != "batched" || f[1].size() < 2 ||
        f[1][0] != 't')
      return bad();
    const std::string t = f[1].substr(1);
    const std::string m =
        f.size() == 5 && f[2].size() > 1 && f[2][0] == 'm' ? f[2].substr(1)
                                                           : "1";
    if (f.size() == 5 && m == "1") return bad();
    const std::string bytes = f[f.size() - 2];
    std::string name = std::string("RSA2048.") +
                       (fp128 ? "Fp128" : "Goldilocks2") + ".Msg" +
                       size_name(bytes);
    const bool bench = f[0] == "auto" &&
                       (fp128 ? t == "11" && m == "3" : t == "9" && m == "2");
    if (!bench) name += "." + camel(f[0]) + "T" + t + "M" + m;
    return name + set;
  }
  if (starts_with(config, "sha256-")) {
    const auto p = parts("sha256-");
    if (p.size() != 2) return bad();
    return "SHA256." + camel(p[0]) + hash_size_name(p[1], "Blocks") + set;
  }
  if (starts_with(config, "sha3-256-")) {
    const auto p = parts("sha3-256-");
    if (p.size() != 2) return bad();
    return "SHA3." + camel(p[0]) + hash_size_name(p[1], "Perms") + set;
  }
  if (starts_with(config, "keccak-perms-")) {
    const auto p = parts("keccak-perms-");
    if (p.size() != 2) return bad();
    return "KeccakPerms." + camel(p[0]) + p[1] + set;
  }
  return camel(config) + set;
}

// META's Lean configuration name: its lean_name, or lean_config_name's.
inline std::string lean_name(const ExportMeta &meta) {
  return meta.lean_name.empty() ? lean_config_name(meta.config, meta.profile)
                                : meta.lean_name;
}

// The module GordieHowe.Generated.<lean_name>.<LEAF> as a path relative to
// formal/, without `.lean`:
// GordieHowe/Generated/MLDSA44/Native/ROMParams/Plan. A dotted LEAF
// (`Valid.WellFormed`) is a module below LEAF's first component
// (GordieHowe/Generated/.../Valid/WellFormed).
inline std::string lean_module_path(const ExportMeta &meta,
                                    const std::string &leaf) {
  std::string l = lean_name(meta) + "." + leaf;
  std::replace(l.begin(), l.end(), '.', '/');
  return "GordieHowe/Generated/" + l;
}

// The module name GordieHowe.Generated.<lean_name>.<LEAF>.
inline std::string lean_module_name(const ExportMeta &meta,
                                    const std::string &leaf) {
  return "GordieHowe.Generated." + lean_name(meta) + "." + leaf;
}

// DIR/<module path>.lean of META's module LEAF (Plan, Program, or a proof
// module of plan_proofs.h), with its directories created. Two exports never
// share a module path: a file there already that is not META's
// configuration's export fails the export, and a rerun of the same export
// replaces its file. The file is META's export when its header holds one of
// TITLES, the modules' title lines for META's configuration; empty, the
// data modules' (`# GordieHowe plan data: <config>-<profile>` and
// `# GordieHowe realized program: <config>-<profile>`).
inline std::string lean_module_file(const std::string &dir,
                                    const ExportMeta &meta,
                                    const std::string &leaf,
                                    std::vector<std::string> titles = {}) {
  const std::filesystem::path p =
      std::filesystem::path(dir) / (lean_module_path(meta, leaf) + ".lean");
  std::filesystem::create_directories(p.parent_path());
  if (std::filesystem::exists(p)) {
    std::ifstream in(p, std::ios::binary);
    std::string head(4096, '\0');
    in.read(head.data(), std::streamsize(head.size()));
    head.resize(size_t(in.gcount()));
    const std::string own = meta.config + "-" + meta.profile;
    if (titles.empty())
      titles = {"# GordieHowe plan data: " + own,
                "# GordieHowe realized program: " + own};
    bool same = false;
    for (const std::string &t : titles)
      same = same || head.find("\n" + t + "\n") != std::string::npos;
    if (!same)
      throw std::runtime_error("plan export: " + p.string() +
                               " holds another configuration's export than " +
                               meta.config + "-" + meta.profile);
  }
  return p.string();
}

// DIR/<lean_plan_module>.lean, as lean_module_file.
inline std::string lean_plan_file(const std::string &dir,
                                  const ExportMeta &meta) {
  return lean_module_file(dir, meta, "Plan");
}

// DIR/<lean_program_module>.lean, as lean_module_file.
inline std::string lean_program_file(const std::string &dir,
                                     const ExportMeta &meta) {
  return lean_module_file(dir, meta, "Program");
}
// DIR/<lean_module_path(META, "Derivs")>.lean, the derivations' module, as
// lean_module_file.
inline std::string lean_derivs_file(const std::string &dir,
                                    const ExportMeta &meta) {
  return lean_module_file(dir, meta, "Derivs",
                          {"# GordieHowe derivations: " + meta.config + "-" +
                           meta.profile});
}

namespace plan_export_internal {

[[noreturn]] inline void export_fail(const std::string &msg) {
  throw std::runtime_error("plan export: " + msg);
}

// A Lean term: an atom, a structure instance or a list, rendered on one
// line when it fits, otherwise one field or element per line.
struct Term {
  enum Kind { kAtom, kObj, kList } kind = kAtom;
  std::string atom;
  std::vector<std::pair<std::string, Term>> fields;
  std::vector<Term> items;

  static Term a(std::string s) {
    Term t;
    t.atom = std::move(s);
    return t;
  }
  static Term obj() {
    Term t;
    t.kind = kObj;
    return t;
  }
  static Term list() {
    Term t;
    t.kind = kList;
    return t;
  }
  Term &f(const std::string &k, Term v) {
    fields.push_back({k, std::move(v)});
    return *this;
  }
  Term &f(const std::string &k, const std::string &atom) {
    return f(k, a(atom));
  }
  Term &push(Term v) {
    items.push_back(std::move(v));
    return *this;
  }

  std::string flat() const {
    switch (kind) {
      case kAtom:
        return atom;
      case kObj: {
        std::string s = "{ ";
        for (size_t i = 0; i < fields.size(); ++i)
          s += (i ? ", " : "") + fields[i].first + " := " +
               fields[i].second.flat();
        return s + " }";
      }
      default: {
        std::string s = "[";
        for (size_t i = 0; i < items.size(); ++i)
          s += (i ? ", " : "") + items[i].flat();
        return s + "]";
      }
    }
  }
  // Rendered at column COL.
  std::string render(size_t col) const {
    const std::string one = flat();
    if (kind == kAtom || col + one.size() <= 100) return one;
    const std::string pad(col, ' ');
    std::string s;
    if (kind == kObj) {
      s = "{ ";
      for (size_t i = 0; i < fields.size(); ++i) {
        if (i) s += ",\n" + pad + "  ";
        const std::string head = fields[i].first + " := ";
        s += head + fields[i].second.render(col + 2 + head.size());
      }
      return s + " }";
    }
    if (items.empty()) return "[]";
    s = "[";
    for (size_t i = 0; i < items.size(); ++i) {
      if (i) s += ",\n" + pad + " ";
      s += items[i].render(col + 1);
    }
    return s + "]";
  }
  // The special members are defined below, where Term is complete: a
  // vector of pairs holding Term is not instantiable inside Term (C++20's
  // constexpr std::vector).
  Term();
  Term(const Term &);
  Term(Term &&) noexcept;
  Term &operator=(const Term &);
  Term &operator=(Term &&) noexcept;
  ~Term();
};
inline Term::Term() = default;
inline Term::Term(const Term &) = default;
inline Term::Term(Term &&) noexcept = default;
inline Term &Term::operator=(const Term &) = default;
inline Term &Term::operator=(Term &&) noexcept = default;
inline Term::~Term() = default;

inline std::string str(const std::string &s) {
  std::string o = "\"";
  for (char c : s) {
    if (c == '"' || c == '\\') o += '\\';
    if (c == '\n') {
      o += "\\n";
      continue;
    }
    o += c;
  }
  return o + "\"";
}
inline std::string nat(Bound x) { return bound_str(x); }
inline std::string integer(SignedInt x) { return int_str(x); }
inline std::string boolean(bool b) { return b ? "true" : "false"; }
inline std::string hex(const uint8_t *b, size_t n) {
  std::string s;
  char x[3];
  for (size_t i = 0; i < n; ++i) {
    std::snprintf(x, sizeof(x), "%02x", b[i]);
    s += x;
  }
  return s;
}
template <class T, class Fn>
Term list_of(const std::vector<T> &v, Fn fn) {
  Term l = Term::list();
  for (const auto &x : v) l.push(fn(x));
  return l;
}

template <class H>
std::string hash_name() {
  if constexpr (std::is_same_v<H, SHA256>) {
    return "SHA-256";
  } else if constexpr (std::is_same_v<H, SHA384>) {
    return "SHA-384";
  } else {
    static_assert(sizeof(H) == 0, "plan export: an unnamed protocol hash");
    return "";
  }
}

// The defining polynomial of F over its prime field: nonzero exponents
// highest first and, when not all 1, their coefficients. In
// characteristic 2 the taps of x^w (mac_taps, from the field's
// arithmetic). An odd extension stored in a power basis (an Elt holding
// its d coordinates as `e`, or Fp64G2's re + im x): x is the element of
// coordinates (0, 1, 0, ...), checked to give the unit coordinates
// x^0..x^(d-1), and x^d = sum_i c_i x^i, read from the field's
// multiplication, gives the modulus x^d - sum_i c_i x^i.
// A field stored in a tower basis instead (coordinate a j + i holding
// u^i v^j, u of degree a over the prime field and v of degree b over u)
// has TOWER, innermost step first: each step's relation x^deg = sum of
// coefficient * (earlier variables and x)^exponents, read from x's powers
// in the field.
struct TowerStep {
  std::string name;
  size_t degree = 0;
  std::vector<std::pair<Bound, std::vector<size_t>>> relation;
};
struct Modulus {
  std::vector<size_t> exps;
  std::vector<Bound> coeffs;
  std::vector<TowerStep> tower;
};
template <class F, class = void>
struct has_coordinate_array : std::false_type {};
template <class F>
struct has_coordinate_array<F, std::void_t<decltype(std::declval<typename F::Elt>().e)>>
    : std::true_type {};
template <class F, class = void>
struct has_base_field : std::false_type {};
template <class F>
struct has_base_field<F, std::void_t<decltype(std::declval<const F &>().base_field())>>
    : std::true_type {};
template <class F>
Modulus modulus_of(const F &f, size_t degree) {
  Modulus m;
  if (degree == 1) return m;
  if constexpr (F::kCharacteristicTwo) {
    if (degree != F::kBits)
      export_fail("a binary field of degree " + std::to_string(degree) +
                  " and " + std::to_string(F::kBits) + " bits");
    const auto taps = ops::mac_taps(f);
    m.exps.push_back(degree);
    for (size_t i = taps.size(); i-- > 0;) m.exps.push_back(taps[i]);
    return m;
  } else if constexpr (!has_base_field<F>::value) {
    // A prime field stored without a base field (F_p256) has degree 1.
    export_fail("a field of degree " + std::to_string(degree) +
                " with no base field");
  } else {
    using Elt = typename F::Elt;
    const auto &b = f.base_field();
    // The element of coordinates C (scalars of the base field).
    auto make = [&](const std::vector<typename F::Scalar> &c) {
      Elt x{};
      if constexpr (has_coordinate_array<F>::value) {
        if (c.size() != x.e.size())
          export_fail("an odd extension of degree " + std::to_string(degree) +
                      " stores " + std::to_string(x.e.size()) +
                      " coordinates");
        for (size_t i = 0; i < c.size(); ++i) x.e[i] = c[i];
      } else if constexpr (std::is_same_v<F, Fp64G2>) {
        if (c.size() != 2) export_fail("Fp64G2 has degree 2");
        x.re = c[0];
        x.im = c[1];
      } else {
        export_fail("no power basis known for an odd extension field of "
                    "degree " + std::to_string(degree));
      }
      return x;
    };
    auto unit = [&](size_t i) {
      std::vector<typename F::Scalar> c(degree, b.zero());
      c[i] = b.one();
      return make(c);
    };
    const Elt x = unit(1);
    Elt pw = f.one();
    size_t inner = degree;  // the first power of x that is not a unit
    for (size_t i = 0; i < degree; ++i) {
      if (pw != unit(i)) {
        inner = i;
        break;
      }
      pw = f.mulf(pw, x);
    }
    const Bound p = field_characteristic(f);
    // Coordinate i of Y, as a prime-field integer.
    auto coord = [&](const Elt &y, size_t i) {
      std::vector<typename F::Scalar> c0(degree, b.zero());
      if constexpr (has_coordinate_array<F>::value) {
        c0[0] = y.e[i];
      } else if constexpr (std::is_same_v<F, Fp64G2>) {
        c0[0] = i == 0 ? y.re : y.im;
      }
      return nat_of(f, make(c0));
    };
    if (inner < degree) {
      // A tower: u = coordinate 1 of degree INNER, v = coordinate INNER
      // of degree OUTER, coordinate inner j + i = u^i v^j.
      const size_t a = inner;
      if (a < 2 || degree % a != 0)
        export_fail("an odd extension of degree " + std::to_string(degree) +
                    " is stored in no power or two-step tower basis");
      const size_t bdeg = degree / a;
      TowerStep su{"u", a, {}}, sv{"v", bdeg, {}};
      for (size_t i = degree; i-- > 0;) {
        const Bound c = coord(pw, i);
        if (c == 0) continue;
        if (i >= a)
          export_fail("u^" + std::to_string(a) + " leaves the span of u's "
                      "powers");
        su.relation.push_back({c, {i}});
      }
      const Elt v = unit(a);
      Elt vj = f.one();
      for (size_t j = 0; j < bdeg; ++j) {
        Elt t = vj;
        for (size_t i = 0; i < a; ++i) {
          if (t != unit(a * j + i))
            export_fail("coordinate " + std::to_string(a * j + i) +
                        " is not u^" + std::to_string(i) + " v^" +
                        std::to_string(j));
          t = f.mulf(t, x);
        }
        vj = f.mulf(vj, v);
      }
      for (size_t k = degree; k-- > 0;) {
        const Bound c = coord(vj, k);
        if (c != 0) sv.relation.push_back({c, {k % a, k / a}});
      }
      m.tower = {su, sv};
      return m;
    }
    // pw = x^d; its coordinates c_i, each read as a prime-field element.
    m.exps.push_back(degree);
    m.coeffs.push_back(1);
    for (size_t i = degree; i-- > 0;) {
      const Bound c = coord(pw, i);
      if (c == 0) continue;
      m.exps.push_back(i);
      m.coeffs.push_back(p - c);
    }
    return m;
  }
}

// The defining polynomial of F's designated subfield in characteristic 2
// (degree F::kSubFieldBits): the subfield's basis is the powers of
// g = beta(1) (checked), and g^D's coordinates in it give
// x^D + sum_i c_i x^i.
template <class F>
Modulus subfield_modulus_of(const F &f, size_t degree) {
  Modulus m;
  if constexpr (F::kCharacteristicTwo) {
    if (degree != F::kSubFieldBits) return m;
    const auto g = f.beta(1);
    auto pw = f.one();
    for (size_t i = 0; i < degree; ++i) {
      if (pw != f.beta(i))
        export_fail("the subfield of degree " + std::to_string(degree) +
                    " is not stored in the power basis of beta(1)");
      pw = f.mulf(pw, g);
    }
    uint8_t b[F::kSubFieldBytes];
    f.to_bytes_subfield(b, pw);
    m.exps.push_back(degree);
    for (size_t i = degree; i-- > 0;)
      if ((b[i / 8] >> (i % 8)) & 1) m.exps.push_back(i);
  }
  (void)f;
  (void)degree;
  return m;
}

// The characteristic of F in decimal, of any width: p - 1's bytes
// (subfield_to_bytes, little-endian) plus one, for a prime wider than a
// Bound (F_p256).
template <class F>
std::string characteristic_str(const F &f) {
  if constexpr (F::kCharacteristicTwo) {
    return "2";
  } else {
    if (!characteristic_wide(f)) return nat(field_characteristic(f));
    constexpr size_t kB = domain_subfield<F>::kBytes;
    uint8_t b[kB];
    subfield_to_bytes(f, b, f.mone());
    // Big-endian digits base 256 of p = (p - 1) + 1.
    std::vector<unsigned> d(b, b + kB);
    std::reverse(d.begin(), d.end());
    for (size_t i = d.size(); i-- > 0;) {
      if (++d[i] < 256) break;
      d[i] = 0;
      if (i == 0) d.insert(d.begin(), 1);
    }
    std::string out;
    for (;;) {
      bool zero = true;
      unsigned r = 0;
      for (unsigned &x : d) {
        const unsigned cur = r * 256 + x;
        x = cur / 10;
        r = cur % 10;
        zero = zero && x == 0;
      }
      out += char('0' + r);
      if (zero) break;
    }
    std::reverse(out.begin(), out.end());
    return out;
  }
}

inline Term field_spec(const std::string &name, const std::string &ch,
                       size_t degree, const Modulus &m) {
  Term t = Term::obj();
  t.f("name", str(name))
      .f("characteristic", ch)
      .f("degree", std::to_string(degree));
  if (!m.exps.empty())
    t.f("modulus", list_of(m.exps, [](size_t e) {
      return Term::a(std::to_string(e));
    }));
  if (!m.coeffs.empty())
    t.f("modulusCoeffs",
        list_of(m.coeffs, [](Bound c) { return Term::a(nat(c)); }));
  if (!m.tower.empty())
    t.f("tower", list_of(m.tower, [](const TowerStep &st) {
      return Term::obj()
          .f("name", str(st.name))
          .f("degree", std::to_string(st.degree))
          .f("relation",
             list_of(st.relation,
                     [](const std::pair<Bound, std::vector<size_t>> &r) {
                       std::string e = "[";
                       for (size_t i = 0; i < r.second.size(); ++i)
                         e += (i ? ", " : "") + std::to_string(r.second[i]);
                       return Term::a("(" + nat(r.first) + ", " + e + "])");
                     }));
    }));
  return t;
}

inline const char *space_type(Space s) {
  return s == Space::kField ? "Field" : s == Space::kSubfield ? "Subfield"
                                                              : "Bit";
}

// The exporter reads the domains' graphs through the compiler tier.
template <class S>
class Exporter : Lowering {
 public:
  using CS = BasicCompiledSystem<S>;
  Exporter(const CS &cs, const ExportMeta &meta) : cs_(cs), meta_(meta) {}

  std::string run() {
    const auto &N = cs_.nodes();
    // Domains first: the requests' tables index into the tables list.
    Term domains = Term::list();
    for (size_t d = 0; d < cs_.num_domains(); ++d)
      domains.push(domain(d));
    for (size_t d = 0; d < cs_.num_domains(); ++d) requests_of(d);

    Term plan = Term::obj();
    plan.f("schemaVersion", "3")
        .f("config", str(config()))
        .f("cppCommit", str(meta_.cpp_commit))
        .f("runId", str(meta_.run_id))
        .f("digest", str(hex(cs_.digest().data(), cs_.digest().size())))
        .f("msgLen", std::to_string(meta_.msg_len))
        .f("ctxLen", std::to_string(meta_.ctx_len))
        .f("hash", str(hash_name<typename S::Hash>()))
        .f("phases", std::to_string(cs_.phases()))
        .f("domains", domains)
        .f("requests", requests_)
        .f("bindings", bindings_)
        .f("tables", tables_)
        .f("macs", macs())
        .f("selections", selections())
        .f("modEqualities", mod_equalities())
        .f("gadgets", gadgets())
        .f("sampleInBalls", list_of(cs_.records().sample_in_balls,
                                    [&](const PlanRecords::SampleInBall &r) {
             // Its record permutation, by challenge.
             const PlanRecords::Permutation *pm = nullptr;
             for (const auto &x : cs_.records().permutations)
               if (x.challenge == r.challenge) pm = &x;
             if (pm == nullptr)
               export_fail("SampleInBall '" + r.name + "': no permutation");
             return Term::obj()
                 .f("name", str(r.name))
                 .f("domain", str(r.domain))
                 .f("tau", std::to_string(r.tau))
                 .f("records", std::to_string(std::max(pm->left, pm->right)))
                 .f("arity", std::to_string(pm->arity))
                 .f("constRecords", std::to_string(pm->const_records))
                 .f("challenge", str(r.challenge));
           }));
    if (!cs_.records().filtered_permutations.empty())
      plan.f("filteredPermutations", filtered_permutations());
    plan.f("challenges", challenges())
        .f("messages", list_of(cs_.messages(), [&](size_t x) {
             Term m = Term::obj();
             m.f("name", str(N[x].name))
                 .f("domain", str(N[x].domain < 0
                                      ? std::string()
                                      : cs_.domain(size_t(N[x].domain)).name))
                 .f("phase", std::to_string(cs_.phase(x)))
                 .f("size", std::to_string(N[x].n))
                 .f("bytes", std::to_string(cs_.message_bytes(x)))
                 .f("maskingSpace", str(space_type(cs_.message_space(x))))
                 .f("subfieldMessage",
                    boolean(cs_.message_space(x) != Space::kField))
                 .f("padSpace", str(pad_node(x)));
             return m;
           }));

    const std::string ns = lean_module_name(meta_, "Plan");
    std::string o;
    o += kLeanLicenseHeader;
    o += "module\n\npublic import GordieHowe.Language.Export\n\n";
    o += "@[expose] public section\n\n";
    o += "/-!\n# GordieHowe plan data: " + config() + "\n\n";
    o += "Generated by `lib/gordiehowe/compiler/plan_export.h` from the "
         "compiled system; do not edit.\n\n";
    o += "- configuration: `" + config() + "`, system `" + cs_.label() +
         "`, compile profile `" + cs_.profile_name() + " v" +
         std::to_string(cs_.profile_version()) + "`\n";
    o += "- C++ commit: `" + meta_.cpp_commit + "`\n";
    o += "- bench run: `" + meta_.run_id + "`\n";
    o += "- system digest: `" + hex(cs_.digest().data(), cs_.digest().size()) +
         "`\n";
    o += "- circuit ids:";
    for (size_t d = 0; d < cs_.num_domains(); ++d)
      o += std::string(d ? "," : "") + " " + cs_.domain(d).name + " `" +
           hex(cs_.compiled_domain(d).circuit_id(), S::Hash::kDigestSize) +
           "`";
    o += "\n\nCoordinate ranges are circuit inputs (input 0 is the constant "
         "one); phases are the C++'s.";
    if (!cs_.records().sample_in_balls.empty())
      o += " A SampleInBall record (c_0, c_1, c_2) is packed as "
           "c_0 + kappa c_1 + kappa^2 c_2 with kappa the fixed public "
           "constant `selection_kappa` (an injective packing for subfield "
           "components; no challenge powers), and the permutation's grand "
           "products are over `delta - pack(record)`.";
    o += "\n-/\n\n";
    o += kLeanModuleOptions;
    o += "namespace " + ns + "\n\n";
    o += "/-- The compiled plan of `" + config() + "`. -/\n";
    o += "def plan : GordieHowe.RealizedProgram.Export.Plan :=\n  ";
    o += plan.render(2) + "\n\nend " + ns + "\n";
    return o;
  }

 private:
  std::string config() const { return meta_.config + "-" + meta_.profile; }

  // A packing-tree node of degree D of domain DM: the field's own name for
  // K, `bit` for GF(2), GF(2^D) or GF(p^D) otherwise.
  static std::string node_name(const DomainBase<S> &dm, const DomainPlan &p,
                               size_t D, bool char2) {
    if (D == p.field_degree) return dm.field_name();
    if (char2 && D == 1) return "bit";
    return std::string(char2 ? "GF(2^" : "GF(p^") + std::to_string(D) + ")";
  }

  // The packing-tree node that holds the pad of message X, named as the
  // packing edges name it: the node of the pad's space (GF(2) for the
  // prime space in characteristic 2, the masked value's subfield for the
  // subfield space), or K when the domain commits the pad unpacked.
  // A message of a field no domain commits (the odd/odd MAC's tag) has its
  // pad uniform in the field, GF(2^w).
  std::string pad_node(size_t x) const {
    const Node &n = cs_.nodes().at(x);
    if (n.domain < 0)
      return S::dispatch(n.field, [](auto tag) {
        using F = typename decltype(tag)::type;
        if constexpr (F::kCharacteristicTwo) {
          return "GF(2^" + std::to_string(F::kBits) + ")";
        } else {
          export_fail("a message of an odd field no domain commits");
          return std::string();
        }
      });
    const DomainBase<S> &dm = cs_.domain(size_t(n.domain));
    const DomainPlan p = cs_.compiled_domain(size_t(n.domain)).plan();
    const Space sp = cs_.message_space(x);
    const uint16_t dg = cs_.message_degree(x);
    return S::dispatch(dm.field_id, [&](auto tag) {
      using F = typename decltype(tag)::type;
      const size_t D = sp == Space::kField    ? p.field_degree
                       : sp == Space::kPrime ? 1
                                             : subfield_degree<F>(dg);
      bool node = false;
      for (const auto &t : p.tree) node = node || t.degree == D;
      return node_name(dm, p, node ? D : p.field_degree,
                       F::kCharacteristicTwo);
    });
  }

  Term domain(size_t di) {
    const DomainBase<S> &dm = cs_.domain(di);
    const DomainPlan p = cs_.compiled_domain(di).plan();
    const auto &N = cs_.nodes();
    Term out = Term::obj();
    S::dispatch(dm.field_id, [&](auto tag) {
      using F = typename decltype(tag)::type;
      const F &f = *static_cast<const F *>(dm.fobj);
      const bool char2 = F::kCharacteristicTwo;
      const std::string ch = characteristic_str(f);
      const Modulus mod = modulus_of(f, p.field_degree);
      // The subfields: the declared nodes of the packing tree, and the
      // masking subfield S0 that maskingSubfield names, also when no value
      // is declared in it (a domain of bits only) and when it is no node of
      // the tree (bits packed straight into the field, masked in S0).
      Term subs = Term::list();
      bool s0_listed = p.s0 == p.field_degree;
      for (const auto &t : p.tree)
        if (t.declared || t.degree == p.s0) {
          subs.push(field_spec(node_name(dm, p, t.degree, char2), ch,
                               t.degree, subfield_modulus_of(f, t.degree)));
          s0_listed = s0_listed || t.degree == p.s0;
        }
      if (!s0_listed)
        subs.push(field_spec(node_name(dm, p, p.s0, char2), ch, p.s0,
                             subfield_modulus_of(f, p.s0)));
      Term lig = Term::obj();
      lig.f("rate", std::to_string(p.rate))
          .f("blockEnc", std::to_string(p.block_enc))
          .f("N", std::to_string(p.N))
          .f("k", std::to_string(p.k))
          .f("t", std::to_string(p.t))
          .f("r", std::to_string(p.r))
          .f("nrow", std::to_string(p.nrow))
          .f("masking", !p.list_radius ? ".uniqueDecoding"
                        : p.split      ? ".split"
                                       : ".listRadius");
      // The low-degree test's repetitions, written only when more than one
      // (schema 3; absent means 1).
      if (p.ldt_reps > 1) lig.f("ldtReps", std::to_string(p.ldt_reps));
      Term packing = list_of(p.tree, [&](const DomainPlan::TreeNode &t) {
        Term e = Term::obj();
        e.f("child", str(node_name(dm, p, t.degree, char2)))
            .f("parent", str(node_name(dm, p, t.parent_degree, char2)))
            .f("mode", t.squaring_chain ? ".squaringChain" : ".subfieldMasks")
            .f("degree", std::to_string(t.parent_degree / t.degree))
            .f("measurements", std::to_string(t.revealed))
            .f("masks", std::to_string(t.masks));
        if (t.chain_cells) e.f("chainCells", std::to_string(t.chain_cells));
        e.f("childDegree", std::to_string(t.degree))
            .f("parentDegree", std::to_string(t.parent_degree))
            .f("declared", t.declared ? "true" : "false")
            .f("routedRows", std::to_string(t.routed));
        return e;
      });
      Term coords = list_of(p.inputs, [&](const DomainPlan::Input &in) {
        const Node &n = N.at(in.id);
        using In = DomainPlan::Input;
        std::string cell, storage;
        if (n.kind == Kind::kPad) {
          // A pad of a declared subfield is named as a cell of that
          // subfield (Subfield<GF<d>>).
          cell = n.pad_degree != 0 &&
                         dm.resolve(n.pad_space) == Space::kSubfield
                     ? type_name(Type{Base::kSubfield, n.pad_degree})
                     : std::string(space_type(dm.resolve(n.pad_space)));
          storage = "pad";
        } else {
          cell = type_name(n.type);
          storage = in.storage == In::kPublic    ? "public"
                    : in.storage == In::kMessage ? "message"
                    : in.storage == In::kView    ? "view"
                                                 : "committed";
        }
        Term c = Term::obj();
        c.f("name", str(n.name))
            .f("offset", std::to_string(in.at))
            .f("length", std::to_string(in.n))
            .f("cellType", str(cell))
            .f("storage", str(storage));
        const size_t ph = cs_.phase(in.id);
        if (ph != 0) c.f("phase", std::to_string(ph));
        return c;
      });
      // A domain without GKR has no circuit: circuits := [].
      Term circuits = Term::list();
      if (p.gkr)
        circuits.push(Term::obj()
                          .f("name", str(dm.name))
                          .f("layers", std::to_string(p.layers))
                          .f("wires", std::to_string(p.wires))
                          .f("quadTerms", std::to_string(p.quad_terms)));
      Term batches = list_of(p.batches, [&](const DomainPlan::Batch &b) {
        Term t = Term::obj();
        t.f("name", str(b.name))
            .f("operandField",
               str(b.bit_operands ? std::string(char2 ? "bit" : "GF(p^1)")
                                  : node_name(dm, p, b.table_degree, char2)))
            .f("arity", std::to_string(b.arity))
            .f("degree", std::to_string(b.degree))
            .f("instances", std::to_string(b.instances))
            .f("width", std::to_string(b.width))
            .f("rounds", std::to_string(b.rounds))
            .f("pads", std::to_string(b.pads));
        if (b.parts.size() > 1) t.f("mergeGroup", "some " + str(b.name));
        if (!b.calls.empty())
          t.f("calls", list_of(b.calls, [&](const std::pair<size_t, size_t> &c) {
            return Term::a("(" + str(N.at(c.first).name) + ", " +
                           std::to_string(c.second) + ")");
          }));
        return t;
      });
      out.f("name", str(dm.name))
          .f("field", field_spec(dm.field_name(), ch, p.field_degree, mod))
          .f("subfields", subs)
          .f("maskingSubfield", str(node_name(dm, p, p.s0, char2)))
          .f("prime", str(space_name(dm.prime)))
          .f("ligero", lig)
          .f("packing", packing)
          .f("coords", coords)
          .f("inputs", std::to_string(p.ninputs))
          .f("publicInputs", std::to_string(p.npub))
          .f("circuits", circuits)
          .f("circuitId", str(hex(p.circuit_id.data(), p.circuit_id.size())))
          .f("affineRows",
             list_of(p.affine_rows,
                     [](const std::pair<std::string, size_t> &r) {
                       return Term::a("(" + str(r.first) + ", " +
                                      std::to_string(r.second) + ")");
                     }))
          .f("quadTriples", std::to_string(p.quad_triples))
          .f("batches", batches)
          .f("streamPoints",
             list_of(p.stream_points, [](const DomainPlan::StreamPoint &x) {
               return Term::obj()
                   .f("name", str(x.name))
                   .f("rows", std::to_string(x.rows))
                   .f("streamBytes", std::to_string(x.bytes));
             }))
          .f("characteristicFloor", nat(field_characteristic(f)));
      // Each predicate's placement target (merged groups once).
      if (!p.placements.empty())
        out.f("placements",
              list_of(p.placements, [&](const DomainPlan::Placed &x) {
                const char *t = x.where == Placement::kAffine ? ".affine"
                                : x.where == Placement::kQuadratic
                                    ? ".quadratic"
                                : x.where == Placement::kBatch ? ".batch"
                                                               : ".circuit";
                Term e = Term::obj();
                e.f("name", str(x.name)).f("target", t);
                if (x.predicates > 1)
                  e.f("predicates", std::to_string(x.predicates));
                e.f("instances", std::to_string(x.instances));
                if (!x.batch.empty()) e.f("batch", str(x.batch));
                return e;
              }));
      if (!p.bit_checks.empty())
        out.f("bitChecks",
              list_of(p.bit_checks, [&](const DomainPlan::BitCheck &c) {
                return Term::obj()
                    .f("node", str(N.at(c.id).name))
                    .f("cells", std::to_string(c.cells))
                    .f("placement", c.in_circuit ? ".circuit" : ".triple");
              }));
      // The domain's tables, in the range lowering's order.
      if constexpr (!F::kCharacteristicTwo) {
        const auto *fd = dynamic_cast<const Domain<F> *>(&dm);
        if (fd == nullptr) export_fail("domain " + dm.name + " is untyped");
        // A group's index within the domain's lookup is its position in
        // range_tables() (the lowering's order: tables, then their groups).
        size_t lookup_group = 0;
        for (const auto &t : fd->range_tables()) {
          table_index_.emplace(std::make_tuple(dm.name, t.table, t.group),
                               std::make_pair(tables_.items.size(),
                                              lookup_group));
          Term tb = Term::obj();
          tb.f("domain", str(dm.name))
              .f("size", nat(t.table))
              .f("sdyn", nat(t.s_dyn))
              .f("staticNeedles", std::to_string(t.static_needles))
              .f("lateNeedles", std::to_string(t.dynamic_needles))
              .f("challenge", str(N.at(t.alpha).name))
              .f("name", str(t.name));
          if (lookup_group != 0) tb.f("group", std::to_string(lookup_group));
          ++lookup_group;
          tb.f("capacity", std::to_string(t.capacity));
          if (t.merged) tb.f("histogram", ".lateOnly");
          tables_.push(tb);
        }
      }
    });
    return out;
  }

  // Domain DI's range requests and the bindings their digits make.
  void requests_of(size_t di) {
    const DomainBase<S> &dm = cs_.domain(di);
    S::dispatch(dm.field_id, [&](auto tag) {
      using F = typename decltype(tag)::type;
      if constexpr (!F::kCharacteristicTwo) {
        const auto *fd = dynamic_cast<const Domain<F> *>(&dm);
        if (fd == nullptr) export_fail("domain " + dm.name + " is untyped");
        for (const auto &r : fd->requests()) request(*fd, r);
      }
    });
  }

  template <class F>
  void request(const Domain<F> &d, const RangeRequest<F> &r) {
    const auto &N = cs_.nodes();
    const F &f = d.field();
    // The bound the range lowering compares integers with.
    const Bound p = field_characteristic(f);
    const bool prime_field = d.prime == Space::kField;
    if (!r.lowered) export_fail("range request '" + r.name + "' is not lowered");
    size_t ph = 0;
    for (size_t id : r.v.deps()) ph = std::max(ph, cs_.phase(id));
    const auto aff =
        range_internal::plan_affine(f, p, prime_field, graph(d), r.v);
    if (!aff.error.empty())
      export_fail("range request '" + r.name + "': " + aff.error);
    const Term expr = affine(aff, d.name);
    const auto &consts = aff.consts;
    bool uniform = true;
    for (size_t j = 1; j < consts.size(); ++j)
      uniform = uniform && consts[j] == consts[0];

    const RangeRealization &R = r.realization;
    Term rz = Term::obj();
    const char *kind = nullptr;
    switch (R.kind) {
      case RealizationKind::kDirect:
        kind = R.late ? ".directLate" : ".direct";
        break;
      case RealizationKind::kDigits:
        kind = ".digits";
        break;
      case RealizationKind::kTwoSided:
        kind = ".twoSided";
        break;
      case RealizationKind::kImplied:
        kind = ".implied";
        break;
      case RealizationKind::kComplement:
        kind = ".complement";
        break;
      default:
        export_fail("range request '" + r.name + "' is realized " +
                    realization_name(R.kind) +
                    ", which schema version 1 has no kind for");
    }
    rz.f("kind", kind);
    if (R.kind != RealizationKind::kImplied) {
      auto it = table_index_.find({d.name, R.table, R.group});
      if (it == table_index_.end())
        export_fail("range request '" + r.name + "': no table " +
                    bound_str(R.table) + " group " + std::to_string(R.group) +
                    " in domain " + d.name);
      if (it->second.first != 0)
        rz.f("table", std::to_string(it->second.first));
      if (it->second.second != 0)
        rz.f("group", std::to_string(it->second.second));
    }
    if (R.k) rz.f("limbs", std::to_string(R.k));
    if (R.kind == RealizationKind::kImplied ||
        R.kind == RealizationKind::kComplement) {
      if (R.lo != 0) rz.f("intervalLo", integer(R.lo));
      if (R.hi != 0) rz.f("intervalHi", integer(R.hi));
    }
    rz.f("bound", nat(R.established))
        .f("staticNeedles", std::to_string(R.late ? 0 : R.needles))
        .f("lateNeedles", std::to_string(R.late ? R.needles : 0));

    requests_.push(Term::obj()
                       .f("name", str(r.name))
                       .f("domain", str(d.name))
                       .f("dim", std::to_string(r.v.n))
                       .f("expr", expr)
                       .f("honest", nat(r.n))
                       .f("max", nat(r.m))
                       .f("phase", std::to_string(ph))
                       .f("realization", rz));

    if (R.bound) {
      if (R.bound_id == SIZE_MAX)
        export_fail("range request '" + r.name + "' binds no recorded node");
      Term b = Term::obj();
      b.f("value", str(N.at(R.bound_id).name)).f("request", str(r.name));
      if (R.bound_offset) {
        if (!uniform)
          export_fail("range request '" + r.name + "' binds x + c with "
                      "per-coordinate offsets");
        b.f("kind", ".offset")
            .f("offset", integer(consts.empty() ? 0 : consts[0]));
      } else {
        b.f("kind", ".digits");
      }
      bindings_.push(b);
    }
  }

  // An affine expression as an IntAffine.
  // Also collects the bounds of its operator terms (op_bounds_).
  Term affine(const PlanRecords::Affine &a, const std::string &domain) const {
    for (size_t i = 0; i < a.terms.size(); ++i)
      if (a.terms[i].first == 'o' && i < a.op_bounds.size() &&
          !a.op_bounds[i].empty())
        op_bounds_.emplace(a.terms[i].second,
                           std::make_pair(domain, a.op_bounds[i]));
    Term terms = Term::list(), coeffs = Term::list();
    for (size_t i = 0; i < a.terms.size(); ++i) {
      const char *k = a.terms[i].first == 'n'   ? ".node "
                      : a.terms[i].first == 's' ? ".sum "
                                                : ".op ";
      terms.push(Term::a(k + str(a.terms[i].second)));
      coeffs.push(Term::a(integer(a.coeffs[i])));
    }
    bool uniform = true;
    for (size_t j = 1; j < a.consts.size(); ++j)
      uniform = uniform && a.consts[j] == a.consts[0];
    Term expr = Term::obj();
    expr.f("terms", terms).f("coeffs", coeffs);
    if (uniform) {
      expr.f("const", integer(a.consts.empty() ? 0 : a.consts[0]));
    } else {
      expr.f("const", "0").f("coordConsts", list_of(a.consts, [](SignedInt c) {
        return Term::a(integer(c));
      }));
    }
    return expr;
  }

  // The gadget of assert_mod NAME (its grouped form, if any) and its
  // quotient's gadget (the grouped form's recorded final quotient).
  const PlanRecords::Mod *grouped_of(const std::string &name) const {
    for (const auto &m : cs_.records().mods)
      if (m.name == name && m.form == PlanRecords::Mod::kGrouped) return &m;
    return nullptr;
  }
  const PlanRecords::Mod *quotient_of(const std::string &name) const {
    const PlanRecords::Mod *g = grouped_of(name);
    const std::string qn = g ? g->final_quotient : name;
    for (const auto &m : cs_.records().mods)
      if (m.name == qn && m.form != PlanRecords::Mod::kGrouped) return &m;
    return nullptr;
  }

  // The assert_mod equalities: the expression, its interval and the
  // quotient's form (the grouped form's final quotient).
  // The integer equalities (assert_int_equal) are the program's mod_0
  // (plan_program.h), not entries here.
  Term mod_equalities() const {
    std::vector<PlanRecords::ModEq> eqs;
    for (const auto &e : cs_.records().mod_equalities)
      if (!e.integer) eqs.push_back(e);
    return list_of(eqs, [&](const PlanRecords::ModEq &e) {
      if (!e.expr.error.empty())
        export_fail("assert_mod '" + e.name + "': " + e.expr.error);
      const PlanRecords::Mod *q = quotient_of(e.name);
      if (q == nullptr) export_fail("assert_mod '" + e.name + "': no quotient");
      Term t = Term::obj();
      t.f("name", str(e.name))
          .f("domain", str(e.domain))
          .f("modulus", nat(e.m))
          .f("expr", affine(e.expr, e.domain))
          .f("dim", std::to_string(e.expr.n));
      switch (q->form) {
        case PlanRecords::Mod::kField:
          t.f("quotient", ".fieldEquality");
          break;
        case PlanRecords::Mod::kBitQuotient:
          t.f("quotient", ".bit");
          break;
        case PlanRecords::Mod::kConstant:
          t.f("quotient", ".constant");
          break;
        case PlanRecords::Mod::kOneDigit:
          // One digit, derived from the two sides.
          t.f("quotient", ".digits")
              .f("digits", "1")
              .f("base", nat(q->qmax + 1))
              .f("topDerived", "true");
          break;
        default:
          t.f("quotient", ".digits")
              .f("digits", std::to_string(q->k))
              .f("base", nat(q->radix));
          // The readable form derives its top digit; the committed-digit
          // form commits every digit.
          if (q->form == PlanRecords::Mod::kDigits) t.f("topDerived", "true");
      }
      if (e.has_interval) {
        if (e.lo != 0) t.f("intervalLo", integer(e.lo));
        if (e.hi != 0) t.f("intervalHi", integer(e.hi));
      }
      return t;
    });
  }

  // The gadgets' and certify conditions' records, then each bounded
  // operator an expression reads (kind op-bound, named as its Term.op),
  // then each public computation (kind public-compute: cached once per
  // statement, or per message).
  Term gadgets() const {
    auto one = [](const std::string &name, const std::string &kind,
                  const std::string &domain,
                  const std::vector<std::pair<std::string, SignedInt>> &ps) {
      return Term::obj()
          .f("name", str(name))
          .f("kind", str(kind))
          .f("domain", str(domain))
          .f("params", list_of(ps, [&kind](const std::pair<std::string, SignedInt> &x) {
               // A certify condition's sides are Bounds stored as their
               // bits (system_core.h's note): read back as nats, exactly.
               const bool side =
                   kind == "certify" && (x.first == "lhs" || x.first == "rhs");
               const std::string v =
                   side ? nat(static_cast<Bound>(x.second)) : integer(x.second);
               return Term::a("(" + str(x.first) + ", " + v + ")");
             }));
    };
    Term l = Term::list();
    for (const auto &g : cs_.records().gadgets)
      l.push(one(g.name, g.kind, g.domain, g.params));
    for (const auto &[name, b] : op_bounds_) {
      std::vector<std::pair<std::string, SignedInt>> ps;
      for (const auto &[k, v] : b.second) ps.push_back({k, SignedInt(v)});
      l.push(one(name, "op-bound", b.first, ps));
    }
    const auto &N = cs_.nodes();
    for (size_t id = 0; id < N.size(); ++id) {
      const Node &n = N[id];
      if (n.kind != Kind::kPublicCompute) continue;
      l.push(one(n.name, "public-compute", field_domain(n),
                 {{"cached", n.cached ? 1 : 0},
                  {"perMessage", n.cached ? 0 : 1},
                  {"n", SignedInt(n.n)},
                  {"phase", SignedInt(cs_.phase(id))}}));
    }
    return l;
  }

  // The domain whose field a public node lies in ("" when none).
  std::string field_domain(const Node &n) const {
    for (size_t d = 0; d < cs_.num_domains(); ++d)
      if (cs_.domain(d).field_id == n.field && cs_.domain(d).fobj == n.fobj)
        return cs_.domain(d).name;
    return "";
  }

  Term macs() const {
    const auto &rec = cs_.records();
    return list_of(rec.macs, [&](const PlanRecords::Mac &m) {
      // The tail: the assert_mod the MAC lowering recorded, its quotient's
      // form, digits and limb bounds.
      const PlanRecords::Mod *grouped = grouped_of(m.tail);
      const PlanRecords::Mod *q = quotient_of(m.tail);
      if (q == nullptr || q->form == PlanRecords::Mod::kField)
        export_fail("MAC '" + m.name + "': its tail '" + m.tail +
                    "' has no quotient");
      Term t = Term::obj();
      t.f("name", str(m.name))
          .f("tagDomain", str(m.tag_domain))
          .f("accDomain", str(m.acc_domain))
          .f("width", std::to_string(m.width))
          .f("nch", std::to_string(m.nch))
          .f("taps", list_of(m.taps, [](size_t x) {
               return Term::a(std::to_string(x));
             }))
          .f("convMax", std::to_string(m.conv_max))
          .f("accMax", nat(m.acc_max));
      Bound n_low = 0, n_high = 0;
      switch (q->form) {
        case PlanRecords::Mod::kConstant:
          t.f("tail", ".constant");
          break;
        case PlanRecords::Mod::kBitQuotient:
          t.f("tail", ".bit");
          n_high = 2;
          break;
        case PlanRecords::Mod::kOneDigit:
          t.f("tail", ".oneDigit");
          n_high = q->qmax + 1;
          break;
        default: {
          // acc = m low + m B high: the limb radix m B, as bits when a power
          // of two; low and high are the quotient's two digits.
          if (q->k != 2)
            export_fail("MAC '" + m.name + "': its tail quotient has " +
                        std::to_string(q->k) + " digits, not low and high");
          const Bound mb = bound_mul(q->m, q->radix);
          size_t e = 0;
          while ((Bound(1) << e) < mb) ++e;
          if ((Bound(1) << e) == mb)
            t.f("radixBits", std::to_string(e));
          else
            t.f("radix", nat(mb));
          t.f("tail", ".digits").f("tailDigits", std::to_string(q->k));
          n_low = q->radix;
          n_high = q->top;
        }
      }
      if (!m.members.empty())
        t.f("members", list_of(m.members, [](const std::string &x) {
          return Term::a(str(x));
        }));
      if (grouped) {
        // The groups as the MAC lowering declared them (chunks), the
        // groups' quotient digits and base and the bound on a group's sum
        // (the assert_mod grouping).
        if (m.groups.size() != grouped->groups)
          export_fail("MAC '" + m.name + "': " + std::to_string(m.groups.size()) +
                      " recorded groups, the tail has " +
                      std::to_string(grouped->groups));
        t.f("groups", std::to_string(grouped->groups))
            .f("groupChunks",
               list_of(m.groups, [](const PlanRecords::Mac::Group &g) {
                 return Term::a("(" + std::to_string(g.first) + ", " +
                                std::to_string(g.count) + ")");
               }))
            .f("quotientDigits", std::to_string(grouped->k))
            .f("quotientBase", nat(grouped->table))
            .f("groupBound", nat(grouped->group_bound));
      }
      t.f("nLow", nat(n_low))
          .f("nHigh", nat(n_high))
          .f("challenge", str(m.challenge));
      return t;
    });
  }

  Term filtered_permutations() const {
    using FP = PlanRecords::FilteredPermutation;
    return list_of(cs_.records().filtered_permutations, [&](const FP &r) {
      return Term::obj()
          .f("name", str(r.name))
          .f("domain", str(r.domain))
          .f("message", str(r.message))
          .f("messageLen", std::to_string(r.message_len))
          .f("windows", list_of(r.windows, [](const FP::Window &w) {
               return Term::obj()
                   .f("name", str(w.name))
                   .f("len", std::to_string(w.len))
                   .f("first", std::to_string(w.first))
                   .f("last", std::to_string(w.last));
             }))
          .f("offsetField", str(r.offset_field))
          .f("positionBits", std::to_string(r.position_bits))
          .f("messageRecords", std::to_string(r.message_records))
          .f("windowRecords", std::to_string(r.window_records))
          .f("challenge", str(r.challenge));
    });
  }

  Term selections() const {
    return list_of(cs_.records().selections,
                   [&](const PlanRecords::Selection &s) {
      if (s.kind == PlanRecords::Selection::kNone)
        export_fail("selection '" + s.name + "': its scan names no kind");
      return Term::obj()
          .f("name", str(s.name))
          .f("domain", str(s.domain))
          .f("kind", s.kind == PlanRecords::Selection::kFixedCutoff
                         ? ".fixedCutoff"
                         : ".risingThreshold")
          .f("candidates", std::to_string(s.candidates))
          .f("outputs", std::to_string(s.outputs))
          .f("width", std::to_string(s.width))
          .f("bound", std::to_string(s.bound))
          .f("challenge", str(s.challenge));
    });
  }

  Term challenges() const {
    const auto &N = cs_.nodes();
    Term l = Term::list();
    for (size_t id = 0; id < N.size(); ++id) {
      const Node &n = N[id];
      if (n.kind != Kind::kChallenge) continue;
      std::string dom;
      for (size_t d = 0; d < cs_.num_domains(); ++d)
        if (cs_.domain(d).field_id == n.field && cs_.domain(d).fobj == n.fobj) {
          dom = cs_.domain(d).name;
          break;
        }
      // The key of a MAC between two odd domains lies in a field no domain
      // commits: its domain is empty.
      bool mac_key = false;
      for (const auto &m : cs_.records().macs) mac_key = mac_key || m.key == id;
      if (dom.empty() && !mac_key)
        export_fail("challenge '" + n.name + "' lies in no domain's field");
      Bound degree = 0;
      for (const auto &c : cs_.records().charges)
        if (c.label == n.name) degree = c.degree;
      Term tests = Term::list();
      for (size_t x : cs_.tests_of(id)) tests.push(Term::a(str(N.at(x).name)));
      l.push(Term::obj()
                 .f("label", str(n.name))
                 .f("domain", str(dom))
                 .f("phase", std::to_string(cs_.phase(id)))
                 .f("sampler", str(n.sampler))
                 .f("degreeBound", nat(degree))
                 .f("tests", tests));
    }
    return l;
  }

  const CS &cs_;
  const ExportMeta &meta_;
  Term requests_ = Term::list(), bindings_ = Term::list(),
       tables_ = Term::list();
  // (domain, T, group within the table) -> (entry in tables, group within
  // the domain's lookup).
  std::map<std::tuple<std::string, Bound, size_t>, std::pair<size_t, size_t>>
      table_index_;
  // Operator terms with interval bounds: name -> (domain, bound terms).
  mutable std::map<std::string,
                   std::pair<std::string,
                             std::vector<std::pair<std::string, Bound>>>>
      op_bounds_;
};

}  // namespace plan_export_internal

// The Lean module of CS's plan (the file's contents).
template <class S>
std::string export_lean_plan(const BasicCompiledSystem<S> &cs,
                             const ExportMeta &meta) {
  return plan_export_internal::Exporter<S>(cs, meta).run();
}
// Its module's path relative to formal/, without `.lean`:
// GordieHowe/Generated/<lean_name with '/' for '.'>/Plan.
inline std::string lean_plan_module(const ExportMeta &meta) {
  return lean_module_path(meta, "Plan");
}

}  // namespace proofs::gordiehowe::compiler

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_COMPILER_PLAN_EXPORT_H_
