// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0

// GordieHowe: the system builder, compile(), and the core protocol.
//
// compile() infers phases, allocates pads, checks the structural conditions
// of the core (pad ownership, pad types, pad dependencies, quadratic triples
// on phase-0 cells, capabilities), and compiles each domain. The compiled
// system runs one fixed schedule:
//
//   statement   label, seed, circuit ids, public inputs, system digest
//   commit      one ZkProver commitment per domain (all phase-0 cells)
//   ldt         with list-radius Ligero (DomainProfile::list_radius), per
//               domain in commit order: the low-degree challenge u_ldt, then
//               the low-degree response w
//   phase k     one challenge round (the phase's challenges, in declaration
//               order, from consecutive bytes of one challenge point of the
//               transcript), then t = x + P for every late variable of
//               phase k, in declaration order
//   fork        the main transcript forks into one transcript per domain
//               (transcript_fork.h)
//   reductions  per domain, on its transcript: a nested fork into one branch
//   + opening   per batch and one for GKR, the batches' masked skips and the
//               masked GKR on their branches, the join, then the domain's
//               Ligero opening over the GKR, batch, affine and quadratic
//               rows
//
// Threading (threads.h) is one knob for every construction:
// ProveOptions::multithreaded and verify's MULTITHREADED argument, both
// defaulting to GH_THREADS=multi. Multi-threaded runs the domains'
// commitment computations, the domains after the fork and the branches of
// each nested fork on a pool; the transcript, and so the proof for one
// RNG, is the same in both modes.

#ifndef PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SYSTEM_H_
#define PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SYSTEM_H_

#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstddef>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <functional>
#include <future>
#include <initializer_list>
#include <map>
#include <memory>
#include <mutex>
#include <optional>
#include <random>
#include <set>
#include <sstream>
#include <stdexcept>
#include <string>
#include <thread>
#include <tuple>
#include <type_traits>
#include <typeinfo>
#include <utility>
#include <vector>

#include "gordiehowe/certify.h"
#include "gordiehowe/core.h"
#include "gordiehowe/compiler/compile_cache.h"
#include "gordiehowe/compiler/compile_options.h"
#include "gordiehowe/compiler/compile_times.h"
#include "gordiehowe/compiler/placement.h"
#include "gordiehowe/compiler/realized_program.h"
#include "gordiehowe/compiler/realized_program_io.h"
#include "gordiehowe/compiler/lowering.h"
#include "gordiehowe/domain.h"
#include "gordiehowe/linear.h"
#include "gordiehowe/predicates.h"
#include "gordiehowe/test_seams.h"
#include "gordiehowe/threads.h"
#include "gordiehowe/transcript_fork.h"
#include "random/random.h"
#include "util/crypto.h"
#include "util/diagnostics.h"
#include "util/prover_profile.h"
#include "zk/zk_common.h"

namespace proofs::gordiehowe {

template <class S>
class BasicCompiledSystem;

template <class Hash, class... Fs>
class BasicConstraintSystem;
template <class S>
class BasicAssignment;
template <class S>
struct BasicProveOptions;
template <class S>
class BasicPrepared;
// Lowers S in place under P and compiles it (defined below), with the
// compile options OPTIONS (compiler/compile_options.h) or the compile cache
// CACHE.
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    BasicConstraintSystem<Hash, Fs...> &s, const CompileProfile &p = {});
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    BasicConstraintSystem<Hash, Fs...> &s, const CompileProfile &p,
    const CompileOptions &options);
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    BasicConstraintSystem<Hash, Fs...> &s, const CompileProfile &p,
    const CompileCache &cache);

// The lowering passes compile() runs (compiler/lowering.h).
namespace compiler {
template <class S>
class MacEqualityLowering;
template <class S>
class ModLowering;
template <class S>
class GroupedLowering;
template <class S>
class ConvLowering;
template <class S>
class PublicExprLowering;
}  // namespace compiler

namespace internal {

// The value forms of a field that has no domain in a system of field set S
// (an operator's parameter field: the MAC tests' chunk powers), through
// Lowering::challenge and Lowering::pub. It declares public values only.
template <class F, class S>
class BareField final : public Domain<F> {
 public:
  BareField(BasicGraph<S> *g, SystemCore *sys, const F *f)
      : Domain<F>(g, sys, f, "", -1, S::template index<F>(), false,
                  Space::kField),
        bg_(g) {}
  std::string field_name() const override { return ""; }

 protected:
  size_t add_node(Node nd, NodeGen<F> gen) const override {
    return bg_->add(std::move(nd), wrap_generator<S>(std::move(gen)));
  }

 private:
  BasicGraph<S> *bg_;
};

}  // namespace internal

// A system over the protocol hash HASH, which every domain profile names,
// and the closed set of fields FS...: every value of the system lies in one
// of them. A field outside the set is a C++ compile error wherever a domain
// of it is created. The system is its root scope; its domains are
// Domain<F> of their fields alone (domain.h), and the field set appears
// here and in what compiles, proves and verifies. Applications name it
// ConstraintSystem<Hash, Fields...> (below).
template <class Hash, class... Fs>
class BasicConstraintSystem : public SystemCore, public Scope {
 public:
  using Set = FieldSet<Hash, Fs...>;
  using Value = typename Set::Value;
  using Compiled = BasicCompiledSystem<Set>;
  using Prepared = BasicPrepared<Set>;
  using Assignment = BasicAssignment<Set>;
  using ProveOptions = BasicProveOptions<Set>;

  explicit BasicConstraintSystem(std::string name)
      : SystemCore(std::move(name)), Scope(this) {
    graph_ = &g_;
    root_ = this;
    g_.system = this;
    g_.wire = [this](const ViewSource &src) { return wire(src); };
  }
  // A system named "system".
  BasicConstraintSystem() : BasicConstraintSystem("system") {}
  BasicConstraintSystem(const BasicConstraintSystem &) = delete;
  BasicConstraintSystem &operator=(const BasicConstraintSystem &) = delete;

  // The domain of the profile P's field, named domain<k> for the k-th
  // domain.
  template <class F, class RSF, class H>
  Domain<F> &domain(const DomainProfile<F, RSF, H> &p) {
    return domain(p, "domain" + std::to_string(domains_.size()));
  }
  // The domain NM of the profile P's field: one per field, so a value's
  // field names its domain.
  template <class F, class RSF, class H>
  Domain<F> &domain(const DomainProfile<F, RSF, H> &p, std::string nm) {
    static_assert(std::is_same_v<H, Hash>,
                  "every domain of a system uses the system's protocol hash");
    // One domain per field, so a value's field names its domain.
    if (Domain<F> *e = domain_of<F>())
      fail("domain '" + nm + "': the system has a domain of its field, '" +
           e->name + "'; a system has one domain per field");
    auto d = std::make_unique<DomainImpl<F, RSF, Set>>(
        &g_, this, p, std::move(nm), static_cast<int>(domains_.size()));
    DomainImpl<F, RSF, Set> &r = *d;
    cores_.push_back(&r);
    domains_.push_back(std::move(d));
    return r;
  }

  const BasicGraph<Set> &graph() const { return g_; }
  const std::vector<std::unique_ptr<DomainBase<Set>>> &domains() const {
    return domains_;
  }

 private:
  friend class compiler::Lowering;
  template <class S>
  friend class compiler::ConstraintSystemBuilder;
  template <class S>
  friend class compiler::MacEqualityLowering;
  template <class S>
  friend class compiler::ModLowering;
  template <class S>
  friend class compiler::GroupedLowering;
  template <class S>
  friend class compiler::ConvLowering;
  template <class S>
  friend class compiler::PublicExprLowering;
  template <class H, class... Gs>
  friend std::unique_ptr<BasicCompiledSystem<FieldSet<H, Gs...>>> compile(
      BasicConstraintSystem<H, Gs...> &s, const CompileProfile &p,
      const CompileOptions &options);

  size_t add_plain(Node nd) override { return g_.add(std::move(nd)); }
  // A Statement struct's bytes (relation.h): one Bytes statement, absorbed
  // before any commitment, in the field of the first binary domain (bytes
  // pack into a binary field's coordinates densely), else the first
  // domain.
  size_t declare_statement(size_t n) override {
    if (cores_.empty())
      fail("system " + system_name() + ": the statement is read before the "
           "relation declares a domain");
    DomainCore *at = cores_[0];
    for (DomainCore *d : cores_)
      if (Set::dispatch(d->field_id, [](auto tag) {
            return decltype(tag)::type::kCharacteristicTwo;
          })) {
        at = d;
        break;
      }
    return Set::dispatch(at->field_id, [&](auto tag) {
      using F = typename decltype(tag)::type;
      return dynamic_cast<Domain<F> &>(*at)
          .pub_in(*this, Bytes{}, "statement", Shape(n))
          .id;
    });
  }
  void statement_codec(
      size_t id,
      std::function<long(const std::vector<uint8_t> &)> accepts) override {
    g_.gens.at(id).accepts_bytes = std::move(accepts);
  }
  std::shared_ptr<const void> constant_elements(
      size_t id, const void *tag) const override {
    const Value v = g_.gens.at(id).eval(ValueStore<Set>{});
    return Set::dispatch(v.index(), [&](auto t) -> std::shared_ptr<const void> {
      using G = typename decltype(t)::type;
      if (field_tag<G>() != tag)
        fail("constant '" + g_.nodes.at(id).name + "' is read in another "
             "field");
      return std::make_shared<const std::vector<typename G::Elt>>(
          Set::template get<G>(v));
    });
  }

  // A core-owned pad of N elements, uniform over the masking space of TYPE,
  // committed in phase 0 (Lowering::pad). It must mask exactly one late
  // value (masked_by); no generator reads it, and pad_copy copies it.
  template <class F>
  Ref<F, AnyType, Committed> pad(Domain<F> &d, Type space, size_t n = 1) {
    Node nd;
    nd.kind = Kind::kPad;
    nd.name = "pad" + std::to_string(g_.nodes.size());
    nd.domain = d.index;
    nd.field = d.field_id;
    nd.fobj = d.fobj;
    nd.n = n;
    nd.pad_space = masking_space(space);
    const uint16_t dg = masking_degree(space);
    nd.pad_degree = dg == 0 ? 0 : normalize_degree<F>(dg);
    const size_t id = g_.add(std::move(nd));
    return Ref<F, AnyType, Committed>{id, n, &d.field(), &g_, {n}};
  }

  // The value forms of field F with no domain here (Lowering::challenge,
  // Lowering::pub), one per field object.
  template <class F>
  Domain<F> &bare_field(const F &f) {
    for (const auto &b : bare_)
      if (b->ftag == field_tag<F>() && b->fobj == &f)
        return *dynamic_cast<Domain<F> *>(b.get());
    bare_.push_back(
        std::make_unique<internal::BareField<F, Set>>(&g_, this, &f));
    return *dynamic_cast<Domain<F> *>(bare_.back().get());
  }

  // The value forms of the field object FOBJ with no domain here, or null
  // when there are none (the plan export reads the odd/odd MAC's field
  // through them).
  const DomainCore *bare_domain(const void *fobj) const {
    for (const auto &b : bare_)
      if (b->fobj == fobj) return b.get();
    return nullptr;
  }

  // The view node of a handle's view operation: a wiring view of the one
  // domain its sources belong to, or, over public values only, a public
  // computation that gathers them (concat_public).
  size_t wire(const ViewSource &src) {
    int dom = -2;
    for (const auto &[id, k] : src) {
      if (id == kZeroCoordinate) continue;
      const int d = g_.nodes.at(id).domain;
      if (dom != -2 && d != dom)
        fail("a view reads values of " +
             std::string(dom < 0 || d < 0 ? "a domain and public values"
                                          : "two domains"));
      dom = d;
    }
    if (dom == -2) fail("a view reads no value");
    if (dom >= 0) return domains_.at(size_t(dom))->wire(src);
    // Public: read through earlier public views.
    ViewSource flat = src;
    for (auto &[id, k] : flat) {
      if (id == kZeroCoordinate) continue;
      auto w = public_views_.find(id);
      if (w != public_views_.end()) std::tie(id, k) = w->second.at(k);
    }
    size_t first = 0;
    while (flat[first].first == kZeroCoordinate) ++first;
    const Node &f0 = g_.nodes.at(flat[first].first);
    std::vector<size_t> deps;
    std::optional<Base> common;
    bool mixed = false;
    for (const auto &[n, k] : flat) {
      if (n == kZeroCoordinate) continue;
      const Base b = g_.nodes.at(n).type.base;
      if (common && *common != b) mixed = true;
      common = b;
    }
    Computes id{"wiring", {}};
    put_u64(id.params, flat.size());
    for (const auto &[n, k] : flat) {
      if (n != kZeroCoordinate) {
        if (g_.nodes.at(n).fobj != f0.fobj)
          fail("a public view reads values of two fields");
        if (std::find(deps.begin(), deps.end(), n) == deps.end())
          deps.push_back(n);
      }
      put_u64(id.params, n == kZeroCoordinate ? ~uint64_t(0) : n);
      put_u64(id.params, k);
    }
    Node nd;
    nd.kind = Kind::kPublicCompute;
    nd.name = "view" + std::to_string(g_.nodes.size());
    nd.field = f0.field;
    nd.fobj = f0.fobj;
    nd.n = flat.size();
    nd.type = mixed ? Type{Base::kField} : Type{*common};
    nd.deps = deps;
    nd.auto_view = true;
    nd.origin = "view";
    nd.challenge_degrees = view_coord_degrees(g_.nodes, flat, deps);
    put_str(nd.descr, id.name);
    put_u64(nd.descr, id.params.size());
    nd.descr.insert(nd.descr.end(), id.params.begin(), id.params.end());
    Generator<Set> gen;
    const Node *pn = &f0;
    gen.eval = with_field<Set>(*pn, [&](const auto &f) {
      using F = std::decay_t<decltype(f)>;
      const F *pf = &f;
      return std::function<Value(const ValueStore<Set> &)>(
          [flat, pf](const ValueStore<Set> &v) {
            std::vector<typename F::Elt> out(flat.size());
            for (size_t i = 0; i < flat.size(); ++i)
              out[i] = flat[i].first == kZeroCoordinate
                           ? pf->zero()
                           : v.template get<F>(flat[i].first)
                                 .at(flat[i].second);
            return Set::template wrap<F>(std::move(out));
          });
    });
    const size_t nid = g_.add(std::move(nd), std::move(gen));
    public_views_[nid] = std::move(flat);
    return nid;
  }

  BasicGraph<Set> g_;
  std::map<size_t, ViewSource> public_views_;  // public view -> its sources
  std::vector<std::unique_ptr<DomainBase<Set>>> domains_;
  std::vector<std::unique_ptr<DomainCore>> bare_;
};

// The system over the protocol hash HASH and the fields FIELDS...: HASH is
// the field profile's (the PQ profile's ProtocolHash, SHA-256 at the ROM
// parameters and SHA-384 at the QROM parameters). No default: every system
// names its hash.
template <class Hash, class... Fs>
using ConstraintSystem = BasicConstraintSystem<Hash, Fs...>;

// Wall-clock milliseconds of one proof, by stage. witness: the phase-0
// generators and the prover's check of the range requests; commit: the
// statement, pads and domain commitments; prove: challenge rounds, the
// later phases' generators (their LogUp values and MAC tags, which read the
// challenges), reductions and openings. LATE is the later phases'
// generators alone, a part of PROVE. Serialization is in none.
struct ProveTimes {
  double witness = 0, commit = 0, prove = 0;
  double late = 0;
  // Per domain, in domain order: its commitment and low-degree test, and
  // its reductions and opening (parts of COMMIT and PROVE; the phase
  // challenges and messages are shared and in neither).
  std::vector<double> domain_commit, domain_prove;
};
// The verifier's time per domain, in domain order: its commitment, its
// low-degree test and its reductions and opening. DOMAIN_POST is the part
// after the phases (its reductions and opening, on its forked transcript).
struct VerifyTimes {
  std::vector<double> domain;
  std::vector<double> domain_post;
  // Proof parsing: the seed, the phase messages and every domain's section
  // decoded from the proof's bytes (the domain verifiers' construction
  // apart).
  double parse = 0;
};

namespace internal {
// The fixed_seed seam's stream: std::mt19937_64 from the seed.
class SeededStream : public RandomEngine {
 public:
  explicit SeededStream(uint64_t seed) : g_(seed) {}
  void bytes(uint8_t *buf, size_t n) override {
    for (size_t i = 0; i < n; ++i) buf[i] = uint8_t(g_());
  }

 private:
  std::mt19937_64 g_;
};
// The fixed_seed seam's line: GH_PROOF_DIGEST <SHA-256, hex> bytes=<size>.
inline void print_proof_digest(const std::vector<uint8_t> &proof) {
  SHA256 sha;
  sha.Update(proof.data(), proof.size());
  uint8_t d[SHA256::kDigestSize];
  sha.DigestData(d);
  char hex[2 * SHA256::kDigestSize + 1];
  hex_to_str(hex, d, SHA256::kDigestSize);
  std::printf("GH_PROOF_DIGEST %s bytes=%zu\n", hex, proof.size());
  std::fflush(stdout);
}
}  // namespace internal

// Test hooks of the prover. TAMPER may change the output of a generator, a
// pad copy or a bit view after it runs (a cheating prover);
// REQUIRE_SATISFIED=false lets ZkProver proceed with an unsatisfied circuit.
// A value is the variant S::Value; its alternative is the node's field.
template <class S>
struct BasicProveOptions {
  std::function<void(size_t id, typename S::Value &value)> tamper;
  ProveTimes *times = nullptr;
  // Receives the bytes of each domain's section of the serialized proof
  // (its batch messages and ZK proof), in domain order.
  std::vector<size_t> *domain_bytes = nullptr;
  // Changes batch B of domain D's zerocheck messages (the alternative of
  // D's field) before they are absorbed. Later rounds are not recomputed,
  // so this is a tampered message, not an adaptive cheater.
  std::function<void(size_t d, size_t b, typename S::Value &messages)>
      batch_tamper;
  // Changes the table words batch B of domain D's reduction reads, not the
  // committed ones: a prover whose zerocheck is honest for other words.
  std::function<void(size_t d, size_t b, typename S::Value &words)>
      batch_words;
  // >= 0: every bit phase's round SWAP_ROUND masks its two messages with
  // each other's pads (compiler/batch.h's Tamper), which the verifier must
  // reject.
  int bit_phase_swap_round = -1;
  bool require_satisfied = true;
  // A test seam: the statement absorbs zeros in place of the system digest,
  // so that proofs of two systems whose descriptions differ can be compared
  // byte for byte (the byte-identity checks of a refactor).
  bool zero_digest = false;
  // The threading knob (threads.h): multi-threaded runs the domains'
  // commitments and their work after the transcript fork on threads of a
  // pool started with the proof. The transcript is the same in both modes,
  // and so is the proof for the same RNG.
  bool multithreaded = default_multithreaded();
  // Test seams (test_seams.h): a fixed-seed proof that prints its digest,
  // and the commitments' computations in domain order on the calling
  // thread.
  std::optional<uint64_t> fixed_seed = prove_seam_defaults().fixed_seed;
  bool serial_commitments = prove_seam_defaults().serial_commitments;
};

// A statement or private assignment: values by handle.
template <class S>
class BasicAssignment {
 public:
  using Value = typename S::Value;
  template <class F, class T, class P>
  BasicAssignment &set(Ref<F, T, P> r, std::vector<typename F::Elt> v) {
    vals_[r.id] = S::template wrap<F>(std::move(v));
    return *this;
  }
  // Canonical integers, in odd characteristic: each is below p, or a
  // run-time error naming the value after the whole conversion (ct.h: no
  // branch on an integer).
  template <class F, class T, class P,
            class = std::enable_if_t<
                !std::is_same_v<typename F::Elt, uint64_t>>>
  BasicAssignment &set(Ref<F, T, P> r, const std::vector<uint64_t> &v) {
    static_assert(!F::kCharacteristicTwo,
                  "Assignment::set: canonical integers exist in odd "
                  "characteristic only");
    const F &f = *r.f;
    // Every 64-bit integer lies below a p beyond 128 bits (a public
    // choice).
    const Bound pb = field_characteristic(f);
    const bool wide = !pb.fits128();
    const NatInt p = wide ? NatInt(0) : static_cast<NatInt>(pb);
    std::vector<typename F::Elt> e(v.size());
    uint64_t ok = 1;
    for (size_t i = 0; i < v.size(); ++i) {
      const uint64_t below = wide ? 1 : ct::lt128(NatInt(v[i]), p);
      ok &= below;
      e[i] = elt_of_nat(f, NatInt(v[i]) & ct::mask128(below));
    }
    if (!ok)
      throw std::runtime_error("Assignment::set '" +
                               r.g->nodes.at(r.id).name +
                               "': an integer is not below p");
    vals_[r.id] = S::template wrap<F>(std::move(e));
    return *this;
  }
  // A Bytes statement's bytes.
  template <class F, class P>
  BasicAssignment &set(Ref<F, Bytes, P> r, std::vector<uint8_t> b) {
    bytes_[r.id] = std::move(b);
    return *this;
  }
  // A host input's bytes.
  BasicAssignment &set(HostInput h, std::vector<uint8_t> b) {
    bytes_[h.id] = std::move(b);
    return *this;
  }
  const Value *find(size_t id) const {
    auto it = vals_.find(id);
    return it == vals_.end() ? nullptr : &it->second;
  }
  const std::vector<uint8_t> *find_bytes(size_t id) const {
    auto it = bytes_.find(id);
    return it == bytes_.end() ? nullptr : &it->second;
  }

 private:
  std::map<size_t, Value> vals_;
  std::map<size_t, std::vector<uint8_t>> bytes_;
};

template <class S>
class BasicCompiledSystem {
 public:
  using Hash = typename S::Hash;
  using Prepared = BasicPrepared<S>;
  using Assignment = BasicAssignment<S>;
  using ProveOptions = BasicProveOptions<S>;
  // A late variable's masked message in the serialized proof.
  struct Span {
    size_t offset, length;
  };

  size_t phases() const { return K_; }
  // The values challenge ID tests: declared and inferred.
  const std::vector<size_t> &tests_of(size_t id) const {
    return nodes_.at(id).tests;
  }
  size_t phase(size_t id) const { return plan_.phase.at(id); }
  template <class F, class T, class P>
  size_t phase(Ref<F, T, P> r) const {
    return phase(r.id);
  }
  template <class F, class T, class P>
  bool late(Ref<F, T, P> r) const {
    return plan_.late(r.id);
  }
  // Late variables in transcript order.
  const std::vector<size_t> &messages() const { return messages_; }
  template <class F, class T, class P>
  Span message_span(Ref<F, T, P> r) const {
    size_t off = Hash::kDigestSize;
    for (size_t x : messages_) {
      const size_t len = msg_bytes(x);
      if (x == r.id) return Span{off, len};
      off += len;
    }
    throw std::runtime_error("not a late variable");
  }
  const std::string &report() const { return report_; }
  // What the compile cache did for this compile (compiler/compile_cache.h).
  const CacheOutcome &cache() const { return cache_; }
  // Forgets the memoized public computations, so that the next prepare()
  // runs its setup again (benches time the setup). A Prepared reads the
  // memoized values, so none may outlive this call.
  void forget_setup() const { memo_.clear(); }
  // The digest of the system description the statement absorbs.
  const std::vector<uint8_t> &digest() const { return digest_; }
  // The plan as compiled, for the plan export (plan_export.h): the
  // transcript label, the nodes after pad allocation, the domains and
  // their compilations, the lowerings' records and profile, and each
  // late variable's masked message (its masking space and bytes).
  const std::string &label() const { return label_; }
  const std::vector<Node> &nodes() const { return nodes_; }
  size_t num_domains() const { return domains_.size(); }
  const DomainBase<S> &domain(size_t d) const { return *domains_.at(d); }
  const CompiledDomainBase<S> &compiled_domain(size_t d) const {
    return *compiled_.at(d);
  }
  const PlanRecords &records() const { return records_; }
  // The realized program (compiler/realized_program.h): the compiler's last
  // stage, from which the domains' provers and verifiers are built, and
  // which the compile cache stores and the Lean export prints.
  const ir::Program &program() const { return *program_; }
  const std::string &profile_name() const { return profile_name_; }
  uint32_t profile_version() const { return profile_version_; }
  Space message_space(size_t id) const { return msg_space(id); }
  uint16_t message_degree(size_t id) const { return msg_degree(id); }
  size_t message_bytes(size_t id) const { return msg_bytes(id); }
  // The messages of batched relation B of the first domain in the
  // serialized proof (they follow the late-variable messages).
  Span batch_message_span(size_t b) const {
    size_t off = Hash::kDigestSize;
    for (size_t x : messages_) off += msg_bytes(x);
    const auto sizes = compiled_.at(0)->batch_message_bytes();
    for (size_t i = 0; i < b; ++i) off += sizes.at(i);
    return Span{off, sizes.at(b)};
  }

  Prepared prepare(const Assignment &statement) const;
  // Test hook: the same with TAMPER applied to each cached public
  // computation after the setup computes it.
  Prepared prepare(
      const Assignment &statement,
      const std::function<void(size_t id, typename S::Value &value)> &tamper)
      const;

  // A test seam: the stream of challenge LABEL starts with PREFIX, then
  // continues with its transcript stream, in every later proof and
  // verification of this system (both parties, so they still agree). A
  // test forces a draw this way, such as LogUp's alpha onto a table value.
  void set_challenge_prefix(const std::string &label,
                            std::vector<uint8_t> prefix) const {
    prefix_[label] = std::move(prefix);
  }
  // A test seam: the value of challenge LABEL in the last proof or
  // verification that drew it, and the stream bytes it read.
  const typename S::Value &drawn_challenge(const std::string &label) const {
    return drawn_.at(label).first;
  }
  size_t drawn_challenge_bytes(const std::string &label) const {
    return drawn_.at(label).second;
  }

  // The committed phase-0 coordinates of domain D: private inputs, unbound
  // phase-0 advice, pads and pad copies.
  size_t coordinates(int d) const {
    size_t k = 0;
    for (size_t id = 0; id < nodes_.size(); ++id)
      if (nodes_[id].domain == d && plan_.cell(id)) k += nodes_[id].n;
    return k;
  }
  // The realization the range lowering selected for a request, and the
  // exclusive bound it proves.
  template <class F>
  const RangeRealization &realization(RangeHandle<F> h) const {
    const auto *d =
        dynamic_cast<const Domain<F> *>(domains_.at(h.domain));
    if (d == nullptr) throw std::runtime_error("realization: not a domain of F");
    const auto &r = d->requests().at(h.request);
    if (!r.lowered) throw std::runtime_error("realization: not lowered");
    return r.realization;
  }
  template <class F>
  Bound proven_bound(RangeHandle<F> h) const {
    return realization(h).established;
  }
  // The same by the request's name (its scoped name, as assert_range
  // declared it). A name no request has, or two domains share, is an
  // error.
  const RangeRealization &realization(const std::string &nm) const {
    const RangeRealization *found = nullptr;
    for (const DomainBase<S> *d : domains_) {
      bool lowered = false;
      const RangeRealization *r = d->find_request(nm, lowered);
      if (r == nullptr) continue;
      if (found != nullptr)
        throw std::runtime_error("realization: two domains have a range "
                                 "request named '" + nm + "'");
      if (!lowered)
        throw std::runtime_error("realization: '" + nm + "' is not lowered");
      found = r;
    }
    if (found == nullptr)
      throw std::runtime_error("realization: no range request is named '" +
                               nm + "'");
    return *found;
  }
  Bound proven_bound(const std::string &nm) const {
    return realization(nm).established;
  }

 private:
  template <class H, class... Gs>
  friend std::unique_ptr<BasicCompiledSystem<FieldSet<H, Gs...>>> compile(
      const BasicConstraintSystem<H, Gs...> &s, const CompileOptions &options);
  friend class BasicPrepared<S>;
  BasicCompiledSystem() = default;

  Space msg_space(size_t x) const {
    return pad_space(static_cast<size_t>(plan_.pad_of[x]));
  }
  // The subfield of a message in the subfield space (its pad's stored
  // degree, 0 for the designated subfield).
  uint16_t msg_degree(size_t x) const {
    return nodes_[static_cast<size_t>(plan_.pad_of[x])].pad_degree;
  }
  // A pad's resolved space; a pad of a field without a domain (the odd
  // MAC's blind) is uniform over its field.
  Space pad_space(size_t p) const {
    const Node &n = nodes_[p];
    if (n.domain < 0) return n.pad_space;
    return domains_[n.domain]->resolve(n.pad_space);
  }
  size_t msg_bytes(size_t x) const {
    const Space s = msg_space(x);
    const uint16_t d = msg_degree(x);
    return nodes_[x].n * with_field<S>(nodes_[x], [s, d](const auto &f) {
             return FieldValues<std::decay_t<decltype(f)>>::codec_bytes(s, d);
           });
  }

  std::string label_;
  std::vector<Node> nodes_;
  std::vector<Generator<S>> gens_;  // by node id
  CompilePlan plan_;
  size_t K_ = 0;
  std::vector<size_t> messages_;
  std::vector<const DomainBase<S> *> domains_;
  std::vector<std::unique_ptr<CompiledDomainBase<S>>> compiled_;
  std::vector<uint8_t> digest_;
  std::string report_;
  PlanRecords records_;
  std::string profile_name_;
  uint32_t profile_version_ = 0;
  std::vector<size_t> public_inputs_;
  CacheOutcome cache_;
  // The realized program the domains were built from.
  std::shared_ptr<const ir::Program> program_;
  // Cached public computations by the digest of node and dependencies.
  mutable std::map<std::vector<uint8_t>, typename S::Value> memo_;
  // The test hooks' prefixes and draws, by challenge label.
  mutable std::map<std::string, std::vector<uint8_t>> prefix_;
  mutable std::map<std::string, std::pair<typename S::Value, size_t>> drawn_;
  // With the profiler on: each domain's batch count and GKR layer count
  // (BasicPrepared::profile_shape), computed once (a DomainPlan per domain
  // inside every timed proof and verification would cost the timings it
  // records).
  mutable std::shared_ptr<std::once_flag> shape_once_ =
      std::make_shared<std::once_flag>();
  mutable std::vector<std::pair<size_t, size_t>> shape_;
};

// ------------------------------------------------------------- compile --

namespace compiler {
// The realized program of a compiled system (compiler/program_builder.h).
template <class S>
ir::Program build_ir(const BasicCompiledSystem<S> &cs);
}  // namespace compiler

namespace internal {

inline const char *kind_name(Kind k) {
  switch (k) {
    case Kind::kPublicInput:
      return "public_input";
    case Kind::kConstant:
      return "constant";
    case Kind::kPrivateInput:
      return "private_input";
    case Kind::kAdvice:
      return "advice";
    case Kind::kDerived:
      return "derive";
    case Kind::kPublicCompute:
      return "public_compute";
    case Kind::kChallenge:
      return "challenge";
    case Kind::kPad:
      return "pad";
    case Kind::kBitView:
      return "bits";
    case Kind::kPadCopy:
      return "pad_copy";
    case Kind::kHostInput:
      return "host_input";
    default:
      return "public_message";
  }
}

}  // namespace internal

// The compiled system refers to S's domains; S must outlive it. With
// OPTIONS.cache on, the domains' circuits come from the entry of the
// system's key when one is stored, and are stored under it otherwise
// (compiler/compile_cache.h).
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    const BasicConstraintSystem<Hash, Fs...> &s,
    const CompileOptions &options) {
  using S = FieldSet<Hash, Fs...>;
  const CompileCache &cache = options.cache;
  using internal::kind_name;
  compiler::compile_times_system(s.system_name());
  GH_COMPILE_REGION("compile");
  std::optional<compiler::CompileRegion> phase_region;
  phase_region.emplace(compiler::compile_times_on() ? "front" : "");
  std::unique_ptr<BasicCompiledSystem<S>> owner(new BasicCompiledSystem<S>);
  BasicCompiledSystem<S> &cs = *owner;
  cs.label_ = "gordiehowe:" + s.system_name();
  cs.nodes_ = s.graph().nodes;
  cs.gens_ = s.graph().gens;
  cs.records_ = s.graph().records;
  if (s.lowered_with()) {
    cs.profile_name_ = s.lowered_with()->name;
    cs.profile_version_ = s.lowered_with()->version;
  }
  for (const auto &d : s.domains()) cs.domains_.push_back(d.get());
  std::vector<Node> &N = cs.nodes_;
  const size_t n0 = N.size();
  if (!s.lowering_failure().empty())
    fail("an earlier lowering of this system failed: " + s.lowering_failure());
  {
    size_t req = 0;
    for (const auto &d : s.domains()) req += d->pending_requests();
    if (req != 0 || s.pending_equalities() != 0)
      fail("system " + s.system_name() + " has " + std::to_string(req) +
           " range requests and " + std::to_string(s.pending_equalities()) +
           " equalities that are not lowered; compile(System&, profile) "
           "lowers them");
  }

  // Declarations reference earlier nodes only; the graph is acyclic by
  // construction, which the challenge check below re-establishes.
  for (size_t id = 0; id < n0; ++id) {
    for (size_t d : N[id].deps)
      if (d >= id) fail("node '" + N[id].name + "' depends on a later node");
    if (N[id].masked_by >= static_cast<long>(id))
      fail("'" + N[id].name + "' is masked by a later pad");
  }

  // Phases. Advice, derived
  // values, public computations and public messages take the largest phase
  // among their dependencies; challenges one more than the largest among their
  // tested values. A declared test is never computed from its challenge.
  for (size_t id = 0; id < n0; ++id)
    if (N[id].kind == Kind::kChallenge)
      for (size_t t : N[id].tests) {
        std::set<size_t> a;
        std::vector<size_t> st{t};
        while (!st.empty()) {
          const size_t x = st.back();
          st.pop_back();
          if (!a.insert(x).second) continue;
          st.insert(st.end(), N[x].deps.begin(), N[x].deps.end());
        }
        if (a.count(id))
          fail("challenge '" + N[id].name + "' tests '" + N[t].name +
               "', which depends on it");
      }
  std::vector<std::vector<size_t>> all_reads;
  for (const DomainBase<S> *d : cs.domains_)
    for (auto &[nm, r] : d->constraint_reads()) all_reads.push_back(r);
  compiler::PhasePlan pp = compiler::infer_phases(N, all_reads);
  std::vector<size_t> phase = pp.phase;
  for (size_t id = 0; id < n0; ++id)
    if (N[id].kind == Kind::kChallenge) N[id].tests = pp.tests[id];
  // Challenges: each tests at least one value, and labels are distinct (each
  // label separates its own decoding stream; the transcript length-prefixes
  // it).
  {
    std::set<std::string> labels;
    for (size_t id = 0; id < n0; ++id) {
      if (N[id].kind != Kind::kChallenge) continue;
      if (N[id].tests.empty())
        fail("challenge '" + N[id].name + "' tests no value: no constraint "
             "reads it with a prover-chosen value; declare what it tests "
             "with depends_on(...)");
      if (!labels.insert(N[id].name).second)
        fail("two challenges share the label '" + N[id].name + "'");
    }
  }

  // A challenge drawn outside a set U (challenge_outside) reads U's values
  // when it is drawn: each is public, and drawn or computed before it, in
  // an earlier phase or, for a challenge, earlier in its own phase (the
  // challenges of a phase are drawn in declaration order).
  for (size_t id = 0; id < n0; ++id)
    for (size_t x : N[id].excludes) {
      const Kind k = N[x].kind;
      const bool pub = k == Kind::kPublicInput || k == Kind::kConstant ||
                       k == Kind::kPublicCompute || k == Kind::kChallenge;
      const bool before =
          phase[x] < phase[id] ||
          (k == Kind::kChallenge && phase[x] == phase[id] && x < id);
      if (!pub || !before)
        fail("challenge '" + N[id].name + "' is drawn outside a set that "
             "reads '" + N[x].name + "', which is not a public value fixed "
             "before it");
    }

  // The challenge-use rule: a constraint that reads a challenge c may read a
  // prover-chosen value v only if v is fixed before c is drawn (phase(v) <
  // phase(c)) or v depends on c. Otherwise the prover chooses v after
  // seeing c, independently of it, and c tests nothing about v. Reads go
  // through derived views, public computations, operator parameters and bit
  // views down to challenges and prover-chosen values (variables, pads, pad
  // copies, public messages).
  for (const DomainBase<S> *d : cs.domains_)
    for (const auto &[what, roots] : d->constraint_reads()) {
      std::set<size_t> chal, vals, seen;
      std::vector<size_t> stack(roots.begin(), roots.end());
      while (!stack.empty()) {
        const size_t id = stack.back();
        stack.pop_back();
        if (!seen.insert(id).second) continue;
        switch (N[id].kind) {
          case Kind::kChallenge:
            chal.insert(id);
            break;
          case Kind::kDerived:
          case Kind::kPublicCompute:
          case Kind::kBitView:
            stack.insert(stack.end(), N[id].deps.begin(), N[id].deps.end());
            break;
          case Kind::kPublicInput:
          case Kind::kConstant:
            break;
          default:
            vals.insert(id);
        }
      }
      for (size_t c : chal)
        for (size_t v : vals)
          if (!(phase[v] < phase[c] || pp.from(v, c)))
            fail("constraint '" + what + "' of domain " + d->name +
                 " reads the challenge '" + N[c].name + "' (phase " +
                 std::to_string(phase[c]) + ") and '" + N[v].name +
                 "' (phase " + std::to_string(phase[v]) +
                 "), which is neither fixed before it nor computed from it");
    }

  // A cached public computation reads statement values and constants only.
  for (size_t id = 0; id < n0; ++id) {
    if (!N[id].cached) continue;
    for (size_t d : N[id].deps)
      if (N[d].kind != Kind::kPublicInput && N[d].kind != Kind::kConstant)
        fail("public_compute '" + N[id].name + "' is cached but reads '" +
             N[d].name + "', which is not a statement value or constant");
  }
  // A statement bound (Ref::bounded) lies on a statement input or on a
  // cached public computation, which reads the statement and constants
  // only: the verifier checks it when it prepares the statement.
  for (size_t id = 0; id < n0; ++id) {
    if (N[id].stmt_bound == 0) continue;
    const bool input = N[id].kind == Kind::kPublicInput;
    const bool cached = N[id].kind == Kind::kPublicCompute && N[id].cached;
    if (!input && !cached)
      fail("'" + N[id].name + "' has a statement bound but is neither a "
           "statement input nor a cached public computation");
  }

  // (Pub-chal): a public value computed from a challenge is an expression,
  // whose degree in the challenge is counted (compiler/public_expr.h). A
  // closure over a challenge belongs to a core realization, declared by a
  // lowering: the MAC's chunk powers, assert_in's and the range lookups'
  // weights. Reads go through public computations to challenges; a public
  // message is the prover's, not a challenge.
  for (size_t id = 0; id < n0; ++id) {
    if (N[id].kind != Kind::kPublicCompute || N[id].expression ||
        N[id].origin != "application")
      continue;
    std::set<size_t> seen;
    std::vector<size_t> stack(N[id].deps.begin(), N[id].deps.end());
    while (!stack.empty()) {
      const size_t x = stack.back();
      stack.pop_back();
      if (!seen.insert(x).second) continue;
      if (N[x].kind == Kind::kChallenge)
        fail("public value '" + N[id].name + "' is computed by a closure from "
             "the challenge '" + N[x].name + "'; write it as an expression "
             "over the challenge, so that its degree is counted "
             "((Pub-chal))");
      if (N[x].kind == Kind::kPublicCompute)
        stack.insert(stack.end(), N[x].deps.begin(), N[x].deps.end());
    }
  }
  // A lowering's closure reads only the challenges of the core
  // realizations: one over a challenge of the source program (a library
  // function's deferred group) has no known degree in it.
  for (size_t id = 0; id < n0; ++id) {
    if (N[id].kind != Kind::kPublicCompute || N[id].expression ||
        public_view(N[id]))
      continue;
    for (size_t c : challenges_read(N, N[id].deps))
      if (!realization_challenge(N[c]))
        fail("public value '" + N[id].name + "' is computed by a closure "
             "from the challenge '" + N[c].name + "', which no core "
             "realization (the MAC, assert_in, the range lookups) draws; "
             "write it as an expression over the challenge, so that its "
             "degree is counted ((Pub-chal))");
  }

  // Degree bounds: a challenge of the source program gets the sum over the
  // predicates that read it of their degree in it (deg_c), computed from the
  // expressions, and its error is that bound over the challenge's field; a core
  // realization's challenge keeps the bound its lowering declared, from the
  // error of its identity. The plan exports the bounds in its charge records.
  // The report lists each computed bound beside any a library function
  // declared, as information only.
  std::string degree_lines;
  {
    std::map<size_t, Bound> computed;
    std::map<size_t, size_t> readers;
    for (const DomainBase<S> *d : cs.domains_)
      for (const auto &[pred, degs] : d->predicate_degrees())
        for (const auto &[c, deg] : degs) {
          if (realization_challenge(N[c])) continue;
          if (deg == kCircuitDegree)
            fail("predicate '" + pred + "' reads the challenge '" +
                 N[c].name + "' through a comparison or a closure, so its "
                 "degree in it is unbounded; write the predicate as a "
                 "polynomial in the challenge (spec section 5)");
          computed[c] = bound_add(computed[c], Bound(deg));
          ++readers[c];
        }
    std::map<std::string, Bound> declared;
    std::vector<PlanRecords::Charge> charges;
    std::map<std::string, size_t> label;
    for (size_t id = 0; id < n0; ++id)
      if (N[id].kind == Kind::kChallenge) label[N[id].name] = id;
    for (const auto &ch : cs.records_.charges) {
      auto it = label.find(ch.label);
      if (it != label.end() && !realization_challenge(N[it->second])) {
        declared[ch.label] = bound_add(declared[ch.label], ch.degree);
        continue;
      }
      charges.push_back(ch);
    }
    for (const auto &[c, deg] : computed) {
      charges.push_back({N[c].name, deg});
      degree_lines +=
          "  degree bound " + N[c].name + ": " + bound_str(deg) + " from " +
          std::to_string(readers[c]) + " predicate" +
          (readers[c] == 1 ? "" : "s");
      auto it = declared.find(N[c].name);
      if (it != declared.end())
        degree_lines += " (declared " + bound_str(it->second) + ")";
      degree_lines += "\n";
    }
    for (const auto &[nm, deg] : declared)
      if (!computed.count(label.at(nm)))
        degree_lines += "  degree bound " + nm +
                             ": 0, no predicate reads it (declared " +
                             bound_str(deg) + ")\n";
    cs.records_.charges = std::move(charges);
  }

  // Kinds that must not read private values.
  for (size_t id = 0; id < n0; ++id) {
    const Node &n = N[id];
    if (n.kind == Kind::kPublicCompute)
      for (size_t d : n.deps)
        if (!is_public(N[d].kind))
          fail("public_compute '" + n.name + "' reads private value '" +
               N[d].name + "'");
    if (n.kind == Kind::kPublicMessage) {
      const size_t x = n.deps.at(0);
      if (!(N[x].kind == Kind::kAdvice && phase[x] >= 1))
        fail("public_message of '" + N[x].name +
             "', which is not a late variable");
    }
  }

  // Pads reach generators only through pad copies, which the core fills
  // through a declared map; a pad copy's type follows its map.
  for (size_t id = 0; id < n0; ++id) {
    Node &n = N[id];
    if (n.kind == Kind::kAdvice)
      for (size_t d : n.deps)
        if (N[d].kind == Kind::kPad && !N[d].key_pad)
          fail("advice '" + n.name + "' lists the pad '" + N[d].name +
               "' as a dependency; a generator never reads a pad: copy it "
               "with pad_copy, which the core fills");
    if (n.kind != Kind::kPadCopy) continue;
    const size_t p = n.deps.at(0);
    if (N[p].kind != Kind::kPad)
      fail("pad_copy '" + n.name + "' copies '" + N[p].name +
           "', which is not a pad");
    if (n.copy_same_field && N[p].fobj != n.fobj)
      fail("pad_copy '" + n.name + "' maps within one field, but the pad '" +
           N[p].name + "' lies in another field");
    if (n.copy_keeps_space) {
      const Space s = cs.pad_space(p);
      n.type = s == Space::kField      ? Type{Base::kField}
               : s == Space::kSubfield ? Type{Base::kSubfield, N[p].pad_degree}
                                       : Type{Base::kBit};
    }
  }

  // Late variables and their pads.
  std::vector<long> pad_of(n0, -1);
  std::map<size_t, size_t> pad_uses;
  for (size_t id = 0; id < n0; ++id) {
    const Node &n = N[id];
    if (n.kind == Kind::kPad) pad_uses[id] = 0;
    if (n.kind != Kind::kAdvice) continue;
    if (phase[id] == 0) {
      if (n.masked_by >= 0)
        fail("'" + n.name + "' is phase 0 and is committed; masked_by "
             "applies to late values only");
      continue;
    }
    if (n.masked_by >= 0) {
      const size_t p = static_cast<size_t>(n.masked_by);
      if (N[p].kind != Kind::kPad)
        fail("'" + n.name + "' is masked_by '" + N[p].name +
             "', which is not a pad");
      if (N[p].domain != n.domain || N[p].n != n.n)
        fail("pad of '" + n.name + "' has another domain or length");
      pad_of[id] = n.masked_by;
    }
  }
  // Fresh pads for late values without masked_by.
  for (size_t id = 0; id < n0; ++id) {
    if (!(N[id].kind == Kind::kAdvice && phase[id] >= 1) || pad_of[id] >= 0)
      continue;
    Node p;
    p.kind = Kind::kPad;
    p.name = "pad(" + N[id].name + ")";
    p.domain = N[id].domain;
    p.field = N[id].field;
    p.fobj = N[id].fobj;
    p.n = N[id].n;
    p.pad_space = masking_space(N[id].type);
    p.pad_degree = masking_degree(N[id].type);
    p.auto_pad = true;
    N.push_back(std::move(p));
    phase.push_back(0);
    pad_of.push_back(-1);
    pad_of[id] = static_cast<long>(N.size() - 1);
    pad_uses[N.size() - 1] = 0;
  }
  // Pad ownership and pad types.
  for (size_t id = 0; id < n0; ++id) {
    if (pad_of[id] < 0) continue;
    const size_t p = static_cast<size_t>(pad_of[id]);
    if (++pad_uses[p] > 1)
      fail("pad '" + N[p].name + "' masks more than one message");
    const Space want = N[id].domain < 0
                           ? masking_space(N[id].type)
                           : cs.domains_.at(N[id].domain)
                                 ->resolve(masking_space(N[id].type));
    const Space have = cs.pad_space(p);
    if (want != have)
      fail(std::string("a pad uniform over the ") + space_name(have) +
           " space cannot mask the " + type_name(N[id].type) + " value '" +
           N[id].name + "', whose masking space is the " + space_name(want) +
           " space");
    // In the subfield space, the pad is uniform in the value's own
    // subfield (a packing-tree node of its domain).
    if (want == Space::kSubfield &&
        N[p].pad_degree != masking_degree(N[id].type))
      fail("a pad uniform over the subfield " +
           type_name(Type{Base::kSubfield, N[p].pad_degree}) +
           " cannot mask the " + type_name(N[id].type) + " value '" +
           N[id].name + "'");
  }
  // A key pad (Node::key_pad) masks no message; every other pad masks one.
  for (const auto &[p, uses] : pad_uses) {
    if (N[p].key_pad && uses != 0)
      fail("key pad '" + N[p].name + "' masks a message");
    if (!N[p].key_pad && uses == 0)
      fail("pad '" + N[p].name + "' masks no message");
  }

  // Messages: late variables by phase, then declaration order.
  std::vector<size_t> messages;
  for (size_t id = 0; id < n0; ++id)
    if (pad_of[id] >= 0) messages.push_back(id);
  std::stable_sort(messages.begin(), messages.end(),
                   [&](size_t a, size_t b) { return phase[a] < phase[b]; });

  size_t K = 0;
  for (size_t id = 0; id < N.size(); ++id) K = std::max(K, phase[id]);

  cs.gens_.resize(N.size());  // auto pads have no closures
  cs.plan_.nodes = &cs.nodes_;
  cs.plan_.options = options;
  cs.plan_.phase = phase;
  cs.plan_.pad_of = pad_of;
  {
    std::map<std::string, size_t> challenge;
    for (size_t id = 0; id < n0; ++id)
      if (N[id].kind == Kind::kChallenge) challenge[N[id].name] = id;
    for (const auto &ch : cs.records_.charges) {
      auto it = challenge.find(ch.label);
      if (it == challenge.end()) continue;
      const Node &n = N[it->second];
      cs.plan_.charges.push_back({ch.label, phase[it->second], n.field,
                                  n.fobj, ch.exact.value_or(ch.degree)});
    }
  }
  for (const DomainBase<S> *d : cs.domains_)
    for (size_t x : d->bound_ids()) {
      if (N[x].domain != d->index)
        fail("'" + N[x].name + "' is bound in domain " + d->name +
             ", which does not own it");
      cs.plan_.bound.insert(x);
    }
  cs.K_ = K;
  cs.messages_ = messages;

  // The compile cache's key: everything the domains' compilation reads
  // (compiler/compile_cache.h), and the entry stored under it.
  using CacheKind = CacheOutcome::Kind;
  compiler::CacheKey key{};
  std::optional<compiler::CacheEntry> entry;
  // The realized program the domains are built from (the entry's on a
  // hit).
  std::shared_ptr<const ir::Program> program;
  std::string uncacheable;
  phase_region.reset();
  phase_region.emplace(compiler::compile_times_on() ? "cache key" : "");
  // Each field's identity bytes (FieldValues::identity), once per field
  // object: the key and the description write them for every node.
  std::map<std::pair<size_t, const void *>, std::vector<uint8_t>> identities;
  auto field_identity = [&](const Node &n) -> const std::vector<uint8_t> & {
    static const std::vector<uint8_t> none;
    if (n.kind == Kind::kHostInput) return none;
    auto [it, fresh] = identities.try_emplace({n.field, n.fobj});
    if (fresh)
      it->second = with_field<S>(n, [](const auto &f) {
        return FieldValues<std::decay_t<decltype(f)>>::identity(f);
      });
    return it->second;
  };
  if (cache.on()) {
    // The key's bytes go to SHA-256 a megabyte at a time.
    std::vector<uint8_t> k;
    SHA256 kh;
    auto flush_key = [&] {
      kh.Update(k.data(), k.size());
      k.clear();
    };
    put_str(k, "gordiehowe-compile-cache");
    put_u64(k, compiler::kCompileCacheFormat);
    put_str(k, kCompilerDigest);
    put_str(k, typeid(S).name());
    put_str(k, cs.label_);
    put_str(k, s.lowered_with() ? s.lowered_with()->name : std::string());
    put_u64(k, s.lowered_with() ? s.lowered_with()->version : 0);
    // The options that force the decisions the entry stores: the placement
    // pins, the Ligero choice's forced repetitions (all domains', and by
    // domain) and masking, and the packing tree's forced chains.
    put_str(k, options.placement_force);
    put_u64(k, options.ldt_reps);
    put_u64(k, options.domain_ldt_reps.size());
    for (const auto &[nm, reps] : options.domain_ldt_reps) {
      put_str(k, nm);
      put_u64(k, reps);
    }
    put_u64(k, options.ligero_masking ? 1 + uint64_t(*options.ligero_masking)
                                      : 0);
    put_u64(k, options.forced_chains.size());
    for (const auto &[edge, chain] : options.forced_chains) {
      put_u64(k, edge.first);
      put_u64(k, edge.second);
      put_u64(k, chain.size());
      for (size_t x : chain) put_u64(k, x);
    }
    put_u64(k, N.size());
    for (size_t id = 0; id < N.size(); ++id) {
      const Node &n = N[id];
      if (k.size() >= (size_t(1) << 20)) flush_key();
      put_u64(k, static_cast<uint64_t>(n.kind));
      put_str(k, n.name);
      const std::vector<uint8_t> &field = field_identity(n);
      put_u64(k, field.size());
      k.insert(k.end(), field.begin(), field.end());
      put_u64(k, n.field);
      put_u64(k, static_cast<uint64_t>(n.domain + 1));
      put_u64(k, n.n);
      put_u64(k, static_cast<uint64_t>(n.type.base));
      put_u64(k, n.type.degree);
      put_u64(k, phase[id]);
      put_u64(k, static_cast<uint64_t>(pad_of[id] + 1));
      put_u64(k, cs.plan_.bound.count(id));
      put_u64(k, static_cast<uint64_t>(n.masked_by + 1));
      put_u64(k, static_cast<uint64_t>(n.pad_space));
      put_u64(k, n.pad_degree);
      put_u64(k, (n.auto_pad ? 1 : 0) | (n.copy_keeps_space ? 2 : 0) |
                     (n.copy_same_field ? 4 : 0) | (n.auto_view ? 8 : 0) |
                     (n.cached ? 16 : 0) | (n.expression ? 32 : 0) |
                     (n.realization ? 64 : 0) |
                     (n.stmt_bound != 0 ? 128 : 0) | (n.zero_pad ? 256 : 0) |
                     (n.key_pad ? 512 : 0));
      // A statement bound, only when declared: a system without one keeps
      // its digest.
      if (n.stmt_bound != 0) {
        put_u64(k, static_cast<uint64_t>(n.stmt_bound));
        put_u64(k, static_cast<uint64_t>(n.stmt_bound >> 64));
      }
      put_u64(k, n.deps.size());
      for (size_t d : n.deps) put_u64(k, d);
      put_u64(k, n.tests.size());
      for (size_t t : n.tests) put_u64(k, t);
      put_str(k, n.sampler);
      put_u64(k, n.excludes.size());
      for (size_t x : n.excludes) put_u64(k, x);
      put_str(k, n.origin);
      put_u64(k, n.descr.size());
      k.insert(k.end(), n.descr.begin(), n.descr.end());
      put_u64(k, n.shape.size());
      for (size_t x : n.shape) put_u64(k, x);
    }
    put_u64(k, s.summaries().size());
    for (const auto &[nm, sum] : s.summaries()) {
      put_str(k, nm);
      put_u64(k, sum.descr.size());
      k.insert(k.end(), sum.descr.begin(), sum.descr.end());
    }
    put_u64(k, s.graph().scopes.size());
    for (const auto &[nm, params] : s.graph().scopes) {
      put_str(k, nm);
      put_u64(k, params.size());
      k.insert(k.end(), params.begin(), params.end());
    }
    put_u64(k, cs.domains_.size());
    for (const DomainBase<S> *d : cs.domains_) {
      flush_key();
      const std::string why = d->describe_key(k);
      if (uncacheable.empty()) uncacheable = why;
    }
    flush_key();
    // The rate run's request scan records the requests the placement rule
    // makes, which a hit does not run.
    if (uncacheable.empty() && !diagnostics::options().rate_requests.empty())
      uncacheable = "the rate request scan records the placement rule's rate "
                    "requests, which a hit would not make";
    // So does a test that records the provisional pass's tableaus.
    if (uncacheable.empty() && options.provisional_record != nullptr)
      uncacheable = "a test records the provisional pass, which a hit "
                    "would not run";
    kh.DigestData(key.data());
    phase_region.reset();
    phase_region.emplace(compiler::compile_times_on() ? "cache read" : "");
    cs.cache_.file = compiler::cache_file(cache, s.system_name(), key);
    if (uncacheable.empty()) {
      if (auto bytes = compiler::read_file(cs.cache_.file)) {
        std::string why;
        entry = compiler::parse_entry(std::move(*bytes), key, why);
        if (entry) {
          GH_COMPILE_REGION("read realized program");
          auto p = ir::read_program(entry->program);
          if (!p) {
            why = "its realized program does not read";
          } else if (p->realizations.size() != cs.domains_.size()) {
            why = "another number of domains";
          } else {
            program = std::make_shared<const ir::Program>(std::move(*p));
          }
          if (!program) entry.reset();
        }
        if (!entry) {
          cs.cache_.kind = CacheKind::kDiscarded;
          cs.cache_.reason = why;
        }
      }
    }
  }

  // Builds each domain, from PROG when given (DomainSource; otherwise its
  // compiler decides and emits), and marks the bit views nobody reads.
  auto build_domains = [&](const ir::Program *prog,
                           const std::vector<std::unique_ptr<
                               CompiledDomainBase<S>>> *donors = nullptr) {
    cs.compiled_.clear();
    cs.plan_.unread.clear();
    cs.plan_.unread_flag.clear();
    for (size_t i = 0; i < cs.domains_.size(); ++i) {
      GH_COMPILE_REGION("domain " + cs.domains_[i]->name);
      const DomainSource src{prog, i,
                             donors == nullptr ? nullptr
                                               : (*donors).at(i).get()};
      cs.compiled_.push_back(
          cs.domains_[i]->compile(cs.plan_, prog == nullptr ? nullptr : &src));
    }
    std::set<size_t> read;
    for (const auto &c : cs.compiled_)
      for (size_t id : c->views_read()) read.insert(id);
    for (const Node &n : N)
      for (size_t d : n.deps) read.insert(d);
    for (size_t id = 0; id < N.size(); ++id)
      if (N[id].kind == Kind::kBitView && !read.count(id))
        cs.plan_.mark_unread(id);
  };
  // Why some domain did not build from the program ("" when all did).
  auto misfit = [&]() -> std::string {
    for (size_t i = 0; i < cs.compiled_.size(); ++i)
      if (!cs.compiled_[i]->loaded())
        return "domain " + cs.domains_[i]->name +
               " does not build from its realized program: " +
               cs.compiled_[i]->misfit();
    return "";
  };
  // A fresh compile: each domain's compiler, the realized program built
  // from them, and the domains built from it, as on a hit.
  auto compile_fresh = [&] {
    build_domains(nullptr);
    {
      GH_COMPILE_REGION("realized program");
      ir::Program p = compiler::build_ir(cs);
      for (size_t i = 0; i < cs.compiled_.size(); ++i) {
        auto r = cs.compiled_[i]->realization();
        if (!r)
          fail("the circuit of domain " + cs.domains_[i]->name +
               " does not fit its realization record");
        p.realizations.push_back(std::move(*r));
      }
      program = std::make_shared<const ir::Program>(std::move(p));
    }
    GH_COMPILE_REGION("realize");
    // The compilers donate their batch kernels (DomainSource::donor).
    std::vector<std::unique_ptr<CompiledDomainBase<S>>> compilers =
        std::move(cs.compiled_);
    build_domains(program.get(), &compilers);
    const std::string why = misfit();
    if (!why.empty()) fail("compiler error: " + why);
  };
  phase_region.reset();
  phase_region.emplace(compiler::compile_times_on() ? "domains" : "");
  // A hit builds every domain from the entry's program. A program that
  // does not fit a domain leaves it unbuilt, so the system compiles afresh
  // and the entry is replaced.
  if (program) {
    build_domains(program.get());
    if (const std::string why = misfit(); !why.empty()) {
      cs.cache_.kind = CacheKind::kDiscarded;
      cs.cache_.reason = why;
      entry.reset();
      program.reset();
    }
  }
  if (!program) compile_fresh();
  phase_region.reset();
  phase_region.emplace(compiler::compile_times_on() ? "back" : "");

  // Pad dependencies: no message
  // may depend, through any chain of reads, on its own pad or the pad of a
  // later message. A public message t = x + P depends on P. Challenges carry no
  // pad dependency.
  std::vector<std::set<size_t>> pads(N.size());
  for (size_t id = 0; id < N.size(); ++id) {
    const Node &n = N[id];
    if (n.kind == Kind::kPad) {
      pads[id].insert(id);
      continue;
    }
    if (n.kind == Kind::kChallenge) continue;
    for (size_t d : n.deps) pads[id].insert(pads[d].begin(), pads[d].end());
    if (n.kind == Kind::kPublicMessage) {
      const size_t x = n.deps.at(0);
      // The pad is allocated above, possibly after this node.
      const size_t p = static_cast<size_t>(pad_of[x]);
      pads[id].insert(p);
    }
  }
  // Public messages read auto pads with larger ids: one more pass so that
  // later readers see them.
  for (size_t id = 0; id < N.size(); ++id) {
    if (N[id].kind == Kind::kChallenge || N[id].kind == Kind::kPad) continue;
    for (size_t d : N[id].deps) pads[id].insert(pads[d].begin(), pads[d].end());
  }
  // Message order: late variables by (phase, declaration).
  std::map<size_t, size_t> msg_of_pad;
  for (size_t j = 0; j < messages.size(); ++j)
    msg_of_pad[static_cast<size_t>(pad_of[messages[j]])] = j;
  auto check_message = [&](size_t j, const std::string &what,
                           const std::set<size_t> &dep_pads) {
    for (size_t p : dep_pads) {
      // A key pad masks no message: drawn before every message.
      if (N[p].key_pad) continue;
      const size_t k = msg_of_pad.at(p);
      if (k == j) fail("message " + what + " depends on its own pad '" +
                       N[p].name + "'");
      if (k > j)
        fail("message " + what + " depends on the pad '" + N[p].name +
             "' of the later message '" + N[messages[k]].name + "'");
    }
  };
  for (size_t j = 0; j < messages.size(); ++j)
    check_message(j, "'" + N[messages[j]].name + "'", pads[messages[j]]);
  // A generator that is not a message reads a pad (through pad copies and
  // what is computed from them) only after the pad's message is formed: the
  // prover runs generators in (phase, declaration) order and forms each
  // message right after its value. A pad copy itself is filled by the core.
  for (size_t id = 0; id < n0; ++id) {
    if (N[id].kind != Kind::kAdvice || pad_of[id] >= 0) continue;
    for (size_t p : pads[id]) {
      if (N[p].key_pad) continue;
      const size_t m = messages[msg_of_pad.at(p)];
      if (phase[m] > phase[id] || (phase[m] == phase[id] && m > id))
        fail("generator '" + N[id].name + "' reads the pad '" + N[p].name +
             "' of the message '" + N[m].name + "', which is formed after "
             "it; a generator reads a pad (through pad_copy) only after the "
             "pad's message");
    }
  }
  // The other masked messages pass the check by construction. Each
  // domain's batch reductions, GKR reduction and packing measurements come
  // after every late message in the transcript, so every graph pad they
  // depend on masks an earlier message. Their own pads (batch pads, GKR
  // pads, packing masks) are core-internal: drawn fresh per proof, never
  // graph nodes, and read by no generator.

  // System description and digest.
  const auto &scopes = s.graph().scopes;
  auto describe = [&] {
    // The description's bytes go to the hash a megabyte at a time. A
    // domain writes its description whole, which can exceed what one
    // SHA256::Update takes (INT_MAX bytes: the Keccak comparison's perms
    // preset at 256 permutations, its output words as affine rows), so
    // flush hashes it in pieces of a megabyte; the digest is the same.
    std::vector<uint8_t> descr;
    Hash h;
    auto flush = [&] {
      constexpr size_t kPiece = size_t(1) << 20;
      for (size_t at = 0; at < descr.size(); at += kPiece)
        h.Update(descr.data() + at, std::min(kPiece, descr.size() - at));
      descr.clear();
    };
    cs.public_inputs_.clear();
    put_str(descr, cs.label_);
    put_u64(descr, N.size());
    for (size_t id = 0; id < N.size(); ++id) {
      const Node &n = N[id];
      if (descr.size() >= (size_t(1) << 20)) flush();
      put_u64(descr, static_cast<uint64_t>(n.kind));
      put_str(descr, n.name);
      // A host input has bytes, no field.
      const std::vector<uint8_t> &field = field_identity(n);
      put_u64(descr, field.size());
      descr.insert(descr.end(), field.begin(), field.end());
      put_u64(descr, static_cast<uint64_t>(n.domain + 1));
      put_u64(descr, n.n);
      // A statement bound sets bit 24 and follows as two words: a system
      // without one keeps its description.
      put_u64(descr, static_cast<uint64_t>(n.type.base) |
                         (static_cast<uint64_t>(n.type.degree) << 8) |
                         (n.stmt_bound != 0 ? uint64_t(1) << 24 : 0));
      if (n.stmt_bound != 0) {
        put_u64(descr, static_cast<uint64_t>(n.stmt_bound));
        put_u64(descr, static_cast<uint64_t>(n.stmt_bound >> 64));
      }
      put_u64(descr, phase[id]);
      put_u64(descr, static_cast<uint64_t>(pad_of[id] + 1));
      // A subfield pad's degree in the second byte: 0 (the designated
      // subfield) leaves the description of every earlier system unchanged.
      // A zero pad (Node::zero_pad) sets bit 24 and a key pad
      // (Node::key_pad) bit 25: unset in every earlier system.
      put_u64(descr, static_cast<uint64_t>(n.pad_space) |
                         (static_cast<uint64_t>(n.pad_degree) << 8) |
                         (n.zero_pad ? uint64_t(1) << 24 : 0) |
                         (n.key_pad ? uint64_t(1) << 25 : 0));
      put_u64(descr, n.deps.size());
      for (size_t d : n.deps) put_u64(descr, d);
      put_u64(descr, n.tests.size());
      for (size_t t : n.tests) put_u64(descr, t);
      put_str(descr, n.sampler);
      // The values a challenge's excluded set reads: only for the sampler
      // "field-minus-tables", so every other description is unchanged.
      if (!n.excludes.empty()) {
        put_u64(descr, n.excludes.size());
        for (size_t x : n.excludes) put_u64(descr, x);
      }
      put_u64(descr, n.descr.size());
      descr.insert(descr.end(), n.descr.begin(), n.descr.end());
      if (n.kind == Kind::kPublicInput) cs.public_inputs_.push_back(id);
    }
    for (const auto &c : cs.compiled_) {
      flush();
      c->describe(descr);
    }
    // The compile profile and each lowering's description.
    put_str(descr, s.lowered_with() ? s.lowered_with()->name : std::string());
    put_u64(descr, s.lowered_with() ? s.lowered_with()->version : 0);
    put_u64(descr, s.summaries().size());
    for (const auto &[nm, sum] : s.summaries()) {
      put_str(descr, nm);
      put_u64(descr, sum.descr.size());
      descr.insert(descr.end(), sum.descr.begin(), sum.descr.end());
    }
    // The scopes, names and parameters (absent from a system without one, so
    // its description is unchanged; the encoding stays injective because
    // every earlier part is self-delimiting).
    if (!scopes.empty()) {
      put_u64(descr, scopes.size());
      for (const auto &[nm, params] : scopes) {
        put_str(descr, nm);
        put_u64(descr, params.size());
        descr.insert(descr.end(), params.begin(), params.end());
      }
    }
    flush();
    cs.digest_.resize(Hash::kDigestSize);
    h.DigestData(cs.digest_.data());
  };
  phase_region.reset();
  phase_region.emplace(compiler::compile_times_on() ? "describe and digest" : "");
  describe();
  phase_region.reset();

  // A hit: the restored system's digest is the stored one. Otherwise the
  // domains compile afresh and their entry replaces the stored one.
  if (entry) {
    if (entry->digest == cs.digest_) {
      cs.cache_.kind = CacheKind::kHit;
    } else {
      cs.cache_.kind = CacheKind::kDiscarded;
      cs.cache_.reason =
          "the restored system's digest differs from the stored one";
      compile_fresh();
      describe();
    }
  }
  cs.program_ = program;
  phase_region.emplace(compiler::compile_times_on() ? "store" : "");
  if (cache.on() && cs.cache_.kind != CacheKind::kHit) {
    std::string why = uncacheable;
    compiler::CacheEntry fresh;
    fresh.digest = cs.digest_;
    fresh.program = ir::write_program(*program);
    if (why.empty())
      why = compiler::write_file(
          cache.dir, cs.cache_.file,
          compiler::entry_bytes(key, fresh));
    if (!why.empty()) {
      cs.cache_.kind = CacheKind::kNotStored;
      cs.cache_.reason = why;
    } else if (cs.cache_.kind != CacheKind::kDiscarded) {
      cs.cache_.kind = CacheKind::kStored;
    }
  }

  phase_region.reset();
  if (compiler::compile_times_on() && cache.on()) {
    static const char *kinds[] = {"off", "hit", "stored", "not-stored",
                                  "discarded"};
    std::fprintf(stderr, "GH_CACHE system=%s outcome=%s file=%s reason=%s\n",
                 s.system_name().c_str(),
                 kinds[static_cast<int>(cs.cache_.kind)],
                 cs.cache_.file.c_str(), cs.cache_.reason.c_str());
  }
  phase_region.emplace(compiler::compile_times_on() ? "report" : "");
  // Compile report.
  std::ostringstream o;
  o << "system " << s.system_name() << ": phases 1.." << K << "\n";
  if (s.lowered_with())
    o << "  profile " << s.lowered_with()->name << " v"
      << s.lowered_with()->version << "\n";
  for (const auto &[nm, sum] : s.summaries()) {
    o << "  lowering " << nm << "\n";
    for (const auto &l : sum.report) o << "    " << l << "\n";
  }
  for (const auto &c : cs.compiled_) o << c->report();
  // Node lines grouped by scope: the root's, then each scope's in
  // declaration order (a node belongs to the longest scope prefixing its
  // name).
  std::vector<int> scope_of(N.size(), -1);
  for (size_t id = 0; id < N.size(); ++id) {
    size_t best = 0;
    for (size_t k = 0; k < scopes.size(); ++k) {
      const std::string pre = scopes[k].first + ".";
      if (N[id].name.rfind(pre, 0) == 0 && pre.size() > best) {
        best = pre.size();
        scope_of[id] = int(k);
      }
    }
  }
  std::vector<size_t> order;
  for (int k = -1; k < int(scopes.size()); ++k)
    for (size_t id = 0; id < N.size(); ++id)
      if (scope_of[id] == k) order.push_back(id);
  int printed_scope = -1;
  for (size_t id : order) {
    const Node &n = N[id];
    if (scope_of[id] != printed_scope) {
      printed_scope = scope_of[id];
      o << "  scope " << scopes[size_t(printed_scope)].first << "\n";
    }
    o << "  [" << id << "] " << kind_name(n.kind) << " " << n.name;
    if (n.domain >= 0) o << " @" << cs.domains_[n.domain]->name;
    o << " n=" << n.n;
    if (n.kind == Kind::kPad)
      o << " space=" << space_name(n.pad_space)
        << (n.pad_degree != 0 ? " GF<" + std::to_string(n.pad_degree) + ">"
                              : std::string())
        << (n.auto_pad ? " (auto)" : "") << (n.zero_pad ? " (zero)" : "")
        << (n.key_pad ? " (key)" : "");
    else if (n.kind != Kind::kChallenge && !is_public(n.kind) &&
             n.kind != Kind::kHostInput)
      o << " type=" << type_name(n.type);
    if (n.cached) o << " cached (setup)";
    if (n.stmt_bound != 0) o << " bound=" << bound_str(n.stmt_bound);
    // Subfield membership comes from the domain's relative packing and its
    // subfield step; a domain without them commits no subfield cell.
    const bool subfield =
        n.kind == Kind::kPad
            ? cs.pad_space(id) == Space::kSubfield
            : (n.kind != Kind::kChallenge && !is_public(n.kind) &&
               n.type.base == Base::kSubfield);
    if (subfield)
      o << " checked (Subfield membership: relative packing)";
    o << " phase=" << phase[id];
    if (cs.plan_.late(id)) o << " LATE pad=" << pad_of[id];
    if (n.kind == Kind::kChallenge) {
      o << " sampler=" << n.sampler << " field=";
      const DomainBase<S> *fd = nullptr;
      for (const DomainBase<S> *d : cs.domains_)
        if (d->field_id == n.field && d->fobj == n.fobj) {
          fd = d;
          break;
        }
      if (fd)
        o << fd->field_name();
      else
        o << "#" << n.field;
      o << " by=" << n.origin << " tests=";
      for (size_t i = 0; i < n.tests.size(); ++i)
        o << (i ? "," : "") << n.tests[i];
    }
    o << "\n";
  }
  o << degree_lines;
  size_t late_bytes = 0;
  for (size_t x : messages) late_bytes += cs.msg_bytes(x);
  o << "  late-variable bytes: " << late_bytes << " in " << messages.size()
    << " messages\n";
  cs.report_ = o.str();
  // The compile_report switch (util/diagnostics.h) prints each compiled
  // system's report.
  if (diagnostics::options().compile_report)
    std::fprintf(stderr, "GH_REPORT_BEGIN\n%sGH_REPORT_END\n",
                 cs.report_.c_str());
  return owner;
}

// compile(S, OPTIONS) with default options, or with the compile cache CACHE.
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    const BasicConstraintSystem<Hash, Fs...> &s) {
  return compile(s, CompileOptions{});
}
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    const BasicConstraintSystem<Hash, Fs...> &s, const CompileCache &cache) {
  CompileOptions options;
  options.cache = cache;
  return compile(s, options);
}

// Lowers S in place under the profile P, once per system, and compiles it
// with OPTIONS. A second call with the same profile (name, version,
// unsound_no_mac, unsound_per_chunk_mac) reuses the lowered system; a
// different profile is a CompileError.
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    BasicConstraintSystem<Hash, Fs...> &s, const CompileProfile &p,
    const CompileOptions &options) {
  using S = FieldSet<Hash, Fs...>;
  if (!s.failure_.empty())
    fail("an earlier lowering of this system failed: " + s.failure_);
  if (s.profile_) {
    if (s.profile_->name != p.name || s.profile_->version != p.version)
      fail("system " + s.system_name() + " was lowered under the profile " +
           s.profile_->name + " v" + std::to_string(s.profile_->version) +
           "; it cannot be lowered again under " + p.name + " v" +
           std::to_string(p.version));
    if (s.profile_->unsound_no_mac != p.unsound_no_mac)
      fail("system " + s.system_name() + " was lowered " +
           (s.profile_->unsound_no_mac ? "with" : "without") +
           " the MAC ablation; it cannot be lowered again " +
           (p.unsound_no_mac ? "with" : "without") + " it");
    if (s.profile_->unsound_per_chunk_mac != p.unsound_per_chunk_mac)
      fail("system " + s.system_name() + " was lowered " +
           (s.profile_->unsound_per_chunk_mac ? "with" : "without") +
           " the per-chunk MAC ablation; it cannot be lowered again " +
           (p.unsound_per_chunk_mac ? "with" : "without") + " it");
    size_t req = 0;
    for (const auto &d : s.domains()) req += d->pending_requests();
    if (req != 0 || s.pending_equalities() != 0)
      fail("system " + s.system_name() + " was lowered; its " + std::to_string(req) +
           " range requests and " + std::to_string(s.pending_equalities()) +
           " equalities declared since are not lowered");
  } else {
    s.profile_ = p;
    compiler::compile_times_system(s.system_name());
    GH_COMPILE_REGION("lowering");
    try {
      compiler::ConstraintSystemBuilder<S> b(s, *s.profile_);
      compiler::GroupedLowering<S> grouped;
      compiler::MacEqualityLowering<S> mac;
      compiler::ModLowering<S> mod(false);
      compiler::ModLowering<S> int_equal(true);
      compiler::ConvLowering<S> conv;
      compiler::PublicExprLowering<S> public_expr;
      compiler::RangeLowering<S> range;
      for (compiler::BasicLowering<S> *l :
           std::initializer_list<compiler::BasicLowering<S> *>{
               &grouped, &mac, &mod, &int_equal, &conv, &public_expr,
               &range}) {
        s.lowering_ = l->name();
        const size_t first = s.graph().nodes.size();
        GH_COMPILE_REGION(l->name());
        l->rewrite(b);
        s.mutable_graph().records.lowered.push_back(
            {l->name(), first, s.graph().nodes.size()});
        s.lowering_.clear();
        if (l == &mod && !mod.ran()) continue;
        if (l == &grouped && !grouped.ran()) continue;
        if (l == &int_equal && !int_equal.ran()) continue;
        if (l == &conv && !conv.ran()) continue;
        if (l == &public_expr && !public_expr.ran()) continue;
        s.summaries_.push_back({l->name(), l->summary()});
      }
    } catch (const CompileError &e) {
      s.lowering_.clear();
      s.failure_ = e.what();
      throw;
    }
  }
  return compile(static_cast<const BasicConstraintSystem<Hash, Fs...> &>(s),
                 options);
}

// compile(S, P, OPTIONS) with default options, or with the compile cache
// CACHE.
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    BasicConstraintSystem<Hash, Fs...> &s, const CompileProfile &p) {
  return compile(s, p, CompileOptions{});
}
template <class Hash, class... Fs>
std::unique_ptr<BasicCompiledSystem<FieldSet<Hash, Fs...>>> compile(
    BasicConstraintSystem<Hash, Fs...> &s, const CompileProfile &p,
    const CompileCache &cache) {
  CompileOptions options;
  options.cache = cache;
  return compile(s, p, options);
}

// ------------------------------------------------------------- runtime --

template <class S>
class BasicPrepared {
 public:
  using Hash = typename S::Hash;
  using Transcript = BasicTranscript<Hash>;
  using Value = typename S::Value;
  using Assignment = BasicAssignment<S>;
  using ProveOptions = BasicProveOptions<S>;
  // A test hook: changes a cached public computation of this statement
  // after the setup computes it (a verifier holding another value).
  using SetupTamper = std::function<void(size_t id, Value &value)>;
  BasicPrepared(const BasicCompiledSystem<S> &cs, const Assignment &st,
                const SetupTamper &tamper = nullptr)
      : cs_(cs) {
    statement(st);
    if (rejected_.empty()) setup(tamper);
  }

  // The time of the setup: the cached public computations of this
  // statement (zero when every one was memoized).
  double setup_ms() const { return setup_ms_; }

 private:
  void statement(const Assignment &st) {
    const auto &cs = cs_;
    auto reject = [&](const Node &n, long code) {
      if (!rejected_.empty() || code == kAccepted) return;
      rejected_ = n.name;
      rejected_row_ = code >= 0 ? size_t(code) : SIZE_MAX;
    };
    for (size_t id : cs.public_inputs_) {
      const Node &n = cs.nodes_[id];
      if (n.type.base == Base::kBytes) {
        // Absorbed as its bytes packed into elements of its field.
        const auto *b = st.find_bytes(id);
        if (b == nullptr || b->size() != n.n)
          throw std::runtime_error("statement value '" + n.name +
                                   "' missing or of the wrong length");
        bytes_[id] = *b;
        statement_[id] = with_field<S>(n, [&](const auto &f) {
          using F = std::decay_t<decltype(f)>;
          return Value(S::template wrap<F>(pack_bytes(f, *b)));
        });
        if (cs.gens_[id].accepts_bytes)
          reject(n, cs.gens_[id].accepts_bytes(*b));
        continue;
      }
      const Value *v = st.find(id);
      if (v == nullptr || size_of(*v) != n.n)
        throw std::runtime_error("statement value '" + n.name +
                                 "' missing or of the wrong length");
      statement_[id] = *v;
      const bool typed = with_field<S>(n, [&](const auto &f) {
        using F = std::decay_t<decltype(f)>;
        return FieldValues<F>::in_type(f, S::template get<F>(*v), n.type);
      });
      if (!typed) reject(n, kRejected);
      if (cs.gens_[id].accepts) reject(n, cs.gens_[id].accepts(*v));
      if (n.stmt_bound != 0 && !below(n, *v)) reject(n, kRejected);
    }
  }

  // Whether every coordinate of X, a value of node N, lies in N's
  // statement bound.
  bool below(const Node &n, const Value &x) const {
    return with_field<S>(n, [&](const auto &f) {
      using F = std::decay_t<decltype(f)>;
      return FieldValues<F>::below(f, S::template get<F>(x), n.stmt_bound);
    });
  }

  // The cached public computations, memoized in the compiled system by the
  // digest of the node and its dependencies' values.
  void setup(const SetupTamper &tamper) {
    using Clock = std::chrono::steady_clock;
    const auto t0 = Clock::now();
    const auto &N = cs_.nodes_;
    ValueStore<S> v(N.size());
    for (const auto &[id, x] : statement_) v.v[id] = x;
    v.bytes = bytes_;
    for (size_t id = 0; id < N.size(); ++id) {
      if (N[id].kind == Kind::kConstant && cs_.gens_[id].eval)
        v.v[id] = cs_.gens_[id].eval(v);
      if (!N[id].cached) continue;
      Hash h;
      std::vector<uint8_t> key;
      put_u64(key, id);
      for (size_t d : N[id].deps) {
        const auto b = with_field<S>(N[d], [&](const auto &f) {
          using F = std::decay_t<decltype(f)>;
          return FieldValues<F>::bytes(f, S::template get<F>(v.value(d)));
        });
        put_u64(key, b.size());
        key.insert(key.end(), b.begin(), b.end());
      }
      h.Update(key.data(), key.size());
      std::vector<uint8_t> dg(Hash::kDigestSize);
      h.DigestData(dg.data());
      auto it = cs_.memo_.find(dg);
      if (it == cs_.memo_.end()) {
        typename S::Value x;
        // A computation that refuses the statement: a malformed statement,
        // not memoized.
        try {
          x = cs_.gens_[id].eval(v);
        } catch (const StatementRefused &) {
          rejected_ = N[id].name;
          rejected_row_ = SIZE_MAX;
          break;
        }
        const bool typed = with_field<S>(N[id], [&](const auto &f) {
          using F = std::decay_t<decltype(f)>;
          return FieldValues<F>::in_type(f, S::template get<F>(x), N[id].type);
        });
        if (!typed)
          throw std::runtime_error("public computation '" + N[id].name +
                                   "' is not of its declared type");
        it = cs_.memo_.emplace(dg, std::move(x)).first;
      }
      v.held[id] = &it->second;
      cached_[id] = &it->second;
      // The test hook replaces this statement's copy, never the memo's.
      if (tamper) {
        auto x = std::make_shared<Value>(it->second);
        tamper(id, *x);
        check_size(id, *x);
        v.held[id] = x.get();
        cached_[id] = x.get();
        tampered_.push_back(std::move(x));
      }
      // A cached value outside its statement bound: a malformed statement.
      if (N[id].stmt_bound != 0 && !below(N[id], *cached_[id])) {
        rejected_ = N[id].name;
        rejected_row_ = SIZE_MAX;
        break;
      }
    }
    setup_ms_ =
        std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
  }

 public:

  // The statement value its codec refused ("" when every value is well
  // formed), and the row a per-row codec refused (SIZE_MAX otherwise).
  const std::string &rejected_statement() const { return rejected_; }
  size_t rejected_row() const { return rejected_row_; }

  std::vector<uint8_t> prove(const Assignment &priv, RandomEngine &caller_rng,
                             const ProveOptions &opt = {}) const {
    // The fixed_seed seam: one seeded stream per proof.
    internal::SeededStream seeded(opt.fixed_seed.value_or(0));
    RandomEngine &rng = opt.fixed_seed ? seeded : caller_rng;
    using Clock = std::chrono::steady_clock;
    auto ms = [](Clock::time_point t0) {
      return std::chrono::duration<double, std::milli>(Clock::now() - t0)
          .count();
    };
    if (!rejected_.empty())
      throw std::runtime_error("prover: the statement value '" + rejected_ +
                               "' is not well formed");
    ProveTimes times;
    // The profiler (util/prover_profile.h): one session per section of the
    // proof, named gh.p.<section>.
    profiling::Session all("gh.p.all", "main", 0, 0);
    std::optional<profiling::Session> sec;
    sec.emplace("gh.p.setup", "main", 0, 0);
    const auto pool = make_pool(opt.multithreaded);
    // The kernels' data-parallel chunks run on the pool (util/parallel.h).
    parallel::Scope par_scope(pool.get());
    const auto &N = cs_.nodes_;
    ValueStore<S> v(N.size());
    const BasicProofSeed<Hash> seed = BasicProofSeed<Hash>::draw(rng);
    for (const auto &[id, x] : statement_) v.v[id] = x;
    for (const auto &[id, b] : bytes_) v.bytes[id] = b;
    for (const auto &[id, x] : cached_) v.held[id] = x;

    // Pads, then phase-0 values.
    auto t0 = Clock::now();
    for (size_t id = 0; id < N.size(); ++id)
      if (N[id].kind == Kind::kPad) {
        const Space sp = cs_.pad_space(id);
        const uint16_t dg = N[id].pad_degree;
        const size_t n = N[id].n;
        // A zero pad leaves its message unmasked (Node::zero_pad).
        const bool zero = N[id].zero_pad;
        v.v[id] = with_field<S>(N[id], [&](const auto &f) {
          using F = std::decay_t<decltype(f)>;
          return S::template wrap<F>(
              zero ? std::vector<typename F::Elt>(n, f.zero())
                   : FieldValues<F>::sample(f, sp, n, rng, dg));
        });
      }
    times.commit += ms(t0);
    // Phase 0's constants and public computations (the statement's, which
    // the verifier computes inside its own time) are statement work: in
    // COMMIT, before the generators.
    sec.reset();
    sec.emplace("gh.p.public0", "main", 0, 0);
    t0 = Clock::now();
    evaluate(0, v, /*prover=*/true, opt, Part::kPublic);
    times.commit += ms(t0);
    sec.reset();
    sec.emplace("gh.p.witness0", "main", 0, 0);
    t0 = Clock::now();
    // The profiler's per-generator times (util/prover_profile.h).
    std::optional<profiling::GeneratorSession> gens;
    gens.emplace("gh.p.witness0");
    const auto ti = profiling::generator_times ? Clock::now() : t0;
    for (size_t id = 0; id < N.size(); ++id) {
      if (N[id].kind == Kind::kHostInput) {
        const auto *b = priv.find_bytes(id);
        if (b == nullptr || b->size() != N[id].n)
          throw std::runtime_error("host input '" + N[id].name +
                                   "' missing or of the wrong length");
        v.bytes[id] = *b;
        continue;
      }
      if (N[id].kind != Kind::kPrivateInput) continue;
      const Value *x = priv.find(id);
      if (x == nullptr) throw std::runtime_error("missing private input");
      v.v[id] = *x;
      check_value(id, v.v[id]);
    }
    if (profiling::generator_times)
      profiling::generator_times->add("<private inputs>", "input", ms(ti));
    {
      const WitnessRun run;
      evaluate(0, v, /*prover=*/true, opt, Part::kPrivate);
    }
    times.witness += ms(t0);
    gens.reset();
    sec.reset();
    sec.emplace("gh.p.statement", "main", 0, 0);

    t0 = Clock::now();
    Transcript tp(reinterpret_cast<const uint8_t *>(cs_.label_.data()),
                  cs_.label_.size(), seed);
    begin(v, tp, opt.zero_digest);
    std::vector<std::unique_ptr<DomainProverBase<S>>> provers;
    for (const auto &c : cs_.compiled_) provers.push_back(c->prover());
    times.domain_commit.assign(provers.size(), 0);
    times.domain_prove.assign(provers.size(), 0);
    // Each domain's commitment: its computation, then its transcript
    // writes, in domain order. Single-threaded the computations draw from
    // RNG in domain order. On the pool each draws from its thread's engine
    // over OpenSSL's CSPRNG (thread_random, threads.h), so no engine is
    // shared between threads; the proof's bytes then depend on the
    // schedule and may differ between runs and modes.
    sec.reset();
    sec.emplace("gh.p.commit", "main", 0, 0);
    internal::TaskPool *commit_pool =
        opt.serial_commitments ? nullptr : pool.get();
    internal::run_tasks(commit_pool, provers.size(), [&](size_t d) {
      const std::string fname = cs_.domains_[d]->field_name();
      profiling::Session ses("gh.p.commit.domain", fname.c_str(), d, 0);
      const auto td = Clock::now();
      if (commit_pool != nullptr && provers.size() > 1) {
        provers[d]->commit_compute(v, thread_random());
      } else {
        provers[d]->commit_compute(v, rng);
      }
      times.domain_commit[d] += ms(td);
    }, commit_first());
    sec.reset();
    sec.emplace("gh.p.commit_write_ldt", "main", 0, 0);
    for (size_t d = 0; d < provers.size(); ++d) {
      const auto td = Clock::now();
      provers[d]->commit_write(tp);
      times.domain_commit[d] += ms(td);
    }
    for (size_t d = 0; d < provers.size(); ++d) {
      const auto td = Clock::now();
      provers[d]->ldt(tp);
      times.domain_commit[d] += ms(td);
    }
    times.commit += ms(t0);
    sec.reset();
    sec.emplace("gh.p.phases", "main", 0, 0);

    for (size_t k = 1; k <= cs_.K_; ++k) {
      t0 = Clock::now();
      const std::string over = challenges(k, v, tp);
      if (!over.empty())
        throw std::runtime_error("prover: challenge '" + over +
                                 "' read past its stream budget");
      times.prove += ms(t0);
      t0 = Clock::now();
      evaluate(k, v, /*prover=*/true, opt);
      const double late = ms(t0);
      times.late += late;
      times.prove += late;
      t0 = Clock::now();
      absorb_messages(k, v, tp);
      times.prove += ms(t0);
    }
    // The prover's check that the predicates hold covers the range requests
    // before any domain proves: an affine row or a lookup that a violated
    // request breaks is otherwise found only by the verifier.
    sec.reset();
    sec.emplace("gh.p.unmet_range", "main", 0, 0);
    if (opt.require_satisfied) {
      t0 = Clock::now();
      for (const auto &c : cs_.compiled_) {
        const std::string r = c->unmet_range(v);
        if (!r.empty())
          throw std::runtime_error("prover: the range request '" + r +
                                   "' does not hold");
      }
      times.witness += ms(t0);
    }
    t0 = Clock::now();
    // Every phase message precedes every domain's reductions and opening, and
    // a domain's opening follows its own reductions (inside prove), so each
    // opening follows every message its rows read. After the phases the
    // transcript forks: each domain proves on its own branch
    // (transcript_fork.h), on the pool when multi-threaded, the last domain
    // on this thread.
    sec.reset();
    sec.emplace("gh.p.post_fork", "main", 0, 0);
    const auto sub = fork::domains(tp, field_names());
    const auto shape = profile_shape();
    std::vector<uint8_t> proved(provers.size(), 0);
    internal::run_tasks(pool.get(), provers.size(), [&](size_t d) {
      typename DomainProverBase<S>::BatchTamper bt;
      if (opt.batch_tamper)
        bt = [&opt, d](size_t b, Value &m) { opt.batch_tamper(d, b, m); };
      typename DomainProverBase<S>::BatchTamper bw;
      if (opt.batch_words)
        bw = [&opt, d](size_t b, Value &m) { opt.batch_words(d, b, m); };
      const std::string fname = cs_.domains_[d]->field_name();
      profiling::Session ses("gh.prove.post", fname.c_str(), shape[d].first,
                              shape[d].second);
      const auto td = Clock::now();
      proved[d] = provers[d]->prove(v, *sub[d], opt.require_satisfied, bt, bw,
                                    opt.bit_phase_swap_round, pool.get());
      times.domain_prove[d] += ms(td);
    });
    for (uint8_t ok : proved)
      if (!ok) throw std::runtime_error("prover: a domain failed to prove");
    times.prove += ms(t0);
    if (opt.times != nullptr) *opt.times = times;
    sec.reset();
    sec.emplace("gh.p.serialize", "main", 0, 0);

    std::vector<uint8_t> out(seed.bytes, seed.bytes + sizeof(seed.bytes));
    for (size_t x : cs_.messages_) {
      const Space sp = cs_.msg_space(x);
      const uint16_t dg = cs_.msg_degree(x);
      with_field<S>(N[x], [&](const auto &f) {
        using F = std::decay_t<decltype(f)>;
        FieldValues<F>::encode(f, out, S::template get<F>(v.msg[x]), sp, dg);
      });
    }
    if (opt.domain_bytes != nullptr) opt.domain_bytes->clear();
    for (auto &p : provers) {
      const size_t before = out.size();
      p->write(out);
      if (opt.domain_bytes != nullptr)
        opt.domain_bytes->push_back(out.size() - before);
    }
    if (opt.fixed_seed) internal::print_proof_digest(out);
    return out;
  }

  // TIMES, when set, receives each domain's verification time and the
  // proof's parsing time.
  bool verify(const std::vector<uint8_t> &proof,
              VerifyTimes *times = nullptr,
              bool multithreaded = default_multithreaded()) const {
    using Clock = std::chrono::steady_clock;
    auto ms = [](Clock::time_point t0) {
      return std::chrono::duration<double, std::milli>(Clock::now() - t0)
          .count();
    };
    // A malformed statement has no proof.
    if (!rejected_.empty()) return false;
    profiling::Session all("gh.v.all", "main", 0, 0);
    const auto pool = make_pool(multithreaded);
    parallel::Scope par_scope(pool.get());
    const auto &N = cs_.nodes_;
    ValueStore<S> v(N.size());
    const auto t_parse = Clock::now();
    ReadBuffer rb(proof);
    BasicProofSeed<Hash> seed;
    if (!seed.read(rb)) return false;
    for (size_t x : cs_.messages_) {
      const Space sp = cs_.msg_space(x);
      const uint16_t dg = cs_.msg_degree(x);
      const bool ok = with_field<S>(N[x], [&](const auto &f) {
        using F = std::decay_t<decltype(f)>;
        auto t = FieldValues<F>::decode(f, rb, N[x].n, sp, dg);
        if (!t) return false;
        v.msg[x] = S::template wrap<F>(std::move(*t));
        return true;
      });
      if (!ok) return false;
    }
    double parse = ms(t_parse);
    std::vector<std::unique_ptr<DomainVerifierBase<S>>> vs;
    for (const auto &c : cs_.compiled_) vs.push_back(c->verifier());
    const auto t_sections = Clock::now();
    for (auto &d : vs)
      if (!d->read(rb)) return false;
    if (rb.remaining() != 0) return false;
    parse += ms(t_sections);

    Transcript tv(reinterpret_cast<const uint8_t *>(cs_.label_.data()),
                  cs_.label_.size(), seed);
    begin(v, tv);
    for (const auto &[id, b] : bytes_) v.bytes[id] = b;
    for (const auto &[id, x] : cached_) v.held[id] = x;
    ProveOptions none;
    evaluate(0, v, /*prover=*/false, none);
    std::vector<double> dt(vs.size(), 0);
    std::optional<profiling::Session> sec;
    sec.emplace("gh.v.recv_ldt", "main", 0, 0);
    for (size_t d = 0; d < vs.size(); ++d) {
      const auto td = Clock::now();
      vs[d]->recv(tv);
      dt[d] += ms(td);
    }
    for (size_t d = 0; d < vs.size(); ++d) {
      const auto td = Clock::now();
      vs[d]->ldt(tv);
      dt[d] += ms(td);
    }
    sec.reset();
    sec.emplace("gh.v.phases", "main", 0, 0);
    for (size_t k = 1; k <= cs_.K_; ++k) {
      if (!challenges(k, v, tv).empty()) return false;
      evaluate(k, v, /*prover=*/false, none);
      absorb_messages(k, v, tv);
    }
    sec.reset();
    sec.emplace("gh.v.post_fork", "main", 0, 0);
    // The same fork as the prover's. Every branch runs to completion; the
    // proof accepts iff every domain verifies.
    const auto names = field_names();
    const auto sub = fork::domains(tv, names);
    const auto shape = profile_shape();
    std::vector<uint8_t> verified(vs.size(), 0);
    std::vector<double> post(vs.size(), 0);
    internal::run_tasks(pool.get(), vs.size(), [&](size_t d) {
      // The profiler: the domain's scopes, on whichever thread runs it.
      profiling::Session ses("gh.verify.post", names[d].c_str(),
                              shape[d].first, shape[d].second);
      const auto td = Clock::now();
      verified[d] = vs[d]->verify(v, *sub[d], pool.get());
      post[d] = ms(td);
    });
    bool ok = true;
    for (size_t d = 0; d < vs.size(); ++d) {
      ok = ok && verified[d] != 0;
      dt[d] += post[d];
    }
    if (times != nullptr) {
      times->domain = std::move(dt);
      times->domain_post = std::move(post);
      times->parse = parse;
    }
    return ok;
  }

 private:
  // Statement: circuit ids, public inputs, system digest.
  void begin(ValueStore<S> &v, Transcript &t, bool zero_digest = false) const {
    for (const auto &c : cs_.compiled_) t.write(c->circuit_id(), Hash::kDigestSize);
    for (const auto &[id, x] : statement_) {
      v.v[id] = x;
      const auto b = with_field<S>(cs_.nodes_[id], [&](const auto &f) {
        using F = std::decay_t<decltype(f)>;
        return FieldValues<F>::bytes(f, S::template get<F>(x));
      });
      t.write(b.data(), b.size());
    }
    if (zero_digest) {
      const std::vector<uint8_t> zeros(cs_.digest_.size(), 0);
      t.write(zeros.data(), zeros.size());
    } else {
      t.write(cs_.digest_.data(), cs_.digest_.size());
    }
  }

  // With the profiler on: each domain's batch count and GKR layer count (0
  // without GKR), which the PQ_PHASE gh.prove.post and gh.verify.post lines
  // print as inputs= and depth=; zeros when profiling is off.
  std::vector<std::pair<size_t, size_t>> profile_shape() const {
    if (!profiling::enabled())
      return std::vector<std::pair<size_t, size_t>>(cs_.compiled_.size(),
                                                    {0, 0});
    std::call_once(*cs_.shape_once_, [this] {
      cs_.shape_.assign(cs_.compiled_.size(), {0, 0});
      for (size_t d = 0; d < cs_.compiled_.size(); ++d) {
        const DomainPlan p = cs_.compiled_[d]->plan();
        cs_.shape_[d] = {p.batches.size(), p.layers};
      }
    });
    return cs_.shape_;
  }

  std::vector<std::string> field_names() const {
    std::vector<std::string> out;
    for (const auto *d : cs_.domains_) out.push_back(d->field_name());
    return out;
  }

  // The commitment that runs on the calling thread: the largest tableau's
  // (a commitment on a worker ran up to 1.6 times slower, so the longest
  // one stays on the caller).
  size_t commit_first() const {
    size_t best = 0;
    for (size_t d = 1; d < cs_.compiled_.size(); ++d)
      if (cs_.compiled_[d]->tableau_size() > cs_.compiled_[best]->tableau_size())
        best = d;
    return best;
  }

  // The multi-threaded mode's pool (threads.h); none single-threaded.
  std::unique_ptr<internal::TaskPool> make_pool(bool multithreaded) const {
    if (!multithreaded) return nullptr;
    // The domains, their branches and the kernels' chunks (util/parallel.h)
    // share one pool: min(available cores, kMaxThreads) threads, the
    // calling thread among them.
    const size_t n = std::min(internal::available_cores(), kMaxThreads);
    if (n < 2) return nullptr;
    return std::make_unique<internal::TaskPool>(n - 1);
  }
  static constexpr size_t kMaxThreads = 2 * parallel::kChunks;

  // A challenge stream with a test prefix (set_challenge_prefix):
  // the prefix's bytes, then the stream's.
  class PrefixedStream : public RandomEngine {
   public:
    PrefixedStream(const std::vector<uint8_t> &prefix, RandomEngine &rest)
        : prefix_(prefix), rest_(rest) {}
    void bytes(uint8_t *buf, size_t n) override {
      for (size_t i = 0; i < n; ++i) {
        if (at_ < prefix_.size()) {
          buf[i] = prefix_[at_];
        } else {
          rest_.bytes(buf + i, 1);
        }
        ++at_;
      }
    }
    size_t read() const { return at_; }

   private:
    const std::vector<uint8_t> &prefix_;
    RandomEngine &rest_;
    size_t at_ = 0;
  };

  // One challenge round: the phase's challenges, in declaration order, decoded
  // from consecutive bytes of the transcript's stream at one challenge point;
  // the next write absorbs the point's write-back. Each challenge after the
  // first grants the point the bytes the earlier ones read, so each
  // challenge may read as much as one point does.
  // Returns the label of a challenge whose stream ran past its budget, or
  // "".
  std::string challenges(size_t k, ValueStore<S> &v, Transcript &t) const {
    for (size_t id = 0; id < cs_.nodes_.size(); ++id) {
      const Node &n = cs_.nodes_[id];
      if (n.kind != Kind::kChallenge || cs_.plan_.phase[id] != k) continue;
      const size_t before = t.stats().read_bytes;
      const auto pre = cs_.prefix_.find(n.name);
      if (pre == cs_.prefix_.end()) {
        v.v[id] = cs_.gens_[id].sample(t, v);
      } else {
        PrefixedStream ps(pre->second, t);
        v.v[id] = cs_.gens_[id].sample(ps, v);
        cs_.drawn_[n.name] = {v.v[id], ps.read()};
      }
      // A stream read past its budget (fs_stream_budget) is an exhausted
      // transcript, which the prover refuses and the verifier rejects.
      if (t.exhausted()) return n.name;
      t.extend_point_budget(t.stats().read_bytes - before);
    }
    return "";
  }

  // The values evaluate() computes: every value, the constants and public
  // computations alone (which read only the statement, constants and other
  // public computations), or every other value.
  enum class Part { kAll, kPublic, kPrivate };
  // Every value of phase K in PART that this party computes, in declaration
  // order. The prover forms t = x + P right after each late x.
  void evaluate(size_t k, ValueStore<S> &v, bool prover,
                const ProveOptions &opt, Part part = Part::kAll) const {
    const auto &N = cs_.nodes_;
    for (size_t id = 0; id < N.size(); ++id) {
      const Node &n = N[id];
      if (cs_.plan_.phase[id] != k) continue;
      const bool pub =
          n.kind == Kind::kConstant || n.kind == Kind::kPublicCompute;
      if (part == Part::kPublic && !pub) continue;
      if (part == Part::kPrivate && pub) continue;
      switch (n.kind) {
        case Kind::kConstant:
          v.v[id] = cs_.gens_[id].eval(v);
          check_size(id, v.v[id]);
          break;
        case Kind::kPublicCompute: {
          if (n.cached) break;  // computed in the setup
          v.v[id] = cs_.gens_[id].eval(v);
          check_size(id, v.v[id]);
          const bool typed = with_field<S>(n, [&](const auto &f) {
            using F = std::decay_t<decltype(f)>;
            return FieldValues<F>::in_type(f, S::template get<F>(v.v[id]),
                                           n.type);
          });
          if (!typed)
            throw std::runtime_error("public computation '" + n.name +
                                     "' is not of its declared type");
          break;
        }
        case Kind::kPublicMessage:
          v.v[id] = v.msg[n.deps.at(0)];
          break;
        case Kind::kAdvice:
        case Kind::kDerived:
        case Kind::kBitView:
        case Kind::kPadCopy:
          if (!prover || cs_.plan_.is_unread(id)) break;
          if (profiling::generator_times) {
            const auto tg = profiling::Clock::now();
            v.v[id] = cs_.gens_[id].eval(v);
            static const char *const kinds[] = {"advice", "derived",
                                                "bitview", "padcopy"};
            profiling::generator_times->add(
                n.name,
                kinds[n.kind == Kind::kAdvice    ? 0
                      : n.kind == Kind::kDerived ? 1
                      : n.kind == Kind::kBitView ? 2
                                                 : 3],
                profiling::elapsed(tg));
          } else {
            v.v[id] = cs_.gens_[id].eval(v);
          }
          if (n.kind != Kind::kDerived) {
            if (opt.tamper) {
              opt.tamper(id, v.v[id]);
              // Later programs read the changed value from its elements.
              v.packed_bits.erase(id);
            }
            if (profiling::generator_times) {
              const auto tc = profiling::Clock::now();
              check_value(id, v.v[id]);
              profiling::generator_times->add("<type checks>", "check",
                                               profiling::elapsed(tc));
            } else {
              check_value(id, v.v[id]);
            }
          }
          if (cs_.plan_.late(id)) {
            const size_t p = static_cast<size_t>(cs_.plan_.pad_of[id]);
            // A late value of a declared subfield E has its message in E:
            // the honest prover's value lies there (no commitment checks
            // a late value's membership).
            if (n.type.base == Base::kSubfield && n.type.degree != 0) {
              const bool in = with_field<S>(n, [&](const auto &f) {
                using F = std::decay_t<decltype(f)>;
                return FieldValues<F>::in_type(
                    f, S::template get<F>(v.v[id]), n.type);
              });
              if (!in)
                throw std::runtime_error("value '" + n.name +
                                         "' is not of its declared type");
            }
            v.msg[id] = with_field<S>(n, [&](const auto &f) {
              using F = std::decay_t<decltype(f)>;
              return S::template wrap<F>(
                  FieldValues<F>::add(f, S::template get<F>(v.v[id]),
                                      S::template get<F>(v.v[p])));
            });
          }
          break;
        default:
          break;
      }
    }
  }

  void absorb_messages(size_t k, const ValueStore<S> &v, Transcript &t) const {
    for (size_t x : cs_.messages_) {
      if (cs_.plan_.phase[x] != k) continue;
      with_field<S>(cs_.nodes_[x], [&](const auto &f) {
        using F = std::decay_t<decltype(f)>;
        FieldValues<F>::absorb(f, t, S::template get<F>(v.msg[x]));
      });
    }
  }

  static size_t size_of(const Value &x) {
    return std::visit([](const auto &e) { return e.size(); }, x);
  }
  // A value's alternative is its node's field: a tamper hook that swaps it
  // is rejected here.
  void check_size(size_t id, const Value &x) const {
    if (x.index() != cs_.nodes_[id].field)
      throw std::runtime_error("value '" + cs_.nodes_[id].name +
                               "' lies in another field");
    if (size_of(x) != cs_.nodes_[id].n)
      throw std::runtime_error("value '" + cs_.nodes_[id].name +
                               "' has the wrong length");
  }
  void check_value(size_t id, const Value &x) const {
    check_size(id, x);
    const Node &n = cs_.nodes_[id];
    const bool typed = with_field<S>(n, [&](const auto &f) {
      using F = std::decay_t<decltype(f)>;
      return FieldValues<F>::has_type(f, S::template get<F>(x), n.type);
    });
    if (!typed)
      throw std::runtime_error("value '" + n.name +
                               "' is not of its declared type");
  }

  const BasicCompiledSystem<S> &cs_;
  std::map<size_t, Value> statement_;
  // In the compiled memo, or in TAMPERED_ (the setup's test hook).
  std::map<size_t, const Value *> cached_;
  std::vector<std::shared_ptr<const Value>> tampered_;
  std::map<size_t, std::vector<uint8_t>> bytes_;  // Bytes statements
  double setup_ms_ = 0;
  std::string rejected_;
  size_t rejected_row_ = SIZE_MAX;
};

template <class S>
BasicPrepared<S> BasicCompiledSystem<S>::prepare(
    const Assignment &statement) const {
  return BasicPrepared<S>(*this, statement);
}

template <class S>
BasicPrepared<S> BasicCompiledSystem<S>::prepare(
    const Assignment &statement,
    const std::function<void(size_t id, typename S::Value &value)> &tamper)
    const {
  return BasicPrepared<S>(*this, statement, tamper);
}

}  // namespace proofs::gordiehowe

// The lowerings: range requests and the cross-domain equality.
#include "gordiehowe/compiler/compiled_domain.h"  // IWYU pragma: export
#include "gordiehowe/compiler/mac.h"              // IWYU pragma: export
#include "gordiehowe/compiler/mod.h"              // IWYU pragma: export
#include "gordiehowe/compiler/public_expr.h"      // IWYU pragma: export
#include "gordiehowe/compiler/conv.h"             // IWYU pragma: export
#include "gordiehowe/compiler/range.h"            // IWYU pragma: export

// The realized program's builder, which reads the compiled system.
#include "gordiehowe/compiler/program_builder.h"

#endif  // PRIVACY_PROOFS_ZK_LIB_GORDIEHOWE_SYSTEM_H_
