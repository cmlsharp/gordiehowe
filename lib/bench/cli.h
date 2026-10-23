// Copyright 2026 Chad Sharp and Paul Grubbs
// SPDX-License-Identifier: Apache-2.0
//
// The bench executables' command line: PROGRAM COMMAND [FLAG...], each
// command with its own flags, every flag declared with its default and a
// line of help. A flag is "--name VALUE" or "--name=VALUE"; a switch is
// "--name". An undeclared flag, a missing value or an unknown command is a
// usage error (exit status 2); "PROGRAM help" and "PROGRAM COMMAND --help"
// print the usage.
//
// The flags every command of a GordieHowe bench takes (add_common_flags):
//   --profile ID         the field profile (param_sets.h's kId)
//   --seed N             fixed-seed proofs (ProveSeams::fixed_seed): each
//                        proof prints GH_PROOF_DIGEST
//   --serial-commitments the commitments in domain order on one thread
//                        (ProveSeams::serial_commitments)
//   --diagnostics LIST   the diagnostic switches (util/diagnostics.h), by
//                        their field names, comma-separated
//   --rate-requests FILE the placement rule's rate requests
//                        (diagnostics::Options::rate_requests)
// GH_THREADS (gordiehowe/threads.h) stays the threading knob.

#ifndef PRIVACY_PROOFS_ZK_LIB_BENCH_CLI_H_
#define PRIVACY_PROOFS_ZK_LIB_BENCH_CLI_H_

#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <exception>
#include <functional>
#include <map>
#include <stdexcept>
#include <string>
#include <vector>

#include "gordiehowe/test_seams.h"
#include "params/param_sets.h"
#include "util/diagnostics.h"

namespace proofs::bench {

// A usage error: the message and the command's usage go to stderr.
struct UsageError : std::runtime_error {
  using std::runtime_error::runtime_error;
};

// One command's flags: declared, then parsed, then read.
class Flags {
 public:
  // A flag with a value, DEFAULT when not given.
  Flags &flag(const std::string &name, const std::string &dflt,
              const std::string &help) {
    declare(name, Spec{false, dflt, help});
    return *this;
  }
  // A switch, off unless given.
  Flags &toggle(const std::string &name, const std::string &help) {
    declare(name, Spec{true, "", help});
    return *this;
  }

  void parse(const std::vector<std::string> &args) {
    for (size_t i = 0; i < args.size(); ++i) {
      const std::string &a = args[i];
      if (a.rfind("--", 0) != 0) throw UsageError("unexpected argument " + a);
      std::string name = a.substr(2), value;
      const size_t eq = name.find('=');
      const bool inline_value = eq != std::string::npos;
      if (inline_value) {
        value = name.substr(eq + 1);
        name = name.substr(0, eq);
      }
      const auto it = specs_.find(name);
      if (it == specs_.end()) throw UsageError("unknown flag --" + name);
      if (it->second.toggle) {
        if (inline_value) throw UsageError("--" + name + " takes no value");
        value = "1";
      } else if (!inline_value) {
        if (i + 1 == args.size())
          throw UsageError("--" + name + " needs a value");
        value = args[++i];
      }
      given_[name] = value;
    }
  }

  bool given(const std::string &name) const {
    spec(name);
    return given_.count(name) != 0;
  }
  // A switch's state.
  bool on(const std::string &name) const {
    check_toggle(name, true);
    return given(name);
  }
  // A flag's value, its default when not given.
  std::string str(const std::string &name) const {
    check_toggle(name, false);
    const auto it = given_.find(name);
    return it != given_.end() ? it->second : spec(name).dflt;
  }
  uint64_t num(const std::string &name) const {
    const std::string v = str(name);
    size_t end = 0;
    uint64_t n = 0;
    try {
      n = std::stoull(v, &end, 10);
    } catch (const std::exception &) {
      end = 0;
    }
    if (v.empty() || end != v.size() || v[0] == '-')
      throw UsageError("--" + name + " needs a non-negative integer, got '" +
                       v + "'");
    return n;
  }
  // A flag's value as a comma-separated list (empty for an empty value).
  std::vector<std::string> list(const std::string &name) const {
    std::vector<std::string> out;
    const std::string v = str(name);
    size_t at = 0;
    while (at < v.size()) {
      size_t end = v.find(',', at);
      if (end == std::string::npos) end = v.size();
      out.push_back(v.substr(at, end - at));
      at = end + 1;
    }
    return out;
  }

  std::string usage() const {
    std::string out;
    for (const std::string &name : order_) {
      const Spec &s = specs_.at(name);
      std::string head = "  --" + name + (s.toggle ? "" : " VALUE");
      if (head.size() < 28) head.resize(28, ' ');
      out += head + " " + s.help;
      if (!s.toggle) out += " (default: " + (s.dflt.empty() ? "none" : s.dflt) + ")";
      out += "\n";
    }
    return out;
  }

 private:
  struct Spec {
    bool toggle;
    std::string dflt, help;
  };
  void declare(const std::string &name, Spec s) {
    if (!specs_.emplace(name, std::move(s)).second)
      throw std::logic_error("flag --" + name + " declared twice");
    order_.push_back(name);
  }
  const Spec &spec(const std::string &name) const {
    const auto it = specs_.find(name);
    if (it == specs_.end())
      throw std::logic_error("flag --" + name + " is not declared");
    return it->second;
  }
  void check_toggle(const std::string &name, bool toggle) const {
    if (spec(name).toggle != toggle)
      throw std::logic_error("flag --" + name + (toggle ? " is not a switch"
                                                        : " is a switch"));
  }
  std::map<std::string, Spec> specs_;
  std::vector<std::string> order_;
  std::map<std::string, std::string> given_;
};

// One command of a bench executable: its flags (DECLARE) and its body
// (RUN), which returns the exit status.
struct Command {
  std::string name, help;
  std::function<void(Flags &)> declare;
  std::function<int(const Flags &)> run;
};

// PROGRAM COMMAND [FLAG...]: parses the command's flags and runs it. A
// usage error exits 2, any other exception 1.
inline int run_commands(int argc, char **argv, const std::string &summary,
                        const std::vector<Command> &commands) {
  const std::string program = argc > 0 ? argv[0] : "bench";
  auto usage = [&](FILE *to) {
    std::fprintf(to, "%s\nusage: %s COMMAND [FLAG...]\ncommands:\n",
                 summary.c_str(), program.c_str());
    for (const Command &c : commands) {
      std::fprintf(to, "  %-14s %s\n", c.name.c_str(), c.help.c_str());
    }
    std::fprintf(to, "%s COMMAND --help lists the command's flags.\n",
                 program.c_str());
  };
  if (argc < 2) {
    usage(stderr);
    return 2;
  }
  const std::string name = argv[1];
  if (name == "help" || name == "--help") {
    usage(stdout);
    return 0;
  }
  for (const Command &c : commands) {
    if (c.name != name) continue;
    Flags flags;
    c.declare(flags);
    const std::vector<std::string> args(argv + 2, argv + argc);
    for (const std::string &a : args) {
      if (a == "--help") {
        std::printf("usage: %s %s [FLAG...]\n%s\nflags:\n%s", program.c_str(),
                    c.name.c_str(), c.help.c_str(), flags.usage().c_str());
        return 0;
      }
    }
    try {
      flags.parse(args);
      return c.run(flags);
    } catch (const UsageError &e) {
      std::fprintf(stderr, "%s %s: %s\nflags:\n%s", program.c_str(),
                   c.name.c_str(), e.what(), flags.usage().c_str());
      return 2;
    } catch (const std::exception &e) {
      std::fprintf(stderr, "%s %s failed: %s\n", program.c_str(),
                   c.name.c_str(), e.what());
      return 1;
    }
  }
  std::fprintf(stderr, "unknown command %s\n", name.c_str());
  usage(stderr);
  return 2;
}

// ------------------------------------------------------ common flags --

// The kId of the default field profile, the first of AllProfiles.
template <class First, class... Rest>
const char *first_profile_id(param_sets::ProfileList<First, Rest...>) {
  return First::kId;
}
inline const char *default_profile_id() {
  return first_profile_id(param_sets::AllProfiles{});
}

// The diagnostic switches by name (util/diagnostics.h).
inline const std::vector<std::pair<const char *, bool diagnostics::Options::*>>
    &diagnostic_names() {
  static const std::vector<std::pair<const char *, bool diagnostics::Options::*>>
      names = {{"profile", &diagnostics::Options::profile},
               {"profile_timeline", &diagnostics::Options::profile_timeline},
               {"profile_generators", &diagnostics::Options::profile_generators},
               {"eval_time", &diagnostics::Options::eval_time},
               {"ligero_layout", &diagnostics::Options::ligero_layout},
               {"range_groups", &diagnostics::Options::range_groups},
               {"compile_report", &diagnostics::Options::compile_report},
               {"compile_times", &diagnostics::Options::compile_times},
               {"count_times", &diagnostics::Options::count_times}};
  return names;
}

// The flags every GordieHowe bench command takes (see the header).
inline void add_common_flags(Flags &f) {
  std::string names;
  for (const auto &[n, m] : diagnostic_names())
    names += std::string(names.empty() ? "" : ",") + n;
  f.flag("profile", default_profile_id(), "the field profile (its kId)")
      .flag("seed", "", "fixed-seed proofs from this seed, each printing "
                        "GH_PROOF_DIGEST")
      .toggle("serial-commitments",
              "the commitments in domain order on the calling thread")
      .flag("diagnostics", "", "diagnostic switches, comma-separated, of " + names)
      .flag("rate-requests", "", "append the placement rule's rate requests "
                                 "to this file");
}

// Applies the common flags' process-wide options (the diagnostic switches
// and the proof options' seams) and returns the field profile id.
inline std::string apply_common_flags(const Flags &f) {
  diagnostics::Options d;
  for (const std::string &n : f.list("diagnostics")) {
    bool found = false;
    for (const auto &[name, member] : diagnostic_names()) {
      if (n == name) {
        d.*member = true;
        found = true;
      }
    }
    if (!found) throw UsageError("unknown diagnostic " + n);
  }
  d.rate_requests = f.str("rate-requests");
  diagnostics::set(d);
  gordiehowe::ProveSeams s;
  if (f.given("seed")) s.fixed_seed = f.num("seed");
  s.serial_commitments = f.on("serial-commitments");
  gordiehowe::set_prove_seam_defaults(s);
  return f.str("profile");
}

// The common flags of one invocation, as arguments to pass on (report_bench
// to its workers).
inline std::vector<std::string> common_args(const Flags &f) {
  std::vector<std::string> out;
  for (const char *k : {"seed", "diagnostics", "rate-requests"})
    if (f.given(k)) out.insert(out.end(), {std::string("--") + k, f.str(k)});
  if (f.on("serial-commitments")) out.push_back("--serial-commitments");
  return out;
}

}  // namespace proofs::bench

#endif  // PRIVACY_PROOFS_ZK_LIB_BENCH_CLI_H_
