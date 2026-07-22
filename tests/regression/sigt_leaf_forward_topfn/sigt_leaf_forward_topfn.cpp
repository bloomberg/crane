#include "sigt_leaf_forward_topfn.h"

/// sigt_leaf_forward_string reproduced the case where the destructured
/// leaf is forwarded into a *functor/closure parameter* whose concrete type
/// is only known at template instantiation, and got fixed via
/// crane_call_erased. This test is different: the "consumer"
/// (`wrap_string : string -> bool`) is a plain TOP-LEVEL Coq function with an
/// already fully concrete, statically-known signature at the point the
/// literal action closure is *written* (domain `domty 0` is a concrete alias
/// for `string * unit`, not behind any module abstraction) -- the erasure
/// only shows up later, when a *different* piece of code (`run`) accesses the
/// same closure generically through a value-dependent match on a
/// runtime-varying index. This matches Parser.v's
/// `find_predicate_and_action` / grammar-table shape far more closely than
/// the functor version.
///
/// This used to fail to *compile*: because the literal closure is stored via
/// existT into an erased std::any field, mark_own_param_for_pair_erasure
/// forced the lambda's self-destructure to go through
/// any_cast<pair<any,any>>, on the assumption (true for the functor case)
/// that such a lambda's parameter always ends up generic/erased. Here the
/// domain `domty 0` resolves to a fully *concrete* type at this literal (a
/// literal index `0`, not an abstract parameter), so the lambda's C++
/// parameter is rendered with its real concrete type -- and any_cast-ing an
/// already-concrete pair as if it were std::any does not compile. Fixed by
/// only forcing that rewrite when the lambda's own parameter type is
/// actually erased/generic at this instantiation.
bool wrap_string(const std::string &s) { return (s == s); }

domty garg(uint64_t n) {
  if (n <= 0) {
    return std::make_pair(
        std::string(1, (static_cast<char>(
                           (false ? 1 : 0) | (false ? 2 : 0) | (false ? 4 : 0) |
                           (true ? 8 : 0) | (false ? 16 : 0) | (true ? 32 : 0) |
                           (true ? 64 : 0) | (false ? 128 : 0)))) +
            std::string(
                1, (static_cast<char>((true ? 1 : 0) | (false ? 2 : 0) |
                                      (false ? 4 : 0) | (true ? 8 : 0) |
                                      (false ? 16 : 0) | (true ? 32 : 0) |
                                      (true ? 64 : 0) | (false ? 128 : 0)))) +
            std::string(),
        std::monostate{});
  } else {
    uint64_t _x = n - 1;
    return std::make_pair(UINT64_C(0), std::monostate{});
  }
}

bool run(const SigT<std::pair<uint64_t, List<uint64_t>>,
                    std::pair<std::any, std::any>> &e) {
  const auto &[x0, a1] = e;
  const auto &[n, _x] = x0;
  const auto &[f, _x0] = std::any_cast<std::pair<std::any, std::any>>(a1);
  if (std::any_cast<bool>(
          std::any_cast<std::function<std::any(std::any)>>(f)(garg(n)))) {
    return true;
  } else {
    return false;
  }
}

bool check(std::monostate) { return run(my_entry); }
