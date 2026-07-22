#ifndef INCLUDED_SIGT_LEAF_FORWARD_TOPFN
#define INCLUDED_SIGT_LEAF_FORWARD_TOPFN

#include "crane_fn.h"
#include <any>
#include <functional>
#include <memory>
#include <string>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

template <typename A, typename P> struct SigT {
  // DATA
  A x;
  P a1;

  // ACCESSORS
  SigT<A, P> clone() const { return {x, a1}; }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

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
bool wrap_string(const std::string &s);
using domty = std::any;
using prod2 = std::pair<uint64_t, List<uint64_t>>;
using pred_ty = std::any;
using act_ty = std::any;
using psem = std::pair<pred_ty, act_ty>;
using entry = SigT<prod2, psem>;
const entry my_entry = SigT<prod2, psem>::existt(
    std::make_pair(UINT64_C(0), List<uint64_t>::nil()),
    std::make_pair(
        crane_erase_fn([](const std::pair<std::string, std::monostate> &tup) {
          const auto &[v, _x] = tup;
          return wrap_string(v);
        }),
        crane_erase_fn([](const std::pair<std::string, std::monostate> &tup) {
          const auto &[v, _x] = tup;
          return wrap_string(v);
        })));
domty garg(uint64_t n);
bool run(const SigT<std::pair<uint64_t, List<uint64_t>>,
                    std::pair<std::any, std::any>> &e);
bool check(std::monostate _x);

#endif // INCLUDED_SIGT_LEAF_FORWARD_TOPFN
