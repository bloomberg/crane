#ifndef INCLUDED_SIGT_LEAF_FORWARD_TOPFN
#define INCLUDED_SIGT_LEAF_FORWARD_TOPFN

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <functional>
#include <memory>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A, typename P> struct SigT;
using domty = crane::obj;
using pred_ty = crane::obj;
using act_ty = crane::obj;

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

  template <typename _U>
  List(const List<_U> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const _U &>) {
                    return crane_convert<A>(a);
                  } else {
                    throw std::logic_error("unreachable: inactive constructor "
                                           "field at this instantiation");
                  }
                }(),
                (l ? std::make_shared<List<A>>(crane_convert<List<A>>(*l))
                   : nullptr)};
          }
        }()) {}

  static List<A> nil() { return List<A>(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List<A>(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    auto _next = [&](variant_t &_v) -> std::shared_ptr<List<A>> {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l && _alt->l.use_count() == 1) {
          std::atomic_thread_fence(std::memory_order_acquire);
          return std::move(_alt->l);
        }
      }
      return nullptr;
    };
    std::shared_ptr<List<A>> _cur = _next(v_mut());
    while (_cur) {
      _cur = _next(_cur->v_mut());
    }
  }

  List(const List &) = default;
  List &operator=(const List &) = default;
  List(List &&) noexcept = default;
  List &operator=(List &&) noexcept = default;

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

  template <typename _U0, typename _U1> operator SigT<_U0, _U1>() const {
    return {[&]() -> _U0 {
              if constexpr (crane_convertible<_U0, const A &>) {
                return crane_convert<_U0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> _U1 {
              if constexpr (crane_convertible<_U1, const P &>) {
                return crane_convert<_U1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

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
using prod2 = std::pair<uint64_t, List<uint64_t>>;
using psem = std::pair<pred_ty, act_ty>;
using entry = SigT<prod2, psem>;
const entry my_entry = SigT<prod2, psem>::existt(
    std::make_pair(UINT64_C(0), List<uint64_t>::nil()),
    std::make_pair(
        crane::obj(crane_erase_fn([](const auto &tup) {
          const auto &[v, _x] =
              crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
          return wrap_string(crane::any_cast<std::string>(v));
        })),
        crane::obj(crane_erase_fn([](const auto &tup) {
          const auto &[v, _x] =
              crane::any_cast<std::pair<crane::obj, crane::obj>>(tup);
          return wrap_string(crane::any_cast<std::string>(v));
        }))));
domty garg(uint64_t n);
bool run(const SigT<std::pair<uint64_t, List<uint64_t>>,
                    std::pair<crane::obj, crane::obj>> &e);
bool check(std::monostate _x);

#endif // INCLUDED_SIGT_LEAF_FORWARD_TOPFN
