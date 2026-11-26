#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <functional>
#include <memory>
#include <stdexcept>
#include <utility>
#include <variant>

template <typename A> struct List;
template <typename A, typename P> struct SigT;

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

  template <typename CraneU>
  List(const List<CraneU> &_other)
      : v_([&]() -> variant_t {
          if (std::holds_alternative<typename List<CraneU>::Nil>(_other.v())) {
            return Nil{};
          } else {
            const auto &[a, l] =
                std::get<typename List<CraneU>::Cons>(_other.v());
            return Cons{
                [&]() -> A {
                  if constexpr (crane_convertible<A, const CraneU &>) {
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

  static List<A> cons(A a, crane::shared_child_slot<List<A>> l) {
    return List<A>(Cons{std::move(a), l.take()});
  }

  // MANIPULATORS
  ~List() {
    // Release the children this node alone owns in a loop, not recursively, so
    // a deep value cannot overflow the stack.
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
  List(List &&) = default;
  List &operator=(List &&) = default;

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

  template <typename CraneU0, typename CraneU1>
  operator SigT<CraneU0, CraneU1>() const {
    return {[&]() -> CraneU0 {
              if constexpr (crane_convertible<CraneU0, const A &>) {
                return crane_convert<CraneU0>(x);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }(),
            [&]() -> CraneU1 {
              if constexpr (crane_convertible<CraneU1, const P &>) {
                return crane_convert<CraneU1>(a1);
              } else {
                throw std::logic_error("unreachable: inactive constructor "
                                       "field at this instantiation");
              }
            }()};
  }

  // CREATORS
  static SigT<A, P> existt(A x, P a1) { return {std::move(x), std::move(a1)}; }
};

/// Regression test for the parse-a-lot LL-parser bad_any_cast in the
/// product-payload case (now fixed).
///
/// The earlier repro (sigt_fn_any) stored a function *directly* into a field of
/// type std::any; Crane's fix wraps such a store in crane_erase_fn(...)
/// so the std::any holds a std::function.
///
/// But parse-a-lot's grammar does not store the predicate/action functions
/// directly. It stores them as the two *components of a product*:
///
/// production_semty p := predicate_semty p * action_semty p     (Defs.v:972)
///
/// where predicate_semty/action_semty are value-dependent function types
/// that Crane erases to std::any. So the C++ payload is
/// std::pair<std::any, std::any>, and the two lambdas are erased to
/// std::any *through the pair conversion*. This path goes through the
/// custom-constructor code (prod -> std::make_pair), which the original
/// crane_erase_fn fix did not cover, so the lambdas were stored as raw
/// closures and the parser crashed reading them back with
/// any_cast<std::function<std::any(std::any)>>.
///
/// The fix extends the crane_erase_fn wrapping to function values boxed into
/// erased fields through a custom constructor.  This file distills exactly that
/// product-payload shape.
template <typename M>
concept SEM = requires {
  typename M::idx;
  typename M::sem;
};

template <SEM S> struct Make {
  using prod2 = std::pair<typename S::idx, List<typename S::idx>>;
  /// predicate_semty-analog: value-dependent function type -> std::any.
  using pred_ty = crane::obj;
  /// action_semty-analog: value-dependent function type -> std::any.
  using act_ty = crane::obj;
  /// production_semty-analog: a *pair* of the two erased function types, i.e.
  /// C++ std::pair<std::any, std::any>.
  using psem = std::pair<pred_ty, act_ty>;
  /// grammar_entry-analog.
  using entry = SigT<prod2, psem>;

  /// Store the predicate/action pair. The two lambdas are erased to std::any
  /// through the pair conversion — the fix's crane_erase_fn is NOT applied.
  template <typename F1, typename F2>
  static entry mk(typename S::idx a, F1 &&f, F2 &&g) {
    return SigT<prod2, psem>::existt(
        std::make_pair(std::move(a), List<typename S::idx>::nil()),
        std::make_pair(crane::obj(crane_erase_fn(f)),
                       crane::obj(crane_erase_fn(g))));
  }

  /// Look up + apply the predicate, exactly like Parser.v:113 if p vs' ....
  /// Applying just the predicate is enough to hit the crash: it is the first
  /// any_cast<std::function<...>> the parser performs. The action g stays in
  /// the stored pair so the payload keeps its product-of-erased-functions
  /// shape.
  template <typename F1>
  static bool run(const SigT<std::pair<typename S::idx, List<typename S::idx>>,
                             std::pair<crane::obj, crane::obj>> &e,
                  F1 &&arg) {
    const auto &[x0, a1] = e;
    const auto &[a, _] = x0;
    const auto &[f, _] = a1;
    if (crane::any_cast<bool>(
            crane::any_cast<crane::fn<crane::obj(crane::obj)>>(f)(arg(a)))) {
      return true;
    } else {
      return false;
    }
  }
};

struct Inst {
  using idx = std::monostate;
  using sem = uint64_t;
};

using M = Make<Inst>;
[[gnu::used]] inline const M::entry my_entry =
    M::mk(std::monostate{},
          crane_erase_fn<bool>([](uint64_t n) { return n == UINT64_C(0); }),
          crane_erase_fn<uint64_t>([](uint64_t n) { return (n + 1); }));
Inst::sem my_arg(std::monostate _x);
/// In Rocq this is true (predicate 0 =? 0 holds), and the extracted C++ now
/// returns true as well (before the fix it threw std::bad_any_cast).
bool check();
