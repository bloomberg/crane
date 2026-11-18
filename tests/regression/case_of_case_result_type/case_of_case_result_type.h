#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <optional>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

template <typename A> struct List;

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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1 &&, const A &>
  T1 fold_left(F0 &&f, T1 a0) const {
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<A> *_loop_self = this;
    T1 _loop_a0 = std::move(a0);
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        return _loop_a0;
      } else {
        const auto &[a1, a2] = std::get<typename List<A>::Cons>(_sv.v());
        _loop_self = crane_raw(a2);
        _loop_a0 = f(std::move(_loop_a0), a1);
      }
    }
  }
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A match (or if) whose scrutinee is another match: after case-of-case the
/// immediately invoked lambda is annotated with the inner match's result type
/// instead of the outer one.
///
/// - t: inner list nat, outer nat: -> List<uint64_t> does not compile.
/// - g: inner bool, outer nat under Nat.leb: -> bool compiles and
/// turns 12 into true (1); g 3 4 is true in Rocq, false in C++.
/// - u: same at a top-level constant: Rocq 12, C++ 1.
/// - v: a projection of a match on a fold_left pair: -> pt on a lambda
/// returning px; does not compile.
/// - w: a match whose branches are all lambdas, applied to k: the
/// lambdas move out of the match and the branches kept their arrow type,
/// -> crane::fn<uint64_t(uint64_t)>; does not compile.
/// - t2: the bool match inside a pair in a match branch: Rocq
/// t2 1 = (0, 151), C++ (0, 1).
///
/// The wrong values have no diagnostic (with a literal left operand clang
/// flags g via -Wtautological-constant-out-of-range-compare).
struct CaseOfCaseResultType {
  static uint64_t h(uint64_t n);
  static inline const uint64_t t = []() -> uint64_t {
    auto _cs = []() {
      List<bool> m = List<bool>::nil();
      uint64_t acc = UINT64_C(0);
      if (std::holds_alternative<typename List<bool>::Nil>(m.v_mut())) {
        return UINT64_C(0);
      } else {
        return acc;
      }
    }();
    if (_cs <= 0) {
      return h(UINT64_C(1));
    } else {
      uint64_t _x = _cs - 1;
      return UINT64_C(0);
    }
  }();
  static bool g(uint64_t k, uint64_t n);
  static inline const uint64_t u = []() -> uint64_t {
    auto _cs = h(UINT64_C(0));
    if (_cs <= 0) {
      return h(UINT64_C(5));
    } else {
      uint64_t _x = _cs - 1;
      return h(UINT64_C(5));
    }
  }();

  struct pt {
    uint64_t px;
    bool py;
  };

  static inline const uint64_t v = []() -> uint64_t {
    auto [_x, _x0] = List<List<bool>>::nil().template fold_left<
        std::pair<std::optional<uint64_t>, pt>>(
        [](std::pair<std::optional<uint64_t>, pt>,
           List<bool>) {
          return std::make_pair(std::optional<uint64_t>(),
                                pt{UINT64_C(0), true});
        },
        std::make_pair(std::optional<uint64_t>(), pt{UINT64_C(0), true}));
    return UINT64_C(3);
  }();
  /// A match applied to an argument: the argument is pushed into the
  /// branches, which then return what their functions did.
  static bool w(uint64_t k, uint64_t n);
  /// The bool match sits in the second component of a pair in a branch
  /// of an outer match: after case-of-case its IIFE kept -> bool and
  /// t2 1 gave (0, 1).
  static std::pair<uint64_t, uint64_t> t2(uint64_t n);
};
