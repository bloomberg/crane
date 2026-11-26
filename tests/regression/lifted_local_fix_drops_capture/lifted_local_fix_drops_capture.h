#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
#include <stdexcept>
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
};

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// A local fixpoint inside a polymorphic definition is lifted to a static
/// template helper (f_crane_go), but the helper still reads the enclosing
/// parameter n, which it neither captures nor takes: "use of undeclared
/// identifier 'n'".
struct LiftedLocalFixDropsCapture {
  template <typename T1> static uint64_t f(const T1 &x, uint64_t n) {
    const List<std::pair<bool, T1>> &_lc1_l = List<std::pair<bool, T1>>::cons(
        std::make_pair(false, x), List<std::pair<bool, T1>>::nil());
    // Loop replaces the tail recursion: each recursive call updates the loop
    // variables.
    const List<std::pair<bool, T1>> *_lc1_loop_l = &_lc1_l;
    while (true) {
      if (std::holds_alternative<typename List<std::pair<bool, T1>>::Nil>(
              _lc1_loop_l->v())) {
        return n;
      } else {
        const auto &[_, a1] = std::get<typename List<std::pair<bool,
                                                               T1>>::Cons>(
            _lc1_loop_l->v());
        _lc1_loop_l = crane_raw(a1);
      }
    }
  }

  static inline const uint64_t t = f<bool>(true, UINT64_C(7));
};
