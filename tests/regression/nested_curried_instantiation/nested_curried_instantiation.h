#pragma once

#include "crane_fn.h"
#include "fn.h"
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

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, const A &>
  List<T1> map(F0 &&f) const {
    // Builds the result front to back: _write points at the empty tail the next
    // cell fills.
    std::optional<List<T1>> _root{};
    std::shared_ptr<List<T1>> *_write = nullptr;
    const List<A> *_loop_self = this;
    while (true) {
      auto &&_sv = *_loop_self;
      if (std::holds_alternative<typename List<A>::Nil>(_sv.v())) {
        auto _value = List<T1>::nil();
        (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_value)))
                : _root.emplace(std::move(_value)));
        break;
      } else {
        const auto &[a0, a1] = std::get<typename List<A>::Cons>(_sv.v());
        auto _cell = typename List<T1>::Cons(f(a0), nullptr);
        List<T1> &_node =
            (_write ? *(*_write = std::make_shared<List<T1>>(std::move(_cell)))
                    : _root.emplace(std::move(_cell)));
        _write = &std::get<typename List<T1>::Cons>(_node.v_mut()).l;
        _loop_self = crane_raw(a1);
        continue;
      }
    }
    return std::move(*_root);
  }
};

struct NestedCurriedInstantiation {
  template <typename T1> static T1 hd_or(T1 d, const List<T1> &l) {
    if (std::holds_alternative<typename List<T1>::Nil>(l.v())) {
      return d;
    } else {
      const auto &[a0, _] = std::get<typename List<T1>::Cons>(l.v());
      return a0;
    }
  }

  template <typename T1, typename F0>
    requires std::is_invocable_r_v<T1, F0 &, T1> &&
             std::is_invocable_r_v<T1, F0 &, const T1 &>
  static T1 twice(F0 &&f, const T1 &x) {
    return f(f(x));
  }

  static inline const uint64_t result = []() {
    return twice<crane::fn<uint64_t(uint64_t)>>(
        hd_or<crane::fn<
            crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>(
            [](crane::fn<uint64_t(uint64_t)>) {
              return [](uint64_t n) { return n; };
            },
            List<crane::fn<
                crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>::cons(
                [](crane::fn<uint64_t(uint64_t)> g) {
                  return [=, g = std::move(g)](uint64_t n) {
                    return g(n) + UINT64_C(1);
                  };
                },
                List<crane::fn<crane::fn<uint64_t(uint64_t)>(
                    crane::fn<uint64_t(uint64_t)>)>>::nil())),
        [](uint64_t n) { return n * UINT64_C(2); })(UINT64_C(3));
  }();
  /// No transformer needed: a two-argument element, bool -> nat -> nat, at an
  /// instantiation map reads as bool -> (nat -> nat).
  static inline const uint64_t result2 = []() {
    return List<bool>::cons(true,
                            List<bool>::cons(false,
                                             List<bool>::nil()))
               .template map<crane::fn<uint64_t(uint64_t)>>(
        hd_or<crane::fn<crane::fn<uint64_t(uint64_t)>(bool)>>(
            [](bool) {
              return [](uint64_t n) { return n; };
            },
            List<crane::fn<crane::fn<uint64_t(uint64_t)>(bool)>>::cons(
                [](bool b) {
                  return [=](uint64_t n) -> uint64_t {
                    if (b) {
                      return n * UINT64_C(10);
                    } else {
                      return n;
                    }
                  };
                },
                List<crane::fn<crane::fn<uint64_t(uint64_t)>(bool)>>::nil())))
               .template fold_left<uint64_t>(
        [](uint64_t a,
           const crane::fn<uint64_t(uint64_t)> &f) {
          return a + f(UINT64_C(4));
        },
        UINT64_C(0));
  }();
  /// The same under a fold: fold_left's step, at the transformer type, takes
  /// its accumulator and returns its result at the curried type the member
  /// fold_left's template argument writes.
  static inline const uint64_t result3 = []() {
    return twice<crane::fn<uint64_t(uint64_t)>>(
        List<uint64_t>::cons(
            UINT64_C(1),
            List<uint64_t>::cons(UINT64_C(2),
                                 List<uint64_t>::nil()))
            .template fold_left<crane::fn<
            crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>(
            [](crane::fn<
                crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>,
               uint64_t e) {
              return [=](crane::fn<uint64_t(uint64_t)> g) {
                return [=, g = std::move(g)](uint64_t n) { return g(n) + e; };
              };
            },
            [](crane::fn<uint64_t(uint64_t)> g) {
              return [=, g = std::move(g)](uint64_t n) {
                return g(n) + UINT64_C(1);
              };
            }),
        [](uint64_t n) { return n; })(UINT64_C(3));
  }();
};
