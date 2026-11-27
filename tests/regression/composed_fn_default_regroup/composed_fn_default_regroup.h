#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <atomic>
#include <cstdint>
#include <memory>
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
};

struct ComposedFnDefaultRegroup {
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
            []() {
              crane::fn<uint64_t(bool, uint64_t)> cf =
                  [](bool b, uint64_t n) -> uint64_t {
                    if (b) {
                      return n + UINT64_C(1);
                    } else {
                      return n + UINT64_C(5);
                    }
                  };
              crane::fn<bool(crane::fn<uint64_t(uint64_t)>)> cg =
                  [](const crane::fn<uint64_t(uint64_t)> &g) {
                    return g(UINT64_C(0)) == UINT64_C(0);
                  };
              return [=, cf = std::move(cf), cg = std::move(cg)](
                  const crane::fn<uint64_t(uint64_t)> &c) {
                return [=, c = c, cf = cf, cg = cg](uint64_t _pa0) {
                  return cf(cg(c), _pa0);
                };
              };
            }(),
            List<crane::fn<
                crane::fn<uint64_t(uint64_t)>(crane::fn<uint64_t(uint64_t)>)>>::nil()),
        [](uint64_t n) { return n; })(UINT64_C(6));
  }();
};
