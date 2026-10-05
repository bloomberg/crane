#ifndef INCLUDED_CALLBACK_STAYS_CONCRETE
#define INCLUDED_CALLBACK_STAYS_CONCRETE

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <system_error>
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
  List(List &&) = default;
  List &operator=(List &&) = default;

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct CallbackStaysConcrete {
  /// A callback the body only calls -- through a local fixpoint entered where
  /// it is written, or under a bind that is desugared into statements -- keeps
  /// its own type, and is passed by reference rather than erased into a
  /// crane::fn.
  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &>
  static uint64_t sum_map_acc(F0 &&f, const List<uint64_t> &l, uint64_t acc) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
      return acc;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
      return sum_map_acc(f, *a1, (acc + f(a0)));
    }
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, const uint64_t &>
  static uint64_t better_sum(F0 &&f, const List<uint64_t> &l) {
    auto go_impl = [&](auto &_self_go, const List<uint64_t> &l0,
                       uint64_t acc) -> uint64_t {
      if (std::holds_alternative<typename List<uint64_t>::Nil>(l0.v())) {
        return acc;
      } else {
        const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l0.v());
        return _self_go(_self_go, *a1, (acc + f(a0)));
      }
    };
    auto go = [&](const List<uint64_t> &l0, uint64_t acc) -> uint64_t {
      return go_impl(go_impl, l0, acc);
    };
    return go(l, UINT64_C(0));
  }

  template <typename F0>
    requires std::is_invocable_r_v<uint64_t, F0 &, uint64_t &>
  static uint64_t apply_io(F0 &&f, uint64_t n) {
    uint64_t x = n;
    return f(x);
  }
};

#endif // INCLUDED_CALLBACK_STAYS_CONCRETE
