#ifndef INCLUDED_VOID_CALLBACK
#define INCLUDED_VOID_CALLBACK

#include "crane_fn.h"
#include "obj.h"
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
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

struct VoidCallback {
  /// 1. Pure HOF with void callback — the callback returns unit
  template <typename F0>
  static void for_each(F0 &&f, const List<uint64_t> &xs) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      for_each(f, *a1);
      return;
    }
  }

  static void print_nat(uint64_t _x);
  static constexpr std::monostate test_for_each = std::monostate{};

  /// 2. Monadic for-each: callback returns itree ioE unit
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, const uint64_t &>
  static void for_each_m(F0 &&f, const List<uint64_t> &xs) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      f(a0);
      for_each_m(f, *a1);
      return;
    }
  }

  static void test_for_each_m();
  /// 3. Pure function returning unit, used in let
  static void side_effect_pure(uint64_t _x);
  static constexpr uint64_t use_side_effect = UINT64_C(42);

  /// 4. Callback that ignores argument and returns nat
  template <typename F0>
  static uint64_t ignore_and_count(F0 &&f, const List<uint64_t> &xs) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      return (ignore_and_count(f, *a1) + 1);
    }
  }

  static constexpr uint64_t test_ignore = UINT64_C(3);

  /// 5. Nested void callbacks
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static void apply_twice(F0 &&f, uint64_t x0_) {
    f(x0_);
    return;
  }

  static constexpr std::monostate test_apply_twice = std::monostate{};

  /// 6. Void function as argument to polymorphic function
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &&>
  static T2 apply_to(F0 &&f, T1 x0_) {
    return f(std::move(x0_));
  }

  static constexpr std::monostate test_apply_to_void = std::monostate{};
  /// 7. Void returning function in a match arm
  static void void_in_match(bool b);
  /// 8. Option of void function result
  static std::optional<std::monostate> void_option(bool b);
};

#endif // INCLUDED_VOID_CALLBACK
