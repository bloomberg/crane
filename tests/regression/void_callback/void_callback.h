#ifndef INCLUDED_VOID_CALLBACK
#define INCLUDED_VOID_CALLBACK

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
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

using namespace std::string_literals;

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

struct VoidCallback {
  /// 1. Pure HOF with void callback — the callback returns unit
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
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
  static inline const std::monostate test_for_each = []() {
    for_each(print_nat,
             List<uint64_t>::cons(
                 UINT64_C(1),
                 List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil())));
    return std::monostate{};
  }();

  /// 2. Monadic for-each: callback returns itree ioE unit
  static void for_each_m(crane::fn<void(uint64_t)> f,
                         const List<uint64_t> &xs) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      f(a0);
      for_each_m(std::move(f), *a1);
      return;
    }
  }

  static void test_for_each_m();
  /// 3. Pure function returning unit, used in let
  static void side_effect_pure(uint64_t _x);
  static inline const uint64_t use_side_effect = UINT64_C(42);

  /// 4. Callback that ignores argument and returns nat
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static uint64_t ignore_and_count(F0 &&f, const List<uint64_t> &xs) {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
      return (ignore_and_count(f, *a1) + 1);
    }
  }

  static inline const uint64_t test_ignore = ignore_and_count(
      print_nat,
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));

  /// 5. Nested void callbacks
  template <typename F0>
    requires std::is_invocable_r_v<void, F0 &, uint64_t &>
  static void apply_twice(F0 &&f, uint64_t x0_) {
    f(x0_);
    return;
  }

  static inline const std::monostate test_apply_twice = []() {
    apply_twice(print_nat, UINT64_C(42));
    return std::monostate{};
  }();

  /// 6. Void function as argument to polymorphic function
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 apply_to(F0 &&f, T1 x0_) {
    return f(std::move(x0_));
  }

  static inline const std::monostate test_apply_to_void = []() {
    apply_to<uint64_t, std::monostate>(
        [](const uint64_t &_wa0) {
          print_nat(_wa0);
          return std::monostate{};
        },
        UINT64_C(5));
    return std::monostate{};
  }();
  /// 7. Void returning function in a match arm
  static void void_in_match(bool b);
  /// 8. Option of void function result
  static std::optional<std::monostate> void_option(bool b);
};

#endif // INCLUDED_VOID_CALLBACK
