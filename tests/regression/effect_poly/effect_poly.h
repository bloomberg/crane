#ifndef INCLUDED_EFFECT_POLY
#define INCLUDED_EFFECT_POLY

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <any>
#include <atomic>
#include <crane_itree.h>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <system_error>
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

struct EffectPoly {
  /// 1. Polymorphic monadic map
  template <typename T1, typename T2>
  static T2 map_result(std::type_identity_t<crane::fn<T2(T1)>> f, const T1 &m) {
    T1 a = m;
    return f(std::move(a));
  }

  static uint64_t test_map_result();

  /// 2. Polymorphic bind-and-return
  template <typename T1> static T1 lift_pure(const T1 &x0_) { return x0_; }

  static uint64_t test_lift_nat();
  static std::string test_lift_string();
  static bool test_lift_bool();
  /// 3. Monadic when / guard
  static void when_(bool b, std::monostate action);
  static void test_when();
  /// 4. Monadic unless
  static void unless(bool b, std::monostate action);
  static void test_unless();
  /// 5. Monadic sequence of list of actions
  static void sequence_void(const List<std::monostate> &actions);
  static void test_sequence_void();

  /// 6. Polymorphic fold over itree results
  template <typename T1, typename T2>
  static T1 fold_m(std::type_identity_t<crane::fn<T1(T1, T2)>> f,
                   const T1 &init, const List<T2> &xs) {
    if (std::holds_alternative<typename List<T2>::Nil>(xs.v())) {
      return init;
    } else {
      const auto &[a0, a1] = std::get<typename List<T2>::Cons>(xs.v());
      T1 acc = f(init, a0);
      return fold_m<T1, T2>(std::move(f), std::move(acc), *a1);
    }
  }

  static uint64_t sum_with_logging(uint64_t acc, uint64_t n);
  static uint64_t test_fold();
  /// 7. Returning a pair from a monadic computation
  static std::pair<std::string, std::string> read_two_lines();
  /// 8. Chaining monadic functions with different return types
  static int64_t chain_types();
};

#endif // INCLUDED_EFFECT_POLY
