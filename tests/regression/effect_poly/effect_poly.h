#ifndef INCLUDED_EFFECT_POLY
#define INCLUDED_EFFECT_POLY

#include <any>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

using namespace std::string_literals;

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

  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct EffectPoly {
  /// 1. Polymorphic monadic map
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 map_result(F0 &&f, const T1 &m) {
    T1 a = m;
    return f(a);
  }

  static uint64_t test_map_result();

  /// 2. Polymorphic bind-and-return
  template <typename T1> static T1 lift_pure(const T1 &_x0) { return _x0; }

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
  template <typename T1, typename T2, typename F0>
  static T1 fold_m(F0 &&f, const T1 &init, const List<T2> &xs) {
    if (std::holds_alternative<typename List<T2>::Nil>(xs.v())) {
      return init;
    } else {
      const auto &[a0, a1] = std::get<typename List<T2>::Cons>(xs.v());
      T1 acc = f(init, a0);
      return fold_m<T1, T2>(f, acc, *a1);
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
