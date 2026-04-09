#ifndef INCLUDED_EFFECT_POLY
#define INCLUDED_EFFECT_POLY

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
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::shared_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  explicit List(Nil _v) : d_v_(std::move(_v)) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  static std::shared_ptr<List<t_A>> nil() {
    return std::make_shared<List<t_A>>(Nil{});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         const std::shared_ptr<List<t_A>> &a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), a1});
  }

  static std::shared_ptr<List<t_A>> cons(t_A a0,
                                         std::shared_ptr<List<t_A>> &&a1) {
    return std::make_shared<List<t_A>>(Cons{std::move(a0), std::move(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct EffectPoly {
  /// 1. Polymorphic monadic map
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 map_result(F0 &&f, const T1 m) {
    T1 a = m;
    return f(a);
  }

  static unsigned int test_map_result();

  /// 2. Polymorphic bind-and-return
  template <typename T1> static T1 lift_pure(const T1 _x0) { return _x0; }

  static unsigned int test_lift_nat();
  static std::string test_lift_string();
  static bool test_lift_bool();
  /// 3. Monadic when / guard
  static void when_(const bool b, const std::monostate action);
  static void test_when(); /// 4. Monadic unless
  static void unless(const bool b, const std::monostate action);
  static void test_unless();
  /// 5. Monadic sequence of list of actions
  static void
  sequence_void(const std::shared_ptr<List<std::monostate>> &actions);
  static void test_sequence_void(); /// 6. Polymorphic fold over itree results

  template <typename T1, typename T2, typename F0>
  static T1 fold_m(F0 &&f, const T1 init, const std::shared_ptr<List<T2>> &xs) {
    return std::visit(
        Overloaded{
            [&](const typename List<T2>::Nil _args) -> T1 { return init; },
            [&](const typename List<T2>::Cons _args) -> T1 {
              T1 acc = f(init, _args.d_a0);
              return fold_m<T1, T2>(f, acc, _args.d_a1);
            }},
        xs->v());
  }

  static unsigned int sum_with_logging(const unsigned int acc,
                                       const unsigned int n);
  static unsigned int test_fold();
  /// 7. Returning a pair from a monadic computation
  static std::pair<std::string, std::string> read_two_lines();
  /// 8. Chaining monadic functions with different return types
  static int64_t chain_types();
};

#endif // INCLUDED_EFFECT_POLY
