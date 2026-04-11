#ifndef INCLUDED_VOID_CALLBACK
#define INCLUDED_VOID_CALLBACK

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
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

struct VoidCallback {
  /// 1. Pure HOF with void callback — the callback returns unit
  template <MapsTo<void, unsigned int> F0>
  static void for_each(F0 &&f, const std::shared_ptr<List<unsigned int>> &xs) {
    {
      std::visit(Overloaded{[](const typename List<unsigned int>::Nil _args)
                                -> std::monostate { return std::monostate{}; },
                            [&](const typename List<unsigned int>::Cons _args)
                                -> std::monostate {
                              for_each(f, _args.d_a1);
                              return std::monostate{};
                            }},
                 xs->v());
      return;
    }
  }

  static void print_nat(const unsigned int _x);
  static inline const std::monostate test_for_each = []() {
    for_each(print_nat,
             List<unsigned int>::cons(
                 1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())));
    return std::monostate{};
  }();

  /// 2. Monadic for-each: callback returns itree ioE unit
  template <MapsTo<void, unsigned int> F0>
  static void for_each_m(F0 &&f,
                         const std::shared_ptr<List<unsigned int>> &xs) {
    {
      std::visit(Overloaded{[](const typename List<unsigned int>::Nil _args)
                                -> std::monostate { return std::monostate{}; },
                            [&](const typename List<unsigned int>::Cons _args)
                                -> std::monostate {
                              f(_args.d_a0);
                              for_each_m(f, _args.d_a1);
                              return std::monostate{};
                            }},
                 xs->v());
      return;
    }
  }

  static void test_for_each_m();
  /// 3. Pure function returning unit, used in let
  static void side_effect_pure(const unsigned int _x);
  static inline const unsigned int use_side_effect = 42u;

  /// 4. Callback that ignores argument and returns nat
  template <MapsTo<void, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  ignore_and_count(F0 &&f, const std::shared_ptr<List<unsigned int>> &xs) {
    return std::visit(
        Overloaded{
            [](const typename List<unsigned int>::Nil _args) -> unsigned int {
              return 0u;
            },
            [&](const typename List<unsigned int>::Cons _args) -> unsigned int {
              return (ignore_and_count(f, _args.d_a1) + 1);
            }},
        xs->v());
  }

  static inline const unsigned int test_ignore = ignore_and_count(
      print_nat,
      List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));

  /// 5. Nested void callbacks
  template <MapsTo<void, unsigned int> F0>
  static void apply_twice(F0 &&f, const unsigned int _x0) {
    f(_x0);
    return;
  }

  static inline const std::monostate test_apply_twice = []() {
    apply_twice(print_nat, 42u);
    return std::monostate{};
  }();

  /// 6. Void function as argument to polymorphic function
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 apply_to(F0 &&f, const T1 _x0) {
    return f(_x0);
  }

  static inline const std::monostate test_apply_to_void = []() {
    apply_to<unsigned int, std::monostate>(
        [](const unsigned int &_wa0) {
          print_nat(_wa0);
          return std::monostate{};
        },
        5u);
    return std::monostate{};
  }();
  /// 7. Void returning function in a match arm
  static void void_in_match(const bool b);
  /// 8. Option of void function result
  __attribute__((pure)) static std::optional<std::monostate>
  void_option(const bool b);
};

#endif // INCLUDED_VOID_CALLBACK
