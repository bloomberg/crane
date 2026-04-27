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
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename t_A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    t_A d_a0;
    std::unique_ptr<List<t_A>> d_a1;
  };

  using variant_t = std::variant<Nil, Cons>;
  using crane_element_type = t_A;

private:
  // DATA
  variant_t d_v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : d_v_(_v) {}

  explicit List(Cons _v) : d_v_(std::move(_v)) {}

  List(const List<t_A> &_other) : d_v_(std::move(_other.clone().d_v_)) {}

  List(List<t_A> &&_other) : d_v_(std::move(_other.d_v_)) {}

  __attribute__((pure)) List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  __attribute__((pure)) List<t_A> &operator=(List<t_A> &&_other) {
    d_v_ = std::move(_other.d_v_);
    return *this;
  }

  // ACCESSORS
  __attribute__((pure)) List<t_A> clone() const {
    auto &&_sv = *(this);
    if (std::holds_alternative<Nil>(_sv.v())) {
      return List<t_A>(Nil{});
    } else {
      const auto &[d_a0, d_a1] = std::get<Cons>(_sv.v());
      t_A __c0;
      if constexpr (
          requires { d_a0 ? 0 : 0; } && requires { *d_a0; } &&
          requires { d_a0->clone(); } && requires { d_a0.get(); }) {
        using _E = std::remove_cvref_t<decltype(*d_a0)>;
        __c0 = d_a0 ? std::make_unique<_E>(d_a0->clone()) : nullptr;
      } else if constexpr (requires { d_a0.clone(); }) {
        __c0 = d_a0.clone();
      } else {
        __c0 = d_a0;
      }
      return List<t_A>(
          Cons{std::move(__c0),
               d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ = Cons{
          [&]<typename _DstT = t_A>(auto &&__v) -> _DstT {
            if constexpr (
                requires { *__v; } &&
                !requires { std::declval<_DstT>().get(); })
              return _DstT(*__v);
            else if constexpr (
                !requires { *__v; } &&
                requires { std::declval<_DstT>().get(); }) {
              using _E =
                  std::remove_pointer_t<decltype(std::declval<_DstT>().get())>;
              return std::make_unique<_E>(std::move(__v));
            } else
              return _DstT(__v);
          }(d_a0),
          d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  __attribute__((pure)) variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) List<t_A> *operator->() { return this; }

  __attribute__((pure)) const List<t_A> *operator->() const { return this; }

  __attribute__((pure)) bool operator!=(std::nullptr_t) const { return true; }

  __attribute__((pure)) bool operator==(std::nullptr_t) const { return false; }

  // MANIPULATORS
  void reset() { *this = List<t_A>(); }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct VoidCallback {
  /// 1. Pure HOF with void callback — the callback returns unit
  template <MapsTo<void, unsigned int> F0>
  static void for_each(F0 &&f, const List<unsigned int> &xs) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      for_each(f, *(d_a1));
      return;
    }
  }

  static void print_nat(const unsigned int &_x);
  static inline const std::monostate test_for_each = []() {
    for_each(print_nat,
             List<unsigned int>::cons(
                 1u, List<unsigned int>::cons(2u, List<unsigned int>::nil())));
    return std::monostate{};
  }();

  /// 2. Monadic for-each: callback returns itree ioE unit
  template <MapsTo<void, unsigned int> F0>
  static void for_each_m(F0 &&f, const List<unsigned int> &xs) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      f(d_a0);
      for_each_m(f, *(d_a1));
      return;
    }
  }

  static void test_for_each_m();
  /// 3. Pure function returning unit, used in let
  static void side_effect_pure(const unsigned int &_x);
  static inline const unsigned int use_side_effect = 42u;

  /// 4. Callback that ignores argument and returns nat
  template <MapsTo<void, unsigned int> F0>
  __attribute__((pure)) static unsigned int
  ignore_and_count(F0 &&f, const List<unsigned int> &xs) {
    if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<unsigned int>::Cons>(xs.v());
      return (ignore_and_count(f, *(d_a1)) + 1);
    }
  }

  static inline const unsigned int test_ignore = ignore_and_count(
      print_nat,
      List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));

  /// 5. Nested void callbacks
  template <MapsTo<void, unsigned int> F0>
  static void apply_twice(F0 &&f, unsigned int _x0) {
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
  static void void_in_match(const bool &b);
  /// 8. Option of void function result
  __attribute__((pure)) static std::optional<std::monostate>
  void_option(const bool &b);
};

#endif // INCLUDED_VOID_CALLBACK
