#ifndef INCLUDED_EFFECT_HIGHER_ORDER
#define INCLUDED_EFFECT_HIGHER_ORDER

#include <cstdlib>
#include <functional>
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

  List<t_A> &operator=(const List<t_A> &_other) {
    d_v_ = std::move(_other.clone().d_v_);
    return *this;
  }

  List<t_A> &operator=(List<t_A> &&_other) {
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
      return List<t_A>(Cons{
          d_a0, d_a1 ? std::make_unique<List<t_A>>(d_a1->clone()) : nullptr});
    }
  }

  // CREATORS
  template <typename _U> explicit List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      d_v_ = Nil{};
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<_U>::Cons>(_other.v());
      d_v_ =
          Cons{t_A(d_a0), d_a1 ? std::make_unique<List<t_A>>(*d_a1) : nullptr};
    }
  }

  __attribute__((pure)) static List<t_A> nil() { return List(Nil{}); }

  __attribute__((pure)) static List<t_A> cons(t_A a0, const List<t_A> &a1) {
    return List(Cons{std::move(a0), std::make_unique<List<t_A>>(a1)});
  }

  // MANIPULATORS
  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  __attribute__((pure)) const variant_t &v() const { return d_v_; }
};

struct EffectHigherOrder {
  /// 1. Higher-order function with effectful callback
  template <MapsTo<void, std::string> F0>
  static void apply_effect(F0 &&f, const std::string _x0) {
    f(_x0);
    return;
  }

  /// 2. Map-like function over a list with effects
  template <MapsTo<void, std::string> F0>
  static void for_each_str(F0 &&f, const List<std::string> &xs) {
    if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
      return;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::string>::Cons>(xs.v());
      f(d_a0);
      for_each_str(f, *(d_a1));
      return;
    }
  } /// 3. Callback that returns a value

  template <typename F0> static std::string with_line(F0 &&f) {
    std::string _bind_result = []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
    return f(_bind_result);
  }

  /// 4. Nested bind in callback
  template <MapsTo<std::string, std::string> F0>
  static std::string transform_input(F0 &&f) {
    std::string line;
    std::getline(std::cin, line);
    return f(line);
  }

  /// 5. Effectful callback passed as argument
  static void greet_all(const List<std::string> &names);
  /// 6. Callback with env effect
  static std::string lookup_or_ask(const std::string name);
  /// 7. Chain of lookups
  static List<std::string> lookup_all(const List<std::string> &names);
  /// 8. Effect in let-bound function
  static std::string process_input();
};

#endif // INCLUDED_EFFECT_HIGHER_ORDER
