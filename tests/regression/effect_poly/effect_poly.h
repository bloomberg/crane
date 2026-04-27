#ifndef INCLUDED_EFFECT_POLY
#define INCLUDED_EFFECT_POLY

#include <cstdint>
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

struct EffectPoly {
  /// 1. Polymorphic monadic map
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 map_result(F0 &&f, const T1 &m) {
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
  static void when_(const bool &b, std::monostate action);
  static void test_when();
  /// 4. Monadic unless
  static void unless(const bool &b, std::monostate action);
  static void test_unless();
  /// 5. Monadic sequence of list of actions
  static void sequence_void(const List<std::monostate> &actions);
  static void test_sequence_void();

  /// 6. Polymorphic fold over itree results
  template <typename T1, typename T2, typename F0>
  static T1 fold_m(F0 &&f, const T1 init, const List<T2> &xs) {
    if (std::holds_alternative<typename List<T2>::Nil>(xs.v())) {
      return init;
    } else {
      const auto &[d_a0, d_a1] = std::get<typename List<T2>::Cons>(xs.v());
      T1 acc = f(init, d_a0);
      return fold_m<T1, T2>(f, acc, *(d_a1));
    }
  }

  static unsigned int sum_with_logging(unsigned int acc, unsigned int n);
  static unsigned int test_fold();
  /// 7. Returning a pair from a monadic computation
  static std::pair<std::string, std::string> read_two_lines();
  /// 8. Chaining monadic functions with different return types
  static int64_t chain_types();
};

#endif // INCLUDED_EFFECT_POLY
