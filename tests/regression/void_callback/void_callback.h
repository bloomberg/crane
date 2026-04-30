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
#include <vector>

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
  List<t_A> clone() const {
    List<t_A> _out{};

    struct _CloneFrame {
      const List<t_A> *_src;
      List<t_A> *_dst;
    };

    std::vector<_CloneFrame> _stack{};
    _stack.push_back({this, &_out});
    while (!_stack.empty()) {
      auto _frame = _stack.back();
      _stack.pop_back();
      const List<t_A> *_src = _frame._src;
      List<t_A> *_dst = _frame._dst;
      if (std::holds_alternative<Nil>(_src->v())) {
        _dst->d_v_ = Nil{};
      } else {
        const auto &_alt = std::get<Cons>(_src->v());
        _dst->d_v_ = Cons{_alt.d_a0,
                          _alt.d_a1 ? std::make_unique<List<t_A>>() : nullptr};
        auto &_dst_alt = std::get<Cons>(_dst->d_v_);
        if (_alt.d_a1) {
          _stack.push_back({_alt.d_a1.get(), _dst_alt.d_a1.get()});
        }
      }
    }
    return _out;
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

  static List<t_A> nil() { return List(Nil{}); }

  static List<t_A> cons(t_A a0, List<t_A> a1) {
    return List(
        Cons{std::move(a0), std::make_unique<List<t_A>>(std::move(a1))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::unique_ptr<List<t_A>>> _stack{};
    auto _drain = [&](List<t_A> &_node) {
      if (std::holds_alternative<Cons>(_node.d_v_)) {
        auto &_alt = std::get<Cons>(_node.d_v_);
        if (_alt.d_a1) {
          _stack.push_back(std::move(_alt.d_a1));
        }
      }
    };
    _drain(*this);
    while (!_stack.empty()) {
      auto _node = std::move(_stack.back());
      _stack.pop_back();
      if (_node) {
        _drain(*_node);
      }
    }
  }

  inline variant_t &v_mut() { return d_v_; }

  // ACCESSORS
  const variant_t &v() const { return d_v_; }
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
  static unsigned int ignore_and_count(F0 &&f, const List<unsigned int> &xs) {
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
  static std::optional<std::monostate> void_option(const bool &b);
};

#endif // INCLUDED_VOID_CALLBACK
