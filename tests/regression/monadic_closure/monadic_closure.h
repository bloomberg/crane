#ifndef INCLUDED_MONADIC_CLOSURE
#define INCLUDED_MONADIC_CLOSURE

#include <any>
#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

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
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }
};

struct MonadicClosure {
  /// 1. Lambda capturing a bind result
  template <typename T1>
  static int64_t _capture_bind_f(const T1, const std::string line) {
    return static_cast<int64_t>(line.length());
  }

  static int64_t capture_bind();

  /// 2. Higher-order function taking a pure callback
  template <typename T1, typename T2, typename F0>
    requires std::is_invocable_r_v<T2, F0 &, T1 &>
  static T2 apply_after_effect(F0 &&f, const T1 &m) {
    T1 x = m;
    return f(x);
  }

  static int64_t test_apply_after();
  /// 3. Function returning a closure from monadic context
  static std::function<std::string(std::string)> make_greeter();

  /// 4. Passing effectful result to a HOF
  template <typename F0>
    requires std::is_invocable_r_v<int64_t, F0 &, int64_t &>
  static int64_t with_length(F0 &&f) {
    std::string line;
    std::getline(std::cin, line);
    return f(static_cast<int64_t>(line.length()));
  }

  static int64_t test_with_length();
  /// 5. Nested closures over bindings
  static int64_t nested_capture();

  /// 6. Closure used in a fold-like pattern
  template <typename F0>
    requires std::is_invocable_r_v<bool, F0 &, std::string &>
  static uint64_t count_matching(F0 &&pred, const List<std::string> &xs) {
    if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
      return UINT64_C(0);
    } else {
      const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(xs.v());
      uint64_t n = count_matching(pred, *a1);
      if (pred(a0)) {
        return (n + 1);
      } else {
        return n;
      }
    }
  }

  static uint64_t test_count();
  /// 7. Effect inside a let, result used later
  static int64_t let_effect_capture();
  /// 8. Two closures with different captured variables
  static std::pair<int64_t, int64_t> two_closures();
};

#endif // INCLUDED_MONADIC_CLOSURE
