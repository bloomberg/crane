#ifndef INCLUDED_MONADIC_CLOSURE
#define INCLUDED_MONADIC_CLOSURE

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

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
  explicit List(Nil _v) : d_v_(_v) {}

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

struct MonadicClosure {
  /// 1. Lambda capturing a bind result
  template <typename T1>
  __attribute__((pure)) static int64_t _capture_bind_f(const T1,
                                                       const std::string line) {
    return line.length();
  }

  static int64_t capture_bind();

  /// 2. Higher-order function taking a pure callback
  template <typename T1, typename T2, MapsTo<T2, T1> F0>
  static T2 apply_after_effect(F0 &&f, const T1 m) {
    T1 x = m;
    return f(x);
  }

  static int64_t test_apply_after();
  /// 3. Function returning a closure from monadic context
  static std::function<std::string(std::string)> make_greeter();

  /// 4. Passing effectful result to a HOF
  template <MapsTo<int64_t, int64_t> F0> static int64_t with_length(F0 &&f) {
    std::string line;
    std::getline(std::cin, line);
    return f(line.length());
  }

  static int64_t test_with_length();
  /// 5. Nested closures over bindings
  static int64_t nested_capture();

  /// 6. Closure used in a fold-like pattern
  template <MapsTo<bool, std::string> F0>
  static unsigned int
  count_matching(F0 &&pred, const std::shared_ptr<List<std::string>> &xs) {
    if (std::holds_alternative<typename List<std::string>::Nil>(xs->v())) {
      return 0u;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename List<std::string>::Cons>(xs->v());
      unsigned int n = count_matching(pred, d_a1);
      if (pred(d_a0)) {
        return (n + 1);
      } else {
        return n;
      }
    }
  }

  static unsigned int test_count();
  /// 7. Effect inside a let, result used later
  static int64_t let_effect_capture();
  /// 8. Two closures with different captured variables
  static std::pair<int64_t, int64_t> two_closures();
};

#endif // INCLUDED_MONADIC_CLOSURE
