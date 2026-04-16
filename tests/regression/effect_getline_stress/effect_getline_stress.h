#ifndef INCLUDED_EFFECT_GETLINE_STRESS
#define INCLUDED_EFFECT_GETLINE_STRESS

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

struct EffectGetlineStress {
  /// 1. get_line in both branches of if-then-else
  static std::string get_or_default(const bool ask);
  /// 2. get_line in a match arm
  static std::string get_nth_line(const unsigned int n);
  /// 3. Recursive function that uses get_line in a loop
  static std::shared_ptr<List<std::string>>
  read_lines(const unsigned int n, std::shared_ptr<List<std::string>> acc);
  /// 4. get_line result immediately used in another effect
  static void read_and_echo();
  /// 5. get_line result used in a let chain
  static int64_t get_line_length();
  /// 6. Two get_lines with results combined
  static std::string concat_two_lines();
  /// 7. get_line inside a monadic map
  static std::pair<std::string, int64_t> get_and_measure();
  /// 8. Conditional get_line with print
  static std::string interactive_prompt(const bool ask);
};

#endif // INCLUDED_EFFECT_GETLINE_STRESS
