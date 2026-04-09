#ifndef INCLUDED_EFFECT_OPTION_MATCH
#define INCLUDED_EFFECT_OPTION_MATCH

#include <cstdlib>
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

struct EffectOptionMatch {
  /// 1. get_env returns option, match immediately
  static std::string show_or_default(const std::string name,
                                     const std::string default0);
  /// 2. get_env with effect in one branch
  static std::string show_or_ask(const std::string name);
  /// 3. Multiple option matches in sequence
  static std::string
  get_first_set(const std::shared_ptr<List<std::string>> &names);
  /// 4. set then get, match on result
  static bool set_and_verify(const std::string name, const std::string value);
  /// 5. Recursive function with option matching
  static std::optional<std::string>
  find_env_value(const std::shared_ptr<List<std::string>> &names);
};

#endif // INCLUDED_EFFECT_OPTION_MATCH
