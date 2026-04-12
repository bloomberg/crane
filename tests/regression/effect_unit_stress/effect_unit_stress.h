#ifndef INCLUDED_EFFECT_UNIT_STRESS
#define INCLUDED_EFFECT_UNIT_STRESS

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

struct EffectUnitStress {
  /// 1. Ret tt at different nesting depths
  static void ret_tt_simple();
  static void ret_tt_after_bind();
  static void ret_tt_after_effect();
  /// 2. Bind where RHS is Ret of the LHS binding
  static std::string bind_identity();
  /// 3. Bind where RHS ignores the binding
  static unsigned int bind_ignore();
  /// 4. Multiple Ret tt in if-then-else
  static void conditional_tt(const bool b);
  /// 5. Ret in one branch, effect in other
  static void conditional_mixed(const bool b);
  /// 6. Tuple of monadic results
  static std::pair<std::string, std::string> pair_of_effects();
  /// 7. match on nat with monadic body
  static std::string nat_dispatch(const unsigned int n);
  /// 8. let in monadic context with pure computation
  static int64_t let_pure_in_monadic();
  /// 9. Nested if in monadic context
  static std::string nested_if_monadic(const bool b1, const bool b2);
  /// 10. Monadic function returning option
  static std::optional<unsigned int>
  safe_head(const std::shared_ptr<List<unsigned int>> &xs);
};

#endif // INCLUDED_EFFECT_UNIT_STRESS
