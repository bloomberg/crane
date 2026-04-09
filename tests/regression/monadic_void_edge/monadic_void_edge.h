#ifndef INCLUDED_MONADIC_VOID_EDGE
#define INCLUDED_MONADIC_VOID_EDGE

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

struct MonadicVoidEdge {
  /// 1. Bind where LHS is void and RHS returns a value
  static unsigned int bind_void_then_value();
  /// 2. Bind where both sides are void
  static void bind_void_void();
  /// 3. Let-binding the result of a monadic void call
  static unsigned int let_bind_monadic_void();
  /// 4. Passing unit through a chain of binds
  static void unit_chain();
  /// 5. Match on a value obtained from a bind
  static unsigned int match_after_bind();
  /// 6. Void function called in a non-tail bind position
  static std::string void_nontail();
  /// 7. Nested binds returning unit at every level
  static void deeply_nested_void();

  /// 8. Higher-order: pass a monadic void function as callback
  template <MapsTo<void, unsigned int> F0>
  static void apply_effect(F0 &&f, const unsigned int _x0) {
    f(std::move(_x0));
    return;
  }

  static void test_apply_effect();
  /// 9. Monadic function returning option unit
  static std::optional<std::monostate> maybe_print(const bool b);
  /// 10. Bind result used in a pair
  static std::pair<unsigned int, unsigned int> bind_into_pair();
  /// 11. Void function result stored in list (should stay Unit, not void)
  static std::shared_ptr<List<std::monostate>> unit_in_list();
  /// 12. Mixed: some binds void, some value, interleaved
  static unsigned int mixed_binds();
  /// 13. Function that takes itree as argument and sequences
  static void sequence_effects(const std::monostate e1,
                               const std::monostate e2);
  static void test_sequence();
};

#endif // INCLUDED_MONADIC_VOID_EDGE
