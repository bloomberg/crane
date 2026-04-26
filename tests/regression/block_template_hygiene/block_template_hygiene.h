#ifndef INCLUDED_BLOCK_TEMPLATE_HYGIENE
#define INCLUDED_BLOCK_TEMPLATE_HYGIENE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

template <typename T> struct is_unique_ptr : std::false_type {};

template <typename T>
struct is_unique_ptr<std::unique_ptr<T>> : std::true_type {
  using element_type = T;
};

template <typename T> auto clone_value(const T &x) { return x; }

template <typename T>
std::unique_ptr<T> clone_value(const std::unique_ptr<T> &x) {
  if constexpr (requires { x->clone(); }) {
    return x ? std::make_unique<T>(x->clone()) : nullptr;
  } else {
    return x ? std::make_unique<T>(*x) : nullptr;
  }
}

template <typename Target, typename Source>
Target clone_as_value(const Source &x) {
  using T = std::remove_cvref_t<Target>;
  using S = std::remove_cvref_t<Source>;
  if constexpr (requires(const S &s) {
                  s.has_value();
                  *s;
                }) {
    if (!x.has_value())
      return T{};
    using TInner = std::remove_cvref_t<decltype(*std::declval<const T &>())>;
    return T{clone_as_value<TInner>(*x)};
  } else if constexpr (std::is_same_v<T, S>) {
    if constexpr (is_unique_ptr<T>::value) {
      return clone_value(x);
    } else if constexpr (requires { x.clone(); }) {
      return x.clone();
    } else {
      return x;
    }
  } else if constexpr (is_unique_ptr<S>::value) {
    if (!x)
      return T{};
    return clone_as_value<T>(*x);
  } else if constexpr (is_unique_ptr<T>::value) {
    using Inner = typename is_unique_ptr<T>::element_type;
    return std::make_unique<Inner>(clone_as_value<Inner>(x));
  } else {
    return T(x);
  }
}

struct BlockTemplateHygiene {
  /// Test 1: Two consecutive get_line calls with the SAME binder name s.
  /// The second s should be freshened (e.g., s0) by Crane's rename_id.
  static std::string same_name_twice();
  /// Test 2: Three consecutive get_line calls, all named s.
  /// Tests multiple rounds of freshening.
  static std::string same_name_thrice();
  /// Test 3: get_line with bind name s — the exact variable name that the old
  /// IIFE template used internally (std::string s; std::getline(std::cin, s)).
  /// With block templates, there is no internal variable; %result IS the
  /// bind target, so no collision.
  /// Note: we use cat s "!" instead of Ret s to prevent the monad right
  /// identity optimization (bind m Ret = m) from bypassing the bind handler.
  static std::string shadow_internal_name();
  /// Test 4: Multiple different block templates in the same scope.
  /// Uses get_line (block template) interleaved with print (expression
  /// template) to verify that block templates don't interfere with expression
  /// templates.
  static std::string interleaved_templates();
  /// Test 5: Block template with %a0 argument alongside %result.
  /// Uses our custom read_trimmed which has both %result and %a0.
  static std::string block_with_args();
  /// Test 6: Multiple block templates with %a0, same binder name.
  /// Two calls to read_trimmed both named s.
  static std::string block_with_args_same_name();
  /// Test 7: Block template result used as an argument to another call.
  /// Tests that the generated variable is properly referenced after the
  /// block expansion.
  static void result_in_expr();
  /// Test 8: Block template in a let-binding context (non-monadic).
  /// Uses a let to capture an intermediate value derived from a block
  /// template result.
  static std::string let_after_block();
  /// Test 9: get_line bound to the name result to stress-test that
  /// the C++ variable result doesn't collide with any internal
  /// expansion logic.
  static std::string bind_named_result();
  /// Test 10: get_line bound to the name _r — the internal IIFE
  /// fallback variable name. Ensures no collision with the expression-
  /// position IIFE wrapper's internal variable.
  static std::string bind_named_underscore_r();
  /// Test 11: Block template in pure expression position (not in bind).
  /// Verifies that the IIFE fallback generates valid C++ when a block
  /// template is used as a subexpression.
  /// bind get_line Ret triggers the monad right identity optimization,
  /// placing get_line directly in expression position.
  static std::string expr_position_iife();
};

#endif // INCLUDED_BLOCK_TEMPLATE_HYGIENE
