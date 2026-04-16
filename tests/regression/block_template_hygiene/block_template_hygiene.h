#ifndef INCLUDED_BLOCK_TEMPLATE_HYGIENE
#define INCLUDED_BLOCK_TEMPLATE_HYGIENE

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

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
