#include <block_template_hygiene.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

/// Test 1: Two consecutive get_line calls with the SAME binder name s.
/// The second s should be freshened (e.g., s0) by Crane's rename_id.
std::string BlockTemplateHygiene::same_name_twice() {
  std::string _x;
  std::getline(std::cin, _x);
  std::string s;
  std::getline(std::cin, s);
  return s + " (second)"s;
}

/// Test 2: Three consecutive get_line calls, all named s.
/// Tests multiple rounds of freshening.
std::string BlockTemplateHygiene::same_name_thrice() {
  std::string _x;
  std::getline(std::cin, _x);
  std::string _x0;
  std::getline(std::cin, _x0);
  std::string s;
  std::getline(std::cin, s);
  return s + " (third)"s;
}

/// Test 3: get_line with bind name s — the exact variable name that the old
/// IIFE template used internally (std::string s; std::getline(std::cin, s)).
/// With block templates, there is no internal variable; %result IS the
/// bind target, so no collision.
/// Note: we use cat s "!" instead of Ret s to prevent the monad right
/// identity optimization (bind m Ret = m) from bypassing the bind handler.
std::string BlockTemplateHygiene::shadow_internal_name() {
  std::string s;
  std::getline(std::cin, s);
  return s + "!"s;
}

/// Test 4: Multiple different block templates in the same scope.
/// Uses get_line (block template) interleaved with print (expression template)
/// to verify that block templates don't interfere with expression templates.
std::string BlockTemplateHygiene::interleaved_templates() {
  std::string a;
  std::getline(std::cin, a);
  std::cout << a;
  std::string b;
  std::getline(std::cin, b);
  std::cout << b << '\n';
  std::string c;
  std::getline(std::cin, c);
  return a + b + c;
}

/// Test 5: Block template with %a0 argument alongside %result.
/// Uses our custom read_trimmed which has both %result and %a0.
std::string BlockTemplateHygiene::block_with_args() {
  std::string s;
  {
    std::ifstream _f("data.txt"s);
    std::getline(_f, s);
  };
  return s + " read"s;
}

/// Test 6: Multiple block templates with %a0, same binder name.
/// Two calls to read_trimmed both named s.
std::string BlockTemplateHygiene::block_with_args_same_name() {
  std::string _x;
  {
    std::ifstream _f("a.txt"s);
    std::getline(_f, _x);
  };
  std::string s;
  {
    std::ifstream _f("b.txt"s);
    std::getline(_f, s);
  };
  return s + " done"s;
}

/// Test 7: Block template result used as an argument to another call.
/// Tests that the generated variable is properly referenced after the
/// block expansion.
void BlockTemplateHygiene::result_in_expr() {
  std::string name;
  std::getline(std::cin, name);
  std::cout << "Hello, "s + name << '\n';
  return;
}

/// Test 8: Block template in a let-binding context (non-monadic).
/// Uses a let to capture an intermediate value derived from a block
/// template result.
std::string BlockTemplateHygiene::let_after_block() {
  std::string first;
  std::getline(std::cin, first);
  std::string last;
  std::getline(std::cin, last);
  std::string full = first + " "s + last;
  return full;
}

/// Test 9: get_line bound to the name result to stress-test that
/// the C++ variable result doesn't collide with any internal
/// expansion logic.
std::string BlockTemplateHygiene::bind_named_result() {
  std::string result;
  std::getline(std::cin, result);
  return result + "!"s;
}

/// Test 10: get_line bound to the name _r — the internal IIFE
/// fallback variable name. Ensures no collision with the expression-
/// position IIFE wrapper's internal variable.
std::string BlockTemplateHygiene::bind_named_underscore_r() {
  std::string _r;
  std::getline(std::cin, _r);
  return _r + "!"s;
}

/// Test 11: Block template in pure expression position (not in bind).
/// Verifies that the IIFE fallback generates valid C++ when a block
/// template is used as a subexpression.
/// bind get_line Ret triggers the monad right identity optimization,
/// placing get_line directly in expression position.
std::string BlockTemplateHygiene::expr_position_iife() {
  return []() -> std::string {
    std::string _r;
    std::getline(std::cin, _r);
    return _r;
  }();
}
