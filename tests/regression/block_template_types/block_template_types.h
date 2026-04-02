#ifndef INCLUDED_BLOCK_TEMPLATE_TYPES
#define INCLUDED_BLOCK_TEMPLATE_TYPES

#include <string>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct BlockTemplateTypes {
  /// %result inferred as unsigned int.
  static unsigned int test_read_nat();
  /// %result inferred as bool, with unsigned int in same scope.
  static std::string test_is_positive();
  /// %result inferred as unsigned int from string argument.
  /// Tests %a0 and %result together with nat return type.
  static unsigned int test_parse_nat();
  /// Three different block template types in one function:
  /// std::string (get_line), unsigned int (read_nat), bool (is_positive).
  static std::string test_mixed();
  /// Two unsigned int block templates with arithmetic on results.
  static unsigned int test_nat_arith();
};

#endif // INCLUDED_BLOCK_TEMPLATE_TYPES
