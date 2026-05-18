#ifndef INCLUDED_BLOCK_TEMPLATE_TYPES
#define INCLUDED_BLOCK_TEMPLATE_TYPES

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>

struct BlockTemplateTypes {
  /// %result inferred as unsigned int.
  static uint64_t test_read_nat();
  /// %result inferred as bool, with unsigned int in same scope.
  static std::string test_is_positive();
  /// %result inferred as unsigned int from string argument.
  /// Tests %a0 and %result together with nat return type.
  static uint64_t test_parse_nat();
  /// Three different block template types in one function:
  /// std::string (get_line), unsigned int (read_nat), bool (is_positive).
  static std::string test_mixed();
  /// Two unsigned int block templates with arithmetic on results.
  static uint64_t test_nat_arith();
};

#endif // INCLUDED_BLOCK_TEMPLATE_TYPES
