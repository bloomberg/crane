#ifndef INCLUDED_BLOCK_TEMPLATE_TYPES
#define INCLUDED_BLOCK_TEMPLATE_TYPES

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>

struct BlockTemplateTypes {
  static uint64_t test_read_nat();
  static std::string test_is_positive();
  static uint64_t test_parse_nat();
  static std::string test_mixed();
  static uint64_t test_nat_arith();
};

#endif // INCLUDED_BLOCK_TEMPLATE_TYPES
