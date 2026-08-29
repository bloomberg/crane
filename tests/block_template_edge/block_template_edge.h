#ifndef INCLUDED_BLOCK_TEMPLATE_EDGE
#define INCLUDED_BLOCK_TEMPLATE_EDGE

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <utility>

struct BlockTemplateEdge {
  static std::string block_in_if();
  static int64_t block_in_arith();
  static std::string two_strings();
  static uint64_t block_unused();
  static int64_t block_then_pure();
};

#endif // INCLUDED_BLOCK_TEMPLATE_EDGE
