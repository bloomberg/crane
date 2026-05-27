#ifndef INCLUDED_BLOCK_TEMPLATE_EDGE
#define INCLUDED_BLOCK_TEMPLATE_EDGE

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <utility>

struct BlockTemplateEdge {
  /// 1. Block template result used immediately in if-then-else
  static std::string block_in_if();
  /// 2. Block template result used in arithmetic
  static int64_t block_in_arith();
  /// 3. Two block templates of same type back-to-back
  static std::string two_strings();
  /// 4. Block template result bound but unused
  static uint64_t block_unused();
  /// 5. Block template followed by non-block operation
  static int64_t block_then_pure();
};

#endif // INCLUDED_BLOCK_TEMPLATE_EDGE
