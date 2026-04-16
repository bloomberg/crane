#ifndef INCLUDED_BLOCK_TEMPLATE_EDGE
#define INCLUDED_BLOCK_TEMPLATE_EDGE

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct BlockTemplateEdge {
  /// 1. Block template result used immediately in if-then-else
  static std::string block_in_if();
  /// 2. Block template result used in arithmetic
  static int64_t block_in_arith();
  /// 3. Two block templates of same type back-to-back
  static std::string two_strings();
  /// 4. Block template result bound but unused
  static unsigned int block_unused();
  /// 5. Block template followed by non-block operation
  static int64_t block_then_pure();
};

#endif // INCLUDED_BLOCK_TEMPLATE_EDGE
