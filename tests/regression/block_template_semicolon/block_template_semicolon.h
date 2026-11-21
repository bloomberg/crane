#pragma once

#include <crane_string.h>
#include <fstream>
#include <string>
#include <string_view>

struct BlockTemplateSemicolon {
  /// String argument with semicolons in expression position (monad right
  /// identity)
  /// Tests gen_block_iife semicolon splitting
  static std::string read_semicolon_expr();
  /// String argument with semicolons in statement position (bind with
  /// computation)
  /// Tests Sblock_custom semicolon splitting
  static std::string read_semicolon_stmt();
  /// String argument with no semicolons (control case)
  static std::string read_normal();
};
