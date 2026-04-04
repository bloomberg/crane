#ifndef INCLUDED_BLOCK_TEMPLATE_SEMICOLON
#define INCLUDED_BLOCK_TEMPLATE_SEMICOLON

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct BlockTemplateSemicolon {
  /// String argument with semicolons in expression position (monad right
  /// identity) Tests gen_block_iife semicolon splitting
  static std::string read_semicolon_expr();
  /// String argument with semicolons in statement position (bind with
  /// computation) Tests Sblock_custom semicolon splitting
  static std::string read_semicolon_stmt();
  /// String argument with no semicolons (control case)
  static std::string read_normal();
};

#endif // INCLUDED_BLOCK_TEMPLATE_SEMICOLON
