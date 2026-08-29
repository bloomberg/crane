#ifndef INCLUDED_BLOCK_TEMPLATE_SEMICOLON
#define INCLUDED_BLOCK_TEMPLATE_SEMICOLON

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>

using namespace std::string_literals;

struct BlockTemplateSemicolon {
  static std::string read_semicolon_expr();
  static std::string read_semicolon_stmt();
  static std::string read_normal();
};

#endif // INCLUDED_BLOCK_TEMPLATE_SEMICOLON
