#include <block_template_semicolon.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>

/// String argument with semicolons in expression position (monad right
/// identity) Tests gen_block_iife semicolon splitting
std::string BlockTemplateSemicolon::read_semicolon_expr() {
  return []() -> std::string {
    std::string _r;
    {
      std::ifstream _f("path;with;semicolons"s);
      std::getline(_f, _r);
    };
    return _r;
  }();
}

/// String argument with semicolons in statement position (bind with
/// computation) Tests Sblock_custom semicolon splitting
std::string BlockTemplateSemicolon::read_semicolon_stmt() {
  std::string s;
  {
    std::ifstream _f("path;with;semicolons"s);
    std::getline(_f, s);
  };
  return s + " done"s;
}

/// String argument with no semicolons (control case)
std::string BlockTemplateSemicolon::read_normal() {
  std::string s;
  {
    std::ifstream _f("normal_path.txt"s);
    std::getline(_f, s);
  };
  return s + " ok"s;
}
