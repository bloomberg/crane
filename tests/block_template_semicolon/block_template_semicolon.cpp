#include "block_template_semicolon.h"

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

std::string BlockTemplateSemicolon::read_semicolon_stmt() {
  std::string s;
  {
    std::ifstream _f("path;with;semicolons"s);
    std::getline(_f, s);
  };
  return s + " done"s;
}

std::string BlockTemplateSemicolon::read_normal() {
  std::string s;
  {
    std::ifstream _f("normal_path.txt"s);
    std::getline(_f, s);
  };
  return s + " ok"s;
}
