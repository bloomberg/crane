#include <bake_string_literal.h>

#include <iostream>
#include <string>

int main() {
  std::string w = BakeStringLiteral::word;
  std::cout << w << std::endl;
  return (w == "abc" && BakeStringLiteral::word_ok) ? 0 : 1;
}
