#include <block_template_edge.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>

/// 1. Block template result used immediately in if-then-else
std::string BlockTemplateEdge::block_in_if() {
  bool b;
  b = true;
  return [&]() {
    if (b) {
      return "yes";
    } else {
      return "no";
    }
  }();
}

/// 2. Block template result used in arithmetic
int64_t BlockTemplateEdge::block_in_arith() {
  std::string n;
  std::getline(std::cin, n);
  return ((n.length() + int64_t(1)) & 0x7FFFFFFFFFFFFFFFLL);
}

/// 3. Two block templates of same type back-to-back
std::string BlockTemplateEdge::two_strings() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return a + b;
}

/// 4. Block template result bound but unused
unsigned int BlockTemplateEdge::block_unused() {
  std::string _x;
  std::getline(std::cin, _x);
  return 42u;
}

/// 5. Block template followed by non-block operation
int64_t BlockTemplateEdge::block_then_pure() {
  std::string s;
  std::getline(std::cin, s);
  int64_t n = s.length();
  return ((n + n) & 0x7FFFFFFFFFFFFFFFLL);
}
