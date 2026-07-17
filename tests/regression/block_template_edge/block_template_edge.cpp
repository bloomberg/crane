#include "block_template_edge.h"

/// 1. Block template result used immediately in if-then-else
std::string BlockTemplateEdge::block_in_if() {
  bool b;
  b = true;
  return [=]() mutable -> std::string {
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
  return static_cast<int64_t>(
      (static_cast<uint64_t>(static_cast<int64_t>(n.length())) +
       static_cast<uint64_t>(INT64_C(1))) &
      0x7FFFFFFFFFFFFFFFULL);
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
uint64_t BlockTemplateEdge::block_unused() {
  std::string _x;
  std::getline(std::cin, _x);
  return UINT64_C(42);
}

/// 5. Block template followed by non-block operation
int64_t BlockTemplateEdge::block_then_pure() {
  std::string s;
  std::getline(std::cin, s);
  int64_t n = static_cast<int64_t>(std::move(s).length());
  return static_cast<int64_t>(
      (static_cast<uint64_t>(n) + static_cast<uint64_t>(n)) &
      0x7FFFFFFFFFFFFFFFULL);
}
