#include <match_monadic.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. Match on custom inductive with effects in each arm
std::string MatchMonadic::color_name(const Color c) {
  switch (c) {
  case Color::e_RED: {
    std::cout << "red"s << '\n';
    return "red";
  }
  case Color::e_GREEN: {
    std::cout << "green"s << '\n';
    return "green";
  }
  case Color::e_BLUE: {
    std::cout << "blue"s << '\n';
    return "blue";
  }
  default:
    std::unreachable();
  }
}

/// 2. Match on bool inside a bind chain
std::string MatchMonadic::conditional_read(const bool b) {
  if (b) {
    std::string line;
    std::getline(std::cin, line);
    return "got: "s + line;
  } else {
    return "skipped";
  }
}

/// 3. Nested match: match on result of another match
std::string MatchMonadic::nested_match(const unsigned int n, const bool b) {
  std::string label;
  if (n <= 0) {
    label = "zero";
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      label = "one";
    } else {
      unsigned int _x = n0 - 1;
      label = "many";
    }
  }
  if (b) {
    std::cout << label << '\n';
    return label;
  } else {
    return "ignored";
  }
}

/// 4. Match on option in monadic context
unsigned int MatchMonadic::handle_option(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int n = *o;
    std::cout << "found"s << '\n';
    return n;
  } else {
    std::cout << "missing"s << '\n';
    return 0u;
  }
}

/// 5. Recursive function matching on tree
unsigned int
MatchMonadic::tree_sum(const std::shared_ptr<Tree<unsigned int>> &t) {
  return std::visit(
      Overloaded{
          [](const typename Tree<unsigned int>::Leaf _args) -> unsigned int {
            return 0u;
          },
          [](const typename Tree<unsigned int>::Node _args) -> unsigned int {
            std::cout << "visiting"s << '\n';
            unsigned int sl = tree_sum(_args.d_a0);
            unsigned int sr = tree_sum(_args.d_a2);
            return ((sl + _args.d_a1) + sr);
          }},
      t->v());
}

/// 6. Match result used in bind
std::string MatchMonadic::match_then_bind(const unsigned int n) {
  std::string tag;
  if (n <= 0) {
    tag = "A";
  } else {
    unsigned int _x = n - 1;
    tag = "B";
  }
  std::string line;
  std::getline(std::cin, line);
  return tag + line;
}

/// 7. Match inside a bind continuation
int64_t MatchMonadic::bind_then_match() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = line.length();
  if (len == int64_t(0)) {
    std::cout << "empty"s << '\n';
    return int64_t(0);
  } else {
    return len;
  }
}

/// 8. Multiple matches in sequence
std::string MatchMonadic::multi_match(const bool a, const bool b) {
  std::string x;
  if (a) {
    x = "A";
  } else {
    x = "a";
  }
  std::string y;
  if (b) {
    y = "B";
  } else {
    y = "b";
  }
  std::cout << x + y << '\n';
  return x + y;
}
