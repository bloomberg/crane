#include "match_monadic.h"

/// 1. Match on custom inductive with effects in each arm
std::string MatchMonadic::color_name(Color c) {
  switch (c) {
  case Color::RED: {
    std::cout << "red"s << '\n';
    return "red";
  }
  case Color::GREEN: {
    std::cout << "green"s << '\n';
    return "green";
  }
  case Color::BLUE: {
    std::cout << "blue"s << '\n';
    return "blue";
  }
  default:
    std::unreachable();
  }
}

/// 2. Match on bool inside a bind chain
std::string MatchMonadic::conditional_read(bool b) {
  if (b) {
    std::string line;
    std::getline(std::cin, line);
    return "got: "s + line;
  } else {
    return "skipped";
  }
}

/// 3. Nested match: match on result of another match
std::string MatchMonadic::nested_match(uint64_t n, bool b) {
  std::string label;
  if (n <= 0) {
    label = "zero";
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      label = "one";
    } else {
      uint64_t _x = n0 - 1;
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
uint64_t MatchMonadic::handle_option(const std::optional<uint64_t> &o) {
  if (o.has_value()) {
    const uint64_t &n = *o;
    std::cout << "found"s << '\n';
    return n;
  } else {
    std::cout << "missing"s << '\n';
    return UINT64_C(0);
  }
}

/// 5. Recursive function matching on tree
uint64_t MatchMonadic::tree_sum(const Tree<uint64_t> &t) {
  if (std::holds_alternative<typename Tree<uint64_t>::Leaf>(t.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1, a2] = std::get<typename Tree<uint64_t>::Node>(t.v());
    std::cout << "visiting"s << '\n';
    uint64_t sl = tree_sum(*a0);
    uint64_t sr = tree_sum(*a2);
    return ((sl + a1) + sr);
  }
}

/// 6. Match result used in bind
std::string MatchMonadic::match_then_bind(uint64_t n) {
  std::string tag;
  if (n <= 0) {
    tag = "A";
  } else {
    uint64_t _x = n - 1;
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
  int64_t len = static_cast<int64_t>(line.length());
  if (len == int64_t(0)) {
    std::cout << "empty"s << '\n';
    return int64_t(0);
  } else {
    return len;
  }
}

/// 8. Multiple matches in sequence
std::string MatchMonadic::multi_match(bool a, bool b) {
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
