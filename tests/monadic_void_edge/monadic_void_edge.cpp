#include "monadic_void_edge.h"

uint64_t MonadicVoidEdge::bind_void_then_value() {
  std::cout << "hello"s << '\n';
  return UINT64_C(42);
}

void MonadicVoidEdge::bind_void_void() {
  std::cout << "a"s << '\n';
  std::cout << "b"s << '\n';
  return;
}

uint64_t MonadicVoidEdge::let_bind_monadic_void() {
  []() {
    std::cout << "side effect"s << '\n';
    return std::monostate{};
  }();
  return UINT64_C(99);
}

void MonadicVoidEdge::unit_chain() {
  std::monostate x = std::monostate{};
  x;
  return;
}

uint64_t MonadicVoidEdge::match_after_bind() {
  bool b = true;
  return (b ? UINT64_C(1) : UINT64_C(0));
}

std::string MonadicVoidEdge::void_nontail() {
  std::cout << "prefix"s << '\n';
  std::string name;
  std::getline(std::cin, name);
  std::cout << name << '\n';
  return name;
}

void MonadicVoidEdge::deeply_nested_void() {
  std::cout << "1"s << '\n';
  std::cout << "2"s << '\n';
  std::cout << "3"s << '\n';
  std::cout << "4"s << '\n';
  return;
}

void MonadicVoidEdge::test_apply_effect() {
  apply_effect(
      [](uint64_t) {
        std::cout << "applied"s << '\n';
        return std::monostate{};
      },
      UINT64_C(5));
  return;
}

std::optional<std::monostate> MonadicVoidEdge::maybe_print(bool b) {
  if (b) {
    std::cout << "yes"s << '\n';
    return std::make_optional<std::monostate>(std::monostate{});
  } else {
    return std::optional<std::monostate>();
  }
}

std::pair<uint64_t, uint64_t> MonadicVoidEdge::bind_into_pair() {
  uint64_t a = UINT64_C(1);
  uint64_t b = UINT64_C(2);
  return std::make_pair(a, b);
}

List<std::monostate> MonadicVoidEdge::unit_in_list() {
  std::monostate x = std::monostate{};
  std::monostate y = std::monostate{};
  return List<std::monostate>::cons(
      x, List<std::monostate>::cons(y, List<std::monostate>::nil()));
}

uint64_t MonadicVoidEdge::mixed_binds() {
  std::cout << "start"s << '\n';
  uint64_t a = UINT64_C(10);
  std::cout << "middle"s << '\n';
  uint64_t b = UINT64_C(20);
  std::cout << "end"s << '\n';
  return (a + b);
}

void MonadicVoidEdge::sequence_effects(const std::monostate &e1,
                                       const std::monostate &) {
  e1;
  return;
}

void MonadicVoidEdge::test_sequence() {
  sequence_effects(
      []() {
        std::cout << "first"s << '\n';
        return std::monostate{};
      }(),
      []() {
        std::cout << "second"s << '\n';
        return std::monostate{};
      }());
  return;
}
