#include "monadic_void_edge.h"

/// 1. Bind where LHS is void and RHS returns a value
uint64_t MonadicVoidEdge::bind_void_then_value() {
  std::cout << std::string("hello") << '\n';
  return UINT64_C(42);
}

/// 2. Bind where both sides are void
void MonadicVoidEdge::bind_void_void() {
  std::cout << std::string("a") << '\n';
  std::cout << std::string("b") << '\n';
  return;
}

/// 3. Let-binding the result of a monadic void call
uint64_t MonadicVoidEdge::let_bind_monadic_void() {
  []() {
    std::cout << std::string("side effect") << '\n';
    return std::monostate{};
  }();
  return UINT64_C(99);
}

/// 4. Passing unit through a chain of binds
void MonadicVoidEdge::unit_chain() {
  std::monostate x = std::monostate{};
  x;
  return;
}

/// 5. Match on a value obtained from a bind
uint64_t MonadicVoidEdge::match_after_bind() {
  bool b = true;
  return (b ? UINT64_C(1) : UINT64_C(0));
}

/// 6. Void function called in a non-tail bind position
std::string MonadicVoidEdge::void_nontail() {
  std::cout << std::string("prefix") << '\n';
  std::string name;
  std::getline(std::cin, name);
  std::cout << name << '\n';
  return name;
}

/// 7. Nested binds returning unit at every level
void MonadicVoidEdge::deeply_nested_void() {
  std::cout << std::string("1") << '\n';
  std::cout << std::string("2") << '\n';
  std::cout << std::string("3") << '\n';
  std::cout << std::string("4") << '\n';
  return;
}

void MonadicVoidEdge::test_apply_effect() {
  apply_effect(
      [](uint64_t) {
        std::cout << std::string("applied") << '\n';
        return std::monostate{};
      },
      UINT64_C(5));
  return;
}

/// 9. Monadic function returning option unit
std::optional<std::monostate> MonadicVoidEdge::maybe_print(bool b) {
  if (b) {
    std::cout << std::string("yes") << '\n';
    return std::make_optional<std::monostate>(std::monostate{});
  } else {
    return std::optional<std::monostate>();
  }
}

/// 10. Bind result used in a pair
std::pair<uint64_t, uint64_t> MonadicVoidEdge::bind_into_pair() {
  uint64_t a = UINT64_C(1);
  uint64_t b = UINT64_C(2);
  return std::make_pair(a, b);
}

/// 11. Void function result stored in list (should stay Unit, not void)
List<std::monostate> MonadicVoidEdge::unit_in_list() {
  std::monostate x = std::monostate{};
  std::monostate y = std::monostate{};
  return List<std::monostate>::cons(
      x, List<std::monostate>::cons(y, List<std::monostate>::nil()));
}

/// 12. Mixed: some binds void, some value, interleaved
uint64_t MonadicVoidEdge::mixed_binds() {
  std::cout << std::string("start") << '\n';
  uint64_t a = UINT64_C(10);
  std::cout << std::string("middle") << '\n';
  uint64_t b = UINT64_C(20);
  std::cout << std::string("end") << '\n';
  return (a + b);
}

/// 13. Function that takes itree as argument and sequences
void MonadicVoidEdge::sequence_effects(const std::monostate &e1,
                                       const std::monostate &) {
  e1;
  return;
}

void MonadicVoidEdge::test_sequence() {
  sequence_effects(
      []() {
        std::cout << std::string("first") << '\n';
        return std::monostate{};
      }(),
      []() {
        std::cout << std::string("second") << '\n';
        return std::monostate{};
      }());
  return;
}
