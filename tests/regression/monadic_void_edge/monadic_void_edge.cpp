#include <monadic_void_edge.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. Bind where LHS is void and RHS returns a value
unsigned int MonadicVoidEdge::bind_void_then_value() {
  std::cout << "hello"s << '\n';
  return 42u;
}

/// 2. Bind where both sides are void
void MonadicVoidEdge::bind_void_void() {
  std::cout << "a"s << '\n';
  std::cout << "b"s << '\n';
  return;
}

/// 3. Let-binding the result of a monadic void call
unsigned int MonadicVoidEdge::let_bind_monadic_void() {
  []() {
    std::cout << "side effect"s << '\n';
    return std::monostate{};
  }();
  return 99u;
}

/// 4. Passing unit through a chain of binds
void MonadicVoidEdge::unit_chain() {
  std::monostate x = std::monostate{};
  x;
  return;
}

/// 5. Match on a value obtained from a bind
unsigned int MonadicVoidEdge::match_after_bind() {
  bool b = true;
  return [&]() {
    if (b) {
      return 1u;
    } else {
      return 0u;
    }
  }();
}

/// 6. Void function called in a non-tail bind position
std::string MonadicVoidEdge::void_nontail() {
  std::cout << "prefix"s << '\n';
  std::string name;
  std::getline(std::cin, name);
  std::cout << name << '\n';
  return name;
}

/// 7. Nested binds returning unit at every level
void MonadicVoidEdge::deeply_nested_void() {
  std::cout << "1"s << '\n';
  std::cout << "2"s << '\n';
  std::cout << "3"s << '\n';
  std::cout << "4"s << '\n';
  return;
}

void MonadicVoidEdge::test_apply_effect() {
  apply_effect(
      [](unsigned int _x) {
        std::cout << "applied"s << '\n';
        return;
      },
      5u);
  return;
}

/// 9. Monadic function returning option unit
std::optional<std::monostate> MonadicVoidEdge::maybe_print(const bool b) {
  if (b) {
    std::cout << "yes"s << '\n';
    return std::make_optional<std::monostate>(std::monostate{});
  } else {
    return std::optional<std::monostate>();
  }
}

/// 10. Bind result used in a pair
std::pair<unsigned int, unsigned int> MonadicVoidEdge::bind_into_pair() {
  unsigned int a = 1u;
  unsigned int b = 2u;
  return std::make_pair(a, b);
}

/// 11. Void function result stored in list (should stay Unit, not void)
std::shared_ptr<List<std::monostate>> MonadicVoidEdge::unit_in_list() {
  std::monostate x = std::monostate{};
  std::monostate y = std::monostate{};
  return List<std::monostate>::cons(
      x, List<std::monostate>::cons(y, List<std::monostate>::nil()));
}

/// 12. Mixed: some binds void, some value, interleaved
unsigned int MonadicVoidEdge::mixed_binds() {
  std::cout << "start"s << '\n';
  unsigned int a = 10u;
  std::cout << "middle"s << '\n';
  unsigned int b = 20u;
  std::cout << "end"s << '\n';
  return (a + b);
}

/// 13. Function that takes itree as argument and sequences
void MonadicVoidEdge::sequence_effects(const std::monostate e1,
                                       const std::monostate e2) {
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
