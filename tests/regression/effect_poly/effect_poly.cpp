#include <effect_poly.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

unsigned int EffectPoly::test_map_result() {
  return map_result<unsigned int, unsigned int>(
      [](unsigned int x) { return (x + 1); }, 41u);
}

unsigned int EffectPoly::test_lift_nat() {
  return lift_pure<unsigned int>(42u);
}

std::string EffectPoly::test_lift_string() {
  return lift_pure<std::string>("hello");
}

bool EffectPoly::test_lift_bool() {
  return lift_pure<bool>(true);
} /// 3. Monadic when / guard

void EffectPoly::when_(const bool b, const std::monostate) {
  if (b) {
    return;
  } else {
    return;
  }
}

void EffectPoly::test_when() {
  when_(true, []() {
    std::cout << "guarded"s << '\n';
    return std::monostate{};
  }());
  return;
} /// 4. Monadic unless

void EffectPoly::unless(const bool b, const std::monostate) {
  if (b) {
    return;
  } else {
    return;
  }
}

void EffectPoly::test_unless() {
  unless(false, []() {
    std::cout << "unguarded"s << '\n';
    return std::monostate{};
  }());
  return;
}

/// 5. Monadic sequence of list of actions
void EffectPoly::sequence_void(
    const std::shared_ptr<List<std::monostate>> &actions) {
  {
    std::visit(Overloaded{[](const typename List<std::monostate>::Nil)
                              -> std::monostate { return std::monostate{}; },
                          [](const typename List<std::monostate>::Cons _args)
                              -> std::monostate {
                            _args.d_a0;
                            sequence_void(_args.d_a1);
                            return std::monostate{};
                          }},
               actions->v());
    return;
  }
}

void EffectPoly::test_sequence_void() {
  sequence_void(List<std::monostate>::cons(
      []() {
        std::cout << "a"s << '\n';
        return std::monostate{};
      }(),
      List<std::monostate>::cons(
          []() {
            std::cout << "b"s << '\n';
            return std::monostate{};
          }(),
          List<std::monostate>::nil())));
  return;
}

unsigned int EffectPoly::sum_with_logging(const unsigned int acc,
                                          const unsigned int n) {
  std::cout << "adding"s << '\n';
  return (acc + n);
}

unsigned int EffectPoly::test_fold() {
  return fold_m<unsigned int, unsigned int>(
      sum_with_logging, 0u,
      List<unsigned int>::cons(
          1u,
          List<unsigned int>::cons(
              2u, List<unsigned int>::cons(3u, List<unsigned int>::nil()))));
}

/// 7. Returning a pair from a monadic computation
std::pair<std::string, std::string> EffectPoly::read_two_lines() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return std::make_pair(a, b);
}

/// 8. Chaining monadic functions with different return types
int64_t EffectPoly::chain_types() {
  std::cout << "enter a number:"s << '\n';
  std::string line;
  std::getline(std::cin, line);
  int64_t len = line.length();
  return len;
}
