#include "effect_poly.h"

uint64_t EffectPoly::test_map_result() {
  return map_result<uint64_t, uint64_t>([](uint64_t x) { return (x + 1); },
                                        UINT64_C(41));
}

uint64_t EffectPoly::test_lift_nat() {
  return lift_pure<uint64_t>(UINT64_C(42));
}

std::string EffectPoly::test_lift_string() {
  return lift_pure<std::string>("hello");
}

bool EffectPoly::test_lift_bool() { return lift_pure<bool>(true); }

/// 3. Monadic when / guard
void EffectPoly::when_(bool b, std::monostate action) {
  if (b) {
    {
      std::move(action);
      return;
    }
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
}

/// 4. Monadic unless
void EffectPoly::unless(bool b, std::monostate action) {
  if (b) {
    return;
  } else {
    {
      std::move(action);
      return;
    }
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
void EffectPoly::sequence_void(const List<std::monostate> &actions) {
  if (std::holds_alternative<typename List<std::monostate>::Nil>(actions.v())) {
    return;
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::monostate>::Cons>(actions.v());
    a0;
    sequence_void(*a1);
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

uint64_t EffectPoly::sum_with_logging(uint64_t acc, uint64_t n) {
  std::cout << "adding"s << '\n';
  return (acc + n);
}

uint64_t EffectPoly::test_fold() {
  return fold_m<uint64_t, uint64_t>(
      sum_with_logging, UINT64_C(0),
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))));
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
  int64_t len = static_cast<int64_t>(std::move(line).length());
  return len;
}
