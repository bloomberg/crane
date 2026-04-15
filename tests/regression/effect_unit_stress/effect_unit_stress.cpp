#include <effect_unit_stress.h>

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

/// 1. Ret tt at different nesting depths
void EffectUnitStress::ret_tt_simple() { return; }

void EffectUnitStress::ret_tt_after_bind() { return; }

void EffectUnitStress::ret_tt_after_effect() {
  std::cout << "x"s << '\n';
  return;
}

/// 2. Bind where RHS is Ret of the LHS binding
std::string EffectUnitStress::bind_identity() {
  return []() -> std::string {
    std::string _r;
    std::getline(std::cin, _r);
    return _r;
  }();
}

/// 3. Bind where RHS ignores the binding
unsigned int EffectUnitStress::bind_ignore() {
  std::string _x;
  std::getline(std::cin, _x);
  return 0u;
}

/// 4. Multiple Ret tt in if-then-else
void EffectUnitStress::conditional_tt(const bool b) {
  if (b) {
    return;
  } else {
    return;
  }
}

/// 5. Ret in one branch, effect in other
void EffectUnitStress::conditional_mixed(const bool b) {
  if (b) {
    std::cout << "yes"s << '\n';
    return;
  } else {
    return;
  }
}

/// 6. Tuple of monadic results
std::pair<std::string, std::string> EffectUnitStress::pair_of_effects() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return std::make_pair(a, b);
}

/// 7. match on nat with monadic body
std::string EffectUnitStress::nat_dispatch(const unsigned int n) {
  if (n <= 0) {
    return "zero";
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return "one";
    } else {
      unsigned int _x = n0 - 1;
      return "many";
    }
  }
}

/// 8. let in monadic context with pure computation
int64_t EffectUnitStress::let_pure_in_monadic() {
  std::string s;
  std::getline(std::cin, s);
  int64_t n = s.length();
  int64_t m = ((n + int64_t(1)) & 0x7FFFFFFFFFFFFFFFLL);
  return m;
}

/// 9. Nested if in monadic context
std::string EffectUnitStress::nested_if_monadic(const bool b1, const bool b2) {
  if (b1) {
    if (b2) {
      return "both";
    } else {
      return "first";
    }
  } else {
    if (b2) {
      return "second";
    } else {
      return "neither";
    }
  }
}

/// 10. Monadic function returning option
std::optional<unsigned int>
EffectUnitStress::safe_head(const std::shared_ptr<List<unsigned int>> &xs) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(xs->v())) {
    std::cout << "empty!"s << '\n';
    return std::optional<unsigned int>();
  } else {
    const auto &_m = *std::get_if<typename List<unsigned int>::Cons>(&xs->v());
    return std::make_optional<unsigned int>(_m.d_a0);
  }
}
