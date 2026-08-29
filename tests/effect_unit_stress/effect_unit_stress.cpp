#include "effect_unit_stress.h"

void EffectUnitStress::ret_tt_simple() { return; }

void EffectUnitStress::ret_tt_after_bind() { return; }

void EffectUnitStress::ret_tt_after_effect() {
  std::cout << "x"s << '\n';
  return;
}

std::string EffectUnitStress::bind_identity() {
  return []() -> std::string {
    std::string _r;
    std::getline(std::cin, _r);
    return _r;
  }();
}

uint64_t EffectUnitStress::bind_ignore() {
  std::string _x;
  std::getline(std::cin, _x);
  return UINT64_C(0);
}

void EffectUnitStress::conditional_tt(bool b) {
  if (b) {
    return;
  } else {
    return;
  }
}

void EffectUnitStress::conditional_mixed(bool b) {
  if (b) {
    std::cout << "yes"s << '\n';
    return;
  } else {
    return;
  }
}

std::pair<std::string, std::string> EffectUnitStress::pair_of_effects() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return std::make_pair(a, b);
}

std::string EffectUnitStress::nat_dispatch(uint64_t n) {
  if (n <= 0) {
    return "zero";
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return "one";
    } else {
      uint64_t _x = n0 - 1;
      return "many";
    }
  }
}

int64_t EffectUnitStress::let_pure_in_monadic() {
  std::string s;
  std::getline(std::cin, s);
  int64_t n = static_cast<int64_t>(std::move(s).length());
  int64_t m = static_cast<int64_t>(
      (static_cast<uint64_t>(n) + static_cast<uint64_t>(INT64_C(1))) &
      0x7FFFFFFFFFFFFFFFULL);
  return m;
}

std::string EffectUnitStress::nested_if_monadic(bool b1, bool b2) {
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

std::optional<uint64_t> EffectUnitStress::safe_head(const List<uint64_t> &xs) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    std::cout << "empty!"s << '\n';
    return std::optional<uint64_t>();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
    return std::make_optional<uint64_t>(a0);
  }
}
