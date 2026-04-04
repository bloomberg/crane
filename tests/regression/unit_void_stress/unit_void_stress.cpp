#include <unit_void_stress.h>

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

void UnitVoidStress::consume(const unsigned int n) {
  if (n <= 0) {
    return;
  } else {
    unsigned int m = n - 1;
    consume(m);
    return;
  }
}

void UnitVoidStress::discard(const unsigned int _x) { return; }

__attribute__((pure)) std::pair<unsigned int, std::monostate>
UnitVoidStress::pair_with_void_call(const unsigned int n) {
  return std::make_pair(42u, [&]() {
    consume(std::move(n));
    return std::monostate{};
  }());
}

__attribute__((pure)) std::optional<std::monostate>
UnitVoidStress::some_void_call(const unsigned int n) {
  return std::make_optional<std::monostate>([&]() {
    consume(std::move(n));
    return std::monostate{};
  }());
}

void UnitVoidStress::id_void_call(const unsigned int _x0) {
  consume(_x0);
  return;
}

__attribute__((pure)) std::pair<unsigned int, std::monostate>
UnitVoidStress::pair_with_discard(const unsigned int n) {
  return std::make_pair(n, [&]() {
    discard(n);
    return std::monostate{};
  }());
}

void UnitVoidStress::store_and_call(const unsigned int _x0) {
  consume(_x0);
  return;
}

__attribute__((pure)) std::pair<unsigned int, std::monostate>
UnitVoidStress::pair_via_let(const unsigned int n) {
  consume(n);
  std::monostate u = std::monostate{};
  return std::make_pair(42u, u);
}

void UnitVoidStress::cond_void(const bool b, const unsigned int n) {
  if (b) {
    consume(n);
    return;
  } else {
    discard(n);
    return;
  }
}

void UnitVoidStress::match_nat_void(const unsigned int n) {
  if (n <= 0) {
    return;
  } else {
    unsigned int m = n - 1;
    consume(m);
    return;
  }
}

__attribute__((pure))
std::pair<std::pair<unsigned int, std::monostate>, unsigned int>
UnitVoidStress::nested_pair_void(const unsigned int n) {
  return std::make_pair(std::make_pair(n,
                                       [&]() {
                                         consume(n);
                                         return std::monostate{};
                                       }()),
                        42u);
}

__attribute__((pure)) std::optional<std::pair<unsigned int, std::monostate>>
UnitVoidStress::option_pair_void(const unsigned int n) {
  return std::make_optional<std::pair<unsigned int, std::monostate>>(
      std::make_pair(n, [&]() {
        consume(n);
        return std::monostate{};
      }()));
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
UnitVoidStress::let_void_then_pair(const unsigned int n) {
  return std::make_pair(std::move(n), 42u);
}

__attribute__((pure)) unsigned int
UnitVoidStress::seq_voids_value(const unsigned int _x) {
  return 42u;
}

__attribute__((pure)) unsigned int
UnitVoidStress::void_in_one_branch(const bool b, const unsigned int n) {
  if (b) {
    return 42u;
  } else {
    return std::move(n);
  }
}

void UnitVoidStress::even_void(const unsigned int n) {
  if (n <= 0) {
    return;
  } else {
    unsigned int m = n - 1;
    odd_void(m);
    return;
  }
}

void UnitVoidStress::odd_void(const unsigned int n) {
  if (n <= 0) {
    return;
  } else {
    unsigned int m = n - 1;
    even_void(m);
    return;
  }
}

void UnitVoidStress::match_opt_void(const std::optional<unsigned int> o) {
  if (o.has_value()) {
    unsigned int n = *o;
    consume(n);
    return;
  } else {
    return;
  }
}
