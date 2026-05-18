#include "unit_void_stress.h"

void UnitVoidStress::consume(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t m = n - 1;
    consume(m);
    return;
  }
}

void UnitVoidStress::discard(uint64_t) { return; }

std::pair<uint64_t, std::monostate>
UnitVoidStress::pair_with_void_call(uint64_t n) {
  return std::make_pair(UINT64_C(42), [=]() mutable {
    consume(n);
    return std::monostate{};
  }());
}

std::optional<std::monostate> UnitVoidStress::some_void_call(uint64_t n) {
  return std::make_optional<std::monostate>([=]() mutable {
    consume(n);
    return std::monostate{};
  }());
}

void UnitVoidStress::id_void_call(uint64_t _x0) {
  consume(_x0);
  return;
}

std::pair<uint64_t, std::monostate>
UnitVoidStress::pair_with_discard(uint64_t n) {
  return std::make_pair(std::move(n), [=]() mutable {
    discard(n);
    return std::monostate{};
  }());
}

void UnitVoidStress::store_and_call(uint64_t _x0) {
  consume(_x0);
  return;
}

std::pair<uint64_t, std::monostate> UnitVoidStress::pair_via_let(uint64_t n) {
  consume(n);
  std::monostate u = std::monostate{};
  return std::make_pair(UINT64_C(42), u);
}

void UnitVoidStress::cond_void(bool b, uint64_t n) {
  if (b) {
    consume(n);
    return;
  } else {
    discard(n);
    return;
  }
}

void UnitVoidStress::match_nat_void(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t m = n - 1;
    consume(m);
    return;
  }
}

std::pair<std::pair<uint64_t, std::monostate>, uint64_t>
UnitVoidStress::nested_pair_void(uint64_t n) {
  return std::make_pair(std::make_pair(n,
                                       [=]() mutable {
                                         consume(n);
                                         return std::monostate{};
                                       }()),
                        UINT64_C(42));
}

std::optional<std::pair<uint64_t, std::monostate>>
UnitVoidStress::option_pair_void(uint64_t n) {
  return std::make_optional<std::pair<uint64_t, std::monostate>>(
      std::make_pair(n, [=]() mutable {
        consume(n);
        return std::monostate{};
      }()));
}

std::pair<uint64_t, uint64_t> UnitVoidStress::let_void_then_pair(uint64_t n) {
  return std::make_pair(std::move(n), UINT64_C(42));
}

uint64_t UnitVoidStress::seq_voids_value(uint64_t) { return UINT64_C(42); }

uint64_t UnitVoidStress::void_in_one_branch(bool b, uint64_t n) {
  if (b) {
    return UINT64_C(42);
  } else {
    return n;
  }
}

void UnitVoidStress::even_void(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t m = n - 1;
    odd_void(m);
    return;
  }
}

void UnitVoidStress::odd_void(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t m = n - 1;
    even_void(m);
    return;
  }
}

void UnitVoidStress::match_opt_void(const std::optional<uint64_t> &o) {
  if (o.has_value()) {
    const uint64_t &n = *o;
    consume(n);
    return;
  } else {
    return;
  }
}
