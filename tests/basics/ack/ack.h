#pragma once

#include <cstdint>

struct Ack {
  static uint64_t ack(uint64_t m, uint64_t n);
};

struct Nat {
  static constexpr uint64_t one = UINT64_C(1);
};
