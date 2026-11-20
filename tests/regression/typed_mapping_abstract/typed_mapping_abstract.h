#pragma once

#include <cstdint>

struct TypedMappingAbstract {
  static std::int64_t ticks(uint64_t n, std::int64_t c);
  static uint64_t count_to(uint64_t n);
  static std::int64_t later(std::int64_t c);
};
