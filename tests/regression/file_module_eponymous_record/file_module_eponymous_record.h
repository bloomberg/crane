#pragma once

#include <cstdint>

struct catalog;

struct Catalog0 {
  static catalog grow(const catalog &c);
};

struct catalog {
  uint64_t size;
};

const uint64_t answer = Catalog0::grow(catalog{UINT64_C(1)}).size;
