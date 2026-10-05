#ifndef INCLUDED_FILE_MODULE_EPONYMOUS_RECORD
#define INCLUDED_FILE_MODULE_EPONYMOUS_RECORD

#include <cstdint>

struct catalog;

struct Catalog0 {
  static catalog grow(const catalog &c);
};

struct catalog {
  uint64_t size;
};

inline constexpr uint64_t answer = UINT64_C(2);

#endif // INCLUDED_FILE_MODULE_EPONYMOUS_RECORD
