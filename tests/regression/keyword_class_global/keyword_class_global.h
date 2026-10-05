#ifndef INCLUDED_KEYWORD_CLASS_GLOBAL
#define INCLUDED_KEYWORD_CLASS_GLOBAL

#include <cstdint>

struct KeywordClassGlobal {
  static uint64_t class_(uint64_t n);
  static constexpr uint64_t t = UINT64_C(8);
};

#endif // INCLUDED_KEYWORD_CLASS_GLOBAL
