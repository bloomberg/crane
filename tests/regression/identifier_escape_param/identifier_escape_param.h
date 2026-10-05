#ifndef INCLUDED_IDENTIFIER_ESCAPE_PARAM
#define INCLUDED_IDENTIFIER_ESCAPE_PARAM

#include <cstdint>

struct IdentifierEscapeParam {
  static uint64_t id_from_param(uint64_t double0);
  static uint64_t add_one_from_param(uint64_t double0);
  static constexpr uint64_t t = UINT64_C(7);
};

#endif // INCLUDED_IDENTIFIER_ESCAPE_PARAM
