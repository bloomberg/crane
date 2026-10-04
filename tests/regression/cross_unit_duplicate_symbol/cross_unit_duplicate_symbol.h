#ifndef INCLUDED_CROSS_UNIT_DUPLICATE_SYMBOL
#define INCLUDED_CROSS_UNIT_DUPLICATE_SYMBOL

#include <cross_unit_duplicate_symbol_lib.h>
#include <cstdint>

struct Use {
  static inline const Lib::lst two =
      Lib::lst::cons(UINT64_C(1), Lib::lst::cons(UINT64_C(2), Lib::lst::nil()));

  static inline const uint64_t answer = Lib::len(two);
};

#endif // INCLUDED_CROSS_UNIT_DUPLICATE_SYMBOL
