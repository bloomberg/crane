#include "cross_unit_duplicate_symbol_lib.h"

uint64_t Lib::len(const Lib::lst &l) {
  if (std::holds_alternative<typename Lib::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[_, a1] = std::get<typename Lib::lst::Cons>(l.v());
    return (len(*a1) + 1);
  }
}
