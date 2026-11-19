#include "erased_let_not_result_type.h"

ErasedLetNotResultType::Syms::semty
ErasedLetNotResultType::Syms::cast(uint64_t, uint64_t,
                                   ErasedLetNotResultType::Syms::semty v) {
  return v;
}

ErasedLetNotResultType::Syms::semty
ErasedLetNotResultType::Syms::default_(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t m = n - 1;
    return m;
  }
}

uint64_t
ErasedLetNotResultType::Syms::size(uint64_t n,
                                   ErasedLetNotResultType::Syms::semty b) {
  if (n <= 0) {
    if (crane::any_cast<bool>(std::move(b))) {
      return UINT64_C(1);
    } else {
      return UINT64_C(0);
    }
  } else {
    uint64_t _x = n - 1;
    return crane::any_cast<uint64_t>(std::move(b));
  }
}
