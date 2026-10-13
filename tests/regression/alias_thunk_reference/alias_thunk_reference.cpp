#include "alias_thunk_reference.h"

bool Nat::eq_dec(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      uint64_t _x = m - 1;
      return false;
    }
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      uint64_t n1 = m - 1;
      bool s = eq_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

AliasThunkReference::A::stream AliasThunkReference::A::ones() {
  return stream::lazy_([]() -> typename AliasThunkReference::A::stream::Cons {
    return {UINT64_C(1), ones()};
  });
}

uint64_t AliasThunkReference::A::hd(const AliasThunkReference::A::stream &s) {
  const auto &[a0, a1] =
      std::get<typename AliasThunkReference::A::stream::Cons>(s.v());
  return a0;
}

uint64_t AliasThunkReference::A::absurd_nat() {
  throw std::logic_error("absurd case");
}
