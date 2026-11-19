#include "alias_thunk_reference.h"

AliasThunkReference::A::stream AliasThunkReference::A::ones() {
  return stream::lazy_([]() -> typename AliasThunkReference::A::stream::Cons {
    return {UINT64_C(1), ones()};
  });
}

uint64_t AliasThunkReference::A::hd(const AliasThunkReference::A::stream &s) {
  const auto &[a0, _] =
      std::get<typename AliasThunkReference::A::stream::Cons>(s.v());
  return a0;
}

uint64_t AliasThunkReference::A::absurd_nat() {
  throw std::logic_error("absurd case");
}
