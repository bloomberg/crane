#include "decode_list.h"

DecodeList::instruction DecodeList::decode(uint64_t b1, uint64_t b2) {
  if (b1 == UINT64_C(0)) {
    return instruction::nop();
  } else {
    return instruction::ldm((UINT64_C(16) ? b2 % UINT64_C(16) : b2));
  }
}

List<DecodeList::instruction>
DecodeList::decode_list(const List<uint64_t> &bytes) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(bytes.v())) {
    return List<DecodeList::instruction>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(bytes.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<uint64_t>::Nil>(_sv0.v())) {
      return List<DecodeList::instruction>::nil();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<uint64_t>::Cons>(_sv0.v());
      return List<DecodeList::instruction>::cons(decode(a0, a00),
                                                 decode_list(*a10));
    }
  }
}
