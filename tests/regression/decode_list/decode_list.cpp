#include "decode_list.h"

DecodeList::instruction DecodeList::decode(unsigned int b1, unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

List<DecodeList::instruction>
DecodeList::decode_list(const List<unsigned int> &bytes) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(bytes.v())) {
    return List<DecodeList::instruction>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<unsigned int>::Cons>(bytes.v());
    auto &&_sv0 = *a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return List<DecodeList::instruction>::nil();
    } else {
      const auto &[a00, a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      return List<DecodeList::instruction>::cons(decode(a0, a00),
                                                 decode_list(*a10));
    }
  }
}
