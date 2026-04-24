#include <decode_list.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) DecodeList::instruction
DecodeList::decode(const unsigned int &b1, const unsigned int &b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

__attribute__((pure)) List<DecodeList::instruction>
DecodeList::decode_list(const List<unsigned int> &bytes) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(bytes.v())) {
    return List<DecodeList::instruction>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(bytes.v());
    auto &&_sv0 = *(d_a1);
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0.v())) {
      return List<DecodeList::instruction>::nil();
    } else {
      const auto &[d_a00, d_a10] =
          std::get<typename List<unsigned int>::Cons>(_sv0.v());
      return List<DecodeList::instruction>::cons(decode(d_a0, d_a00),
                                                 decode_list(*(d_a10)));
    }
  }
}
