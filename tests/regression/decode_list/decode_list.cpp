#include <decode_list.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<DecodeList::instruction>
DecodeList::decode(const unsigned int b1, const unsigned int b2) {
  if (b1 == 0u) {
    return instruction::nop();
  } else {
    return instruction::ldm((16u ? b2 % 16u : b2));
  }
}

std::shared_ptr<List<std::shared_ptr<DecodeList::instruction>>>
DecodeList::decode_list(const std::shared_ptr<List<unsigned int>> &bytes) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(bytes->v())) {
    return List<std::shared_ptr<DecodeList::instruction>>::nil();
  } else {
    const auto &_m =
        *std::get_if<typename List<unsigned int>::Cons>(&bytes->v());
    auto &&_sv0 = _m.d_a1;
    if (std::holds_alternative<typename List<unsigned int>::Nil>(_sv0->v())) {
      return List<std::shared_ptr<DecodeList::instruction>>::nil();
    } else {
      const auto &_m0 =
          *std::get_if<typename List<unsigned int>::Cons>(&_sv0->v());
      return List<std::shared_ptr<DecodeList::instruction>>::cons(
          decode(_m.d_a0, _m0.d_a0), decode_list(_m0.d_a1));
    }
  }
}
