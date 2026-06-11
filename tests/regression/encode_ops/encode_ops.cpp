#include "encode_ops.h"

bool EncodeOps::pair_in_range(const std::pair<uint64_t, uint64_t> &p) {
  const auto &[b1, b2] = p;
  return (b1 < UINT64_C(256) && b2 < UINT64_C(256));
}

List<uint64_t>
EncodeOps::encode_list2(const List<EncodeOps::instruction2> &prog) {
  if (std::holds_alternative<typename List<EncodeOps::instruction2>::Nil>(
          prog.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<EncodeOps::instruction2>::Cons>(prog.v());
    auto [b1, b2] = a0.encode2();
    return List<uint64_t>::cons(b1,
                                List<uint64_t>::cons(b2, encode_list2(*a1)));
  }
}

List<uint64_t>
EncodeOps::encode_list3(const List<EncodeOps::instruction3> &prog) {
  if (std::holds_alternative<typename List<EncodeOps::instruction3>::Nil>(
          prog.v())) {
    return List<uint64_t>::nil();
  } else {
    const auto &[a0, a1] =
        std::get<typename List<EncodeOps::instruction3>::Cons>(prog.v());
    std::pair<uint64_t, uint64_t> p = a0.encode3();
    return List<uint64_t>::cons(
        p.first, List<uint64_t>::cons(p.second, encode_list3(*a1)));
  }
}
