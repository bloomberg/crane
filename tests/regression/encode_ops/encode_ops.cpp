#include <encode_ops.h>

bool EncodeOps::pair_in_range(const std::pair<unsigned int, unsigned int> &p) {
  const unsigned int &b1 = p.first;
  const unsigned int &b2 = p.second;
  return (b1 < 256u && b2 < 256u);
}

List<unsigned int>
EncodeOps::encode_list2(const List<EncodeOps::instruction2> &prog) {
  if (std::holds_alternative<typename List<EncodeOps::instruction2>::Nil>(
          prog.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<EncodeOps::instruction2>::Cons>(prog.v());
    auto _cs = d_a0.encode2();
    const unsigned int &b1 = _cs.first;
    const unsigned int &b2 = _cs.second;
    return List<unsigned int>::cons(
        b1, List<unsigned int>::cons(b2, encode_list2(*(d_a1))));
  }
}

List<unsigned int>
EncodeOps::encode_list3(const List<EncodeOps::instruction3> &prog) {
  if (std::holds_alternative<typename List<EncodeOps::instruction3>::Nil>(
          prog.v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<EncodeOps::instruction3>::Cons>(prog.v());
    std::pair<unsigned int, unsigned int> p = d_a0.encode3();
    return List<unsigned int>::cons(
        p.first, List<unsigned int>::cons(p.second, encode_list3(*(d_a1))));
  }
}
