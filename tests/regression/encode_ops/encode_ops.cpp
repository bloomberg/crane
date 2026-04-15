#include <encode_ops.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool
EncodeOps::pair_in_range(const std::pair<unsigned int, unsigned int> p) {
  const unsigned int &b1 = p.first;
  const unsigned int &b2 = p.second;
  return (b1 < 256u && b2 < 256u);
}

std::shared_ptr<List<unsigned int>> EncodeOps::encode_list2(
    const std::shared_ptr<List<std::shared_ptr<EncodeOps::instruction2>>>
        &prog) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<EncodeOps::instruction2>>::Nil>(
          prog->v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &_m = *std::get_if<
        typename List<std::shared_ptr<EncodeOps::instruction2>>::Cons>(
        &prog->v());
    auto _cs = _m.d_a0->encode2();
    const unsigned int &b1 = _cs.first;
    const unsigned int &b2 = _cs.second;
    return List<unsigned int>::cons(
        b1, List<unsigned int>::cons(b2, encode_list2(_m.d_a1)));
  }
}

std::shared_ptr<List<unsigned int>> EncodeOps::encode_list3(
    const std::shared_ptr<List<std::shared_ptr<EncodeOps::instruction3>>>
        &prog) {
  if (std::holds_alternative<
          typename List<std::shared_ptr<EncodeOps::instruction3>>::Nil>(
          prog->v())) {
    return List<unsigned int>::nil();
  } else {
    const auto &_m = *std::get_if<
        typename List<std::shared_ptr<EncodeOps::instruction3>>::Cons>(
        &prog->v());
    std::pair<unsigned int, unsigned int> p = _m.d_a0->encode3();
    return List<unsigned int>::cons(
        p.first, List<unsigned int>::cons(p.second, encode_list3(_m.d_a1)));
  }
}
