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
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<EncodeOps::instruction2>>::Nil
                 &) -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::nil();
          },
          [](const typename List<std::shared_ptr<EncodeOps::instruction2>>::Cons
                 &_args) -> std::shared_ptr<List<unsigned int>> {
            auto _cs = _args.d_a0->encode2();
            const unsigned int &b1 = _cs.first;
            const unsigned int &b2 = _cs.second;
            return List<unsigned int>::cons(
                b1, List<unsigned int>::cons(b2, encode_list2(_args.d_a1)));
          }},
      prog->v());
}

std::shared_ptr<List<unsigned int>> EncodeOps::encode_list3(
    const std::shared_ptr<List<std::shared_ptr<EncodeOps::instruction3>>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<EncodeOps::instruction3>>::Nil
                 &) -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::nil();
          },
          [](const typename List<std::shared_ptr<EncodeOps::instruction3>>::Cons
                 &_args) -> std::shared_ptr<List<unsigned int>> {
            std::pair<unsigned int, unsigned int> p = _args.d_a0->encode3();
            return List<unsigned int>::cons(
                p.first,
                List<unsigned int>::cons(p.second, encode_list3(_args.d_a1)));
          }},
      prog->v());
}
