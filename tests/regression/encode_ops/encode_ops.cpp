#include <encode_ops.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) bool
EncodeOps::pair_in_range(const std::pair<unsigned int, unsigned int> p) {
  unsigned int b1 = p.first;
  unsigned int b2 = p.second;
  return (b1 < 256u && b2 < 256u);
}

std::shared_ptr<List<unsigned int>> EncodeOps::encode_list2(
    const std::shared_ptr<List<std::shared_ptr<EncodeOps::instruction2>>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<EncodeOps::instruction2>>::Nil
                 _args) -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::nil();
          },
          [](const typename List<std::shared_ptr<EncodeOps::instruction2>>::Cons
                 _args) -> std::shared_ptr<List<unsigned int>> {
            unsigned int b1 = _args.d_a0->encode2().first;
            unsigned int b2 = _args.d_a0->encode2().second;
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
                 _args) -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::nil();
          },
          [](const typename List<std::shared_ptr<EncodeOps::instruction3>>::Cons
                 _args) -> std::shared_ptr<List<unsigned int>> {
            std::pair<unsigned int, unsigned int> p = _args.d_a0->encode3();
            return List<unsigned int>::cons(
                p.first,
                List<unsigned int>::cons(p.second, encode_list3(_args.d_a1)));
          }},
      prog->v());
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
Nat::divmod(const unsigned int x, const unsigned int y, const unsigned int q,
            const unsigned int u) {
  if (x <= 0) {
    return std::make_pair(std::move(q), std::move(u));
  } else {
    unsigned int x_ = x - 1;
    if (u <= 0) {
      return Nat::divmod(std::move(x_), y, (q + 1), y);
    } else {
      unsigned int u_ = u - 1;
      return Nat::divmod(std::move(x_), y, q, std::move(u_));
    }
  }
}

__attribute__((pure)) unsigned int Nat::div(const unsigned int x,
                                            const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
