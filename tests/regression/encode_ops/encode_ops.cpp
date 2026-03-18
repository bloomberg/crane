#include <encode_ops.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

__attribute__((pure)) std::pair<unsigned int, unsigned int>
EncodeOps::encode1(const std::shared_ptr<EncodeOps::instruction1> &i) {
  return std::visit(
      Overloaded{[](const typename EncodeOps::instruction1::CLB _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(240u, 0u);
                 },
                 [](const typename EncodeOps::instruction1::CMC _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(243u, 0u);
                 },
                 [](const typename EncodeOps::instruction1::DAA _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(251u, 0u);
                 },
                 [](const typename EncodeOps::instruction1::FIM _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(
                       (32u + (((_args.d_a0 - (_args.d_a0 % 2u)) > _args.d_a0
                                    ? 0
                                    : (_args.d_a0 - (_args.d_a0 % 2u))))),
                       (_args.d_a1 % 256u));
                 },
                 [](const typename EncodeOps::instruction1::JUN _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair((64u + Nat::div(_args.d_a0, 256u)),
                                         (_args.d_a0 % 256u));
                 },
                 [](const typename EncodeOps::instruction1::LDM1 _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair((208u + (_args.d_a0 % 16u)), 0u);
                 },
                 [](const typename EncodeOps::instruction1::NOP1 _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(0u, 0u);
                 },
                 [](const typename EncodeOps::instruction1::RDM _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(233u, 0u);
                 },
                 [](const typename EncodeOps::instruction1::TCS _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(249u, 0u);
                 },
                 [](const typename EncodeOps::instruction1::WPM _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(227u, 0u);
                 },
                 [](const typename EncodeOps::instruction1::WR0 _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(228u, 0u);
                 }},
      i->v());
}

__attribute__((pure)) bool
EncodeOps::pair_in_range(const std::pair<unsigned int, unsigned int> p) {
  unsigned int b1 = p.first;
  unsigned int b2 = p.second;
  return (b1 < 256u && b2 < 256u);
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
EncodeOps::encode2(const std::shared_ptr<EncodeOps::instruction2> &i) {
  return std::visit(
      Overloaded{[](const typename EncodeOps::instruction2::NOP2 _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(0u, 0u);
                 },
                 [](const typename EncodeOps::instruction2::LDM2 _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(13u, (_args.d_a0 % 16u));
                 }},
      i->v());
}

std::shared_ptr<List<unsigned int>> EncodeOps::encode_list2(
    const std::shared_ptr<List<std::shared_ptr<EncodeOps::instruction2>>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<EncodeOps::instruction2>>::Nil
                 _args) -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::Nil_();
          },
          [](const typename List<std::shared_ptr<EncodeOps::instruction2>>::Cons
                 _args) -> std::shared_ptr<List<unsigned int>> {
            unsigned int b1 = encode2(_args.d_a0).first;
            unsigned int b2 = encode2(_args.d_a0).second;
            return List<unsigned int>::ctor::Cons_(
                b1,
                List<unsigned int>::ctor::Cons_(b2, encode_list2(_args.d_a1)));
          }},
      prog->v());
}

__attribute__((pure)) std::pair<unsigned int, unsigned int>
EncodeOps::encode3(const std::shared_ptr<EncodeOps::instruction3> &i) {
  return std::visit(
      Overloaded{[](const typename EncodeOps::instruction3::NOP3 _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(0u, 0u);
                 },
                 [](const typename EncodeOps::instruction3::LDM3 _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(((13u * 16u) + (_args.d_a0 % 16u)),
                                         0u);
                 }},
      i->v());
}

std::shared_ptr<List<unsigned int>> EncodeOps::encode_list3(
    const std::shared_ptr<List<std::shared_ptr<EncodeOps::instruction3>>>
        &prog) {
  return std::visit(
      Overloaded{
          [](const typename List<std::shared_ptr<EncodeOps::instruction3>>::Nil
                 _args) -> std::shared_ptr<List<unsigned int>> {
            return List<unsigned int>::ctor::Nil_();
          },
          [](const typename List<std::shared_ptr<EncodeOps::instruction3>>::Cons
                 _args) -> std::shared_ptr<List<unsigned int>> {
            std::pair<unsigned int, unsigned int> p = encode3(_args.d_a0);
            return List<unsigned int>::ctor::Cons_(
                p.first, List<unsigned int>::ctor::Cons_(
                             p.second, encode_list3(_args.d_a1)));
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
