#include <algorithm>
#include <any>
#include <cassert>
#include <encode_bytes_in_range.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::pair<unsigned int, unsigned int> EncodeBytesInRange::encode(
    const std::shared_ptr<EncodeBytesInRange::instruction> &i) {
  return std::visit(
      Overloaded{[](const typename EncodeBytesInRange::instruction::CLB _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(240u, 0u);
                 },
                 [](const typename EncodeBytesInRange::instruction::CMC _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(243u, 0u);
                 },
                 [](const typename EncodeBytesInRange::instruction::DAA _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(251u, 0u);
                 },
                 [](const typename EncodeBytesInRange::instruction::FIM _args)
                     -> std::pair<unsigned int, unsigned int> {
                   unsigned int r = _args._a0;
                   unsigned int d = _args._a1;
                   return std::make_pair(
                       (32u + (((r - (r % 2u)) > r ? 0 : (r - (r % 2u))))),
                       (std::move(d) % 256u));
                 },
                 [](const typename EncodeBytesInRange::instruction::JUN _args)
                     -> std::pair<unsigned int, unsigned int> {
                   unsigned int a = _args._a0;
                   return std::make_pair((64u + Nat::div(a, 256u)), (a % 256u));
                 },
                 [](const typename EncodeBytesInRange::instruction::LDM _args)
                     -> std::pair<unsigned int, unsigned int> {
                   unsigned int n = _args._a0;
                   return std::make_pair((208u + (std::move(n) % 16u)), 0u);
                 },
                 [](const typename EncodeBytesInRange::instruction::NOP _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(0u, 0u);
                 },
                 [](const typename EncodeBytesInRange::instruction::RDM _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(233u, 0u);
                 },
                 [](const typename EncodeBytesInRange::instruction::TCS _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(249u, 0u);
                 },
                 [](const typename EncodeBytesInRange::instruction::WPM _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(227u, 0u);
                 },
                 [](const typename EncodeBytesInRange::instruction::WR0 _args)
                     -> std::pair<unsigned int, unsigned int> {
                   return std::make_pair(228u, 0u);
                 }},
      i->v());
}

bool EncodeBytesInRange::pair_in_range(
    const std::pair<unsigned int, unsigned int> p) {
  unsigned int b1 = p.first;
  unsigned int b2 = p.second;
  return ((b1 < 256u) && (b2 < 256u));
}

std::pair<unsigned int, unsigned int> Nat::divmod(const unsigned int x,
                                                  const unsigned int y,
                                                  const unsigned int q,
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

unsigned int Nat::div(const unsigned int x, const unsigned int y) {
  if (y <= 0) {
    return std::move(y);
  } else {
    unsigned int y_ = y - 1;
    return Nat::divmod(x, y_, 0u, y_).first;
  }
}
