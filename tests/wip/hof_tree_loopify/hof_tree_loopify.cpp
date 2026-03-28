#include <hof_tree_loopify.h>

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

std::shared_ptr<HofTreeLoopify::tree<unsigned int>>
HofTreeLoopify::depth_tree(const unsigned int n) {
  if (n <= 0) {
    return tree<unsigned int>::leaf();
  } else {
    unsigned int m = n - 1;
    return tree<unsigned int>::node(depth_tree(std::move(m)), n,
                                    tree<unsigned int>::leaf());
  }
}

__attribute__((pure)) unsigned int Nat::tail_add(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return std::move(m);
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_add(std::move(n0), (m + 1));
  }
}

__attribute__((pure)) unsigned int Nat::tail_addmul(const unsigned int r,
                                                    const unsigned int n,
                                                    const unsigned int m) {
  if (n <= 0) {
    return std::move(r);
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

__attribute__((pure)) unsigned int Nat::tail_mul(const unsigned int n,
                                                 const unsigned int m) {
  return Nat::tail_addmul(0u, n, m);
}

__attribute__((pure)) unsigned int
Nat::of_uint_acc(const std::shared_ptr<Uint> &d, const unsigned int acc) {
  return std::visit(
      Overloaded{
          [&](const typename Uint::Nil _args) -> unsigned int {
            return std::move(acc);
          },
          [&](const typename Uint::D0 _args) -> unsigned int {
            return Nat::of_uint_acc(_args.d_a0,
                                    Nat::tail_mul(10u, std::move(acc)));
          },
          [&](const typename Uint::D1 _args) -> unsigned int {
            return Nat::of_uint_acc(_args.d_a0,
                                    (Nat::tail_mul(10u, std::move(acc)) + 1));
          },
          [&](const typename Uint::D2 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0, ((Nat::tail_mul(10u, std::move(acc)) + 1) + 1));
          },
          [&](const typename Uint::D3 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1));
          },
          [&](const typename Uint::D4 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1));
          },
          [&](const typename Uint::D5 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                 1));
          },
          [&](const typename Uint::D6 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D7 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D8 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                ((((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint::D9 _args) -> unsigned int {
            return Nat::of_uint_acc(
                _args.d_a0,
                (((((((((Nat::tail_mul(10u, std::move(acc)) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          }},
      d->v());
}

__attribute__((pure)) unsigned int
Nat::of_uint(const std::shared_ptr<Uint> &d) {
  return Nat::of_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint_acc(const std::shared_ptr<Uint0> &d, const unsigned int acc) {
  return std::visit(
      Overloaded{
          [&](const typename Uint0::Nil0 _args) -> unsigned int {
            return std::move(acc);
          },
          [&](const typename Uint0::D10 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(_args.d_a0,
                                        Nat::tail_mul(16u, std::move(acc)));
          },
          [&](const typename Uint0::D11 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0, (Nat::tail_mul(16u, std::move(acc)) + 1));
          },
          [&](const typename Uint0::D12 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0, ((Nat::tail_mul(16u, std::move(acc)) + 1) + 1));
          },
          [&](const typename Uint0::D13 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1));
          },
          [&](const typename Uint0::D14 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1));
          },
          [&](const typename Uint0::D15 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                 1));
          },
          [&](const typename Uint0::D16 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D17 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D18 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) + 1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::D19 _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Da _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Db _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Dc _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Dd _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) + 1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::De _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                ((((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          },
          [&](const typename Uint0::Df _args) -> unsigned int {
            return Nat::of_hex_uint_acc(
                _args.d_a0,
                (((((((((((((((Nat::tail_mul(16u, std::move(acc)) + 1) + 1) +
                             1) +
                            1) +
                           1) +
                          1) +
                         1) +
                        1) +
                       1) +
                      1) +
                     1) +
                    1) +
                   1) +
                  1) +
                 1));
          }},
      d->v());
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint(const std::shared_ptr<Uint0> &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_num_uint(const std::shared_ptr<Uint1> &d) {
  return std::visit(
      Overloaded{[](const typename Uint1::UIntDecimal _args) -> unsigned int {
                   return Nat::of_uint(_args.d_a0);
                 },
                 [](const typename Uint1::UIntHexadecimal _args)
                     -> unsigned int { return Nat::of_hex_uint(_args.d_a0); }},
      d->v());
}
