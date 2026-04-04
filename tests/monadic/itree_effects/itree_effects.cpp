#include <itree_effects.h>

#include <cstdlib>
#include <ctime>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// ------------------------------------------------------------------
void ITreeEffects::greet() {
  std::cout << "What is your name?"s << '\n';
  std::string name;
  std::getline(std::cin, name);
  std::cout << name << '\n';
  return;
}

unsigned int ITreeEffects::roll_dice(const unsigned int sides) {
  unsigned int n = (std::rand() % sides);
  return (n + 1u);
}

void ITreeEffects::timed_greeting() {
  unsigned int t = static_cast<unsigned int>(std::time(nullptr));
  std::cout << [&]() {
    if (t <= 43200u) {
      return "Good morning";
    } else {
      return "Good afternoon";
    }
  }() << '\n';
  return;
}

void ITreeEffects::echo_loop(const unsigned int n) {
  {
    [&]() {
      auto _acc = std::monostate{};
      for (unsigned int _i = 0; _i < n; _i++) {
        _acc = [](std::monostate acc) {
          std::string line;
          std::getline(std::cin, line);
          std::cout << line << '\n';
          return acc;
        }(std::move(_acc));
      }
      return _acc;
    }();
    return;
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
                   return Nat::of_uint(_args.d_u);
                 },
                 [](const typename Uint1::UIntHexadecimal _args)
                     -> unsigned int { return Nat::of_hex_uint(_args.d_u); }},
      d->v());
}
