#include <z_overflow.h>

#include <cstdint>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int Nat::tail_add(const unsigned int n,
                                                 const unsigned int m) {
  if (n <= 0) {
    return m;
  } else {
    unsigned int n0 = n - 1;
    return Nat::tail_add(n0, (m + 1));
  }
}

__attribute__((pure)) unsigned int Nat::tail_addmul(const unsigned int r,
                                                    const unsigned int n,
                                                    const unsigned int m) {
  if (n <= 0) {
    return r;
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
  if (std::holds_alternative<typename Uint::Nil>(d->v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D0>(&d->v());
    return Nat::of_uint_acc(_m.d_a0, Nat::tail_mul(10u, acc));
  } else if (std::holds_alternative<typename Uint::D1>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D1>(&d->v());
    return Nat::of_uint_acc(_m.d_a0, (Nat::tail_mul(10u, acc) + 1));
  } else if (std::holds_alternative<typename Uint::D2>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D2>(&d->v());
    return Nat::of_uint_acc(_m.d_a0, ((Nat::tail_mul(10u, acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D3>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D3>(&d->v());
    return Nat::of_uint_acc(_m.d_a0, (((Nat::tail_mul(10u, acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D4>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D4>(&d->v());
    return Nat::of_uint_acc(_m.d_a0,
                            ((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D5>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D5>(&d->v());
    return Nat::of_uint_acc(
        _m.d_a0, (((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D6>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D6>(&d->v());
    return Nat::of_uint_acc(
        _m.d_a0, ((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D7>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D7>(&d->v());
    return Nat::of_uint_acc(
        _m.d_a0,
        (((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D8>(d->v())) {
    const auto &_m = *std::get_if<typename Uint::D8>(&d->v());
    return Nat::of_uint_acc(
        _m.d_a0,
        ((((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else {
    const auto &_m = *std::get_if<typename Uint::D9>(&d->v());
    return Nat::of_uint_acc(
        _m.d_a0,
        (((((((((Nat::tail_mul(10u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  }
}

__attribute__((pure)) unsigned int
Nat::of_uint(const std::shared_ptr<Uint> &d) {
  return Nat::of_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint_acc(const std::shared_ptr<Uint0> &d, const unsigned int acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d->v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D10>(&d->v());
    return Nat::of_hex_uint_acc(_m.d_a0, Nat::tail_mul(16u, acc));
  } else if (std::holds_alternative<typename Uint0::D11>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D11>(&d->v());
    return Nat::of_hex_uint_acc(_m.d_a0, (Nat::tail_mul(16u, acc) + 1));
  } else if (std::holds_alternative<typename Uint0::D12>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D12>(&d->v());
    return Nat::of_hex_uint_acc(_m.d_a0, ((Nat::tail_mul(16u, acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D13>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D13>(&d->v());
    return Nat::of_hex_uint_acc(_m.d_a0,
                                (((Nat::tail_mul(16u, acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D14>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D14>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0, ((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D15>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D15>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0, (((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D16>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D16>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0, ((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D17>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D17>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        (((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D18>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D18>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        ((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D19>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::D19>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        (((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Da>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::Da>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        ((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Db>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::Db>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        (((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dc>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::Dc>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        ((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dd>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::Dd>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        (((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::De>(d->v())) {
    const auto &_m = *std::get_if<typename Uint0::De>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        ((((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else {
    const auto &_m = *std::get_if<typename Uint0::Df>(&d->v());
    return Nat::of_hex_uint_acc(
        _m.d_a0,
        (((((((((((((((Nat::tail_mul(16u, acc) + 1) + 1) + 1) + 1) + 1) + 1) +
                 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  }
}

__attribute__((pure)) unsigned int
Nat::of_hex_uint(const std::shared_ptr<Uint0> &d) {
  return Nat::of_hex_uint_acc(d, 0u);
}

__attribute__((pure)) unsigned int
Nat::of_num_uint(const std::shared_ptr<Uint1> &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d->v())) {
    const auto &_m = *std::get_if<typename Uint1::UIntDecimal>(&d->v());
    return Nat::of_uint(_m.d_u);
  } else {
    const auto &_m = *std::get_if<typename Uint1::UIntHexadecimal>(&d->v());
    return Nat::of_hex_uint(_m.d_u);
  }
}
