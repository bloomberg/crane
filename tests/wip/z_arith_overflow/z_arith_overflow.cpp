#include "z_arith_overflow.h"

uint64_t Nat::tail_add(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return m;
  } else {
    uint64_t n0 = n - 1;
    return Nat::tail_add(n0, (m + 1));
  }
}

uint64_t Nat::tail_addmul(uint64_t r, uint64_t n, uint64_t m) {
  if (n <= 0) {
    return r;
  } else {
    uint64_t n0 = n - 1;
    return Nat::tail_addmul(Nat::tail_add(m, r), n0, m);
  }
}

uint64_t Nat::tail_mul(uint64_t n, uint64_t m) {
  return Nat::tail_addmul(UINT64_C(0), n, m);
}

uint64_t Nat::of_uint_acc(const Uint &d, uint64_t acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Nat::of_uint_acc(*a0, Nat::tail_mul(UINT64_C(10), acc));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Nat::of_uint_acc(*a0, (Nat::tail_mul(UINT64_C(10), acc) + 1));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Nat::of_uint_acc(*a0, ((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Nat::of_uint_acc(*a0,
                            (((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Nat::of_uint_acc(
        *a0, ((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Nat::of_uint_acc(
        *a0, (((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Nat::of_uint_acc(
        *a0,
        ((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Nat::of_uint_acc(
        *a0,
        (((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Nat::of_uint_acc(
        *a0,
        ((((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Nat::of_uint_acc(
        *a0,
        (((((((((Nat::tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  }
}

uint64_t Nat::of_uint(const Uint &d) {
  return Nat::of_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_hex_uint_acc(const Uint0 &d, uint64_t acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return Nat::of_hex_uint_acc(*a0, Nat::tail_mul(UINT64_C(16), acc));
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return Nat::of_hex_uint_acc(*a0, (Nat::tail_mul(UINT64_C(16), acc) + 1));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return Nat::of_hex_uint_acc(*a0,
                                ((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, (((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, ((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return Nat::of_hex_uint_acc(
        *a0, (((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
                1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        ((((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) +
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
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return Nat::of_hex_uint_acc(
        *a0,
        (((((((((((((((Nat::tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) +
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
  }
}

uint64_t Nat::of_hex_uint(const Uint0 &d) {
  return Nat::of_hex_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return Nat::of_uint(u);
  } else {
    const auto &[u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return Nat::of_hex_uint(u);
  }
}
