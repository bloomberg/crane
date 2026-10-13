#include "Nat.h"

#include "Datatypes.h"
#include "Decimal.h"
#include "Hexadecimal.h"
#include "Number.h"

namespace Nat {

uint64_t succ(uint64_t x) { return (x + 1); }

Datatypes::Comparison compare(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return Datatypes::Comparison::EQ;
    } else {
      uint64_t _x = m - 1;
      return Datatypes::Comparison::LT;
    }
  } else {
    uint64_t n_ = n - 1;
    if (m <= 0) {
      return Datatypes::Comparison::GT;
    } else {
      uint64_t m_ = m - 1;
      return compare(n_, m_);
    }
  }
}

bool even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      uint64_t n_ = n0 - 1;
      return even(n_);
    }
  }
}

bool odd(uint64_t n) { return !(even(n)); }

uint64_t pow(uint64_t n, uint64_t m) {
  if (m <= 0) {
    return UINT64_C(1);
  } else {
    uint64_t m0 = m - 1;
    return (n * pow(n, m0));
  }
}

uint64_t tail_add(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return m;
  } else {
    uint64_t n0 = n - 1;
    return tail_add(n0, (m + 1));
  }
}

uint64_t tail_addmul(uint64_t r, uint64_t n, uint64_t m) {
  if (n <= 0) {
    return r;
  } else {
    uint64_t n0 = n - 1;
    return tail_addmul(tail_add(m, r), n0, m);
  }
}

uint64_t tail_mul(uint64_t n, uint64_t m) {
  return tail_addmul(UINT64_C(0), n, m);
}

uint64_t of_uint_acc(const Decimal::Uint &d, uint64_t acc) {
  if (std::holds_alternative<typename Decimal::Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Decimal::Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D0>(d.v());
    return of_uint_acc(*a0, tail_mul(UINT64_C(10), acc));
  } else if (std::holds_alternative<typename Decimal::Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D1>(d.v());
    return of_uint_acc(*a0, (tail_mul(UINT64_C(10), acc) + 1));
  } else if (std::holds_alternative<typename Decimal::Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D2>(d.v());
    return of_uint_acc(*a0, ((tail_mul(UINT64_C(10), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Decimal::Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D3>(d.v());
    return of_uint_acc(*a0, (((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Decimal::Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D4>(d.v());
    return of_uint_acc(*a0,
                       ((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Decimal::Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D5>(d.v());
    return of_uint_acc(
        *a0, (((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Decimal::Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D6>(d.v());
    return of_uint_acc(
        *a0, ((((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Decimal::Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D7>(d.v());
    return of_uint_acc(
        *a0,
        (((((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Decimal::Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Decimal::Uint::D8>(d.v());
    return of_uint_acc(
        *a0,
        ((((((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else {
    const auto &[a0] = std::get<typename Decimal::Uint::D9>(d.v());
    return of_uint_acc(
        *a0,
        (((((((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1));
  }
}

uint64_t of_uint(const Decimal::Uint &d) { return of_uint_acc(d, UINT64_C(0)); }

uint64_t of_hex_uint_acc(const Hexadecimal::Uint &d, uint64_t acc) {
  if (std::holds_alternative<typename Hexadecimal::Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D0>(d.v());
    return of_hex_uint_acc(*a0, tail_mul(UINT64_C(16), acc));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D1>(d.v());
    return of_hex_uint_acc(*a0, (tail_mul(UINT64_C(16), acc) + 1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D2>(d.v());
    return of_hex_uint_acc(*a0, ((tail_mul(UINT64_C(16), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D3>(d.v());
    return of_hex_uint_acc(*a0, (((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D4>(d.v());
    return of_hex_uint_acc(*a0,
                           ((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D5>(d.v());
    return of_hex_uint_acc(
        *a0, (((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D6>(d.v());
    return of_hex_uint_acc(
        *a0, ((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D7>(d.v());
    return of_hex_uint_acc(
        *a0,
        (((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D8>(d.v());
    return of_hex_uint_acc(
        *a0,
        ((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::D9>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::D9>(d.v());
    return of_hex_uint_acc(
        *a0,
        (((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::Da>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::Da>(d.v());
    return of_hex_uint_acc(
        *a0,
        ((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::Db>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::Db>(d.v());
    return of_hex_uint_acc(
        *a0,
        (((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::Dc>(d.v());
    return of_hex_uint_acc(
        *a0,
        ((((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::Dd>(d.v());
    return of_hex_uint_acc(
        *a0,
        (((((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
               1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Hexadecimal::Uint::De>(d.v())) {
    const auto &[a0] = std::get<typename Hexadecimal::Uint::De>(d.v());
    return of_hex_uint_acc(
        *a0,
        ((((((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
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
    const auto &[a0] = std::get<typename Hexadecimal::Uint::Df>(d.v());
    return of_hex_uint_acc(
        *a0,
        (((((((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) +
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

uint64_t of_hex_uint(const Hexadecimal::Uint &d) {
  return of_hex_uint_acc(d, UINT64_C(0));
}

uint64_t of_num_uint(const Number::Uint &d) {
  if (std::holds_alternative<typename Number::Uint::UIntDecimal>(d.v())) {
    const auto &[u] = std::get<typename Number::Uint::UIntDecimal>(d.v());
    return of_uint(u);
  } else {
    const auto &[u] = std::get<typename Number::Uint::UIntHexadecimal>(d.v());
    return of_hex_uint(u);
  }
}

Decimal::Uint to_little_uint(uint64_t n, Decimal::Uint acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t n0 = n - 1;
    return to_little_uint(n0, Decimal::Little::succ(std::move(acc)));
  }
}

Decimal::Uint to_uint(uint64_t n) {
  return to_little_uint(n, Decimal::Uint::d0(Decimal::Uint::nil())).rev();
}

Hexadecimal::Uint to_little_hex_uint(uint64_t n, Hexadecimal::Uint acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t n0 = n - 1;
    return to_little_hex_uint(n0, Hexadecimal::Little::succ(std::move(acc)));
  }
}

Hexadecimal::Uint to_hex_uint(uint64_t n) {
  return to_little_hex_uint(n, Hexadecimal::Uint::d0(Hexadecimal::Uint::nil()))
      .rev();
}

Number::Uint to_num_uint(uint64_t n) {
  return Number::Uint::uintdecimal(to_uint(n));
}

Number::Uint to_num_hex_uint(uint64_t n) {
  return Number::Uint::uinthexadecimal(to_hex_uint(n));
}

std::optional<uint64_t> of_int(const Decimal::Signed_int &d) {
  auto &&_sv = d.norm();
  if (std::holds_alternative<typename Decimal::Signed_int::Pos>(_sv.v())) {
    const auto &[d0] = std::get<typename Decimal::Signed_int::Pos>(_sv.v());
    return std::make_optional<uint64_t>(of_uint(d0));
  } else {
    return std::optional<uint64_t>();
  }
}

std::optional<uint64_t> of_hex_int(const Hexadecimal::Signed_int &d) {
  auto &&_sv = d.norm();
  if (std::holds_alternative<typename Hexadecimal::Signed_int::Pos>(_sv.v())) {
    const auto &[d0] = std::get<typename Hexadecimal::Signed_int::Pos>(_sv.v());
    return std::make_optional<uint64_t>(of_hex_uint(d0));
  } else {
    return std::optional<uint64_t>();
  }
}

std::optional<uint64_t> of_num_int(const Number::Signed_int &d) {
  if (std::holds_alternative<typename Number::Signed_int::IntDecimal>(d.v())) {
    const auto &[i] = std::get<typename Number::Signed_int::IntDecimal>(d.v());
    return of_int(i);
  } else {
    const auto &[i] =
        std::get<typename Number::Signed_int::IntHexadecimal>(d.v());
    return of_hex_int(i);
  }
}

Decimal::Signed_int to_int(uint64_t n) {
  return Decimal::Signed_int::pos(to_uint(n));
}

Hexadecimal::Signed_int to_hex_int(uint64_t n) {
  return Hexadecimal::Signed_int::pos(to_hex_uint(n));
}

Number::Signed_int to_num_int(uint64_t n) {
  return Number::Signed_int::intdecimal(to_int(n));
}

std::pair<uint64_t, uint64_t> divmod(uint64_t x, uint64_t y, uint64_t q,
                                     uint64_t u) {
  if (x <= 0) {
    return std::make_pair(q, u);
  } else {
    uint64_t x_ = x - 1;
    if (u <= 0) {
      return divmod(x_, y, (q + 1), y);
    } else {
      uint64_t u_ = u - 1;
      return divmod(x_, y, q, u_);
    }
  }
}

uint64_t gcd(uint64_t a, uint64_t b) {
  if (a <= 0) {
    return b;
  } else {
    uint64_t a_ = a - 1;
    auto &&_once1 = (a_ + 1);
    return gcd((_once1 ? b % _once1 : b), (a_ + 1));
  }
}

uint64_t square(uint64_t n) { return (n * n); }

uint64_t sqrt_iter(uint64_t k, uint64_t p, uint64_t q, uint64_t r) {
  if (k <= 0) {
    return p;
  } else {
    uint64_t k_ = k - 1;
    if (r <= 0) {
      return sqrt_iter(k_, (p + 1), ((q + 1) + 1), ((q + 1) + 1));
    } else {
      uint64_t r_ = r - 1;
      return sqrt_iter(k_, p, q, r_);
    }
  }
}

uint64_t sqrt(uint64_t n) {
  return sqrt_iter(n, UINT64_C(0), UINT64_C(0), UINT64_C(0));
}

uint64_t log2_iter(uint64_t k, uint64_t p, uint64_t q, uint64_t r) {
  if (k <= 0) {
    return p;
  } else {
    uint64_t k_ = k - 1;
    if (r <= 0) {
      return log2_iter(k_, (p + 1), (q + 1), q);
    } else {
      uint64_t r_ = r - 1;
      return log2_iter(k_, p, (q + 1), r_);
    }
  }
}

uint64_t log2(uint64_t n) {
  return log2_iter((n ? n - 1 : n), UINT64_C(0), UINT64_C(1), UINT64_C(0));
}

uint64_t div2(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return UINT64_C(0);
    } else {
      uint64_t n_ = n0 - 1;
      return (div2(n_) + 1);
    }
  }
}

bool testbit(uint64_t a, uint64_t n) {
  if (n <= 0) {
    return odd(a);
  } else {
    uint64_t n0 = n - 1;
    return testbit(div2(a), n0);
  }
}

uint64_t shiftl(uint64_t a, uint64_t n) {
  if (n <= 0) {
    return a;
  } else {
    uint64_t n0 = n - 1;
    auto &&_once1 = shiftl(a, n0);
    return (_once1 + _once1);
  }
}

uint64_t shiftr(uint64_t a, uint64_t n) {
  if (n <= 0) {
    return a;
  } else {
    uint64_t n0 = n - 1;
    return div2(shiftr(a, n0));
  }
}

uint64_t land(uint64_t a, uint64_t b) {
  return bitwise([](bool _x0, bool _x1) -> bool { return (_x0 && _x1); }, a, a,
                 b);
}

uint64_t lor(uint64_t a, uint64_t b) {
  return bitwise([](bool _x0, bool _x1) -> bool { return (_x0 || _x1); },
                 std::max(a, b), a, b);
}

uint64_t ldiff(uint64_t a, uint64_t b) {
  return bitwise([](bool b0, bool b_) { return (b0 && !(b_)); }, a, a, b);
}

uint64_t lxor(uint64_t a, uint64_t b) {
  return bitwise(Datatypes::xorb, std::max(a, b), a, b);
}

} // namespace Nat
