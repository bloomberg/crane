#include "nat_module_family_returns.h"

Uint Little::succ(const Uint &d) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return Uint::d1(Uint::nil());
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return Uint::d1(*a0);
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return Uint::d2(*a0);
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return Uint::d3(*a0);
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return Uint::d4(*a0);
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return Uint::d5(*a0);
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return Uint::d6(*a0);
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return Uint::d7(*a0);
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return Uint::d8(*a0);
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return Uint::d9(*a0);
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return Uint::d0(succ(*a0));
  }
}

Uint0 Coq_Little::succ(const Uint0 &d) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return Uint0::d10(Uint0::nil0());
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return Uint0::d10(*a0);
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return Uint0::d12(*a0);
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return Uint0::d13(*a0);
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return Uint0::d14(*a0);
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return Uint0::d15(*a0);
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return Uint0::d16(*a0);
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return Uint0::d17(*a0);
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return Uint0::d18(*a0);
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return Uint0::d19(*a0);
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return Uint0::da(*a0);
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return Uint0::db(*a0);
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return Uint0::dc(*a0);
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return Uint0::dd(*a0);
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
    return Uint0::de(*a0);
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
    return Uint0::df(*a0);
  } else {
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
    return Uint0::d11(succ(*a0));
  }
}

uint64_t Nat::succ(uint64_t x) { return (x + 1); }

Comparison Nat::compare(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return Comparison::EQ;
    } else {
      uint64_t _x = m - 1;
      return Comparison::LT;
    }
  } else {
    uint64_t n_ = n - 1;
    if (m <= 0) {
      return Comparison::GT;
    } else {
      uint64_t m_ = m - 1;
      return compare(n_, m_);
    }
  }
}

bool Nat::even(uint64_t n) {
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

bool Nat::odd(uint64_t n) { return !(even(n)); }

uint64_t Nat::pow(uint64_t n, uint64_t m) {
  if (m <= 0) {
    return UINT64_C(1);
  } else {
    uint64_t m0 = m - 1;
    return (n * pow(n, m0));
  }
}

uint64_t Nat::tail_add(uint64_t n, uint64_t m) {
  if (n <= 0) {
    return m;
  } else {
    uint64_t n0 = n - 1;
    return tail_add(n0, (m + 1));
  }
}

uint64_t Nat::tail_addmul(uint64_t r, uint64_t n, uint64_t m) {
  if (n <= 0) {
    return r;
  } else {
    uint64_t n0 = n - 1;
    return tail_addmul(tail_add(m, r), n0, m);
  }
}

uint64_t Nat::tail_mul(uint64_t n, uint64_t m) {
  return tail_addmul(UINT64_C(0), n, m);
}

uint64_t Nat::of_uint_acc(const Uint &d, uint64_t acc) {
  if (std::holds_alternative<typename Uint::Nil>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint::D0>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D0>(d.v());
    return of_uint_acc(*a0, tail_mul(UINT64_C(10), acc));
  } else if (std::holds_alternative<typename Uint::D1>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D1>(d.v());
    return of_uint_acc(*a0, (tail_mul(UINT64_C(10), acc) + 1));
  } else if (std::holds_alternative<typename Uint::D2>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D2>(d.v());
    return of_uint_acc(*a0, ((tail_mul(UINT64_C(10), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D3>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D3>(d.v());
    return of_uint_acc(*a0, (((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D4>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D4>(d.v());
    return of_uint_acc(*a0,
                       ((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D5>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D5>(d.v());
    return of_uint_acc(
        *a0, (((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D6>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D6>(d.v());
    return of_uint_acc(
        *a0, ((((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D7>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D7>(d.v());
    return of_uint_acc(
        *a0,
        (((((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint::D8>(d.v())) {
    const auto &[a0] = std::get<typename Uint::D8>(d.v());
    return of_uint_acc(
        *a0,
        ((((((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else {
    const auto &[a0] = std::get<typename Uint::D9>(d.v());
    return of_uint_acc(
        *a0,
        (((((((((tail_mul(UINT64_C(10), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1));
  }
}

uint64_t Nat::of_uint(const Uint &d) { return of_uint_acc(d, UINT64_C(0)); }

uint64_t Nat::of_hex_uint_acc(const Uint0 &d, uint64_t acc) {
  if (std::holds_alternative<typename Uint0::Nil0>(d.v())) {
    return acc;
  } else if (std::holds_alternative<typename Uint0::D11>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D11>(d.v());
    return of_hex_uint_acc(*a0, tail_mul(UINT64_C(16), acc));
  } else if (std::holds_alternative<typename Uint0::D10>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D10>(d.v());
    return of_hex_uint_acc(*a0, (tail_mul(UINT64_C(16), acc) + 1));
  } else if (std::holds_alternative<typename Uint0::D12>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D12>(d.v());
    return of_hex_uint_acc(*a0, ((tail_mul(UINT64_C(16), acc) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D13>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D13>(d.v());
    return of_hex_uint_acc(*a0, (((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D14>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D14>(d.v());
    return of_hex_uint_acc(*a0,
                           ((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D15>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D15>(d.v());
    return of_hex_uint_acc(
        *a0, (((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D16>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D16>(d.v());
    return of_hex_uint_acc(
        *a0, ((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D17>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D17>(d.v());
    return of_hex_uint_acc(
        *a0,
        (((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1));
  } else if (std::holds_alternative<typename Uint0::D18>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D18>(d.v());
    return of_hex_uint_acc(
        *a0,
        ((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) + 1) +
         1));
  } else if (std::holds_alternative<typename Uint0::D19>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::D19>(d.v());
    return of_hex_uint_acc(
        *a0,
        (((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Da>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Da>(d.v());
    return of_hex_uint_acc(
        *a0,
        ((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Db>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Db>(d.v());
    return of_hex_uint_acc(
        *a0,
        (((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dc>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dc>(d.v());
    return of_hex_uint_acc(
        *a0,
        ((((((((((((tail_mul(UINT64_C(16), acc) + 1) + 1) + 1) + 1) + 1) + 1) +
              1) +
             1) +
            1) +
           1) +
          1) +
         1));
  } else if (std::holds_alternative<typename Uint0::Dd>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::Dd>(d.v());
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
  } else if (std::holds_alternative<typename Uint0::De>(d.v())) {
    const auto &[a0] = std::get<typename Uint0::De>(d.v());
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
    const auto &[a0] = std::get<typename Uint0::Df>(d.v());
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

uint64_t Nat::of_hex_uint(const Uint0 &d) {
  return of_hex_uint_acc(d, UINT64_C(0));
}

uint64_t Nat::of_num_uint(const Uint1 &d) {
  if (std::holds_alternative<typename Uint1::UIntDecimal>(d.v())) {
    const auto &[u] = std::get<typename Uint1::UIntDecimal>(d.v());
    return of_uint(u);
  } else {
    const auto &[u] = std::get<typename Uint1::UIntHexadecimal>(d.v());
    return of_hex_uint(u);
  }
}

Uint Nat::to_little_uint(uint64_t n, Uint acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t n0 = n - 1;
    return to_little_uint(n0, Little::succ(std::move(acc)));
  }
}

Uint Nat::to_uint(uint64_t n) {
  return to_little_uint(n, Uint::d0(Uint::nil())).rev();
}

Uint0 Nat::to_little_hex_uint(uint64_t n, Uint0 acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t n0 = n - 1;
    return to_little_hex_uint(n0, Coq_Little::succ(std::move(acc)));
  }
}

Uint0 Nat::to_hex_uint(uint64_t n) {
  return to_little_hex_uint(n, Uint0::d11(Uint0::nil0())).rev0();
}

Uint1 Nat::to_num_uint(uint64_t n) { return Uint1::uintdecimal(to_uint(n)); }

Uint1 Nat::to_num_hex_uint(uint64_t n) {
  return Uint1::uinthexadecimal(to_hex_uint(n));
}

std::optional<uint64_t> Nat::of_int(const Signed_int &d) {
  auto &&_sv = d.norm();
  if (std::holds_alternative<typename Signed_int::Pos>(_sv.v())) {
    const auto &[d0] = std::get<typename Signed_int::Pos>(_sv.v());
    return std::make_optional<uint64_t>(of_uint(d0));
  } else {
    return std::optional<uint64_t>();
  }
}

std::optional<uint64_t> Nat::of_hex_int(const Signed_int0 &d) {
  auto &&_sv = d.norm0();
  if (std::holds_alternative<typename Signed_int0::Pos0>(_sv.v())) {
    const auto &[d0] = std::get<typename Signed_int0::Pos0>(_sv.v());
    return std::make_optional<uint64_t>(of_hex_uint(d0));
  } else {
    return std::optional<uint64_t>();
  }
}

std::optional<uint64_t> Nat::of_num_int(const Signed_int1 &d) {
  if (std::holds_alternative<typename Signed_int1::IntDecimal>(d.v())) {
    const auto &[i] = std::get<typename Signed_int1::IntDecimal>(d.v());
    return of_int(i);
  } else {
    const auto &[i] = std::get<typename Signed_int1::IntHexadecimal>(d.v());
    return of_hex_int(i);
  }
}

Signed_int Nat::to_int(uint64_t n) { return Signed_int::pos(to_uint(n)); }

Signed_int0 Nat::to_hex_int(uint64_t n) {
  return Signed_int0::pos0(to_hex_uint(n));
}

Signed_int1 Nat::to_num_int(uint64_t n) {
  return Signed_int1::intdecimal(to_int(n));
}

std::pair<uint64_t, uint64_t> Nat::divmod(uint64_t x, uint64_t y, uint64_t q,
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

uint64_t Nat::gcd(uint64_t a, uint64_t b) {
  if (a <= 0) {
    return b;
  } else {
    uint64_t a_ = a - 1;
    auto &&_once1 = (a_ + 1);
    return gcd((_once1 ? b % _once1 : b), (a_ + 1));
  }
}

uint64_t Nat::square(uint64_t n) { return (n * n); }

uint64_t Nat::sqrt_iter(uint64_t k, uint64_t p, uint64_t q, uint64_t r) {
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

uint64_t Nat::sqrt(uint64_t n) {
  return sqrt_iter(n, UINT64_C(0), UINT64_C(0), UINT64_C(0));
}

uint64_t Nat::log2_iter(uint64_t k, uint64_t p, uint64_t q, uint64_t r) {
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

uint64_t Nat::log2(uint64_t n) {
  return log2_iter((n ? n - 1 : n), UINT64_C(0), UINT64_C(1), UINT64_C(0));
}

uint64_t Nat::div2(uint64_t n) {
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

bool Nat::testbit(uint64_t a, uint64_t n) {
  if (n <= 0) {
    return odd(a);
  } else {
    uint64_t n0 = n - 1;
    return testbit(div2(a), n0);
  }
}

uint64_t Nat::shiftl(uint64_t a, uint64_t n) {
  if (n <= 0) {
    return a;
  } else {
    uint64_t n0 = n - 1;
    auto &&_once1 = shiftl(a, n0);
    return (_once1 + _once1);
  }
}

uint64_t Nat::shiftr(uint64_t a, uint64_t n) {
  if (n <= 0) {
    return a;
  } else {
    uint64_t n0 = n - 1;
    return div2(shiftr(a, n0));
  }
}

uint64_t Nat::land(uint64_t a, uint64_t b) {
  return bitwise([](bool _x0, bool _x1) -> bool { return (_x0 && _x1); }, a, a,
                 b);
}

uint64_t Nat::lor(uint64_t a, uint64_t b) {
  return bitwise([](bool _x0, bool _x1) -> bool { return (_x0 || _x1); },
                 std::max(a, b), a, b);
}

uint64_t Nat::ldiff(uint64_t a, uint64_t b) {
  return bitwise([](bool b0, bool b_) { return (b0 && !(b_)); }, a, a, b);
}

uint64_t Nat::lxor(uint64_t a, uint64_t b) {
  return bitwise(Datatypes::xorb, std::max(a, b), a, b);
}

Decidable Nat::Decidable_eq_nat(uint64_t x, uint64_t y) {
  return Decidable{x == y};
}

Decidable Nat::Decidable_le_nat(uint64_t x, uint64_t y) {
  return Decidable{x <= y};
}

bool Nat::eq_dec(uint64_t n, uint64_t m) {
  if (n <= 0) {
    if (m <= 0) {
      return true;
    } else {
      uint64_t _x = m - 1;
      return false;
    }
  } else {
    uint64_t n0 = n - 1;
    if (m <= 0) {
      return false;
    } else {
      uint64_t n1 = m - 1;
      bool s = eq_dec(n0, n1);
      if (s) {
        return true;
      } else {
        return false;
      }
    }
  }
}

Reflect Nat::leb_spec0(uint64_t x, uint64_t y) {
  return Bool::iff_reflect(x <= y);
}

Reflect Nat::ltb_spec0(uint64_t x, uint64_t y) {
  return Bool::iff_reflect(x < y);
}

bool Nat::Private_Dec::max_dec(uint64_t n, uint64_t m) {
  return max_case<bool>(
      n, m,
      [](uint64_t, uint64_t, bool h0) -> bool {
        if (h0) {
          return true;
        } else {
          return false;
        }
      },
      true, false);
}

bool Nat::Private_Dec::min_dec(uint64_t n, uint64_t m) {
  return min_case<bool>(
      n, m,
      [](uint64_t, uint64_t, bool h0) -> bool {
        if (h0) {
          return true;
        } else {
          return false;
        }
      },
      true, false);
}

bool Nat::max_dec(uint64_t x0_, uint64_t x1_) {
  return Private_Dec::max_dec(x0_, x1_);
}

bool Nat::min_dec(uint64_t x0_, uint64_t x1_) {
  return Private_Dec::min_dec(x0_, x1_);
}

uint64_t Nat::sqrt_up(uint64_t a) {
  switch (compare(UINT64_C(0), a)) {
  case Comparison::LT: {
    return (sqrt((a ? a - 1 : a)) + 1);
  }
  default: {
    return UINT64_C(0);
  }
  }
}

uint64_t Nat::log2_up(uint64_t a) {
  switch (compare(UINT64_C(1), a)) {
  case Comparison::LT: {
    return (log2((a ? a - 1 : a)) + 1);
  }
  default: {
    return UINT64_C(0);
  }
  }
}

uint64_t Nat::Private_NLcmProp::lcm(uint64_t a, uint64_t b) {
  auto &&_once1 = gcd(a, b);
  return (a * (_once1 ? b / _once1 : 0));
}

uint64_t Nat::lcm(uint64_t a, uint64_t b) {
  auto &&_once1 = gcd(a, b);
  return (a * (_once1 ? b / _once1 : 0));
}

Reflect Nat::eqb_spec(uint64_t x, uint64_t y) {
  return Bool::iff_reflect(x == y);
}

uint64_t Nat::b2n(bool b) {
  if (b) {
    return UINT64_C(1);
  } else {
    return UINT64_C(0);
  }
}

uint64_t Nat::setbit(uint64_t a, uint64_t n) {
  return lor(a, shiftl(UINT64_C(1), n));
}

uint64_t Nat::clearbit(uint64_t a, uint64_t n) {
  return ldiff(a, shiftl(UINT64_C(1), n));
}

uint64_t Nat::ones(uint64_t n) {
  auto &&_once1 = shiftl(UINT64_C(1), n);
  return (_once1 ? _once1 - 1 : _once1);
}

uint64_t Nat::lnot(uint64_t a, uint64_t n) { return lxor(a, ones(n)); }

bool Nat::Even_Odd_dec(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (Even_Odd_dec(n0)) {
      return false;
    } else {
      return true;
    }
  }
}

Nat::EvenT Nat::EvenT_2(uint64_t,
                        const Sig<uint64_t> &h0) { // Precondition: n == (2 * m)
  const auto &[x0] = h0;
  return Sig<uint64_t>::exist((x0 + 1));
}

Nat::OddT
Nat::OddT_2(uint64_t,
            const Sig<uint64_t> &h0) { // Precondition: n == (2 * m + 1)
  const auto &[x0] = h0;
  return Sig<uint64_t>::exist((x0 + 1));
}

Nat::OddT
Nat::EvenT_S_OddT(uint64_t,
                  const Sig<uint64_t> &h) { // Precondition: (S n) == (2 * m)
  return [&]() {
    const auto &[x0] = h;
    if (x0 <= 0) {
      throw std::logic_error("absurd case");
    } else {
      uint64_t n = x0 - 1;
      return Sig<uint64_t>::exist(n);
    }
  }();
}

Nat::EvenT Nat::OddT_S_EvenT(
    uint64_t, const Sig<uint64_t> &h) { // Precondition: (S n) == (2 * m + 1)
  const auto &[x0] = h;
  return Sig<uint64_t>::exist(x0);
}

Nat::EvenT Nat::even_EvenT(uint64_t n) {
  if (n <= 0) {
    return EvenT_0;
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      throw std::logic_error("absurd case");
    } else {
      uint64_t n1 = n0 - 1;
      Nat::EvenT he = even_EvenT(n1);
      return EvenT_2(n1, std::move(he));
    }
  }
}

Nat::OddT Nat::odd_OddT(uint64_t n) {
  if (n <= 0) {
    throw std::logic_error("absurd case");
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return OddT_1;
    } else {
      uint64_t n1 = n0 - 1;
      Nat::OddT he = odd_OddT(n1);
      return OddT_2(n1, std::move(he));
    }
  }
}

Nat::EvenT Nat::Even_EvenT(uint64_t x0_) { return even_EvenT(x0_); }

Nat::OddT Nat::Odd_OddT(uint64_t x0_) { return odd_OddT(x0_); }

Sum<Nat::EvenT, Nat::OddT> Nat::EvenT_OddT_dec(uint64_t n) {
  if (even(n)) {
    return Sum<Nat::EvenT, Nat::OddT>::inl(even_EvenT(n));
  } else {
    return Sum<Nat::EvenT, Nat::OddT>::inr(odd_OddT(n));
  }
}

bool Datatypes::xorb(bool b1, bool b2) {
  if (b1) {
    if (b2) {
      return false;
    } else {
      return true;
    }
  } else {
    return b2;
  }
}

CompareSpecT Datatypes::CompareSpec2Type(Comparison c) {
  switch (c) {
  case Comparison::EQ: {
    return CompareSpecT::COMPEQT;
  }
  case Comparison::LT: {
    return CompareSpecT::COMPLTT;
  }
  case Comparison::GT: {
    return CompareSpecT::COMPGTT;
  }
  default:
    std::unreachable();
  }
}

Reflect Bool::iff_reflect(bool b) {
  if (b) {
    return Reflect::REFLECTT;
  } else {
    return Reflect::REFLECTF;
  }
}
