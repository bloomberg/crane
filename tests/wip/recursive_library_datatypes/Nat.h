#ifndef INCLUDED_NAT
#define INCLUDED_NAT

#include <algorithm>
#include <cstdint>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

#include "Datatypes.h"
#include "Decimal.h"
#include "Hexadecimal.h"
#include "Number.h"

using t = uint64_t;
inline constexpr uint64_t zero = UINT64_C(0);
inline constexpr uint64_t one = UINT64_C(1);
inline constexpr uint64_t two = UINT64_C(2);
uint64_t succ(uint64_t x);
Comparison compare(uint64_t n, uint64_t m);
bool even(uint64_t n);
bool odd(uint64_t n);
uint64_t pow(uint64_t n, uint64_t m);
uint64_t tail_add(uint64_t n, uint64_t m);
uint64_t tail_addmul(uint64_t r, uint64_t n, uint64_t m);
uint64_t tail_mul(uint64_t n, uint64_t m);
uint64_t of_uint_acc(const Uint::Uint &d, uint64_t acc);
uint64_t of_uint(const Uint::Uint &d);
uint64_t of_hex_uint_acc(const Uint::Uint &d, uint64_t acc);
uint64_t of_hex_uint(const Uint::Uint &d);
uint64_t of_num_uint(const Uint::Uint &d);
Uint::Uint to_little_uint(uint64_t n, Uint::Uint acc);
Uint::Uint to_uint(uint64_t n);
Uint::Uint to_little_hex_uint(uint64_t n, Uint::Uint acc);
Uint::Uint to_hex_uint(uint64_t n);
Uint::Uint to_num_uint(uint64_t n);
Uint::Uint to_num_hex_uint(uint64_t n);
std::optional<uint64_t> of_int(const Signed_int::Signed_int &d);
std::optional<uint64_t> of_hex_int(const Signed_int::Signed_int &d);
std::optional<uint64_t> of_num_int(const Signed_int::Signed_int &d);
Signed_int::Signed_int to_int(uint64_t n);
Signed_int::Signed_int to_hex_int(uint64_t n);
Signed_int::Signed_int to_num_int(uint64_t n);
std::pair<uint64_t, uint64_t> divmod(uint64_t x, uint64_t y, uint64_t q,
                                     uint64_t u);
uint64_t gcd(uint64_t a, uint64_t b);
uint64_t square(uint64_t n);
uint64_t sqrt_iter(uint64_t k, uint64_t p, uint64_t q, uint64_t r);
uint64_t sqrt(uint64_t n);
uint64_t log2_iter(uint64_t k, uint64_t p, uint64_t q, uint64_t r);
uint64_t log2(uint64_t n);
uint64_t div2(uint64_t n);
bool testbit(uint64_t a, uint64_t n);
uint64_t shiftl(uint64_t a, uint64_t n);
uint64_t shiftr(uint64_t a, uint64_t n);

template <typename F0>
uint64_t bitwise(F0 &&op, uint64_t n, uint64_t a, uint64_t b) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    return ((op(odd(a), odd(b)) ? UINT64_C(1) : UINT64_C(0)) +
            (UINT64_C(2) * bitwise(op, n_, div2(a), div2(b))));
  }
}

uint64_t land(uint64_t a, uint64_t b);
uint64_t lor(uint64_t a, uint64_t b);
uint64_t ldiff(uint64_t a, uint64_t b);
uint64_t lxor(uint64_t a, uint64_t b);

#endif // INCLUDED_NAT
