// Copyright 2026 Bloomberg Finance L.P.
// Distributed under the terms of the GNU LGPL v2.1 license.
//
// The PrimInt63 primitives the typed int63 mappings (theories/Mapping/
// StdCore.v, BDE.v) spell as calls rather than as an operator.  An int63 is
// an int64_t holding 0..2^63-1; each function follows Rocq's kernel
// (kernel/uint63_63.ml) exactly.  A result that is a Rocq inductive -- a
// pair, a carry, a comparison -- is built at the type the mapping names:
// a pair from its two components, a carry by its [c0]/[c1] factories, a
// comparison enum by its constructors' declaration order.  Flavor
// independent: only <cstdint> and <bit>.

#pragma once

#include <bit>
#include <cstdint>

namespace crane {

inline constexpr std::uint64_t int63_mask = 0x7FFFFFFFFFFFFFFFULL;

// The 63 low bits of `v`, as an int63.
constexpr std::int64_t int63_of(std::uint64_t v) {
  return static_cast<std::int64_t>(v & int63_mask);
}

// `x` read as a signed 63-bit integer (bit 62 is the sign).
constexpr std::int64_t int63_signed(std::int64_t x) {
  return static_cast<std::int64_t>(static_cast<std::uint64_t>(x) << 1) >> 1;
}

// PrimInt63.asr: arithmetic shift of the signed reading; 0 when y >= 63.
constexpr std::int64_t int63_asr(std::int64_t x, std::int64_t y) {
  return y < 63 ? int63_of(static_cast<std::uint64_t>(int63_signed(x) >> (y & 63)))
                : 0;
}

// PrimInt63.divs / mods: truncating signed division; x / 0 is 0 and
// x mod 0 is x.  The quotient of -2^62 by -1 wraps to -2^62, as Rocq's.
constexpr std::int64_t int63_divs(std::int64_t x, std::int64_t y) {
  return y == 0 ? 0
                : int63_of(static_cast<std::uint64_t>(int63_signed(x) /
                                                      int63_signed(y)));
}

constexpr std::int64_t int63_mods(std::int64_t x, std::int64_t y) {
  return y == 0 ? x
                : int63_of(static_cast<std::uint64_t>(int63_signed(x) %
                                                      int63_signed(y)));
}

// PrimInt63.ltsb / lesb: signed comparisons.
constexpr bool int63_ltsb(std::int64_t x, std::int64_t y) {
  return int63_signed(x) < int63_signed(y);
}

constexpr bool int63_lesb(std::int64_t x, std::int64_t y) {
  return int63_signed(x) <= int63_signed(y);
}

// PrimInt63.compare (unsigned) and compares (signed), as the comparison
// enum: Eq, Lt, Gt in declaration order.
template <class Comparison>
constexpr Comparison int63_compare(std::int64_t x, std::int64_t y) {
  return static_cast<Comparison>(x == y ? 0 : (x < y ? 1 : 2));
}

template <class Comparison>
constexpr Comparison int63_compares(std::int64_t x, std::int64_t y) {
  return int63_compare<Comparison>(int63_signed(x), int63_signed(y));
}

// PrimInt63.head0 / tail0: leading / trailing zeros within 63 bits; 63
// for 0.
constexpr std::int64_t int63_head0(std::int64_t x) {
  return x == 0 ? 63 : std::countl_zero(static_cast<std::uint64_t>(x)) - 1;
}

constexpr std::int64_t int63_tail0(std::int64_t x) {
  return x == 0 ? 63 : std::countr_zero(static_cast<std::uint64_t>(x));
}

// PrimInt63.addmuldiv p x y: (x << p) lor (y >> (63 - p)), each shift 0
// where its count is out of 0..62.
constexpr std::int64_t int63_addmuldiv(std::int64_t p, std::int64_t x,
                                       std::int64_t y) {
  std::uint64_t high =
      p < 63 ? (static_cast<std::uint64_t>(x) << (p & 63)) & int63_mask : 0;
  std::uint64_t low = (p >= 1 && p <= 63)
                          ? static_cast<std::uint64_t>(y) >> ((63 - p) & 63)
                          : 0;
  return int63_of(high | low);
}

// PrimInt63.diveucl: quotient and remainder; by 0, (0, x).
template <class Pair>
constexpr Pair int63_diveucl(std::int64_t x, std::int64_t y) {
  return y == 0 ? Pair{0, x} : Pair{x / y, x % y};
}

// PrimInt63.diveucl_21 xh xl y: (xh * 2^63 + xl) divided by y, where
// xh < y; (0, 0) otherwise.  Long division a bit at a time, as Rocq's.
template <class Pair>
constexpr Pair int63_diveucl_21(std::int64_t xh, std::int64_t xl,
                                std::int64_t y) {
  std::uint64_t d = static_cast<std::uint64_t>(y);
  std::uint64_t nh = static_cast<std::uint64_t>(xh);
  if (d <= nh) {
    return Pair{0, 0};
  }
  std::uint64_t nl = static_cast<std::uint64_t>(xl);
  std::uint64_t q = 0;
  for (int i = 0; i < 63; ++i) {
    nh = (nh << 1) | (nl >> 62);
    nl = (nl << 1) & int63_mask;
    q = (q << 1) & int63_mask;
    if (nh >= d) {
      q |= 1;
      nh -= d;
    }
  }
  return Pair{static_cast<std::int64_t>(q), static_cast<std::int64_t>(nh)};
}

// PrimInt63.mulc: the 126-bit product as (high 63 bits, low 63 bits).
template <class Pair>
constexpr Pair int63_mulc(std::int64_t x, std::int64_t y) {
  std::uint64_t a = static_cast<std::uint64_t>(x);
  std::uint64_t b = static_cast<std::uint64_t>(y);
  std::uint64_t alo = a & 0xFFFFFFFFULL, ahi = a >> 32;
  std::uint64_t blo = b & 0xFFFFFFFFULL, bhi = b >> 32;
  std::uint64_t p0 = alo * blo, p1 = alo * bhi, p2 = ahi * blo, p3 = ahi * bhi;
  std::uint64_t mid = (p0 >> 32) + (p1 & 0xFFFFFFFFULL) + (p2 & 0xFFFFFFFFULL);
  std::uint64_t lo64 = (p0 & 0xFFFFFFFFULL) | (mid << 32);
  std::uint64_t hi64 = p3 + (p1 >> 32) + (p2 >> 32) + (mid >> 32);
  return Pair{static_cast<std::int64_t>((hi64 << 1) | (lo64 >> 63)),
              int63_of(lo64)};
}

// PrimInt63.addc, addcarryc, subc, subcarryc: the result modulo 2^63, C1
// where it carried or borrowed.
template <class Carry>
constexpr Carry int63_addc(std::int64_t x, std::int64_t y) {
  std::int64_t r =
      int63_of(static_cast<std::uint64_t>(x) + static_cast<std::uint64_t>(y));
  return r < x ? Carry::c1(r) : Carry::c0(r);
}

template <class Carry>
constexpr Carry int63_addcarryc(std::int64_t x, std::int64_t y) {
  std::int64_t r = int63_of(static_cast<std::uint64_t>(x) +
                            static_cast<std::uint64_t>(y) + 1);
  return r <= x ? Carry::c1(r) : Carry::c0(r);
}

template <class Carry>
constexpr Carry int63_subc(std::int64_t x, std::int64_t y) {
  std::int64_t r =
      int63_of(static_cast<std::uint64_t>(x) - static_cast<std::uint64_t>(y));
  return y <= x ? Carry::c0(r) : Carry::c1(r);
}

template <class Carry>
constexpr Carry int63_subcarryc(std::int64_t x, std::int64_t y) {
  std::int64_t r = int63_of(static_cast<std::uint64_t>(x) -
                            static_cast<std::uint64_t>(y) - 1);
  return y < x ? Carry::c0(r) : Carry::c1(r);
}

} // namespace crane
