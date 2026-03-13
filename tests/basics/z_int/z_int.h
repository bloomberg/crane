#ifndef INCLUDED_Z_INT
#define INCLUDED_Z_INT

#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

enum class Comparison { e_EQ, e_LT, e_GT };

struct Pos {
  __attribute__((pure)) static unsigned int succ(const unsigned int x);
  __attribute__((pure)) static unsigned int add(const unsigned int x,
                                                const unsigned int y);
  __attribute__((pure)) static unsigned int add_carry(const unsigned int x,
                                                      const unsigned int y);
  __attribute__((pure)) static unsigned int pred_double(const unsigned int x);
  __attribute__((pure)) static unsigned int mul(const unsigned int x,
                                                const unsigned int y);
  __attribute__((pure)) static Comparison
  compare_cont(const Comparison r, const unsigned int x, const unsigned int y);
  __attribute__((pure)) static Comparison compare(const unsigned int _x0,
                                                  const unsigned int _x1);
  __attribute__((pure)) static bool eqb(const unsigned int p,
                                        const unsigned int q);
};

struct BinInt {
  __attribute__((pure)) static int64_t double_(const int64_t x);
  __attribute__((pure)) static int64_t succ_double(const int64_t x);
  __attribute__((pure)) static int64_t pred_double(const int64_t x);
  __attribute__((pure)) static int64_t pos_sub(const unsigned int x,
                                               const unsigned int y);
  __attribute__((pure)) static Comparison compare(const int64_t x,
                                                  const int64_t y);
};

struct Datatypes {
  __attribute__((pure)) static Comparison CompOpp(const Comparison r);
};

struct ZIntTest {
  __attribute__((pure)) static int64_t add_test(const int64_t _x0,
                                                const int64_t _x1);
  __attribute__((pure)) static int64_t mul_test(const int64_t _x0,
                                                const int64_t _x1);
  __attribute__((pure)) static int64_t sub_test(const int64_t _x0,
                                                const int64_t _x1);
  __attribute__((pure)) static int64_t abs_test(const int64_t _x0);
  __attribute__((pure)) static int64_t opp_test(const int64_t _x0);
  __attribute__((pure)) static bool eqb_test(const int64_t _x0,
                                             const int64_t _x1);
  __attribute__((pure)) static bool ltb_test(const int64_t _x0,
                                             const int64_t _x1);
  __attribute__((pure)) static bool leb_test(const int64_t _x0,
                                             const int64_t _x1);
  static inline const int64_t zero_val = INT64_C(0);
  static inline const int64_t pos_val =
      static_cast<int64_t>((2u * (2u * (2u * (2u * (2u * 1u) + 1u)) + 1u)));
  static inline const int64_t neg_val =
      (-static_cast<int64_t>((2u * (2u * 1u + 1u) + 1u)));
  static inline const int64_t big_val = static_cast<int64_t>(
      (2u *
       (2u *
        (2u * (2u * (2u * (2u * (2u * (2u * (2u * 1u + 1u) + 1u) + 1u) + 1u)) +
               1u)))));
  __attribute__((pure)) static int64_t z_sign(const int64_t z);
};

#endif // INCLUDED_Z_INT
