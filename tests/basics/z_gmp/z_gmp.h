#ifndef INCLUDED_Z_GMP
#define INCLUDED_Z_GMP

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <gmpxx.h>
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
  __attribute__((pure)) static mpz_class succ(const mpz_class x);
  __attribute__((pure)) static mpz_class add(const mpz_class x,
                                             const mpz_class y);
  __attribute__((pure)) static mpz_class add_carry(const mpz_class x,
                                                   const mpz_class y);
  __attribute__((pure)) static mpz_class pred_double(const mpz_class x);
  __attribute__((pure)) static mpz_class mul(const mpz_class x,
                                             const mpz_class y);
  __attribute__((pure)) static Comparison
  compare_cont(const Comparison r, const mpz_class x, const mpz_class y);
  __attribute__((pure)) static Comparison compare(const mpz_class _x0,
                                                  const mpz_class _x1);
  __attribute__((pure)) static bool eqb(const mpz_class p, const mpz_class q);
};

struct BinInt {
  __attribute__((pure)) static mpz_class double_(const mpz_class x);
  __attribute__((pure)) static mpz_class succ_double(const mpz_class x);
  __attribute__((pure)) static mpz_class pred_double(const mpz_class x);
  __attribute__((pure)) static mpz_class pos_sub(const mpz_class x,
                                                 const mpz_class y);
  __attribute__((pure)) static Comparison compare(const mpz_class x,
                                                  const mpz_class y);
};

struct Datatypes {
  __attribute__((pure)) static Comparison CompOpp(const Comparison r);
};

struct ZGMPTest {
  __attribute__((pure)) static mpz_class add_test(const mpz_class _x0,
                                                  const mpz_class _x1);
  __attribute__((pure)) static mpz_class mul_test(const mpz_class _x0,
                                                  const mpz_class _x1);
  __attribute__((pure)) static mpz_class sub_test(const mpz_class _x0,
                                                  const mpz_class _x1);
  __attribute__((pure)) static mpz_class abs_test(const mpz_class _x0);
  __attribute__((pure)) static mpz_class opp_test(const mpz_class _x0);
  __attribute__((pure)) static bool eqb_test(const mpz_class _x0,
                                             const mpz_class _x1);
  __attribute__((pure)) static bool ltb_test(const mpz_class _x0,
                                             const mpz_class _x1);
  __attribute__((pure)) static bool leb_test(const mpz_class _x0,
                                             const mpz_class _x1);
  static inline const mpz_class zero_val = mpz_class(0);
  static inline const mpz_class pos_val =
      (2 * (2 * (2 * (2 * (2 * mpz_class(1)) + 1)) + 1));
  static inline const mpz_class neg_val = (-(2 * (2 * mpz_class(1) + 1) + 1));
  static inline const mpz_class big_val =
      (2 *
       (2 *
        (2 * (2 * (2 * (2 * (2 * (2 * (2 * mpz_class(1) + 1) + 1) + 1) + 1)) +
              1))));
  __attribute__((pure)) static mpz_class z_sign(const mpz_class z);
};

#endif // INCLUDED_Z_GMP
