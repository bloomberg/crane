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

enum class comparison { Eq, Lt, Gt };

struct Pos {
  static mpz_class succ(const mpz_class x);
  static mpz_class add(const mpz_class x, const mpz_class y);
  static mpz_class add_carry(const mpz_class x, const mpz_class y);
  static mpz_class pred_double(const mpz_class x);
  static mpz_class mul(const mpz_class x, const mpz_class y);
  static comparison compare_cont(const comparison r, const mpz_class x,
                                 const mpz_class y);
  static comparison compare(const mpz_class _x0, const mpz_class _x1);
  static bool eqb(const mpz_class p, const mpz_class q);
};

struct BinInt {
  static mpz_class double_(const mpz_class x);
  static mpz_class succ_double(const mpz_class x);
  static mpz_class pred_double(const mpz_class x);
  static mpz_class pos_sub(const mpz_class x, const mpz_class y);
  static comparison compare(const mpz_class x, const mpz_class y);
};

struct Datatypes {
  static comparison CompOpp(const comparison r);
};

struct ZGMPTest {
  static mpz_class add_test(const mpz_class _x0, const mpz_class _x1);
  static mpz_class mul_test(const mpz_class _x0, const mpz_class _x1);
  static mpz_class sub_test(const mpz_class _x0, const mpz_class _x1);
  static mpz_class abs_test(const mpz_class _x0);
  static mpz_class opp_test(const mpz_class _x0);
  static bool eqb_test(const mpz_class _x0, const mpz_class _x1);
  static bool ltb_test(const mpz_class _x0, const mpz_class _x1);
  static bool leb_test(const mpz_class _x0, const mpz_class _x1);
  static inline const mpz_class zero_val = mpz_class(0);
  static inline const mpz_class pos_val =
      (2 * (2 * (2 * (2 * (2 * mpz_class(1)) + 1)) + 1));
  static inline const mpz_class neg_val = (-(2 * (2 * mpz_class(1) + 1) + 1));
  static inline const mpz_class big_val =
      (2 *
       (2 *
        (2 * (2 * (2 * (2 * (2 * (2 * (2 * mpz_class(1) + 1) + 1) + 1) + 1)) +
              1))));
  static mpz_class z_sign(const mpz_class z);
};

#endif // INCLUDED_Z_GMP
