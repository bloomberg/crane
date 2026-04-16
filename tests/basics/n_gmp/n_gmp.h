#ifndef INCLUDED_N_GMP
#define INCLUDED_N_GMP

#include <gmpxx.h>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

struct Pos {
  __attribute__((pure)) static mpz_class add_carry(const mpz_class x,
                                                   const mpz_class y);
};

struct NGMPTest {
  __attribute__((pure)) static mpz_class add_test(const mpz_class _x0,
                                                  const mpz_class _x1);
  __attribute__((pure)) static mpz_class mul_test(const mpz_class _x0,
                                                  const mpz_class _x1);
  __attribute__((pure)) static mpz_class sub_test(const mpz_class _x0,
                                                  const mpz_class _x1);
  __attribute__((pure)) static mpz_class div_test(const mpz_class _x0,
                                                  const mpz_class _x1);
  __attribute__((pure)) static bool eqb_test(const mpz_class _x0,
                                             const mpz_class _x1);
  __attribute__((pure)) static bool ltb_test(const mpz_class _x0,
                                             const mpz_class _x1);
  __attribute__((pure)) static bool leb_test(const mpz_class _x0,
                                             const mpz_class _x1);
  __attribute__((pure)) static mpz_class succ_test(const mpz_class _x0);
  __attribute__((pure)) static mpz_class pred_test(const mpz_class _x0);
  __attribute__((pure)) static mpz_class double_test(const mpz_class _x0);
  static inline const mpz_class zero_val = mpz_class(0);
  static inline const mpz_class five_val = mpz_class(5);
  static inline const mpz_class big_val = mpz_class(1000);
  __attribute__((pure)) static bool is_zero(const mpz_class n);
  __attribute__((pure)) static mpz_class pos_add(const mpz_class _x0,
                                                 const mpz_class _x1);
  __attribute__((pure)) static mpz_class pos_succ(const mpz_class _x0);
};

#endif // INCLUDED_N_GMP
