#ifndef INCLUDED_NAT_GMP
#define INCLUDED_NAT_GMP

#include <gmpxx.h>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct NatGMPTest {
  static mpz_class add_test(const mpz_class &_x0, const mpz_class &_x1);
  static mpz_class mul_test(const mpz_class &_x0, const mpz_class &_x1);
  static mpz_class sub_test(const mpz_class &_x0, const mpz_class &_x1);
  static bool eqb_test(const mpz_class &_x0, const mpz_class &_x1);
  static bool ltb_test(const mpz_class &_x0, const mpz_class &_x1);
  static bool leb_test(const mpz_class &_x0, const mpz_class &_x1);
  static mpz_class pred_test(const mpz_class &_x0);
  static mpz_class match_test(const mpz_class &n);
  static inline const mpz_class big_num = mpz_class(200);
  static inline const mpz_class another_big = mpz_class(1000);
  static mpz_class add_big(const mpz_class &n);
};

#endif // INCLUDED_NAT_GMP
