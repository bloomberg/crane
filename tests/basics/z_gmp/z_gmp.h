#ifndef INCLUDED_Z_GMP
#define INCLUDED_Z_GMP

#include <gmpxx.h>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct BinInt {};

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
