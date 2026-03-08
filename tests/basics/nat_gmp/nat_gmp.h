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

struct NatGMPTest {
  static mpz_class add_test(const mpz_class, const mpz_class);

  static mpz_class mul_test(const mpz_class, const mpz_class);

  static mpz_class sub_test(const mpz_class, const mpz_class);

  static bool eqb_test(const mpz_class, const mpz_class);

  static bool ltb_test(const mpz_class, const mpz_class);

  static bool leb_test(const mpz_class, const mpz_class);

  static mpz_class pred_test(const mpz_class);

  static mpz_class match_test(const mpz_class n);

  static inline const mpz_class big_num = mpz_class(200);

  static inline const mpz_class another_big = mpz_class(1000);

  static mpz_class add_big(const mpz_class n);
};
