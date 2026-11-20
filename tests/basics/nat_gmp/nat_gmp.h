#pragma once

#include <gmpxx.h>

struct NatGMPTest {
  static mpz_class add_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class mul_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class sub_test(const mpz_class &x0_, const mpz_class &x1_);
  static bool eqb_test(const mpz_class &x0_, const mpz_class &x1_);
  static bool ltb_test(const mpz_class &x0_, const mpz_class &x1_);
  static bool leb_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class pred_test(const mpz_class &x0_);
  static mpz_class match_test(const mpz_class &n);
  static inline const mpz_class big_num = (200_mpz);
  static inline const mpz_class another_big = (1000_mpz);
  static mpz_class add_big(const mpz_class &n);
};
