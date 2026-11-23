#pragma once

#include <gmpxx.h>

struct Z {};

struct ZGMPTest {
  static mpz_class add_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class mul_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class sub_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class abs_test(const mpz_class &x0_);
  static mpz_class opp_test(const mpz_class &x0_);
  static bool eqb_test(const mpz_class &x0_, const mpz_class &x1_);
  static bool ltb_test(const mpz_class &x0_, const mpz_class &x1_);
  static bool leb_test(const mpz_class &x0_, const mpz_class &x1_);
  static inline const mpz_class zero_val = (0_mpz);
  static inline const mpz_class pos_val = (42_mpz);
  static inline const mpz_class neg_val = (-7_mpz);
  static inline const mpz_class big_val = (1000_mpz);
  static mpz_class z_sign(const mpz_class &z);
};
