#pragma once

#include <gmpxx.h>

struct Pos {
  static mpz_class add_carry(const mpz_class &x, const mpz_class &y);
};

struct N {};

struct NGMPTest {
  static mpz_class add_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class mul_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class sub_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class div_test(const mpz_class &x0_, const mpz_class &x1_);
  static bool eqb_test(const mpz_class &x0_, const mpz_class &x1_);
  static bool ltb_test(const mpz_class &x0_, const mpz_class &x1_);
  static bool leb_test(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class succ_test(const mpz_class &x0_);
  static mpz_class pred_test(const mpz_class &x0_);
  static mpz_class double_test(const mpz_class &x0_);
  static inline const mpz_class zero_val = (0_mpz);
  static inline const mpz_class five_val = (5_mpz);
  static inline const mpz_class big_val = (1000_mpz);
  static bool is_zero(const mpz_class &n);
  static mpz_class pos_add(const mpz_class &x0_, const mpz_class &x1_);
  static mpz_class pos_succ(const mpz_class &x0_);
};
