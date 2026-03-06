#include <algorithm>
#include <any>
#include <cassert>
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

struct BoolOps {
  static inline const bool bool_true = true;

  static inline const bool bool_false = false;

  static bool my_negb(const bool b);

  static bool my_andb(const bool a, const bool b);

  static bool my_orb(const bool a, const bool b);

  static bool my_xorb(const bool a, const bool b);

  static unsigned int if_nat(const bool b, const unsigned int t,
                             const unsigned int f);

  static bool complex_bool(const bool a, const bool b, const bool c);

  static bool nat_eq(const unsigned int, const unsigned int);

  static bool nat_lt(const unsigned int, const unsigned int);

  static bool nat_le(const unsigned int, const unsigned int);

  static inline const bool test_neg_t = my_negb(true);

  static inline const bool test_neg_f = my_negb(false);

  static inline const bool test_and_tt = my_andb(true, true);

  static inline const bool test_and_tf = my_andb(true, false);

  static inline const bool test_or_ff = my_orb(false, false);

  static inline const bool test_or_ft = my_orb(false, true);

  static inline const bool test_xor_tt = my_xorb(true, true);

  static inline const bool test_xor_tf = my_xorb(true, false);

  static inline const unsigned int test_if_t = if_nat(true, 5u, 3u);

  static inline const unsigned int test_if_f = if_nat(false, 5u, 3u);

  static inline const bool test_complex = complex_bool(true, false, true);

  static inline const bool test_eq_tt = nat_eq(5u, 5u);

  static inline const bool test_eq_tf = nat_eq(5u, 3u);

  static inline const bool test_lt = nat_lt(3u, 5u);
};
