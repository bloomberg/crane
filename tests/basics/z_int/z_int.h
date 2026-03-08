#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
#include <cstdlib>
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

enum class comparison { Eq, Lt, Gt };

struct Pos {
  static unsigned int succ(const unsigned int x);

  static unsigned int add(const unsigned int x, const unsigned int y);
  static unsigned int add_carry(const unsigned int x, const unsigned int y);

  static unsigned int pred_double(const unsigned int x);

  static unsigned int mul(const unsigned int x, const unsigned int y);

  static comparison compare_cont(const comparison r, const unsigned int x,
                                 const unsigned int y);

  static comparison compare(const unsigned int, const unsigned int);

  static bool eqb(const unsigned int p, const unsigned int q);
};

struct BinInt {
  static int64_t double_(const int64_t x);

  static int64_t succ_double(const int64_t x);

  static int64_t pred_double(const int64_t x);

  static int64_t pos_sub(const unsigned int x, const unsigned int y);

  static comparison compare(const int64_t x, const int64_t y);
};

struct Datatypes {
  static comparison CompOpp(const comparison r);
};

struct ZIntTest {
  static int64_t add_test(const int64_t, const int64_t);

  static int64_t mul_test(const int64_t, const int64_t);

  static int64_t sub_test(const int64_t, const int64_t);

  static int64_t abs_test(const int64_t);

  static int64_t opp_test(const int64_t);

  static bool eqb_test(const int64_t, const int64_t);

  static bool ltb_test(const int64_t, const int64_t);

  static bool leb_test(const int64_t, const int64_t);

  static inline const int64_t zero_val = INT64_C(0);

  static inline const int64_t pos_val =
      static_cast<int64_t>((2u * (2u * (2u * (2u * (2u * 1u) + 1u)) + 1u)));

  static inline const int64_t neg_val =
      (-static_cast<int64_t>((2u * (2u * 1u + 1u) + 1u)));

  static inline const int64_t big_val = static_cast<int64_t>(
      (2u *
       (2u *
        (2u * (2u * (2u * (2u * (2u * (2u * (2u * 1u + 1u) + 1u) + 1u) + 1u)) +
               1u)))));

  static int64_t z_sign(const int64_t z);
};
