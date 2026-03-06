#include <algorithm>
#include <any>
#include <cassert>
#include <cstdint>
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

struct Int63Arith {
  static inline const int64_t i_zero = int64_t(0);

  static inline const int64_t i_one = int64_t(1);

  static inline const int64_t i_add =
      ((int64_t(10) + int64_t(20)) & 0x7FFFFFFFFFFFFFFFLL);

  static inline const int64_t i_mul =
      ((int64_t(6) * int64_t(7)) & 0x7FFFFFFFFFFFFFFFLL);

  static inline const int64_t i_sub =
      ((int64_t(50) - int64_t(8)) & 0x7FFFFFFFFFFFFFFFLL);

  static inline const bool i_eqb_true = (int64_t(42) == int64_t(42));

  static inline const bool i_eqb_false = (int64_t(42) == int64_t(43));

  static inline const bool i_ltb_true = (int64_t(3) < int64_t(5));

  static inline const bool i_ltb_false = (int64_t(5) < int64_t(3));

  static inline const bool i_leb_true = (int64_t(3) <= int64_t(3));

  static inline const bool i_leb_false = (int64_t(5) <= int64_t(3));

  static int64_t i_abs(const int64_t x);

  static inline const int64_t test_abs_pos = i_abs(int64_t(42));

  static inline const int64_t test_abs_neg =
      i_abs(((int64_t(0) - int64_t(42)) & 0x7FFFFFFFFFFFFFFFLL));
};
