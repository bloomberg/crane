#ifndef INCLUDED_N_INT
#define INCLUDED_N_INT

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Pos {
  __attribute__((pure)) static unsigned int add_carry(const unsigned int x,
                                                      const unsigned int y);
};

struct BinNat {};

struct NIntTest {
  __attribute__((pure)) static unsigned int add_test(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static unsigned int mul_test(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static unsigned int sub_test(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static unsigned int div_test(const unsigned int _x0,
                                                     const unsigned int _x1);
  __attribute__((pure)) static bool eqb_test(const unsigned int _x0,
                                             const unsigned int _x1);
  __attribute__((pure)) static bool ltb_test(const unsigned int _x0,
                                             const unsigned int _x1);
  __attribute__((pure)) static bool leb_test(const unsigned int _x0,
                                             const unsigned int _x1);
  __attribute__((pure)) static unsigned int succ_test(const unsigned int _x0);
  __attribute__((pure)) static unsigned int pred_test(const unsigned int _x0);
  __attribute__((pure)) static unsigned int double_test(const unsigned int _x0);
  static inline const unsigned int zero_val = 0u;
  static inline const unsigned int five_val = (2u * (2u * 1u) + 1u);
  static inline const unsigned int big_val =
      (2u *
       (2u *
        (2u * (2u * (2u * (2u * (2u * (2u * (2u * 1u + 1u) + 1u) + 1u) + 1u)) +
               1u))));
  __attribute__((pure)) static bool is_zero(const unsigned int n);
  __attribute__((pure)) static unsigned int pos_add(const unsigned int _x0,
                                                    const unsigned int _x1);
  __attribute__((pure)) static unsigned int pos_succ(const unsigned int _x0);
};

#endif // INCLUDED_N_INT
