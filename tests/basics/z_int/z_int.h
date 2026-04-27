#ifndef INCLUDED_Z_INT
#define INCLUDED_Z_INT

#include <cstdint>
#include <cstdlib>
#include <memory>
#include <optional>
#include <type_traits>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct ZIntTest {
  __attribute__((pure)) static int64_t add_test(const int64_t &_x0,
                                                const int64_t &_x1);
  __attribute__((pure)) static int64_t mul_test(const int64_t &_x0,
                                                const int64_t &_x1);
  __attribute__((pure)) static int64_t sub_test(const int64_t &_x0,
                                                const int64_t &_x1);
  __attribute__((pure)) static int64_t abs_test(const int64_t &_x0);
  __attribute__((pure)) static int64_t opp_test(const int64_t &_x0);
  __attribute__((pure)) static bool eqb_test(const int64_t &_x0,
                                             const int64_t &_x1);
  __attribute__((pure)) static bool ltb_test(const int64_t &_x0,
                                             const int64_t &_x1);
  __attribute__((pure)) static bool leb_test(const int64_t &_x0,
                                             const int64_t &_x1);
  static inline const int64_t zero_val = INT64_C(0);
  static inline const int64_t pos_val = INT64_C(42);
  static inline const int64_t neg_val = INT64_C(-7);
  static inline const int64_t big_val = INT64_C(1000);
  __attribute__((pure)) static int64_t z_sign(const int64_t &z);
};

#endif // INCLUDED_Z_INT
