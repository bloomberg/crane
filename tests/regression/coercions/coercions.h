#ifndef INCLUDED_COERCIONS
#define INCLUDED_COERCIONS

#include "fn.h"
#include <cstdint>

struct Coercions {
  static uint64_t bool_to_nat(bool b);
  static uint64_t add_bool(uint64_t n, bool b);
  static constexpr uint64_t test_add_true = UINT64_C(6);
  static constexpr uint64_t test_add_false = UINT64_C(5);

  struct Wrapper {
    uint64_t unwrap;
  };

  static uint64_t double_wrapped(const Wrapper &w);
  static constexpr uint64_t test_double_wrapped = UINT64_C(14);

  struct BoolBox {
    bool unbox;
  };

  static uint64_t add_boolbox(uint64_t n, const BoolBox &bb);
  static constexpr uint64_t test_add_boolbox = UINT64_C(11);

  struct Transform {
    crane::fn<uint64_t(uint64_t)> apply_transform;
  };

  static inline const Transform double_transform =
      Transform{[](uint64_t n) { return (n + n); }};
  static constexpr uint64_t test_fun_coercion = UINT64_C(10);
};

#endif // INCLUDED_COERCIONS
