#ifndef INCLUDED_OPAQUE
#define INCLUDED_OPAQUE

#include <stdexcept>
#include <utility>

template <typename A> struct Sig {
  // DATA
  A x;

  // ACCESSORS
  Sig<A> clone() const { return {x}; }

  // CREATORS
  static Sig<A> exist(A x) { return {std::move(x)}; }
};

struct Opaque {
  static uint64_t safe_pred(uint64_t n);
  static uint64_t pred_of_succ(uint64_t n);
  static bool nat_eq_dec(uint64_t n, uint64_t x);
  static bool are_equal(uint64_t n, uint64_t m);
  static Sig<uint64_t> bounded_add(uint64_t _x0, uint64_t _x1, uint64_t _x2);
  static inline const uint64_t test_safe_pred = safe_pred(UINT64_C(5));
  static inline const uint64_t test_pred_succ = pred_of_succ(UINT64_C(7));
  static inline const bool test_eq_true = are_equal(UINT64_C(5), UINT64_C(5));
  static inline const bool test_eq_false = are_equal(UINT64_C(3), UINT64_C(7));
};

#endif // INCLUDED_OPAQUE
