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
  static unsigned int safe_pred(unsigned int n);
  static unsigned int pred_of_succ(unsigned int n);
  static bool nat_eq_dec(unsigned int n, unsigned int x);
  static bool are_equal(unsigned int n, unsigned int m);
  static Sig<unsigned int> bounded_add(unsigned int _x0, unsigned int _x1,
                                       unsigned int _x2);
  static inline const unsigned int test_safe_pred = safe_pred(5u);
  static inline const unsigned int test_pred_succ = pred_of_succ(7u);
  static inline const bool test_eq_true = are_equal(5u, 5u);
  static inline const bool test_eq_false = are_equal(3u, 7u);
};

#endif // INCLUDED_OPAQUE
