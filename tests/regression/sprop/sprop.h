#ifndef INCLUDED_SPROP
#define INCLUDED_SPROP

#include <stdexcept>
#include <utility>

struct SPropTest {
  template <typename T1> static const T1 &sFalse_rect() {
    static const T1 v = []() { throw std::logic_error("absurd case"); }();
    return v;
  }

  template <typename T1> static const T1 &sFalse_rec() {
    static const T1 v = []() { throw std::logic_error("absurd case"); }();
    return v;
  }

  template <typename A> struct Box {
    A box_value;

    // ACCESSORS
    Box<A> clone() const { return Box<A>{(*this).box_value}; }
  };

  static uint64_t guarded_pred(uint64_t n);
  static uint64_t safe_div(uint64_t _x0, uint64_t _x1);
  static inline const uint64_t test_guarded = guarded_pred(UINT64_C(5));
  static inline const uint64_t test_box = UINT64_C(42);
  static inline const uint64_t test_div = safe_div(UINT64_C(10), UINT64_C(3));
};

#endif // INCLUDED_SPROP
