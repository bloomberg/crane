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

  static unsigned int guarded_pred(unsigned int n);
  static unsigned int safe_div(unsigned int _x0, unsigned int _x1);
  static inline const unsigned int test_guarded = guarded_pred(5u);
  static inline const unsigned int test_box = 42u;
  static inline const unsigned int test_div = safe_div(10u, 3u);
};

#endif // INCLUDED_SPROP
