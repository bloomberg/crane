#ifndef INCLUDED_SPROP
#define INCLUDED_SPROP

#include "crane_fn.h"
#include <any>
#include <stdexcept>
#include <utility>

struct SPropTest {
  template <typename T1> static T1 sFalse_rect() {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static T1 sFalse_rec() {
    throw std::logic_error("absurd case");
  }

  template <typename A> struct Box {
    A box_value;

    // ACCESSORS
    template <typename _U> operator Box<_U>() const {
      return {[&]() -> _U {
        if constexpr (crane_convertible<_U, const A &>) {
          return crane_convert<_U>(box_value);
        } else {
          throw std::logic_error(
              "unreachable: inactive constructor field at this instantiation");
        }
      }()};
    }
  };

  static uint64_t guarded_pred(uint64_t n);
  static uint64_t safe_div(uint64_t x0_, uint64_t x1_);
  static inline const uint64_t test_guarded = guarded_pred(UINT64_C(5));
  static inline const uint64_t test_box = UINT64_C(42);
  static inline const uint64_t test_div = safe_div(UINT64_C(10), UINT64_C(3));
};

#endif // INCLUDED_SPROP
