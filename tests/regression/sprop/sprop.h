#ifndef INCLUDED_SPROP
#define INCLUDED_SPROP

#include "crane_fn.h"
#include "obj.h"
#include <cstdint>
#include <stdexcept>
#include <utility>

struct SPropTest {
  template <typename T1> static T1 sFalse_rect() {
    throw std::logic_error("absurd case");
  }

  template <typename T1> static const T1 &sFalse_rec() {
    static const T1 v = [](crane::obj) {
      throw std::logic_error("untranslatable curried proof term");
    };
    return v;
  }

  template <typename A> struct Box {
    A box_value;

    // ACCESSORS
    template <typename CraneU>
      requires crane_convertible<CraneU, const A &>
    operator Box<CraneU>() const {
      return {crane_convert<CraneU>(box_value)};
    }
  };

  static uint64_t guarded_pred(uint64_t n);
  static uint64_t safe_div(uint64_t x0_, uint64_t x1_);
  static constexpr uint64_t test_guarded = UINT64_C(4);
  static constexpr uint64_t test_box = UINT64_C(42);
  static constexpr uint64_t test_div = UINT64_C(3);
};

#endif // INCLUDED_SPROP
