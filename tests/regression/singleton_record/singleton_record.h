#ifndef INCLUDED_SINGLETON_RECORD
#define INCLUDED_SINGLETON_RECORD

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <cstdint>

struct SingletonRecord {
  struct wrapper {
    uint64_t value;
  };

  static inline const wrapper wrapped_five = wrapper{UINT64_C(5)};
  static uint64_t get_value(const wrapper &w);
  static uint64_t get_value2(const wrapper &w);
  static uint64_t unwrap(const wrapper &w);
  static wrapper double_wrapped(const wrapper &w);

  template <typename A> struct box {
    A contents;

    // ACCESSORS
    template <typename CraneU>
      requires crane_convertible<CraneU, const A &>
    operator box<CraneU>() const {
      return {crane_convert<CraneU>(contents)};
    }
  };

  static inline const box<uint64_t> boxed_three = box<uint64_t>{UINT64_C(3)};

  template <typename T1> static T1 unbox(const box<T1> &b) {
    return b.contents;
  }

  static inline const box<box<uint64_t>> nested_box =
      box<box<uint64_t>>{boxed_three};
  static constexpr uint64_t double_unbox = UINT64_C(3);

  struct fn_wrapper {
    crane::fn<uint64_t(uint64_t)> fn;
  };

  static inline const fn_wrapper my_fn_wrapper =
      fn_wrapper{[](uint64_t _x0) -> uint64_t { return (UINT64_C(1) + _x0); }};
  static uint64_t apply_wrapped(const fn_wrapper &w, uint64_t n);
  static constexpr uint64_t test_get = UINT64_C(5);
  static constexpr uint64_t test_get2 = UINT64_C(5);
  static constexpr uint64_t test_unwrap = UINT64_C(5);
  static constexpr uint64_t test_double = UINT64_C(10);
  static constexpr uint64_t test_unbox = UINT64_C(3);
  static constexpr uint64_t test_double_unbox = UINT64_C(3);
  static constexpr uint64_t test_fn = UINT64_C(8);
};

#endif // INCLUDED_SINGLETON_RECORD
