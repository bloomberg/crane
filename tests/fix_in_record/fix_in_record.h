#ifndef INCLUDED_FIX_IN_RECORD
#define INCLUDED_FIX_IN_RECORD

#include <functional>
#include <utility>

struct FixInRecord {
  struct fn_box {
    uint64_t label;
    std::function<uint64_t(uint64_t)> fn;
  };

  static fn_box make_box(uint64_t n);
  static inline const uint64_t test1 = make_box(UINT64_C(10)).fn(UINT64_C(7));
  static inline const uint64_t test2 = []() {
    fn_box bx = make_box(UINT64_C(20));
    uint64_t noise =
        ((((UINT64_C(1) + UINT64_C(2)) + UINT64_C(3)) + UINT64_C(4)) +
         UINT64_C(5));
    return std::move(bx).fn(noise);
  }();
  static inline const uint64_t test3 = []() {
    fn_box bx = make_box(UINT64_C(5));
    return (bx.label + bx.fn(UINT64_C(0)));
  }();
};

#endif // INCLUDED_FIX_IN_RECORD
