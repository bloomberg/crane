#ifndef INCLUDED_FIX_IN_RECORD
#define INCLUDED_FIX_IN_RECORD

#include <functional>
#include <utility>

struct FixInRecord {
  /// A local fixpoint stored in a Rocq record field.
  ///
  /// BUG HYPOTHESIS: Records are translated to C++ structs with named
  /// fields. A field of type nat -> nat becomes
  /// std::function<unsigned int(unsigned int)>. When a local fixpoint
  /// (which uses & capture) is stored in a record field, the
  /// std::function wraps the & closure. After the creating function
  /// returns, the captured references dangle.
  ///
  /// This is a different escape mechanism from option/pair/list:
  /// the closure escapes through a RECORD FIELD.
  struct fn_box {
    uint64_t label;
    std::function<uint64_t(uint64_t)> fn;

    // ACCESSORS
    fn_box clone() const { return fn_box{this->label, this->fn}; }
  };

  static fn_box make_box(uint64_t n);
  /// test1: n=10, base=30, fn = add where add(x) = 30+x.
  /// fn(make_box 10)(7) = 30 + 7 = 37.
  /// Bug: base captured by & in add, dangles after make_box returns.
  static inline const uint64_t test1 = make_box(UINT64_C(10)).fn(UINT64_C(7));
  /// test2: With intervening work.
  /// n=20, base=60, fn(5) = 60+5 = 65.
  static inline const uint64_t test2 = []() {
    fn_box bx = make_box(UINT64_C(20));
    uint64_t noise =
        ((((UINT64_C(1) + UINT64_C(2)) + UINT64_C(3)) + UINT64_C(4)) +
         UINT64_C(5));
    return std::move(bx).fn(noise);
  }();
  /// test3: Use label too (to ensure struct is alive).
  /// n=5, base=15, label=15, fn(0) = 15. label + fn(0) = 30.
  static inline const uint64_t test3 = []() {
    fn_box bx = make_box(UINT64_C(5));
    return (bx.label + bx.fn(UINT64_C(0)));
  }();
};

#endif // INCLUDED_FIX_IN_RECORD
