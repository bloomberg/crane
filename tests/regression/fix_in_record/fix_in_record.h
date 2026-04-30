#ifndef INCLUDED_FIX_IN_RECORD
#define INCLUDED_FIX_IN_RECORD

#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

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
    unsigned int label;
    std::function<unsigned int(unsigned int)> fn;

    // ACCESSORS
    fn_box clone() const { return fn_box{(*(this)).label, (*(this)).fn}; }
  };

  static fn_box make_box(const unsigned int &n);
  /// test1: n=10, base=30, fn = add where add(x) = 30+x.
  /// fn(make_box 10)(7) = 30 + 7 = 37.
  /// Bug: base captured by & in add, dangles after make_box returns.
  static inline const unsigned int test1 = make_box(10u).fn(7u);
  /// test2: With intervening work.
  /// n=20, base=60, fn(5) = 60+5 = 65.
  static inline const unsigned int test2 = []() {
    fn_box bx = make_box(20u);
    unsigned int noise = ((((1u + 2u) + 3u) + 4u) + 5u);
    return std::move(bx).fn(noise);
  }();
  /// test3: Use label too (to ensure struct is alive).
  /// n=5, base=15, label=15, fn(0) = 15. label + fn(0) = 30.
  static inline const unsigned int test3 = []() {
    fn_box bx = make_box(5u);
    return (bx.label + bx.fn(0u));
  }();
};

#endif // INCLUDED_FIX_IN_RECORD
