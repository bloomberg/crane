#ifndef INCLUDED_NAT_ITER_FUNCTION_ACC
#define INCLUDED_NAT_ITER_FUNCTION_ACC

#include <functional>
#include <type_traits>
#include <utility>

/// Nat.iter is lowered to a for whose accumulator is declared auto from
/// the *initial* value.  When the iterated type is a function type the initial
/// value is a lambda, so the accumulator's deduced type is that one closure
/// type, and the assignment of the next iteration's std::function to it has
/// no viable overload.  The accumulator must be declared at the iteration's
/// type, not the seed's.
struct NatIterFunctionAcc {
  static inline const uint64_t run = []() {
    return [](uint64_t _crane_n, auto _crane_f, auto _crane_seed) {
      std::decay_t<decltype(_crane_f(std::move(_crane_seed)))> _crane_acc =
          std::move(_crane_seed);
      for (uint64_t _crane_i = 0; _crane_i < _crane_n; _crane_i++) {
        _crane_acc = _crane_f(std::move(_crane_acc));
      }
      return _crane_acc;
    }(
               UINT64_C(10),
               [](std::function<uint64_t(uint64_t)> f)
                   -> std::function<uint64_t(uint64_t)> {
                 return
                     [=](uint64_t x) mutable { return f((x + UINT64_C(1))); };
               },
               [](uint64_t x) { return x; })(UINT64_C(0));
  }();
};

#endif // INCLUDED_NAT_ITER_FUNCTION_ACC
