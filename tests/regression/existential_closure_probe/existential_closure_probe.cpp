#include "existential_closure_probe.h"

/// Pack a closure into a type-erased wrapper.
ExistentialClosureProbe::wrap ExistentialClosureProbe::pack_fn(uint64_t base) {
  return wrap::wrap0(std::function<uint64_t(uint64_t)>(
      [=](uint64_t x) mutable { return (x + base); }));
}

/// Unpack and apply.
uint64_t
ExistentialClosureProbe::apply_packed(const ExistentialClosureProbe::wrap &_x0,
                                      uint64_t _x1) {
  return unwrap<std::function<uint64_t(uint64_t)>>(_x0)(_x1);
}

/// Store a closure that captures another closure.
ExistentialClosureProbe::wrap
ExistentialClosureProbe::pack_composed(uint64_t a, uint64_t b) {
  std::function<uint64_t(uint64_t)> f = [=](uint64_t x) mutable {
    return (x + a);
  };
  std::function<uint64_t(uint64_t)> g = [=](uint64_t x) mutable {
    return (f(x) * b);
  };
  return wrap::wrap0(g);
}
