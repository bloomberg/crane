#include "existential_closure_probe.h"

/// Pack a closure into a type-erased wrapper.
ExistentialClosureProbe::wrap ExistentialClosureProbe::pack_fn(uint64_t base) {
  return wrap::wrap0(
      crane::fn<uint64_t(uint64_t)>([=](uint64_t x) { return (x + base); }));
}

/// Unpack and apply.
uint64_t
ExistentialClosureProbe::apply_packed(const ExistentialClosureProbe::wrap &x0_,
                                      uint64_t x1_) {
  return unwrap<crane::fn<uint64_t(uint64_t)>>(x0_)(x1_);
}

/// Store a closure that captures another closure.
ExistentialClosureProbe::wrap
ExistentialClosureProbe::pack_composed(uint64_t a, uint64_t b) {
  crane::fn<uint64_t(uint64_t)> f = [=](uint64_t x) { return (x + a); };
  crane::fn<uint64_t(uint64_t)> g = [=, f = std::move(f)](uint64_t x) {
    return (f(x) * b);
  };
  return wrap::wrap0(std::move(g));
}
