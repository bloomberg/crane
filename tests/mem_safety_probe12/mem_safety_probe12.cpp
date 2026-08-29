#include "mem_safety_probe12.h"

MemSafetyProbe12::wrap MemSafetyProbe12::pack_fn_let(uint64_t base) {
  std::function<uint64_t(uint64_t)> f = [=](uint64_t x) mutable {
    return (x + base);
  };
  return wrap::wrap0(f);
}

MemSafetyProbe12::wrap MemSafetyProbe12::pack_fn_direct(uint64_t base) {
  return wrap::wrap0(std::function<uint64_t(uint64_t)>(
      [=](uint64_t x) mutable { return (x + base); }));
}
