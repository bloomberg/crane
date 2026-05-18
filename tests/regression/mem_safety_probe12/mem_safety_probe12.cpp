#include "mem_safety_probe12.h"

/// TEST 3: Pack a LET-BOUND closure.
/// let f := fun x => x + base in Wrap (nat -> nat) f
/// This should work because f has type std::function<...>
/// by the time it's passed to Wrap.
MemSafetyProbe12::wrap MemSafetyProbe12::pack_fn_let(uint64_t base) {
  std::function<uint64_t(uint64_t)> f = [=](uint64_t x) mutable {
    return (x + base);
  };
  return wrap::wrap0(f);
}

/// TEST 4: Pack a DIRECT lambda (no let-binding).
/// Wrap (nat -> nat) (fun x => x + base)
/// BUG: The raw lambda type is stored in std::any,
/// but unwrap tries any_cast<std::function<...>>.
MemSafetyProbe12::wrap MemSafetyProbe12::pack_fn_direct(uint64_t base) {
  return wrap::wrap0(std::function<uint64_t(uint64_t)>(
      [=](uint64_t x) mutable { return (x + base); }));
}
