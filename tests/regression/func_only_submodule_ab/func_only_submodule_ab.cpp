#include "func_only_submodule_ab.h"

uint64_t FuncOnlySubmoduleAb::Root::A::inc(uint64_t n) { return (n + 1); }

uint64_t FuncOnlySubmoduleAb::Root::B::dec(uint64_t x0_) {
  return (x0_ ? x0_ - 1 : x0_);
}
