#include "func_only_submodule_ab.h"

uint64_t FuncOnlySubmoduleAb::Root::A::inc(uint64_t n) { return (n + 1); }

uint64_t FuncOnlySubmoduleAb::Root::B::dec(uint64_t _x0) {
  return (_x0 ? _x0 - 1 : _x0);
}
