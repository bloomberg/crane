#include "module_alias_shadows_global.h"

uint64_t dbl(uint64_t n) { return n + n; }

/// Two levels down, naming the file-scope definitions, which the members
/// of this module and of the enclosing one both hide.
uint64_t ModuleAliasShadowsGlobal::R::dbl(uint64_t x0_) { return ::dbl(x0_); }

uint64_t ModuleAliasShadowsGlobal::dbl(uint64_t x0_) { return ::dbl(x0_); }

/// A definition of another file, which a collision wrapper holds.
bool ModuleAliasShadowsGlobal::even(uint64_t x0_) { return Nat::even(x0_); }

/// Names the members of the enclosing module, which its own hide.
uint64_t ModuleAliasShadowsGlobal::Q::dbl(uint64_t n) {
  return ModuleAliasShadowsGlobal::dbl(ModuleAliasShadowsGlobal::dbl(n));
}

bool Nat::even(uint64_t n) {
  if (n <= 0) {
    return true;
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return false;
    } else {
      uint64_t n_ = n0 - 1;
      return Nat::even(n_);
    }
  }
}
