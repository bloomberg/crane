#include "module_inductive_same_name.h"

/// A submodule containing an inductive of the same name.  A C++ member may
/// not share its enclosing class's name, so the module is emitted as
/// struct Color_Mod holding enum class Color.
uint64_t ModuleInductiveSameName::Color_Mod::v(Color0 c) {
  switch (c) {
  case Color0::R: {
    return UINT64_C(1);
  }
  case Color0::G: {
    return UINT64_C(2);
  }
  default:
    std::unreachable();
  }
}

uint64_t ModuleInductiveSameName::run(uint64_t k) {
  return (Color_Mod::v(Color_Mod::Color0::R) + k);
}
