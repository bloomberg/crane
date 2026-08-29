#include "module_inductive_same_name.h"

uint64_t ModuleInductiveSameName::Color_Mod::v(Color c) {
  switch (c) {
  case Color::R: {
    return UINT64_C(1);
  }
  case Color::G: {
    return UINT64_C(2);
  }
  default:
    std::unreachable();
  }
}

uint64_t ModuleInductiveSameName::run(uint64_t k) {
  return (Color_Mod::v(Color_Mod::Color::R) + k);
}
