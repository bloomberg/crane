#include "inductive_in_module.h"

uint64_t
InductiveInModule::Inner::color_to_nat(InductiveInModule::Inner::Color c) {
  switch (c) {
  case Color::RED: {
    return UINT64_C(0);
  }
  case Color::GREEN: {
    return UINT64_C(1);
  }
  case Color::BLUE: {
    return UINT64_C(2);
  }
  default:
    std::unreachable();
  }
}
