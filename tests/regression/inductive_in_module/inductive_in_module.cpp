#include "inductive_in_module.h"

unsigned int
InductiveInModule::Inner::color_to_nat(InductiveInModule::Inner::Color c) {
  switch (c) {
  case Color::RED: {
    return 0u;
  }
  case Color::GREEN: {
    return 1u;
  }
  case Color::BLUE: {
    return 2u;
  }
  default:
    std::unreachable();
  }
}
