#include "shared_dep_two_targets.h"

Col flip(Col c) {
  switch (c) {
  case Col::RED: {
    return Col::GREEN;
  }
  case Col::GREEN: {
    return Col::RED;
  }
  default:
    std::unreachable();
  }
}
