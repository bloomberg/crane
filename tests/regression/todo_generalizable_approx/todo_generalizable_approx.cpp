#include "todo_generalizable_approx.h"

uint64_t TodoGeneralizableApprox::double_then_add(uint64_t x) {
  uint64_t y = (x + x);
  return (y + UINT64_C(1));
}
