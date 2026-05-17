#include "todo_generalizable_approx.h"

unsigned int TodoGeneralizableApprox::double_then_add(const unsigned int x) {
  unsigned int y = (x + x);
  return (y + 1u);
}
