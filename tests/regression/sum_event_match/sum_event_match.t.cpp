#include "sum_event_match.h"
#include <cassert>

int main() {
  auto t = SumEventMatch::use();
  assert(t != nullptr);
  return 0;
}
