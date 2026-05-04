#include "SetA.h"
#include "SetB.h"

#include <cassert>

int main() {
  // Both SetA and SetB define a function called 'make'.
  // With namespaces they are distinct.
  assert(SetA::make(3u) == 4u); // 3 + 1
  assert(SetB::make(3u) == 6u); // 3 * 2

  // Both can be called together without collision
  assert(SetA::make(5u) + SetB::make(5u) == 6u + 10u);

  return 0;
}
