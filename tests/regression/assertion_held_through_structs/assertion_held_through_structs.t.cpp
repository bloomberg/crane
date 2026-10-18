#include <assertion_held_through_structs.h>
#include <cassert>
#include <iostream>

int main() {
  std::cout << AssertionHeldThroughStructs::Mid::run << std::endl;
  assert(AssertionHeldThroughStructs::Mid::run == 9);
  return 0;
}
