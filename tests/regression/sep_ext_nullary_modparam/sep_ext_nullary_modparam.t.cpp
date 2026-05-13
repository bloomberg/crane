// Regression: nullary module parameter definitions (I::zero, I::one)
// must be emitted with () in functor bodies.

#include "SepExtNullaryModparam.h"

#include <iostream>

namespace {
int testStatus = 0;

void aSsErT(bool condition, const char *message, int line) {
  if (condition) {
    std::cout << "Error " __FILE__ "(" << line << "): " << message
              << "    (failed)" << std::endl;
    if (0 <= testStatus && testStatus <= 100) {
      ++testStatus;
    }
  }
}
} // namespace

#define ASSERT(X) aSsErT(!(X), #X, __LINE__);

using NC = SepExtNullaryModparam::NatCounter;

int main() {
  ASSERT(NC::init() == 0u);
  ASSERT(NC::step(0u) == 1u);
  ASSERT(NC::step(5u) == 6u);
  ASSERT(NC::is_zero(0u) == true);
  ASSERT(NC::is_zero(1u) == false);

  return testStatus;
}
