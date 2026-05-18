// Regression: sigT with dependent second component must use std::any
// for the second template parameter when the concrete type varies
// across constructor branches.

#include "sep_ext_sigt_dependent.h"

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

int main() {
  // pack_a wraps TagA with unit (monostate)
  auto pa = Packer::pack_a;
  ASSERT(Packer::get_tag(pa) == Tag::TAGA);

  // pack_b wraps TagB with a nat
  auto pb = Packer::pack_b(42u);
  ASSERT(Packer::get_tag(pb) == Tag::TAGB);

  // pack_c wraps TagC with a bool
  auto pc = Packer::pack_c(true);
  ASSERT(Packer::get_tag(pc) == Tag::TAGC);

  return testStatus;
}
