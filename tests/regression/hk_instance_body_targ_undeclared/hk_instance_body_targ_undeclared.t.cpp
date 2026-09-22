#include "hk_instance_body_targ_undeclared.h"
#include <cassert>
#include <cstdio>

int main() {
  // Exercising the option instance is enough; the list instance is the
  // control and is here to keep both spellings in the same translation unit.
  assert(!HkInstanceBodyTargUndeclared::on_option(std::nullopt).has_value());
  printf("All hk_instance_body_targ_undeclared tests passed!\n");
  return 0;
}
