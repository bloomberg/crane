#include <id_method_value_unerased.h>

#include <cassert>

int main() {
  using M = IdMethodValueUnerased;
  assert(M::g == 2);
  return 0;
}
