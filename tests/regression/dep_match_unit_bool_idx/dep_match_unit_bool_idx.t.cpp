#include <dep_match_unit_bool_idx.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = DepMatchUnitBoolIdx::go;
  std::cout << "go = " << r << " (want 5)" << std::endl;
  assert(r == 5);
  return 0;
}
