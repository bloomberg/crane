#include <dep_match_unit_pair.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = DepMatchUnitPair::go;
  std::cout << "go = " << r << " (want 3)" << std::endl;
  assert(r == 3);
  return 0;
}
