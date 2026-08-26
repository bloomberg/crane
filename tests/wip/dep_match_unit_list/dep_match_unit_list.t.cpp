#include <dep_match_unit_list.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = DepMatchUnitList::go;
  std::cout << "go = " << r << " (want 1)" << std::endl;
  assert(r == 1);
  return 0;
}
