#include <dep_match_unit_option.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = DepMatchUnitOption::go;
  std::cout << "go = " << r << " (want 4)" << std::endl;
  assert(r == 4);
  return 0;
}
