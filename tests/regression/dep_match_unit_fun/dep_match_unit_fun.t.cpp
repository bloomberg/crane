#include <dep_match_unit_fun.h>
#include <cassert>
#include <iostream>
int main() {
  auto r = DepMatchUnitFun::go;
  std::cout << "go = " << r << " (want 5)" << std::endl;
  assert(r == 5);
  return 0;
}
