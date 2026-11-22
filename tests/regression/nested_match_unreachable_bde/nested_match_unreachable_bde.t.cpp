#include <nested_match_unreachable_bde.h>

#include <iostream>

int main() {
  bool a = NestedMatchUnreachableBde::t1;
  bool b = NestedMatchUnreachableBde::t2;
  bool c = NestedMatchUnreachableBde::t3;
  std::cout << a << " " << b << " " << c << std::endl;
  return (a && !b && c) ? 0 : 1;
}
