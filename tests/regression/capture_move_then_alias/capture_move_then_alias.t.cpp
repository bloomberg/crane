#include <capture_move_then_alias.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = CaptureMoveThenAlias::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 2);
  return 0;
}
