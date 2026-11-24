#include <local_fix_fn_result_join.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = LocalFixFnResultJoin::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 6);
  return 0;
}
