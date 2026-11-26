#include <local_fix_inlined_fn_join.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << LocalFixInlinedFnJoin::result << std::endl;
  assert(LocalFixInlinedFnJoin::result == 2);
  return 0;
}
