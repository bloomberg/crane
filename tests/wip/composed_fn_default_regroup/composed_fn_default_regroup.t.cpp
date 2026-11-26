#include <composed_fn_default_regroup.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << ComposedFnDefaultRegroup::result << std::endl;
  assert(ComposedFnDefaultRegroup::result == 11);
  return 0;
}
