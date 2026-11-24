#include <loopify_nested_list_local_fix.h>

#include <cassert>
#include <iostream>

int main() {
  auto r = LoopifyNestedListLocalFix::result;
  std::cout << "result = " << r << std::endl;
  assert(r == 710);
  return 0;
}
