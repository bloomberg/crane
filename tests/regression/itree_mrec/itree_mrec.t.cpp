#include <itree_mrec.h>

#include <cassert>
#include <iostream>

int main() {
  // sum_to 4 = 4 + 3 + 2 + 1 + 0, computed by mutual recursion through mrec.
  assert(ItreeMrec::is_ten);
  std::cout << "itree_mrec: ok" << std::endl;
  return 0;
}
