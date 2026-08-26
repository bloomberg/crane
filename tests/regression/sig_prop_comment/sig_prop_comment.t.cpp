#include <sig_prop_comment.h>
#include <cassert>
#include <iostream>
int main() {
  std::cout << "go = " << SigSubset::go << " (want 7)" << std::endl;
  assert(SigSubset::go == 7);
  return 0;
}
