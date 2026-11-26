#include <sig_fn_match_join.h>

#include <cassert>
#include <iostream>

int main() {
  std::cout << "result = " << SigFnMatchJoin::result << std::endl;
  assert(SigFnMatchJoin::result == 1);
  return 0;
}
