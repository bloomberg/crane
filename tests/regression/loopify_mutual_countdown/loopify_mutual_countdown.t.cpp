#include <loopify_mutual_countdown.h>

#include <cassert>
#include <iostream>

int main() {
  assert(LoopifyMutualCountdown::even_countdown(10u));
  assert(!LoopifyMutualCountdown::odd_countdown(10u));

  std::cout << "starting deep mutual countdown" << std::endl;
  bool result = LoopifyMutualCountdown::even_countdown(10000000u);
  std::cout << "finished deep mutual countdown" << std::endl;
  assert(result);
  return 0;
}
