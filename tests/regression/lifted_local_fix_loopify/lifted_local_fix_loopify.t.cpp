#include <lifted_local_fix_loopify.h>
#include <cstdint>
#include <iostream>

int main() {
  using L = List<uint64_t>;
  using LL = List<L>;
  // [[1; 2]; [3]; []]
  LL l = LL::cons(L::cons(1, L::cons(2, L::nil())),
                  LL::cons(L::cons(3, L::nil()), LL::cons(L::nil(), LL::nil())));
  uint64_t total = LiftedLocalFixLoopify::total_length(l);
  uint64_t weighted = LiftedLocalFixLoopify::weighted(l);
  std::cout << "total_length = " << total << std::endl;
  std::cout << "weighted = " << weighted << std::endl;
  if (total != 6 || weighted != 9) return 1;

  // Deep enough to overflow the stack unless both helpers are loops.
  const uint64_t n = 1000000;
  L big = L::nil();
  for (uint64_t i = 0; i < n; ++i) big = L::cons(1, std::move(big));
  LL deep = LL::cons(std::move(big), LL::nil());
  uint64_t deep_total = LiftedLocalFixLoopify::total_length(deep);
  uint64_t deep_weighted = LiftedLocalFixLoopify::weighted(deep);
  std::cout << "deep total_length = " << deep_total << std::endl;
  std::cout << "deep weighted = " << deep_weighted << std::endl;
  if (deep_total != n + 1 || deep_weighted != n + 1) return 1;
  return 0;
}
