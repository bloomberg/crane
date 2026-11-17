// A loopified function handing its loop a continuation that takes the old
// one by move: the closure must move the loop variable, not the parameter the
// loop has already moved from.
#include "loopify_capture_move_renamed.h"

#include <cassert>
#include <iostream>

int main() {
  using M = LoopifyCaptureMoveRenamed;
  List<uint64_t> l = List<uint64_t>::nil();
  for (uint64_t i = 1000; i > 0; --i) l = List<uint64_t>::cons(i, l);
  assert(M::count_evens(List<uint64_t>::nil()) == 0);
  assert(M::count_evens(l) == 500);
  assert(M::count_odds(l) == 500);
  assert(M::count_evens(List<uint64_t>::cons(2, List<uint64_t>::cons(3, List<uint64_t>::cons(4, List<uint64_t>::nil())))) == 2);
  std::cout << "loopify_capture_move_renamed: count_evens(1..1000)=" << M::count_evens(l) << " PASSED" << std::endl;
  return 0;
}
