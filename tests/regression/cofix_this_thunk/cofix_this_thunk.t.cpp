#include <cofix_this_thunk.h>

#include <cassert>

int main() {
  // test1: smap (nats_from 0) S = [1, 2, 3, 4, ...]
  // take 4 -> [1, 2, 3, 4] -> sum = 10
  assert(Sseq<unsigned int>::test1() == 10u);

  // test2: smap_direct (nats_from 0) S = [1, 2, 3, 4, ...]
  // take 4 -> [1, 2, 3, 4] -> sum = 10
  assert(Sseq<unsigned int>::test2() == 10u);

  return 0;
}
