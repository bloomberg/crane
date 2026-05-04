#include "SepExtCrossModule.h"

#include <cassert>

int main() {
  // sum_list uses fold_left from List.h and List<T> from Datatypes.h
  auto empty = List<unsigned int>::nil();
  assert(sum_list(empty) == 0u);

  auto pair = make_pair_list(3u, 4u);
  assert(sum_list(pair) == 7u);

  auto single = List<unsigned int>::cons(10u, List<unsigned int>::nil());
  assert(sum_list(single) == 10u);

  return 0;
}
