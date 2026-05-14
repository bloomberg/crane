#include "SepExtCrossModule.h"

#include <cassert>

int main() {
  // sum_list uses fold_left from List.h and List<T> from Datatypes.h
  auto empty = Datatypes::List<unsigned int>::nil();
  assert(SepExtCrossModule::sum_list(empty) == 0u);

  auto pair = SepExtCrossModule::make_pair_list(3u, 4u);
  assert(SepExtCrossModule::sum_list(pair) == 7u);

  auto single = Datatypes::List<unsigned int>::cons(10u, Datatypes::List<unsigned int>::nil());
  assert(SepExtCrossModule::sum_list(single) == 10u);

  return 0;
}
