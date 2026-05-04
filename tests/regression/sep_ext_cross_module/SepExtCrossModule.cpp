#include "SepExtCrossModule.h"

#include "Datatypes.h"
#include "List.h"

unsigned int sum_list(const List<unsigned int> &l) {
  return fold_left<unsigned int, unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      l, 0u);
}

List<unsigned int> make_pair_list(const unsigned int n, const unsigned int m) {
  return List<unsigned int>::cons(
      n, List<unsigned int>::cons(m, List<unsigned int>::nil()));
}
