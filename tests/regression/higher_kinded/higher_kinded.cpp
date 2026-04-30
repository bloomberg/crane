#include <higher_kinded.h>

unsigned int HigherKinded::tree_sum(const HigherKinded::Tree<unsigned int> &t) {
  return tree_fold<unsigned int, unsigned int>(
      [](unsigned int x) { return x; },
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      t);
}
