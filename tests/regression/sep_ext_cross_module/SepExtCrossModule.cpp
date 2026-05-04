#include "SepExtCrossModule.h"

#include "Datatypes.h"
#include "List.h"

namespace SepExtCrossModule {

unsigned int sum_list(const Datatypes::List<unsigned int> &l) {
  return List::template fold_left<unsigned int, unsigned int>(
      [](unsigned int _x0, unsigned int _x1) -> unsigned int {
        return (_x0 + _x1);
      },
      l, 0u);
}

Datatypes::List<unsigned int> make_pair_list(const unsigned int n,
                                             const unsigned int m) {
  return Datatypes::template List<unsigned int>::cons(
      n, Datatypes::template List<unsigned int>::cons(
             m, Datatypes::template List<unsigned int>::nil()));
}

} // namespace SepExtCrossModule
