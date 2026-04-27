#include <topological_sort.h>

__attribute__((pure)) List<unsigned int> ListDef::seq(unsigned int start,
                                                      const unsigned int &len) {
  if (len <= 0) {
    return List<unsigned int>::nil();
  } else {
    unsigned int len0 = len - 1;
    return List<unsigned int>::cons(start, ListDef::seq((start + 1), len0));
  }
}
