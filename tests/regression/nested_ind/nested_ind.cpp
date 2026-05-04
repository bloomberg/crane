#include "nested_ind.h"

NestedInd::rose<unsigned int> NestedInd::leaf(const unsigned int n) {
  return rose<unsigned int>::node(
      n, custom_list<NestedInd::rose<unsigned int>>::cnil());
}
