#include <nested_ind.h>

__attribute__((pure)) NestedInd::rose<unsigned int>
NestedInd::leaf(unsigned int n) {
  return rose<unsigned int>::node(
      n, custom_list<NestedInd::rose<unsigned int>>::cnil());
}
