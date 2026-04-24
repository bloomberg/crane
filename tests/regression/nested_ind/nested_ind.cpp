#include <nested_ind.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) NestedInd::rose<unsigned int>
NestedInd::leaf(unsigned int n) {
  return rose<unsigned int>::node(
      n, custom_list<NestedInd::rose<unsigned int>>::cnil());
}
