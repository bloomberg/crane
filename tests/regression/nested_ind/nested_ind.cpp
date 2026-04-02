#include <nested_ind.h>

#include <algorithm>
#include <functional>
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

std::shared_ptr<NestedInd::rose<unsigned int>>
NestedInd::leaf(const unsigned int n) {
  return rose<unsigned int>::node(
      n, custom_list<std::shared_ptr<NestedInd::rose<unsigned int>>>::cnil());
}
