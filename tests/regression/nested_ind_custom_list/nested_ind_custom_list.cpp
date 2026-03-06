#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nested_ind_custom_list.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<NestedIndCustomList::rose<unsigned int>>
NestedIndCustomList::leaf(const unsigned int n) {
  return rose<unsigned int>::ctor::Node_(
      std::move(n),
      list<std::shared_ptr<NestedIndCustomList::rose<unsigned int>>>::ctor::
          nil_());
}
