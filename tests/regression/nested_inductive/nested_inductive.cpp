#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <nested_inductive.h>
#include <stdexcept>
#include <string>
#include <variant>

std::shared_ptr<NestedInductive::rose<unsigned int>>
NestedInductive::leaf(const unsigned int n) {
  return rose<unsigned int>::ctor::Node_(
      n,
      list<std::shared_ptr<NestedInductive::rose<unsigned int>>>::ctor::nil_());
}
