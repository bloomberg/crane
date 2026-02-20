#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <nested_inductive.h>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

std::shared_ptr<NestedInductive::rose<unsigned int>>
NestedInductive::leaf(const unsigned int n) {
  return rose<unsigned int>::ctor::Node_(
      std::move(n),
      list<std::shared_ptr<NestedInductive::rose<unsigned int>>>::ctor::nil_());
}
