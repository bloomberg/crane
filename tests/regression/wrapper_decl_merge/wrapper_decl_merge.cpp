#include <wrapper_decl_merge.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

__attribute__((pure)) unsigned int
WrapperDeclMerge::A::Nat::fa(const unsigned int n) {
  return std::move(n);
}

__attribute__((pure)) unsigned int
WrapperDeclMerge::B::Nat::fb(const unsigned int n) {
  return (std::move(n) + 1);
}
