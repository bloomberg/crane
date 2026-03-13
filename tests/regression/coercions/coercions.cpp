#include <coercions.h>

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

__attribute__((pure)) unsigned int Coercions::bool_to_nat(const bool b) {
  if (b) {
    return 1u;
  } else {
    return 0u;
  }
}

__attribute__((pure)) unsigned int Coercions::add_bool(const unsigned int n,
                                                       const bool b) {
  return (n + bool_to_nat(b));
}

__attribute__((pure)) unsigned int
Coercions::double_wrapped(const std::shared_ptr<Coercions::Wrapper> &w) {
  return (w->unwrap + w->unwrap);
}

__attribute__((pure)) unsigned int
Coercions::add_boolbox(const unsigned int n,
                       const std::shared_ptr<Coercions::BoolBox> &bb) {
  return (n + bool_to_nat(bb->unbox));
}
