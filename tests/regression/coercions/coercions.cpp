#include <algorithm>
#include <any>
#include <cassert>
#include <coercions.h>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int Coercions::bool_to_nat(const bool b) {
  if (b) {
    return (0 + 1);
  } else {
    return 0;
  }
}

unsigned int Coercions::add_bool(const unsigned int n, const bool b) {
  return (n + bool_to_nat(b));
}

unsigned int
Coercions::double_wrapped(const std::shared_ptr<Coercions::Wrapper> &w) {
  return (w->unwrap + w->unwrap);
}

unsigned int
Coercions::add_boolbox(const unsigned int n,
                       const std::shared_ptr<Coercions::BoolBox> &bb) {
  return (n + bool_to_nat(bb->unbox));
}
