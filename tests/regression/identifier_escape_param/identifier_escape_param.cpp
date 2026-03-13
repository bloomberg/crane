#include <identifier_escape_param.h>

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
IdentifierEscapeParam::id_from_param(const unsigned int double0) {
  return std::move(double0);
}

__attribute__((pure)) unsigned int
IdentifierEscapeParam::add_one_from_param(const unsigned int double0) {
  return (id_from_param(std::move(double0)) + 1);
}
