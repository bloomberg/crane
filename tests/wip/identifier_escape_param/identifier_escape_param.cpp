#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <identifier_escape_param.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int IdentifierEscapeParam::id_from_param(const unsigned int double) {
  return std::move(double);
}

unsigned int
IdentifierEscapeParam::add_one_from_param(const unsigned int double) {
  return (id_from_param(std::move(double)) + 1);
}
