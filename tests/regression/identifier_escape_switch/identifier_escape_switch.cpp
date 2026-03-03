#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <identifier_escape_switch.h>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

unsigned int IdentifierEscapeSwitch::id_from_param(const unsigned int switch0) {
  return std::move(switch0);
}

unsigned int
IdentifierEscapeSwitch::add_one_from_param(const unsigned int switch0) {
  return (id_from_param(std::move(switch0)) + 1);
}
