#include <algorithm>
#include <any>
#include <functional>
#include <iostream>
#include <memory>
#include <stdexcept>
#include <string>
#include <unit_type.h>
#include <variant>

std::shared_ptr<Unit::unit> UnitType::return_unit(const unsigned int _x) {
  return Unit::unit::ctor::tt_();
}

unsigned int UnitType::take_unit(const std::shared_ptr<Unit::unit> &_x) {
  return 5u;
}

unsigned int UnitType::match_unit(const std::shared_ptr<Unit::unit> &u) {
  return std::visit(
      Overloaded{[](const typename Unit::unit::tt _args) -> unsigned int {
        return 7u;
      }},
      u->v());
}

std::shared_ptr<Unit::unit>
UnitType::unit_to_unit(const std::shared_ptr<Unit::unit> &u) {
  return u;
}
