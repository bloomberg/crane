#include <type_app.h>

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

std::shared_ptr<TypeApp::list<unsigned int>>
TypeApp::map_succ(const std::shared_ptr<TypeApp::list<unsigned int>> &_x0) {
  return map<unsigned int, unsigned int>(
      [](unsigned int x) { return (x + 1u); }, _x0);
}

__attribute__((pure)) unsigned int
TypeApp::NatMonoid::append(const unsigned int _x0, const unsigned int _x1) {
  return (_x0 + _x1);
}
