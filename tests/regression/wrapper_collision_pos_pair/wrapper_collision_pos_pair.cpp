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
#include <wrapper_collision_pos_pair.h>

unsigned int WrapperCollisionPosPair::Left::Pos::f(const unsigned int n) {
  return std::move(n);
}

unsigned int WrapperCollisionPosPair::Right::Pos::g(const unsigned int n) {
  return (std::move(n) + 1);
}
