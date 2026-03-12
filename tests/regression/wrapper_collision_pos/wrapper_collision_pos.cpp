#include <wrapper_collision_pos.h>

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

unsigned int WrapperCollisionPos::Left::Pos::id_left(const unsigned int n) {
  return std::move(n);
}

unsigned int WrapperCollisionPos::Right::Pos::inc_right(const unsigned int n) {
  return (std::move(n) + 1);
}
