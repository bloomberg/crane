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
#include <wrapper_collision_token.h>

unsigned int WrapperCollisionToken::Left::Token::id_left(const unsigned int n) {
  return std::move(n);
}

unsigned int
WrapperCollisionToken::Right::Token::inc_right(const unsigned int n) {
  return (std::move(n) + 1);
}
