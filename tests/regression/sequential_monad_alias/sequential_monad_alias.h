#pragma once

#include <iostream>
#include <string>
#include <variant>

struct SequentialMonadAlias {
  static void aliased();
  static void direct();
  static void both();
  static void twice(const std::monostate &m);
};
