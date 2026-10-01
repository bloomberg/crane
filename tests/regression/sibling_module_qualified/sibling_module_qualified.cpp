#include "sibling_module_qualified.h"

Ev::Color SiblingModuleQualified::flip(Ev::Color c) {
  switch (c) {
  case Ev::Color::RED: {
    return Ev::Color::GREEN;
  }
  case Ev::Color::GREEN: {
    return Ev::Color::RED;
  }
  default:
    std::unreachable();
  }
}

Nat SiblingModuleQualified::count(Ev::Color c, Nat n) {
  switch (flip(c)) {
  case Ev::Color::RED: {
    return n;
  }
  case Ev::Color::GREEN: {
    return Nat::s(std::move(n));
  }
  default:
    std::unreachable();
  }
}
