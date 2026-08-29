#include "typeclass_enum_eq.h"

bool TypeclassEnumEq::color_eqb(TypeclassEnumEq::Color x,
                                TypeclassEnumEq::Color y) {
  switch (x) {
  case Color::RED: {
    switch (y) {
    case Color::RED: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Color::GREEN: {
    switch (y) {
    case Color::GREEN: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  case Color::BLUE: {
    switch (y) {
    case Color::BLUE: {
      return true;
    }
    default: {
      return false;
    }
    }
    break;
  }
  default:
    std::unreachable();
  }
}
