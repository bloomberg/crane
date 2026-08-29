#include "typeclass_function_field_probe.h"

Bool0 Datatypes::negb(Bool0 b) {
  switch (b) {
  case Bool0::TRUE_: {
    return Bool0::FALSE_;
  }
  case Bool0::FALSE_: {
    return Bool0::TRUE_;
  }
  default:
    std::unreachable();
  }
}
