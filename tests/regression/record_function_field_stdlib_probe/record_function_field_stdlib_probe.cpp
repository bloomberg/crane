#include "record_function_field_stdlib_probe.h"

Bool0 Datatypes::negb(Bool0 b) {
  switch (b) {
  case Bool0::TRUE_: {
    return Bool0::FALSE_;
  } break;
  case Bool0::FALSE_: {
    return Bool0::TRUE_;
  } break;
  default:
    std::unreachable();
  }
}
