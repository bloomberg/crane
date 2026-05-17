#include "record_function_field_stdlib_probe.h"

Bool0 Datatypes::negb(Bool0 b) {
  switch (b) {
  case Bool0::e_TRUE: {
    return Bool0::e_FALSE;
  }
  case Bool0::e_FALSE: {
    return Bool0::e_TRUE;
  }
  default:
    std::unreachable();
  }
}
