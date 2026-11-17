#include "module_type_enum_in_parameter.h"

ModuleTypeEnumInParameter::Impl::t
ModuleTypeEnumInParameter::Impl::paint(ModuleTypeEnumInParameter::Impl::Color c,
                                       uint64_t n) {
  switch (c) {
  case Color::RED: {
    return (n + UINT64_C(1));
  }
  case Color::GREEN: {
    return (n + UINT64_C(2));
  }
  case Color::BLUE: {
    return (n + UINT64_C(3));
  }
  default:
    std::unreachable();
  }
}
