#include "record_module_function_qualifier.h"

Nat RecordModuleFunctionQualifier::Bag::classify(
    RecordModuleFunctionQualifier::Bag::Kind k) {
  switch (k) {
  case Kind::SMALL: {
    return Nat::s(Nat::o());
  }
  case Kind::LARGE: {
    return Nat::s(Nat::s(Nat::o()));
  }
  default:
    std::unreachable();
  }
}
