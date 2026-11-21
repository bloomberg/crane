#include "prim_string_make_compare.h"

std::string PrimString::make(int64_t, char) {
  throw std::logic_error("unrealized axiom: Corelib.Strings.PrimString.make");
}

Comparison PrimString::compare(const std::string &, const std::string &) {
  throw std::logic_error("unrealized axiom: Corelib.Strings.PrimString.compare");
}
