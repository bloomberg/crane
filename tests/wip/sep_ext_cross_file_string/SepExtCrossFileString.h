#ifndef INCLUDED_SEPEXTCROSSFILESTRING
#define INCLUDED_SEPEXTCROSSFILESTRING

#include <memory>
#include <optional>
#include <type_traits>
#include <variant>

#include "Ascii.h"
#include "Datatypes.h"
#include "String_.h"

namespace SepExtCrossFileString {

struct ShowNat {
  using t = Datatypes::Nat;
  static String::String show(const Datatypes::Nat &n);
};

} // namespace SepExtCrossFileString

#endif // INCLUDED_SEPEXTCROSSFILESTRING
