#include "SepExtCrossFileString.h"

#include "Ascii.h"
#include "Datatypes.h"
#include "String_.h"

namespace SepExtCrossFileString {

String::String ShowNat::show(const Datatypes::Nat &n) {
  if (std::holds_alternative<typename Datatypes::Nat::O>(n.v())) {
    return String::String::string0(Ascii::Ascii::ascii0(false, false, false,
                                                        false, true, true,
                                                        false, false),
                                   String::String::emptystring());
  } else {
    const auto &[a0] = std::get<typename Datatypes::Nat::S>(n.v());
    return show(*a0).append(
        String::String::string0(Ascii::Ascii::ascii0(true, true, false, true,
                                                     false, true, false, false),
                                String::String::emptystring()));
  }
}

} // namespace SepExtCrossFileString
