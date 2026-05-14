#ifndef INCLUDED_SEPEXTDRIVERNOINCLUDE
#define INCLUDED_SEPEXTDRIVERNOINCLUDE

#include <memory>
#include <optional>
#include <type_traits>

#include "Datatypes.h"

namespace SepExtDriverNoInclude {

struct Content {
  static const Datatypes::Nat &x() {
    static const Datatypes::Nat v = Datatypes::Nat::s(Datatypes::Nat::s(
        Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
            Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                    Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                        Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                            Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                Datatypes::Nat::
                                    s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                        Datatypes::Nat::
                                            s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                Datatypes::Nat::
                                                    s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                        Datatypes::Nat::
                                                            s(Datatypes::Nat::s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                                Datatypes::Nat::
                                                                    s(Datatypes::Nat::s(Datatypes::Nat::s(
                                                                        Datatypes::Nat::
                                                                            o()))))))))))))))))))))))))))))))))))))))))));
    return v;
  }
};

} // namespace SepExtDriverNoInclude

#endif // INCLUDED_SEPEXTDRIVERNOINCLUDE
