#ifndef INCLUDED_SEPEXTSIGTANY
#define INCLUDED_SEPEXTSIGTANY

#include "obj.h"
#include <any>
#include <variant>

#include "Specif.h"

namespace SepExtSigtAny {

template <typename M>
concept S = requires { typename M::t; };

template <S X> struct MyMod {
  static const typename Specif::template SigT<crane::obj, crane::obj> &ex() {
    static const typename Specif::template SigT<crane::obj, crane::obj> v =
        Specif::template SigT<crane::obj, crane::obj>::existt(crane::obj(),
                                                              std::monostate{});
    return v;
  }
};

} // namespace SepExtSigtAny

#endif // INCLUDED_SEPEXTSIGTANY
