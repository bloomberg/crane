#ifndef INCLUDED_SEPEXTSIGTANY
#define INCLUDED_SEPEXTSIGTANY

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
#include <variant>

#include "Specif.h"

namespace SepExtSigtAny {

template <typename M>
concept S = requires { typename M::t; };

template <S X> struct MyMod {
  static const typename Specif::template SigT<std::any, std::any> &ex() {
    static const typename Specif::template SigT<std::any, std::any> v =
        Specif::template SigT<std::any, std::any>::existt(std::any{},
                                                          std::monostate{});
    return v;
  }
};

} // namespace SepExtSigtAny

#endif // INCLUDED_SEPEXTSIGTANY
