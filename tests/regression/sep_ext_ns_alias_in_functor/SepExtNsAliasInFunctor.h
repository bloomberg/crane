#ifndef INCLUDED_SEPEXTNSALIASINFUNCTOR
#define INCLUDED_SEPEXTNSALIASINFUNCTOR

#include <memory>
#include <optional>
#include <type_traits>

#include "Datatypes.h"

namespace SepExtNsAliasInFunctor {

template <typename M>
concept S = requires { typename M::t; };

struct Inner {
  static inline const Datatypes::Nat val_x = Datatypes::Nat::o();
};

template <S X> struct MyFunctor {
  using R = Inner;

  static const typename Datatypes::Nat &use_r() {
    static const typename Datatypes::Nat v = R::val_x;
    return v;
  }
};

} // namespace SepExtNsAliasInFunctor

#endif // INCLUDED_SEPEXTNSALIASINFUNCTOR
