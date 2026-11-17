#include "alias_home_constructor_field.h"

Nat AliasHomeConstructorField::Inner::tag(
    const AliasHomeConstructorField::Inner::box &b) {
  if (std::holds_alternative<
          typename AliasHomeConstructorField::Inner::box::Mine>(b.v())) {
    return Nat::o();
  } else {
    return Nat::s(Nat::o());
  }
}
