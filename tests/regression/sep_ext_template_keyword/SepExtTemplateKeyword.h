#ifndef INCLUDED_SEPEXTTEMPLATEKEYWORD
#define INCLUDED_SEPEXTTEMPLATEKEYWORD

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <variant>

#include "Datatypes.h"

namespace SepExtTemplateKeyword {

template <typename M>
concept RawSig = requires {
  typename M::elt;
  typename M::tree;
  requires(
      requires {
        { M::empty } -> std::convertible_to<typename M::tree>;
      } ||
      requires {
        { M::empty() } -> std::convertible_to<typename M::tree>;
      });
  {
    M::elements(std::declval<typename M::tree>())
  } -> std::same_as<Datatypes::List<typename M::elt>>;
};

template <RawSig Raw> struct MakeOps {
  static typename Datatypes::template List<typename Raw::elt>
  to_list(const typename Raw::tree _x0) {
    return Raw::elements(_x0);
  }

  constexpr static bool is_empty(const typename Raw::tree t) {
    auto &&_sv = Raw::elements(t);
    if (std::holds_alternative<
            typename Datatypes::template List<typename Raw::elt>::Nil>(
            _sv.v())) {
      return true;
    } else {
      return false;
    }
  }
};

} // namespace SepExtTemplateKeyword

#endif // INCLUDED_SEPEXTTEMPLATEKEYWORD
