#ifndef INCLUDED_SEPEXTENUMASVALUE
#define INCLUDED_SEPEXTENUMASVALUE

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

#include "Datatypes.h"

namespace SepExtEnumAsValue {

enum class Color { e_RED, e_GREEN, e_BLUE };
template <typename M>
concept ColorParam = requires {
  requires(
      requires {
        { M::default_ } -> std::convertible_to<Color>;
      } ||
      requires {
        { M::default_() } -> std::convertible_to<Color>;
      });
};

template <ColorParam P> struct UseColor {
  static const Color &my_default() {
    static const Color v = P::default_;
    return v;
  }

  static const typename Datatypes::template List<Color> &color_list() {
    static const typename Datatypes::template List<Color> v =
        Datatypes::template List<Color>::cons(
            Color::e_RED,
            Datatypes::template List<Color>::cons(
                Color::e_GREEN,
                Datatypes::template List<Color>::cons(
                    Color::e_BLUE, Datatypes::template List<Color>::nil())));
    return v;
  }

  constexpr static bool is_red(const Color c) {
    switch (c) {
    case Color::e_RED: {
      return true;
    }
    default: {
      return false;
    }
    }
  }
};

} // namespace SepExtEnumAsValue

#endif // INCLUDED_SEPEXTENUMASVALUE
