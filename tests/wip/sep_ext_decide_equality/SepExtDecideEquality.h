#ifndef INCLUDED_SEPEXTDECIDEEQUALITY
#define INCLUDED_SEPEXTDECIDEEQUALITY

#include <concepts>
#include <memory>
#include <optional>
#include <type_traits>
#include <variant>

#include "Datatypes.h"

namespace SepExtDecideEquality {

template <typename M>
concept Sigma = requires {
  typename M::Sigma;
  {
    M::Sigma_dec(std::declval<typename M::Sigma>(),
                 std::declval<typename M::Sigma>())
  } -> std::same_as<bool>;
};

template <Sigma Ty> struct DefsFn {
  struct Strings {
    using String = typename Datatypes::template List<typename Ty::Sigma>;

    static bool
    String_dec(const typename Datatypes::template List<typename Ty::Sigma> &l,
               const typename Datatypes::template List<typename Ty::Sigma> &x) {
      if (std::holds_alternative<
              typename Datatypes::template List<typename Ty::Sigma>::Nil>(
              l.v())) {
        if (std::holds_alternative<
                typename Datatypes::template List<typename Ty::Sigma>::Nil>(
                x.v())) {
          return true;
        } else {
          return false;
        }
      } else {
        const auto &[d_a0, d_a1] = std::get<
            typename Datatypes::template List<typename Ty::Sigma>::Cons>(l.v());
        if (std::holds_alternative<
                typename Datatypes::template List<typename Ty::Sigma>::Nil>(
                x.v())) {
          return false;
        } else {
          const auto &[d_a00, d_a10] = std::get<
              typename Datatypes::template List<typename Ty::Sigma>::Cons>(
              x.v());
          if (Ty::Sigma_dec(d_a0, d_a00)) {
            if (String_dec(*(d_a1), *(d_a10))) {
              return true;
            } else {
              return false;
            }
          } else {
            return false;
          }
        }
      }
    }
  };
};

} // namespace SepExtDecideEquality

#endif // INCLUDED_SEPEXTDECIDEEQUALITY
