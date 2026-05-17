#ifndef INCLUDED_UNDECLTVARTEMPLATE
#define INCLUDED_UNDECLTVARTEMPLATE

#include <variant>

#include "Datatypes.h"

namespace UndeclTvarTemplate {

template <typename M>
concept Ty = requires { typename M::Sigma; };

template <Ty X> struct Make {
  using String = typename Datatypes::template List<typename X::Sigma>;

  template <typename T1>
  static bool
  String_dec(const typename Datatypes::template List<T1> &l,
             const typename Datatypes::template List<typename X::Sigma> &) {
    if (std::holds_alternative<typename Datatypes::template List<T1>::Nil>(
            l.v())) {
      return true;
    } else {
      return false;
    }
  }
};

} // namespace UndeclTvarTemplate

#endif // INCLUDED_UNDECLTVARTEMPLATE
