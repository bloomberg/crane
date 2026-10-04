#ifndef INCLUDED_LISTDEF
#define INCLUDED_LISTDEF

#include <type_traits>
#include <variant>

#include "Datatypes.h"

namespace ListDef {

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, const T1 &>
Datatypes::List<T2> map(F0 &&f, const Datatypes::List<T1> &l) {
  if (std::holds_alternative<typename Datatypes::List<T1>::Nil>(l.v())) {
    return Datatypes::template List<T2>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename Datatypes::List<T1>::Cons>(l.v());
    return Datatypes::template List<T2>::cons(f(a0), map<T1, T2>(f, *a1));
  }
}

} // namespace ListDef

#endif // INCLUDED_LISTDEF
