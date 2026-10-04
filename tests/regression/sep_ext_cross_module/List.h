#ifndef INCLUDED_LIST
#define INCLUDED_LIST

#include <type_traits>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace List {

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T1, F0 &, T1 &, T2 &>
T1 fold_left(F0 &&f, const Datatypes::List<T2> &l, T1 a0) {
  if (std::holds_alternative<typename Datatypes::List<T2>::Nil>(l.v())) {
    return a0;
  } else {
    const auto &[a1, a2] = std::get<typename Datatypes::List<T2>::Cons>(l.v());
    return fold_left<T1, T2>(f, *a2, f(std::move(a0), a1));
  }
}

} // namespace List

#endif // INCLUDED_LIST
