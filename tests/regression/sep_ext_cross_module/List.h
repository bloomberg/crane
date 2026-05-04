#ifndef INCLUDED_LIST
#define INCLUDED_LIST

#include <memory>
#include <optional>
#include <type_traits>
#include <variant>

#include "Datatypes.h"

namespace List {

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T1, F0 &, T1 &, T2 &>
T1 fold_left(F0 &&f, const Datatypes::List<T2> &l, const T1 a0) {
  if (std::holds_alternative<typename Datatypes::List<T2>::Nil>(l.v())) {
    return a0;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename Datatypes::List<T2>::Cons>(l.v());
    return fold_left<T1, T2>(f, *(d_a1), f(a0, d_a0));
  }
}

} // namespace List

#endif // INCLUDED_LIST
