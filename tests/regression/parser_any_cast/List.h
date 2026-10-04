#ifndef INCLUDED_LIST
#define INCLUDED_LIST

#include "crane_fn.h"
#include <type_traits>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace List {

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T1, F0 &, T1 &, T2 &>
T1 fold_left(F0 &&f, const Datatypes::List<T2> &l, T1 a0) {
  T1 _loop_a0 = std::move(a0);
  const Datatypes::List<T2> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename Datatypes::List<T2>::Nil>(
            _loop_l->v())) {
      return _loop_a0;
    } else {
      const auto &[a1, a2] =
          std::get<typename Datatypes::List<T2>::Cons>(_loop_l->v());
      _loop_a0 = f(std::move(_loop_a0), a1);
      _loop_l = crane_raw(a2);
    }
  }
}

} // namespace List

#endif // INCLUDED_LIST
