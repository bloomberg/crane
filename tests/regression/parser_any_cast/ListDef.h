#ifndef INCLUDED_LISTDEF
#define INCLUDED_LISTDEF

#include "crane_fn.h"
#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace ListDef {

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, T1 &>
Datatypes::List<T2> map(F0 &&f, const Datatypes::List<T1> &l) {
  std::shared_ptr<Datatypes::List<T2>> _head{};
  std::shared_ptr<Datatypes::List<T2>> *_write = &_head;
  const Datatypes::List<T1> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename Datatypes::List<T1>::Nil>(
            _loop_l->v())) {
      *_write = std::make_shared<Datatypes::List<T2>>(
          Datatypes::template List<T2>::nil());
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename Datatypes::List<T1>::Cons>(_loop_l->v());
      auto _cell = std::make_shared<Datatypes::template List<T2>>(
          typename Datatypes::template List<T2>::Cons(f(a0), nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename Datatypes::template List<T2>::Cons>(
                    (*_write)->v_mut())
                    .l;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_head);
}

} // namespace ListDef

#endif // INCLUDED_LISTDEF
