#ifndef INCLUDED_LISTDEF
#define INCLUDED_LISTDEF

#include "crane_fn.h"
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace ListDef {

template <typename T1, typename T2, typename F0>
  requires std::is_invocable_r_v<T2, F0 &, const T1 &>
Datatypes::List<T2> map(F0 &&f, const Datatypes::List<T1> &l) {
  std::optional<Datatypes::List<T2>> _root{};
  std::shared_ptr<Datatypes::List<T2>> *_write = nullptr;
  const Datatypes::List<T1> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<typename Datatypes::List<T1>::Nil>(
            _loop_l->v())) {
      auto _value = Datatypes::template List<T2>::nil();
      (_write ? *(*_write =
                      std::make_shared<Datatypes::List<T2>>(std::move(_value)))
              : _root.emplace(std::move(_value)));
      break;
    } else {
      const auto &[a0, a1] =
          std::get<typename Datatypes::List<T1>::Cons>(_loop_l->v());
      auto _cell = typename Datatypes::template List<T2>::Cons(f(a0), nullptr);
      Datatypes::List<T2> &_node =
          (_write ? *(*_write = std::make_shared<Datatypes::List<T2>>(
                          std::move(_cell)))
                  : _root.emplace(std::move(_cell)));
      _write =
          &std::get<typename Datatypes::template List<T2>::Cons>(_node.v_mut())
               .l;
      _loop_l = crane_raw(a1);
      continue;
    }
  }
  return std::move(*_root);
}

} // namespace ListDef

#endif // INCLUDED_LISTDEF
