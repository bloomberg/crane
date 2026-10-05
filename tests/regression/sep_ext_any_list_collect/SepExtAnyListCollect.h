#ifndef INCLUDED_SEPEXTANYLISTCOLLECT
#define INCLUDED_SEPEXTANYLISTCOLLECT

#include "crane_fn.h"
#include "obj.h"
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace SepExtAnyListCollect {

using tuple = crane::obj;
template <typename M>
concept SymTypes = requires {
  typename M::sym;
  typename M::sym_semty;
};

template <SymTypes Ty> struct ListCollect {
  using symbols_semty = tuple;

  static typename Datatypes::template List<symbols_semty>
  collect(typename Ty::sym,
          const typename Datatypes::template List<typename Ty::sym> &,
          const typename Datatypes::Nat &n, symbols_semty default0) {
    {
      const typename Datatypes::Nat &_lc1_n0 = n;
      typename Datatypes::template List<symbols_semty> _lc1_acc =
          Datatypes::template List<symbols_semty>::nil();
      typename Datatypes::template List<symbols_semty> _lc1_loop_acc =
          std::move(_lc1_acc);
      const typename Datatypes::Nat *_lc1_loop_n0 = &_lc1_n0;
      while (true) {
        if (std::holds_alternative<typename Datatypes::Nat::O>(
                _lc1_loop_n0->v())) {
          return _lc1_loop_acc;
        } else {
          const auto &[a0] =
              std::get<typename Datatypes::Nat::S>(_lc1_loop_n0->v());
          _lc1_loop_acc = Datatypes::template List<symbols_semty>::cons(
              default0, std::move(_lc1_loop_acc));
          _lc1_loop_n0 = crane_raw(a0);
        }
      }
    }
  }

  static crane::obj
  head_first(typename Ty::sym,
             const typename Datatypes::template List<typename Ty::sym> &,
             const typename Datatypes::template List<symbols_semty> &l,
             crane::obj default0) {
    if (std::holds_alternative<
            typename Datatypes::template List<symbols_semty>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] =
          std::get<typename Datatypes::template List<symbols_semty>::Cons>(
              l.v());
      return crane::any_cast<std::pair<crane::obj, crane::obj>>(a0).first;
    }
  }

  static crane::obj collect_and_get_first(
      typename Ty::sym x,
      const typename Datatypes::template List<typename Ty::sym> &xs,
      const typename Datatypes::Nat &n, symbols_semty default_tuple,
      crane::obj default_val) {
    return head_first(x, xs, collect(x, xs, n, std::move(default_tuple)),
                      default_val);
  }
};

} // namespace SepExtAnyListCollect

#endif // INCLUDED_SEPEXTANYLISTCOLLECT
