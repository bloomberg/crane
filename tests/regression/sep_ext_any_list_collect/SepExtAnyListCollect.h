#ifndef INCLUDED_SEPEXTANYLISTCOLLECT
#define INCLUDED_SEPEXTANYLISTCOLLECT

#include <any>
#include <utility>
#include <variant>

#include "Datatypes.h"

namespace SepExtAnyListCollect {

using tuple = std::any;
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
    auto go_impl = [&](auto &_self_go, const typename Datatypes::Nat &n0,
                       typename Datatypes::template List<std::any> acc) ->
        typename Datatypes::template List<std::any> {
          if (std::holds_alternative<typename Datatypes::Nat::O>(n0.v())) {
            return acc;
          } else {
            const auto &[a0] = std::get<typename Datatypes::Nat::S>(n0.v());
            return _self_go(_self_go, *a0,
                            Datatypes::template List<std::any>::cons(
                                default0, std::move(acc)));
          }
        };
    auto go = [&](const typename Datatypes::Nat &n0,
                  typename Datatypes::template List<std::any> acc) ->
        typename Datatypes::template List<std::any> {
          return go_impl(go_impl, n0, acc);
        };
    return go(n, Datatypes::template List<std::any>::nil());
  }

  static std::any
  head_first(typename Ty::sym,
             const typename Datatypes::template List<typename Ty::sym> &,
             const typename Datatypes::template List<symbols_semty> &l,
             std::any default0) {
    if (std::holds_alternative<
            typename Datatypes::template List<symbols_semty>::Nil>(l.v())) {
      return default0;
    } else {
      const auto &[a0, a1] =
          std::get<typename Datatypes::template List<symbols_semty>::Cons>(
              l.v());
      return std::any_cast<std::pair<std::any, std::any>>(
                 std::any_cast<std::pair<std::any, std::any>>(a0))
          .first;
    }
  }

  static std::any collect_and_get_first(
      typename Ty::sym x,
      const typename Datatypes::template List<typename Ty::sym> &xs,
      const typename Datatypes::Nat &n, symbols_semty default_tuple,
      std::any default_val) {
    return head_first(x, xs, collect(x, xs, n, default_tuple), default_val);
  }
};

} // namespace SepExtAnyListCollect

#endif // INCLUDED_SEPEXTANYLISTCOLLECT
