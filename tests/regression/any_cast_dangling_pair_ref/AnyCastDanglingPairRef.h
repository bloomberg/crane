#pragma once

#include "crane_fn.h"
#include "obj.h"
#include <utility>

#include "Datatypes.h"

namespace AnyCastDanglingPairRef {
using tuple = crane::obj;
template <typename M>
concept SymTypes = requires {
  typename M::sym;
  typename M::sym_semty;
};

template <SymTypes Ty> struct Destruct {
  using symbols_semty = tuple;

  static std::pair<crane::obj, crane::obj>
  swap_pair(typename Ty::sym, typename Ty::sym,
            const typename Datatypes::template List<typename Ty::sym> &,
            symbols_semty vs) {
    auto [a, t] =
        crane::any_cast<std::pair<crane::obj, crane::obj>>(std::move(vs));
    auto [b, _] =
        crane::any_cast<std::pair<crane::obj, crane::obj>>(std::move(t));
    return std::make_pair(crane::obj(std::move(b)), crane::obj(std::move(a)));
  }

  static std::pair<crane::obj, crane::obj>
  use_both(typename Ty::sym, typename Ty::sym,
           const typename Datatypes::template List<typename Ty::sym> &,
           symbols_semty vs) {
    auto a = crane::any_cast<std::pair<crane::obj, crane::obj>>(vs).first;
    return std::make_pair(
        crane::obj(std::move(a)),
        crane::obj(
            crane_any_cast<std::pair<crane::obj, crane::obj>>(
                crane::any_cast<std::pair<crane::obj, crane::obj>>(
                    std::move(vs))
                    .second)
                .first));
  }
};
} // namespace AnyCastDanglingPairRef
