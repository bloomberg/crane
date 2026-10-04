#ifndef INCLUDED_ANYCASTDANGLINGPAIRREF
#define INCLUDED_ANYCASTDANGLINGPAIRREF

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
    const auto &[a, t] = crane::any_cast<std::pair<crane::obj, crane::obj>>(vs);
    const auto &[b, _x2] =
        crane::any_cast<std::pair<crane::obj, crane::obj>>(t);
    return std::make_pair(crane::obj(b), crane::obj(a));
  }

  static std::pair<crane::obj, crane::obj>
  use_both(typename Ty::sym, typename Ty::sym,
           const typename Datatypes::template List<typename Ty::sym> &,
           symbols_semty vs) {
    auto a = crane::any_cast<std::pair<crane::obj, crane::obj>>(vs).first;
    auto tail = crane::any_cast<std::pair<crane::obj, crane::obj>>(vs).second;
    auto b = crane_any_cast<std::pair<crane::obj, crane::obj>>(std::move(tail))
                 .first;
    return std::make_pair(crane::obj(a), crane::obj(b));
  }
};

} // namespace AnyCastDanglingPairRef

#endif // INCLUDED_ANYCASTDANGLINGPAIRREF
