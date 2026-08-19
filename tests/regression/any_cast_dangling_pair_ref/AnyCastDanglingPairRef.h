#ifndef INCLUDED_ANYCASTDANGLINGPAIRREF
#define INCLUDED_ANYCASTDANGLINGPAIRREF

#include <any>
#include <utility>

#include "Datatypes.h"

namespace AnyCastDanglingPairRef {

using tuple = std::any;
template <typename M>
concept SymTypes = requires {
  typename M::sym;
  typename M::sym_semty;
};

template <SymTypes Ty> struct Destruct {
  using symbols_semty = tuple;

  static std::pair<std::any, std::any>
  swap_pair(typename Ty::sym, typename Ty::sym,
            const typename Datatypes::template List<typename Ty::sym> &,
            symbols_semty vs) {
    const auto &[a, t] = std::any_cast<std::pair<std::any, std::any>>(vs);
    const auto &[b, _x2] = std::any_cast<std::pair<std::any, std::any>>(t);
    return std::make_pair(std::any(b), std::any(a));
  }

  static std::pair<std::any, std::any>
  use_both(typename Ty::sym, typename Ty::sym,
           const typename Datatypes::template List<typename Ty::sym> &,
           symbols_semty vs) {
    auto a = std::any_cast<std::pair<std::any, std::any>>(vs).first;
    auto tail = std::any_cast<std::pair<std::any, std::any>>(vs).second;
    auto b =
        std::any_cast<std::pair<std::any, std::any>>(std::move(tail)).first;
    return std::make_pair(std::any(a), std::any(b));
  }
};

} // namespace AnyCastDanglingPairRef

#endif // INCLUDED_ANYCASTDANGLINGPAIRREF
