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

  static std::pair<typename Ty::sym_semty, typename Ty::sym_semty>
  swap_pair(typename Ty::sym, typename Ty::sym,
            const typename Datatypes::template List<typename Ty::sym> &,
            symbols_semty vs) {
    auto _cs = std::any_cast<std::pair<std::any, std::any>>(vs);
    const auto &a = _cs.first;
    const auto &t = _cs.second;
    auto _cs1 = std::any_cast<std::pair<std::any, std::any>>(t);
    const typename Ty::sym_semty &b = _cs1.first;
    const auto &_x2 = _cs1.second;
    return std::make_pair(b, a);
  }

  static std::pair<typename Ty::sym_semty, typename Ty::sym_semty>
  use_both(typename Ty::sym, typename Ty::sym,
           const typename Datatypes::template List<typename Ty::sym> &,
           symbols_semty vs) {
    typename Ty::sym_semty a =
        std::any_cast<std::pair<std::any, std::any>>(vs).first;
    auto tail = std::any_cast<std::pair<std::any, std::any>>(vs).second;
    typename Ty::sym_semty b =
        std::any_cast<std::pair<std::any, std::any>>(std::move(tail)).first;
    return std::make_pair(a, b);
  }
};

} // namespace AnyCastDanglingPairRef

#endif // INCLUDED_ANYCASTDANGLINGPAIRREF
