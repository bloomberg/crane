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
    const auto &[a, t] = std::any_cast<std::pair<std::any, std::any>>(vs);
    const auto &[b, _x2] = std::any_cast<std::pair<std::any, std::any>>(t);
    return std::make_pair(std::any_cast<typename Ty::sym_semty>(b),
                          std::any_cast<typename Ty::sym_semty>(a));
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
