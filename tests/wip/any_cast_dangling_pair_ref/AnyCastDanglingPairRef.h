#ifndef INCLUDED_ANYCASTDANGLINGPAIRREF
#define INCLUDED_ANYCASTDANGLINGPAIRREF

#include <any>
#include <type_traits>
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
    const std::any &b = std::any_cast<std::pair<std::any, std::any>>(t).first;
    const std::any &_x2 =
        std::any_cast<std::pair<std::any, std::any>>(t).second;
    return std::make_pair(
        [&]() -> typename Ty::sym_semty {
          if constexpr (std::is_same_v<typename Ty::sym_semty, std::any>)
            return b;
          else
            return std::any_cast<typename Ty::sym_semty>(b);
        }(),
        a);
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
