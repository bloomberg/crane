#ifndef INCLUDED_SEPEXTTUPLEANY
#define INCLUDED_SEPEXTTUPLEANY

#include <any>
#include <utility>

#include "Datatypes.h"

namespace SepExtTupleAny {

using tuple = std::any;
template <typename M>
concept SymTypes = requires {
  typename M::symbol;
  typename M::symbol_semty;
};

template <SymTypes Ty> struct Defs {
  using symbols_semty = tuple;

  static std::any
  get_first(typename Ty::symbol,
            const typename Datatypes::template List<typename Ty::symbol> &,
            symbols_semty vs) {
    return std::any_cast<std::pair<std::any, std::any>>(vs).first;
  }
};

} // namespace SepExtTupleAny

#endif // INCLUDED_SEPEXTTUPLEANY
