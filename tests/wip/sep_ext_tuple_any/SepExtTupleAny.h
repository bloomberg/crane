#ifndef INCLUDED_SEPEXTTUPLEANY
#define INCLUDED_SEPEXTTUPLEANY

#include <any>
#include <memory>
#include <optional>
#include <type_traits>
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

  static typename Ty::symbol_semty
  get_first(const typename Ty::symbol,
            const typename Datatypes::template List<typename Ty::symbol> &,
            const symbols_semty vs) {
    return vs.first;
  }
};

} // namespace SepExtTupleAny

#endif // INCLUDED_SEPEXTTUPLEANY
