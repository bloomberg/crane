#ifndef INCLUDED_SEPEXTTUPLEANY
#define INCLUDED_SEPEXTTUPLEANY

#include "obj.h"
#include <utility>

#include "Datatypes.h"

namespace SepExtTupleAny {

using tuple = crane::obj;
template <typename M>
concept SymTypes = requires {
  typename M::symbol;
  typename M::symbol_semty;
};

template <SymTypes Ty> struct Defs {
  using symbols_semty = tuple;

  static crane::obj
  get_first(typename Ty::symbol,
            const typename Datatypes::template List<typename Ty::symbol> &,
            symbols_semty vs) {
    return crane::any_cast<std::pair<crane::obj, crane::obj>>(std::move(vs))
        .first;
  }
};

} // namespace SepExtTupleAny

#endif // INCLUDED_SEPEXTTUPLEANY
