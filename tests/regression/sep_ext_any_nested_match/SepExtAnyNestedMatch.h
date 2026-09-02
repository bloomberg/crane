#ifndef INCLUDED_SEPEXTANYNESTEDMATCH
#define INCLUDED_SEPEXTANYNESTEDMATCH

#include <any>
#include <utility>

#include "Datatypes.h"

namespace SepExtAnyNestedMatch {

using tuple = std::any;
template <typename M>
concept SymTypes = requires {
  typename M::sym;
  typename M::sym_semty;
};

template <SymTypes Ty> struct Destruct {
  using symbols_semty = tuple;

  static std::any
  get_second(typename Ty::sym, typename Ty::sym,
             const typename Datatypes::template List<typename Ty::sym> &,
             symbols_semty vs) {
    return std::any_cast<std::pair<std::any, std::any>>(
               std::any_cast<std::pair<std::any, std::any>>(vs).second)
        .first;
  }
};

} // namespace SepExtAnyNestedMatch

#endif // INCLUDED_SEPEXTANYNESTEDMATCH
