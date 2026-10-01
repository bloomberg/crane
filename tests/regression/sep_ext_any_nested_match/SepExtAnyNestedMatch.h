#ifndef INCLUDED_SEPEXTANYNESTEDMATCH
#define INCLUDED_SEPEXTANYNESTEDMATCH

#include "obj.h"
#include <any>
#include <utility>

#include "Datatypes.h"

namespace SepExtAnyNestedMatch {

using tuple = crane::obj;
template <typename M>
concept SymTypes = requires {
  typename M::sym;
  typename M::sym_semty;
};

template <SymTypes Ty> struct Destruct {
  using symbols_semty = tuple;

  static crane::obj
  get_second(typename Ty::sym, typename Ty::sym,
             const typename Datatypes::template List<typename Ty::sym> &,
             symbols_semty vs) {
    return crane::any_cast<std::pair<crane::obj, crane::obj>>(
               crane::any_cast<std::pair<crane::obj, crane::obj>>(vs).second)
        .first;
  }
};

} // namespace SepExtAnyNestedMatch

#endif // INCLUDED_SEPEXTANYNESTEDMATCH
