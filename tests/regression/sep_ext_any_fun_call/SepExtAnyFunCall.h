#ifndef INCLUDED_SEPEXTANYFUNCALL
#define INCLUDED_SEPEXTANYFUNCALL

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include <utility>

#include "Datatypes.h"
#include "Specif.h"

namespace SepExtAnyFunCall {

using tuple = crane::obj;
template <typename M>
concept SymTypes = requires {
  typename M::sym;
  typename M::sym_semty;
};

template <SymTypes Ty> struct Actions {
  using symbols_semty = tuple;
  using entry = typename Specif::template SigT<
      typename Datatypes::template List<typename Ty::sym>,
      crane::fn<bool(symbols_semty)>>;

  template <typename F1>
  static entry
  make_entry(const typename Datatypes::template List<typename Ty::sym> &gamma,
             F1 &&f) {
    return Specif::template SigT<
        typename Datatypes::template List<typename Ty::sym>,
        crane::fn<bool(crane::obj)>>::existt(gamma, crane_erase_fn<bool>(f));
  }

  static bool apply_entry(entry x0_, symbols_semty x1_) {
    return crane_any_cast<bool>(x0_.projT2()(std::move(x1_)));
  }
};

} // namespace SepExtAnyFunCall

#endif // INCLUDED_SEPEXTANYFUNCALL
