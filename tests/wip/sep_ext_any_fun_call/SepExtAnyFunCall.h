#ifndef INCLUDED_SEPEXTANYFUNCALL
#define INCLUDED_SEPEXTANYFUNCALL

#include <any>
#include <functional>
#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

#include "Datatypes.h"
#include "Specif.h"

namespace SepExtAnyFunCall {

using tuple = std::any;
template <typename M>
concept SymTypes = requires {
  typename M::sym;
  typename M::sym_semty;
};

template <SymTypes Ty> struct Actions {
  using symbols_semty = tuple;
  using entry = typename Specif::template SigT<
      typename Datatypes::template List<typename Ty::sym>,
      std::function<bool(symbols_semty)>>;

  template <typename F1>
    requires std::is_invocable_r_v<bool, F1 &, symbols_semty &>
  static entry
  make_entry(typename Datatypes::template List<typename Ty::sym> gamma,
             F1 &&f) {
    return Specif::template SigT<
        typename Datatypes::template List<typename Ty::sym>,
        std::function<bool(std::any)>>::existt(std::move(gamma), f);
  }

  constexpr static bool apply_entry(const entry _x0, const symbols_semty _x1) {
    return _x0.projT2()(_x1);
  }
};

} // namespace SepExtAnyFunCall

#endif // INCLUDED_SEPEXTANYFUNCALL
