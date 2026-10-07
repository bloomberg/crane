#include "loopify_result_no_default.h"

/// mfr recurses in the first argument of bind, so Set Crane Loopify
/// turns it into an explicit frame stack.  The generated loop declares its
/// result as typename _tcI0::template m<T3> _result{}; -- a
/// default-constructed monadic value -- and at m = itree E that type has no
/// default constructor (an Itree is a lazy cell, built only from a node or a
/// thunk), so the C++ does not compile: "no matching constructor for
/// initialization of 'typename Monad_itree<...>::m<...>'".
///
/// Found in Vellvm with the global Set Crane Loopify: 35 of the 59 errors
/// are this one, in ListUtil.monad_fold_right and ListUtil.map_monad.
Itree<LoopifyResultNoDefault::Ev, uint64_t>
LoopifyResultNoDefault::sum_tree(std::monostate) {
  return mfr<Monad_itree<LoopifyResultNoDefault::Ev>, uint64_t, uint64_t>(
      [](uint64_t r, uint64_t x) {
        return Monad_itree<LoopifyResultNoDefault::Ev>::template ret<uint64_t>(
            (r + x));
      },
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(
                  UINT64_C(3),
                  List<uint64_t>::cons(UINT64_C(4), List<uint64_t>::nil())))),
      UINT64_C(0));
}
