#include "ctor_arg_move_alias_rec.h"

/// Recursive variant of ctor_arg_move_alias: the same use-after-move, but
/// reached through a tail-modulo-cons Fixpoint rather than a one-shot
/// Definition, so every level of the recursion re-triggers it.
///
/// annotate rebuilds the list, interleaving a running total.  Because h
/// occurs exactly once and o is owned (it escapes through the mynil
/// branch), Crane used to emit
///
/// {
/// auto& [a0, a1] = std::get<Mycons>(o.v_mut());
/// return mylist<inner>::mycons(
/// std::move(a0),
/// mylist<inner>::mycons(inner::icons(osum(o), inner::inil()),
/// annotate( *a1 )));
/// }
///
/// std::move(a0) hollowed out o's head element while the sibling argument
/// computed osum(o) over that same o.  The two are unsequenced; clang
/// performed the move first, so osum walked a moved-from inner whose tail
/// shared_ptr was null.
///
/// The field move is now suppressed because the branch body still reads o,
/// so run 1 = 8.
uint64_t CtorArgMoveAliasRec::osum(
    const CtorArgMoveAliasRec::mylist<CtorArgMoveAliasRec::inner> &o) {
  if (std::holds_alternative<typename CtorArgMoveAliasRec::mylist<
          CtorArgMoveAliasRec::inner>::Mynil>(o.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename CtorArgMoveAliasRec::mylist<
        CtorArgMoveAliasRec::inner>::Mycons>(o.v());
    return (a0.isum() + osum(*a1));
  }
}

/// The head element h is consumed into the freshly built cell while the
/// sibling argument still reads o.
CtorArgMoveAliasRec::mylist<CtorArgMoveAliasRec::inner>
CtorArgMoveAliasRec::annotate(
    CtorArgMoveAliasRec::mylist<CtorArgMoveAliasRec::inner> o) {
  if (std::holds_alternative<typename CtorArgMoveAliasRec::mylist<
          CtorArgMoveAliasRec::inner>::Mynil>(o.v_mut())) {
    return o;
  } else {
    auto &[a0, a1] = std::get<typename CtorArgMoveAliasRec::mylist<
        CtorArgMoveAliasRec::inner>::Mycons>(o.v_mut());
    return mylist<CtorArgMoveAliasRec::inner>::mycons(
        a0, mylist<CtorArgMoveAliasRec::inner>::mycons(
                inner::icons(osum(o), inner::inil()), annotate(*a1)));
  }
}

/// For n = 1 the input is [ICons 1 INil; ICons 2 INil], so
/// annotate yields [I 1; I 3; I 2; I 2] and run 1 = 1+3+2+2 = 8.
uint64_t CtorArgMoveAliasRec::run(uint64_t n) {
  return osum(annotate(mylist<CtorArgMoveAliasRec::inner>::mycons(
      inner::icons(n, inner::inil()),
      mylist<CtorArgMoveAliasRec::inner>::mycons(
          inner::icons((n + 1), inner::inil()),
          mylist<CtorArgMoveAliasRec::inner>::mynil()))));
}
