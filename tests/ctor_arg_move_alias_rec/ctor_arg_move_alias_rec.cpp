#include "ctor_arg_move_alias_rec.h"

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

uint64_t CtorArgMoveAliasRec::run(uint64_t n) {
  return osum(annotate(mylist<CtorArgMoveAliasRec::inner>::mycons(
      inner::icons(n, inner::inil()),
      mylist<CtorArgMoveAliasRec::inner>::mycons(
          inner::icons((n + 1), inner::inil()),
          mylist<CtorArgMoveAliasRec::inner>::mynil()))));
}
