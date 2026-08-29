#include "ctor_arg_move_alias.h"

uint64_t CtorArgMoveAlias::osum(
    const CtorArgMoveAlias::mylist<CtorArgMoveAlias::inner> &o) {
  if (std::holds_alternative<
          typename CtorArgMoveAlias::mylist<CtorArgMoveAlias::inner>::Mynil>(
          o.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<
        typename CtorArgMoveAlias::mylist<CtorArgMoveAlias::inner>::Mycons>(
        o.v());
    return (a0.isum() + osum(*a1));
  }
}

CtorArgMoveAlias::pack
CtorArgMoveAlias::grab(CtorArgMoveAlias::mylist<CtorArgMoveAlias::inner> o) {
  if (std::holds_alternative<
          typename CtorArgMoveAlias::mylist<CtorArgMoveAlias::inner>::Mynil>(
          o.v_mut())) {
    return pack::plist(o);
  } else {
    auto &[a0, a1] = std::get<
        typename CtorArgMoveAlias::mylist<CtorArgMoveAlias::inner>::Mycons>(
        o.v_mut());
    return pack::pack0(a0, osum(o));
  }
}

uint64_t CtorArgMoveAlias::run(uint64_t n) {
  auto &&_sv = grab(mylist<CtorArgMoveAlias::inner>::mycons(
      inner::icons(n, inner::icons((n + 1), inner::inil())),
      mylist<CtorArgMoveAlias::inner>::mynil()));
  if (std::holds_alternative<typename CtorArgMoveAlias::pack::Pack0>(_sv.v())) {
    const auto &[a0, a1] =
        std::get<typename CtorArgMoveAlias::pack::Pack0>(_sv.v());
    return (a1 + a0.isum());
  } else {
    const auto &[a0] =
        std::get<typename CtorArgMoveAlias::pack::PList>(_sv.v());
    return osum(a0);
  }
}
