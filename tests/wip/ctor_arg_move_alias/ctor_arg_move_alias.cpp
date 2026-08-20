#include "ctor_arg_move_alias.h"

/// Use-after-move: a constructor field is moved out of an owned scrutinee
/// while a sibling argument of the same call still reads that scrutinee.
///
/// Ingredients, all of which are needed:
///
/// - mylist is polymorphic, so grab stays a free function instead of
/// being methodified onto a const this (a const receiver silently
/// degrades std::move to a copy and hides the problem).
/// - o escapes through the mynil branch, so escape analysis marks it
/// {i owned} and it is passed by value.  Owned scrutinees are destructured
/// with auto& [a0, a1] = std::get<Mycons>(o.v_mut()), i.e. a0 is a
/// mutable reference {i into} o.
/// - the element type inner is a non-trivial inductive, so moving a0
/// really does hollow out o's head (a trivial nat element would make
/// the move a no-op).
/// - h occurs exactly once in the branch, so move-on-last-use fires and
/// emits std::move(a0).
///
/// Crane emits
///
/// {
/// auto& [a0, a1] = std::get<Mycons>(o.v_mut());
/// return pack::pack0(std::move(a0), osum(o));
/// }
///
/// The two arguments are {i unsequenced}: std::move(a0) consumes o's
/// head element, and osum(o) walks the very same o.  Whichever order
/// the compiler picks, one of them is wrong; with clang the move happens
/// first, so osum reads a moved-from inner whose tail shared_ptr is
/// now null and dereferences it.
///
/// Expected run 1 = 6; the extracted program segfaults instead
/// (UBSan: "member call on null pointer of type 'inner'").
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

/// h is the sole occurrence of the head field, so Crane moves it out of
/// o; the sibling argument osum o still reads the whole o.
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
    return pack::pack0(std::move(a0), osum(o));
  }
}

/// o = [ICons n (ICons (S n) INil)], so osum o = 2n+1 and
/// isum h = 2n+1; the result is 4n+2, i.e. 6 for n = 1.
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
