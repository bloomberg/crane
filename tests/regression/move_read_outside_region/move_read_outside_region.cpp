#include "move_read_outside_region.h"

List<uint64_t> MoveReadOutsideRegion::grow(List<uint64_t> l) {
  return l.app(l);
}

/// A two-way case in an argument, read again beside it.
uint64_t MoveReadOutsideRegion::if_in_argument(List<uint64_t> l) {
  List<uint64_t> s = l.app(l);
  return ((grow(s).length() == UINT64_C(0) ? UINT64_C(1) : UINT64_C(0)) +
          s.length());
}

/// A two-way case in a let's right-hand side, read again after the let.
uint64_t MoveReadOutsideRegion::if_in_let(List<uint64_t> l, bool b) {
  List<uint64_t> s = l.app(l);
  uint64_t x;
  if (b) {
    List<uint64_t> z = grow(s);
    x = (z.length() + z.length());
  } else {
    x = UINT64_C(0);
  }
  return (x + std::move(s).length());
}

/// A match in a let's right-hand side, read again after the let.
uint64_t MoveReadOutsideRegion::match_in_let(List<uint64_t> l) {
  List<uint64_t> s = l.app(l);
  uint64_t x = [&]() {
    if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v_mut())) {
      return UINT64_C(0);
    } else {
      List<uint64_t> z = grow(s);
      return (z.length() + z.length());
    }
  }();
  return (x + std::move(s).length());
}

/// A two-way case beside a read in the same call.
uint64_t MoveReadOutsideRegion::if_beside(List<uint64_t> l, bool b) {
  List<uint64_t> s = l.app(l);
  return (b ? grow(s) : List<uint64_t>::nil()).app(s).length();
}

/// A match beside a read in the same call.
uint64_t MoveReadOutsideRegion::match_beside(List<uint64_t> l) {
  List<uint64_t> s = l.app(l);
  return (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())
              ? List<uint64_t>::nil()
              : grow(s))
      .app(s)
      .length();
}

/// A polymorphic local helper closing over n, used twice.
uint64_t MoveReadOutsideRegion::helper_twice(uint64_t n, bool b) {
  return (helper_twice_crane_aux(n, n) + helper_twice_crane_aux(b, n));
}
