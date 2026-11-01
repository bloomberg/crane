#include "splice_partner_other_instance.h"

/// f calls its partner g at another instance, g bool, than its own.
/// Type reconstruction solves a call within a recursive group at the
/// group's own variables, so the call's instantiation reads as none; only
/// the type it is written at says otherwise.  Splicing g's body into f
/// there wrote it at f's variable -- T1 x = true -- and its call of f
/// back became a turn of f's loop passing f's parameters a bool: no
/// C++ for f at a list.  Neither is spliced into the other.
uint64_t SplicePartnerOtherInstance::weight(bool b) {
  if (b) {
    return UINT64_C(10);
  } else {
    return UINT64_C(20);
  }
}

uint64_t SplicePartnerOtherInstance::run(uint64_t n) {
  return f<List<uint64_t>>(
      [](const List<uint64_t> &_x) { return _x.length(); },
      List<uint64_t>::cons(
          UINT64_C(1),
          List<uint64_t>::cons(
              UINT64_C(2),
              List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil()))),
      n);
}
