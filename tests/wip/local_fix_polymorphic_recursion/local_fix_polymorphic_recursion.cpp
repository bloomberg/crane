#include "local_fix_polymorphic_recursion.h"

/// A local fixpoint that calls itself at bool, not at the list nat it
/// is entered at: polymorphic recursion.  Extraction types a local
/// fixpoint's body at one instance, so A is both, and the loop Loopify
/// makes of the tail call declares its variables at bool: bool _lc1_y
/// is initialised from a list, and the List callable is stored in a
/// crane::fn<uint64_t(bool)>.  No C++.  The top-level Fixpoint is
/// self_call_other_instance.
uint64_t LocalFixPolymorphicRecursion::run(uint64_t k, uint64_t n) {
  {
    const crane::fn<uint64_t(bool)> &_lc1_h = [](const List<uint64_t> &_x) {
      return _x.length();
    };
    bool _lc1_y = List<uint64_t>::cons(
        UINT64_C(1), List<uint64_t>::cons(
                         UINT64_C(2), List<uint64_t>::cons(
                                          UINT64_C(3), List<uint64_t>::nil())));
    uint64_t _lc1_n0 = n;
    uint64_t _lc1_loop_n0 = _lc1_n0;
    bool _lc1_loop_y = _lc1_y;
    crane::fn<uint64_t(bool)> _lc1_loop_h = _lc1_h;
    while (true) {
      if (_lc1_loop_n0 <= 0) {
        return _lc1_loop_h(_lc1_loop_y);
      } else {
        uint64_t m = _lc1_loop_n0 - 1;
        _lc1_loop_n0 = m;
        _lc1_loop_y = true;
        _lc1_loop_h = [=](bool b) -> uint64_t {
          if (b) {
            return (UINT64_C(10) + k);
          } else {
            return UINT64_C(20);
          }
        };
      }
    }
  }
}
