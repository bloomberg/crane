#include "local_fix_polymorphic_recursion.h"

/// A local fixpoint that calls itself at bool, not at the list nat it
/// is entered at: polymorphic recursion.  Extraction types a local
/// fixpoint's body at one instance, which the call at bool would pin, so
/// the entry's list would reach a bool loop variable.  Instead the
/// fixpoint's type binder is erased (Extraction.erased_fix_types): y is
/// a crane::obj, h a crane::fn<uint64_t(crane::obj)>, and each closure
/// stored into h goes through crane_erase_fn.  The top-level Fixpoint
/// is self_call_other_instance.
uint64_t LocalFixPolymorphicRecursion::run(uint64_t k, uint64_t n) {
  {
    const crane::fn<uint64_t(crane::obj)> &_lc1_h = crane_erase_fn<uint64_t>(
        [](const List<uint64_t> &_x) { return _x.length(); });
    crane::obj _lc1_y = List<uint64_t>::cons(
        UINT64_C(1), List<uint64_t>::cons(
                         UINT64_C(2), List<uint64_t>::cons(
                                          UINT64_C(3), List<uint64_t>::nil())));
    uint64_t _lc1_n0 = n;
    uint64_t _lc1_loop_n0 = _lc1_n0;
    crane::obj _lc1_loop_y = _lc1_y;
    crane::fn<uint64_t(crane::obj)> _lc1_loop_h = _lc1_h;
    while (true) {
      if (_lc1_loop_n0 <= 0) {
        return _lc1_loop_h(_lc1_loop_y);
      } else {
        uint64_t m = _lc1_loop_n0 - 1;
        _lc1_loop_n0 = m;
        _lc1_loop_y = true;
        _lc1_loop_h = crane_erase_fn<uint64_t>([=](bool b) {
          if (b) {
            return (UINT64_C(10) + k);
          } else {
            return UINT64_C(20);
          }
        });
      }
    }
  }
}
