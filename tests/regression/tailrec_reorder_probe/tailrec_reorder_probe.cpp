#include "tailrec_reorder_probe.h"

/// Variant: TWO arguments depend on pattern-matched fields.
/// l := t, acc1 := mycons h acc1, acc2 := mycons (h+1) acc2
/// Both acc1 and acc2 need h from the OLD l.
std::pair<TailrecReorderProbe::mylist<uint64_t>,
          TailrecReorderProbe::mylist<uint64_t>>
TailrecReorderProbe::dual_accum(
    const TailrecReorderProbe::mylist<uint64_t> &l,
    const TailrecReorderProbe::mylist<uint64_t> &acc1,
    const TailrecReorderProbe::mylist<uint64_t> &acc2) {
  TailrecReorderProbe::mylist<uint64_t> _loop_acc2 = acc2;
  TailrecReorderProbe::mylist<uint64_t> _loop_acc1 = acc1;
  const TailrecReorderProbe::mylist<uint64_t> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename TailrecReorderProbe::mylist<uint64_t>::Mynil>(
            _loop_l->v())) {
      return std::make_pair(_loop_acc1, _loop_acc2);
    } else {
      const auto &[a0, a1] =
          std::get<typename TailrecReorderProbe::mylist<uint64_t>::Mycons>(
              _loop_l->v());
      _loop_acc2 =
          mylist<uint64_t>::mycons((a0 + UINT64_C(1)), std::move(_loop_acc2));
      _loop_acc1 = mylist<uint64_t>::mycons(a0, std::move(_loop_acc1));
      _loop_l = crane_raw(a1);
    }
  }
}

/// Tail-recursive function where the recursive argument is a COMPLEX
/// expression involving multiple pattern variables.
TailrecReorderProbe::mylist<uint64_t>
TailrecReorderProbe::weave(const TailrecReorderProbe::mylist<uint64_t> &l1,
                           const TailrecReorderProbe::mylist<uint64_t> &l2,
                           const TailrecReorderProbe::mylist<uint64_t> &acc) {
  TailrecReorderProbe::mylist<uint64_t> _loop_acc = acc;
  const TailrecReorderProbe::mylist<uint64_t> *_loop_l2 = &l2;
  const TailrecReorderProbe::mylist<uint64_t> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<
            typename TailrecReorderProbe::mylist<uint64_t>::Mynil>(
            _loop_l1->v())) {
      return my_rev_append<uint64_t>(_loop_acc, *_loop_l2);
    } else {
      const auto &[a0, a1] =
          std::get<typename TailrecReorderProbe::mylist<uint64_t>::Mycons>(
              _loop_l1->v());
      if (std::holds_alternative<
              typename TailrecReorderProbe::mylist<uint64_t>::Mynil>(
              _loop_l2->v())) {
        return my_rev_append<uint64_t>(_loop_acc, *_loop_l1);
      } else {
        const auto &[a00, a10] =
            std::get<typename TailrecReorderProbe::mylist<uint64_t>::Mycons>(
                _loop_l2->v());
        _loop_acc = mylist<uint64_t>::mycons(
            a00, mylist<uint64_t>::mycons(a0, std::move(_loop_acc)));
        _loop_l2 = crane_raw(a10);
        _loop_l1 = crane_raw(a1);
      }
    }
  }
}
