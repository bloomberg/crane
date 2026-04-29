#include <tailrec_reorder_probe.h>

/// Variant: TWO arguments depend on pattern-matched fields.
/// l := t, acc1 := mycons h acc1, acc2 := mycons (h+1) acc2
/// Both acc1 and acc2 need h from the OLD l.
__attribute__((pure)) std::pair<TailrecReorderProbe::mylist<unsigned int>,
                                TailrecReorderProbe::mylist<unsigned int>>
TailrecReorderProbe::dual_accum(
    const TailrecReorderProbe::mylist<unsigned int> &l,
    TailrecReorderProbe::mylist<unsigned int> acc1,
    TailrecReorderProbe::mylist<unsigned int> acc2) {
  std::pair<TailrecReorderProbe::mylist<unsigned int>,
            TailrecReorderProbe::mylist<unsigned int>>
      _result;
  TailrecReorderProbe::mylist<unsigned int> _loop_acc2 = std::move(acc2);
  TailrecReorderProbe::mylist<unsigned int> _loop_acc1 = std::move(acc1);
  const TailrecReorderProbe::mylist<unsigned int> *_loop_l = &l;
  while (true) {
    if (std::holds_alternative<
            typename TailrecReorderProbe::mylist<unsigned int>::Mynil>(
            _loop_l->v())) {
      _result = std::make_pair(std::move(_loop_acc1), std::move(_loop_acc2));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename TailrecReorderProbe::mylist<unsigned int>::Mycons>(
              _loop_l->v());
      TailrecReorderProbe::mylist<unsigned int> _next_acc2 =
          mylist<unsigned int>::mycons((d_a0 + 1u), std::move(_loop_acc2));
      TailrecReorderProbe::mylist<unsigned int> _next_acc1 =
          mylist<unsigned int>::mycons(d_a0, std::move(_loop_acc1));
      const TailrecReorderProbe::mylist<unsigned int> *_next_l = d_a1.get();
      _loop_acc2 = std::move(_next_acc2);
      _loop_acc1 = std::move(_next_acc1);
      _loop_l = _next_l;
    }
  }
  return _result;
}

/// Tail-recursive function where the recursive argument is a COMPLEX
/// expression involving multiple pattern variables.
__attribute__((pure)) TailrecReorderProbe::mylist<unsigned int>
TailrecReorderProbe::weave(const TailrecReorderProbe::mylist<unsigned int> &l1,
                           const TailrecReorderProbe::mylist<unsigned int> &l2,
                           TailrecReorderProbe::mylist<unsigned int> acc) {
  TailrecReorderProbe::mylist<unsigned int> _result;
  TailrecReorderProbe::mylist<unsigned int> _loop_acc = std::move(acc);
  const TailrecReorderProbe::mylist<unsigned int> *_loop_l2 = &l2;
  const TailrecReorderProbe::mylist<unsigned int> *_loop_l1 = &l1;
  while (true) {
    if (std::holds_alternative<
            typename TailrecReorderProbe::mylist<unsigned int>::Mynil>(
            _loop_l1->v())) {
      _result = my_rev_append<unsigned int>(std::move(_loop_acc), *(_loop_l2));
      break;
    } else {
      const auto &[d_a0, d_a1] =
          std::get<typename TailrecReorderProbe::mylist<unsigned int>::Mycons>(
              _loop_l1->v());
      if (std::holds_alternative<
              typename TailrecReorderProbe::mylist<unsigned int>::Mynil>(
              _loop_l2->v())) {
        _result =
            my_rev_append<unsigned int>(std::move(_loop_acc), *(_loop_l1));
        break;
      } else {
        const auto &[d_a00, d_a10] = std::get<
            typename TailrecReorderProbe::mylist<unsigned int>::Mycons>(
            _loop_l2->v());
        TailrecReorderProbe::mylist<unsigned int> _next_acc =
            mylist<unsigned int>::mycons(
                d_a00,
                mylist<unsigned int>::mycons(d_a0, std::move(_loop_acc)));
        const TailrecReorderProbe::mylist<unsigned int> *_next_l2 = d_a10.get();
        const TailrecReorderProbe::mylist<unsigned int> *_next_l1 = d_a1.get();
        _loop_acc = std::move(_next_acc);
        _loop_l2 = _next_l2;
        _loop_l1 = _next_l1;
      }
    }
  }
  return _result;
}
