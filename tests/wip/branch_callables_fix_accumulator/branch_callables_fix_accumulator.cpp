#include "branch_callables_fix_accumulator.h"

uint64_t BranchCallablesFixAccumulator::pick(bool b) {
  crane::fn<List<uint64_t>(crane::fn<uint64_t(uint64_t)>)> w;
  auto go =
      [](List<uint64_t> l,
         crane::fn<List<uint64_t>(crane::fn<uint64_t(uint64_t)>)>,
         crane::fn<uint64_t(uint64_t)>)
           -> List<uint64_t> {
        // Loop replaces the tail recursion: each recursive call updates the
        // loop variables.
        List<uint64_t> _loop_l = std::move(l);
        while (true) {
          if (std::holds_alternative<typename List<uint64_t>::Nil>(
                  _loop_l.v_mut())) {
            return List<uint64_t>::nil();
          } else {
            auto &[_, a1] =
                std::get<typename List<uint64_t>::Cons>(_loop_l.v_mut());
            const List<uint64_t> &a1_value = *a1;
            _loop_l = List<uint64_t>(a1_value);
          }
        }
      };
  w = [=](crane::fn<uint64_t(uint64_t)> _pa0) {
    return go(
        List<uint64_t>::nil(),
        [&]() {
          auto _cs =
              List<BranchCallablesFixAccumulator::r3>::nil().template fold_left<
                  BranchCallablesFixAccumulator::r3>(
                  [](BranchCallablesFixAccumulator::r3,
                     BranchCallablesFixAccumulator::r3) {
                    return r3{UINT64_C(0), List<uint64_t>::nil(), true};
                  },
                  r3{UINT64_C(0), List<uint64_t>::nil(), b});
          crane::obj _x = std::move(_cs).ra;
          crane::obj _x0 = std::move(_cs).rb;
          bool c0 = std::move(_cs).rc;
          if (c0) {
            crane::fn<List<uint64_t>(bool)> cf = [](bool) {
              return List<uint64_t>::cons(
                  UINT64_C(1),
                  List<uint64_t>::cons(UINT64_C(2), List<uint64_t>::nil()));
            };
            crane::fn<bool(crane::fn<uint64_t(uint64_t)>)> cg =
                [](const crane::fn<uint64_t(uint64_t)> &) { return true; };
            return [=, cf = std::move(cf), cg = std::move(cg)](
                const crane::fn<uint64_t(uint64_t)> &c) { return cf(cg(c)); };
          } else {
            return [](const crane::fn<uint64_t(uint64_t)> &) {
              return List<uint64_t>::cons(UINT64_C(3), List<uint64_t>::nil());
            };
          }
        }(),
        _pa0);
  };
  return w([](uint64_t s) { return s; }).length();
}
