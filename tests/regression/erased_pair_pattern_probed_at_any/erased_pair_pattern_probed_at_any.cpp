#include "erased_pair_pattern_probed_at_any.h"

List<crane::obj> TFunctor_list(const crane::fn<crane::obj(crane::obj)> &x0_,
                               const List<crane::obj> &x1_) {
  return x1_.template map<crane::obj>(x0_);
}

box<crane::obj> TFunctor_box(const crane::fn<crane::obj(crane::obj)> &f,
                             const box<crane::obj> &b) {
  return box<crane::obj>{f(b.b_payload)};
}

pairs<bool, box<bool>> run(const pairs<Nat, box<Nat>> &m) {
  return tfmap<pairs<crane::obj, box<crane::obj>>, Nat, bool>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> pairs<crane::obj, box<crane::obj>> {
          return TFunctor_pairs<box<crane::obj>>(
              [](auto &&_ec0, box<crane::obj> _ec1) {
                return TFunctor_box(_ec0, _ec1);
              },
              _x0, crane_convert<pairs<crane::obj, box<crane::obj>>>(_x1));
        };
      }(),
      [](Nat _x0) -> bool { return Nat::s(Nat::s(Nat::s(Nat::o()))).ltb(_x0); },
      m);
}
