#include "carrier_traversed_under_pair.h"

List<std::pair<std::optional<Nat>, Exp<crane::obj>>>
TFunctor_tagged(const crane::fn<crane::obj(crane::obj)> &f,
                const List<std::pair<std::optional<Nat>, Exp<crane::obj>>> &l) {
  return l.template map<std::pair<std::optional<Nat>, Exp<crane::obj>>>(
      [=](const std::pair<std::optional<Nat>, Exp<crane::obj>> &p) {
        return std::make_pair(p.first,
                              p.second.template exp_map<crane::obj>(f));
      });
}

blk<crane::obj> TFunctor_blk(const crane::fn<crane::obj(crane::obj)> &f,
                             const blk<crane::obj> &b) {
  return blk<crane::obj>{
      b.b_id,
      tfmap<List<std::pair<std::optional<Nat>, Exp<crane::obj>>>, crane::obj,
            crane::obj>(
          [](auto &&_ec0,
             List<std::pair<std::optional<Nat>, Exp<crane::obj>>> _ec1) {
            return TFunctor_tagged(_ec0, _ec1);
          },
          f, b.b_code)};
}
