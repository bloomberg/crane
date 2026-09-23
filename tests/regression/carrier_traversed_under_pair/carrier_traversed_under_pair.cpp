#include "carrier_traversed_under_pair.h"

List<std::pair<std::optional<Nat>, Exp<std::any>>>
TFunctor_tagged(std::function<std::any(std::any)> f,
                const List<std::pair<std::optional<Nat>, Exp<std::any>>> &l) {
  return l.template map<std::any>([=](const auto &p) mutable {
    return std::make_pair(p.first, p.second.template exp_map<std::any>(f));
  });
}

template <typename _CraneTcArg>
using _crane_carrier_tc_f3d015532548dd2b =
    List<std::pair<std::optional<Nat>, Exp<_CraneTcArg>>>;

blk<std::any> TFunctor_blk(std::function<std::any(std::any)> f,
                           const blk<std::any> &b) {
  return blk<std::any>{
      b.b_id, tfmap<_crane_carrier_tc_f3d015532548dd2b>(
                  [](auto &&_ec0,
                     List<std::pair<std::optional<Nat>, Exp<std::any>>> _ec1) {
                    return TFunctor_tagged(_ec0, _ec1);
                  },
                  std::move(f), b.b_code)};
}
