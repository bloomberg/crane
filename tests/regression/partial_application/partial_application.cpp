#include "partial_application.h"

template <typename _CraneTcArg>
using _crane_carrier_tc = std::pair<_CraneTcArg, Box<_CraneTcArg>>;

Box<std::any> TFunctor_box(Endo<Nat>, std::function<std::any(std::any)> x0_,
                           const Box<std::any> &x1_) {
  return ft_box<std::any, std::any>(std::move(x0_), x1_);
}

std::pair<std::any, Box<std::any>>
TFunctor_pair(std::type_identity_t<TFunctor<Box>> x0_,
              std::function<std::any(std::any)> x1_,
              const std::pair<std::any, Box<std::any>> &x2_) {
  return ft_pair<std::any, std::any>(std::move(x0_), std::move(x1_), x2_);
}

std::pair<bool, Box<bool>>
PartialApplication::convert(const std::pair<Nat, Box<Nat>> &p) {
  return tfmap<_crane_carrier_tc>(
      []() {
        return [](std::function<std::any(std::any)> _x0,
                  std::pair<std::any, Box<std::any>> _x1)
                   -> std::pair<std::any, Box<std::any>> {
          return TFunctor_pair(
              []() {
                return [](std::function<std::any(std::any)> _x0,
                          Box<std::any> _x1) -> Box<std::any> {
                  return TFunctor_box(Endo_id<Nat>, _x0, _x1);
                };
              }(),
              _x0, _x1);
        };
      }(),
      [](const Nat &n) { return n.eqb(Nat::o()); }, p);
}
