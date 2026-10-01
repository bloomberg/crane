#include "partial_application.h"

Box<crane::obj> TFunctor_box(Endo<Nat>, crane::fn<crane::obj(crane::obj)> x0_,
                             const Box<crane::obj> &x1_) {
  return ft_box<crane::obj, crane::obj>(std::move(x0_), x1_);
}

std::pair<crane::obj, Box<crane::obj>>
TFunctor_pair(TFunctor<Box<crane::obj>> h, crane::fn<crane::obj(crane::obj)> f,
              std::pair<crane::obj, Box<crane::obj>> x0_) {
  return ft_pair<crane::obj, crane::obj>(std::move(h), std::move(f),
                                         std::move(x0_));
}

std::pair<bool, Box<bool>>
PartialApplication::convert(const std::pair<Nat, Box<Nat>> &p) {
  return tfmap<std::pair<crane::obj, Box<crane::obj>>, Nat, bool>(
      []() {
        return [](crane::fn<crane::obj(crane::obj)> _x0,
                  const auto &_x1) -> std::pair<crane::obj, Box<crane::obj>> {
          return TFunctor_pair(
              []() {
                return [](crane::fn<crane::obj(crane::obj)> _x0,
                          const auto &_x1) -> Box<crane::obj> {
                  return TFunctor_box(Endo_id<Nat>, _x0,
                                      crane_convert<Box<crane::obj>>(_x1));
                };
              }(),
              _x0, crane_convert<std::pair<crane::obj, Box<crane::obj>>>(_x1));
        };
      }(),
      [](const Nat &n) { return n.eqb(Nat::o()); }, p);
}
