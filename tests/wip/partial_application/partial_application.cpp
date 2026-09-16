#include "partial_application.h"

Box<std::any> TFunctor_box(Endo<Nat>, std::function<std::any(std::any)> f,
                           Box<std::any> x0_) {
  return ft_box(std::move(f), std::move(x0_));
}

std::pair<std::any, Box<std::any>>
TFunctor_pair(TFunctor<Box> h, std::function<std::any(std::any)> f,
              std::pair<std::any, Box<std::any>> x0_) {
  return ft_pair(std::move(h), std::move(f), std::move(x0_));
}

std::pair<bool, Box<bool>>
PartialApplication::convert(const std::pair<Nat, Box<Nat>> &p) {
  return tfmap(
      []() {
        return TFunctor_pair([]() { return TFunctor_box(Endo_id<Nat>); }());
      }(),
      [](const Nat &n) { return n.eqb(Nat::o()); }, p);
}
