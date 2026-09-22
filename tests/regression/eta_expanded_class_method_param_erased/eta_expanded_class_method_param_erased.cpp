#include "eta_expanded_class_method_param_erased.h"

List<std::pair<Nat, Nat>> build(const List<std::pair<Nat, Nat>> &l) {
  return l.template fold_right<List<std::pair<Nat, Nat>>>(
      [](const std::pair<Nat, Nat> &pat,
         const List<std::pair<Nat, Nat>> &eta0_) {
        const auto &[x, d] = pat;
        return map_alist::add(x, d, eta0_);
      },
      map_alist::empty());
}

List<std::pair<Nat, Nat>> build_saturated(const List<std::pair<Nat, Nat>> &l) {
  return l.template fold_right<List<std::pair<Nat, Nat>>>(
      [](const std::pair<Nat, Nat> &p, const List<std::pair<Nat, Nat>> &acc) {
        return map_alist::add(p.first, p.second, acc);
      },
      map_alist::empty());
}

List<std::pair<Nat, Nat>> partial(const Nat &k, const Nat &v,
                                  const List<std::pair<Nat, Nat>> &l) {
  return apply_it(
      [=](List<std::pair<Nat, Nat>> _sat0) mutable {
        return map_alist::add(k, v, _sat0);
      },
      l);
}
