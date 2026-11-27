#include "lazy_direct_layer.h"

LazyDirectLayer::treeF<LazyDirectLayer::tree>
LazyDirectLayer::observe(const LazyDirectLayer::tree &t) {
  const auto &[observe1] =
      crane::get<typename LazyDirectLayer::tree::Go>(t.v());
  return observe1;
}

LazyDirectLayer::tree LazyDirectLayer::Ret(uint64_t n) {
  return tree::go(treeF<LazyDirectLayer::tree>::retf(n));
}

LazyDirectLayer::tree LazyDirectLayer::Tau(const LazyDirectLayer::tree &t) {
  return tree::go(treeF<LazyDirectLayer::tree>::tauf(t));
}

LazyDirectLayer::tree
LazyDirectLayer::Vis(uint64_t e,
                     const crane::fn<LazyDirectLayer::tree(uint64_t)> &k) {
  return tree::go(treeF<LazyDirectLayer::tree>::visf(e, k));
}

LazyDirectLayer::tree LazyDirectLayer::taus(uint64_t n, uint64_t r) {
  if (n <= 0) {
    return tree::lazy_(
        [=]() mutable -> LazyDirectLayer::tree { return Ret(r); });
  } else {
    uint64_t m = n - 1;
    return tree::lazy_(
        [=]() mutable -> LazyDirectLayer::tree { return Tau(taus(m, r)); });
  }
}

LazyDirectLayer::tree LazyDirectLayer::ask(uint64_t n, uint64_t acc) {
  if (n <= 0) {
    return Ret(acc);
  } else {
    uint64_t m = n - 1;
    return Vis(m, [=](uint64_t a) { return ask(m, acc + a); });
  }
}

/// The tree t runs to, answering every event with e + 1, within fuel
/// steps.
std::optional<uint64_t> LazyDirectLayer::run(uint64_t fuel,
                                             const LazyDirectLayer::tree &t) {
  if (fuel <= 0) {
    return std::optional<uint64_t>();
  } else {
    uint64_t f = fuel - 1;
    auto &&_sv = observe(t);
    if (crane::holds_alternative<
            typename LazyDirectLayer::treeF<LazyDirectLayer::tree>::RetF>(
            _sv.v())) {
      const auto &[r0] =
          crane::get<
              typename LazyDirectLayer::treeF<LazyDirectLayer::tree>::RetF>(
              _sv.v());
      return std::make_optional<uint64_t>(r0);
    } else if (
        crane::holds_alternative<
            typename LazyDirectLayer::treeF<LazyDirectLayer::tree>::TauF>(
            _sv.v())) {
      const auto &[t0] =
          crane::get<
              typename LazyDirectLayer::treeF<LazyDirectLayer::tree>::TauF>(
              _sv.v());
      return run(f, t0);
    } else if (
        crane::holds_alternative<
            typename LazyDirectLayer::treeF<LazyDirectLayer::tree>::VisF>(
            _sv.v())) {
      const auto &[e0, k0] =
          crane::get<
              typename LazyDirectLayer::treeF<LazyDirectLayer::tree>::VisF>(
              _sv.v());
      return run(f, k0((e0 + 1)));
    } else {
      return std::optional<uint64_t>();
    }
  }
}
