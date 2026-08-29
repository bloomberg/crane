#include "fold_closure_build.h"

uint64_t
FoldClosureBuild::compose_adders(const FoldClosureBuild::mylist<uint64_t> &l,
                                 uint64_t _x0) {
  return fold_left<std::function<uint64_t(uint64_t)>, uint64_t>(
      [](std::function<uint64_t(uint64_t)> acc,
         uint64_t h) -> std::function<uint64_t(uint64_t)> {
        return [=](uint64_t x) mutable { return acc((h + x)); };
      },
      [](uint64_t x) { return x; }, l)(_x0);
}

FoldClosureBuild::mylist<std::function<uint64_t(uint64_t)>>
FoldClosureBuild::collect_adders(const FoldClosureBuild::mylist<uint64_t> &l) {
  return fold_left<FoldClosureBuild::mylist<std::function<uint64_t(uint64_t)>>,
                   uint64_t>(
      [](FoldClosureBuild::mylist<std::function<uint64_t(uint64_t)>> acc,
         uint64_t h) {
        return mylist<std::function<uint64_t(uint64_t)>>::mycons(
            [=](uint64_t x) mutable { return (h + x); }, acc);
      },
      mylist<std::function<uint64_t(uint64_t)>>::mynil(), l);
}

uint64_t FoldClosureBuild::apply_all(
    const FoldClosureBuild::mylist<std::function<uint64_t(uint64_t)>> &fns,
    uint64_t x) {
  if (std::holds_alternative<typename FoldClosureBuild::mylist<
          std::function<uint64_t(uint64_t)>>::Mynil>(fns.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename FoldClosureBuild::mylist<
        std::function<uint64_t(uint64_t)>>::Mycons>(fns.v());
    return (a0(x) + apply_all(*a1, x));
  }
}

uint64_t
FoldClosureBuild::compose_with_fix(const FoldClosureBuild::mylist<uint64_t> &l,
                                   uint64_t _x0) {
  return fold_left<std::function<uint64_t(uint64_t)>, uint64_t>(
      [](std::function<uint64_t(uint64_t)> acc, uint64_t h) {
        auto go_impl = [=](auto &_self_go, uint64_t x) mutable -> uint64_t {
          if (x <= 0) {
            return acc(h);
          } else {
            uint64_t x_ = x - 1;
            return (_self_go(_self_go, x_) + 1);
          }
        };
        auto go = [=](uint64_t x) mutable -> uint64_t {
          return go_impl(go_impl, x);
        };
        return go;
      },
      [](uint64_t x) { return x; }, l)(_x0);
}
