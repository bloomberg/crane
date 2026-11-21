#include "fold_init_curried_branches.h"

uint64_t FoldInitCurriedBranches::pick(uint64_t n) {
  auto _lc1_pa1 = List<uint64_t>::nil();
  auto _lc1_pa2 = [&]() -> crane::fn<crane::fn<int64_t(bool)>(uint64_t)> {
    if (n <= 0) {
      return [](uint64_t) {
        return [](bool) { return INT64_C(5); };
      };
    } else {
      uint64_t _x = n - 1;
      auto _lc1_pa1 = List<bool>::nil();
      return [=](uint64_t _x0) {
        return [=](bool _x1) -> int64_t {
          return _lc1_pa1.template fold_left<
              crane::fn<crane::fn<int64_t(bool)>(uint64_t)>>(
              [](crane::fn<crane::fn<int64_t(bool)>(uint64_t)> acc,
                 bool) { return acc; },
              [](uint64_t) {
                return [](bool) { return INT64_C(7); };
              })(_x0)(_x1);
        };
      };
    }
  }();
  crane::fn<int64_t(uint64_t, bool)> w =
      [=](uint64_t _x0, bool _x1) -> int64_t {
        return _lc1_pa1.template fold_left<
            crane::fn<crane::fn<int64_t(bool)>(uint64_t)>>(
            [](crane::fn<crane::fn<int64_t(bool)>(uint64_t)>, uint64_t) {
              return [](uint64_t) {
                return [](bool) { return INT64_C(0); };
              };
            },
            _lc1_pa2)(_x0)(_x1);
      };
  auto _once1 = w(UINT64_C(0), true);
  return static_cast<uint64_t>(_once1 < 0 ? 0 : _once1);
}
