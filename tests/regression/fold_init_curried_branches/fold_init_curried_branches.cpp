#include "fold_init_curried_branches.h"

uint64_t FoldInitCurriedBranches::pick(uint64_t n) {
  crane::fn<int64_t(uint64_t, bool)> w =
      List<uint64_t>::nil().template fold_left<
          crane::fn<int64_t(uint64_t, bool)>>(
          [](crane::fn<int64_t(uint64_t, bool)>, uint64_t) {
            return [](uint64_t, bool) { return INT64_C(0); };
          },
          [&]() -> crane::fn<int64_t(uint64_t, bool)> {
            if (n <= 0) {
              return [](uint64_t, bool) { return INT64_C(5); };
            } else {
              uint64_t _x = n - 1;
              return List<bool>::nil().template fold_left<
                  crane::fn<int64_t(uint64_t, bool)>>(
                  [](crane::fn<int64_t(uint64_t, bool)> acc,
                     bool) { return acc; },
                  [](uint64_t, bool) { return INT64_C(7); });
            }
          }());
  auto _once1 = w(UINT64_C(0), true);
  return static_cast<uint64_t>(_once1 < 0 ? 0 : _once1);
}
