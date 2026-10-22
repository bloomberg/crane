#include "family_with_type_binder_at_function.h"

uint64_t FamilyWithTypeBinderAtFunction::use2(uint64_t x0_) {
  static const auto app2_1 =
      crane::immortal(app2<crane::fn<uint64_t(uint64_t)>>(
          [](uint64_t n) { return [=](uint64_t x) { return (x + n); }; },
          UINT64_C(4)));
  return app2_1(x0_);
}

uint64_t FamilyWithTypeBinderAtFunction::clos(const List<uint64_t> &l,
                                              uint64_t x0_) {
  return grect<crane::fn<uint64_t(uint64_t)>, uint64_t>(
      []() { return [](uint64_t x) { return x; }; }(),
      [](const auto &, const auto &, crane::fn<uint64_t(uint64_t)> k) {
        return
            [=, k = std::move(k)](uint64_t x) { return k((x + UINT64_C(1))); };
      },
      l)(x0_);
}
