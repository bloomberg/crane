#include "value_family_over_mapped_container.h"

uint64_t
ValueFamilyOverMappedContainer::sz(const ValueFamilyOverMappedContainer::ty &t,
                                   ValueFamilyOverMappedContainer::den n) {
  if (std::holds_alternative<typename ValueFamilyOverMappedContainer::ty::TNat>(
          t.v())) {
    return crane::any_cast<uint64_t>(std::move(n));
  } else {
    const auto &[a0] =
        std::get<typename ValueFamilyOverMappedContainer::ty::TOpt>(t.v());
    auto _cs = crane::any_cast<std::optional<crane::obj>>(std::move(n));
    if (_cs.has_value()) {
      const auto &x = *_cs;
      return (sz(*a0, x) + 1);
    } else {
      return UINT64_C(0);
    }
  }
}

ValueFamilyOverMappedContainer::den
ValueFamilyOverMappedContainer::mk(uint64_t n) {
  return std::make_optional<crane::obj>(crane::obj(n));
}
