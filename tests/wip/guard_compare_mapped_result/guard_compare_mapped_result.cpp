#include "guard_compare_mapped_result.h"

bool GuardCompareMappedResult::eqt(const GuardCompareMappedResult::tree &a,
                                   const GuardCompareMappedResult::tree &b) {
  if (&b == &a) {
    return Bool::TRUE_;
  } else {
    if (std::holds_alternative<typename GuardCompareMappedResult::tree::Leaf>(
            a.v())) {
      if (std::holds_alternative<typename GuardCompareMappedResult::tree::Leaf>(
              b.v())) {
        return true;
      } else {
        return false;
      }
    } else {
      const auto &[a0, a1, a2] =
          std::get<typename GuardCompareMappedResult::tree::Node>(a.v());
      if (std::holds_alternative<typename GuardCompareMappedResult::tree::Leaf>(
              b.v())) {
        return false;
      } else {
        const auto &[a00, a10, a20] =
            std::get<typename GuardCompareMappedResult::tree::Node>(b.v());
        return ((eqt(*a0, *a00) && a1 == a10) && eqt(*a2, *a20));
      }
    }
  }
}
