#include "iife_name_clash.h"

uint64_t IifeNameClash::double_get(const IifeNameClash::wrapper &w1,
                                   const IifeNameClash::wrapper &w2) {
  uint64_t x = [&]() {
    if (std::holds_alternative<typename IifeNameClash::wrapper::Wrap>(w1.v())) {
      const auto &[n0] =
          std::get<typename IifeNameClash::wrapper::Wrap>(w1.v());
      return n0;
    } else {
      return UINT64_C(0);
    }
  }();
  uint64_t y = [&]() {
    if (std::holds_alternative<typename IifeNameClash::wrapper::Wrap>(w2.v())) {
      const auto &[n0] =
          std::get<typename IifeNameClash::wrapper::Wrap>(w2.v());
      return n0;
    } else {
      return UINT64_C(0);
    }
  }();
  return (x + y);
}
