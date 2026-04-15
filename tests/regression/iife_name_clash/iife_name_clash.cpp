#include <iife_name_clash.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
IifeNameClash::double_get(const std::shared_ptr<IifeNameClash::wrapper> &w1,
                          const std::shared_ptr<IifeNameClash::wrapper> &w2) {
  unsigned int x = [&]() {
    if (std::holds_alternative<typename IifeNameClash::wrapper::Wrap>(
            w1->v())) {
      const auto &[d_n] =
          std::get<typename IifeNameClash::wrapper::Wrap>(w1->v());
      return d_n;
    } else {
      return 0u;
    }
  }();
  unsigned int y = [&]() {
    if (std::holds_alternative<typename IifeNameClash::wrapper::Wrap>(
            w2->v())) {
      const auto &[d_n0] =
          std::get<typename IifeNameClash::wrapper::Wrap>(w2->v());
      return d_n0;
    } else {
      return 0u;
    }
  }();
  return (x + y);
}
