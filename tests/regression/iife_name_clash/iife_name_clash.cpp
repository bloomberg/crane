#include <iife_name_clash.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
IifeNameClash::double_get(const std::shared_ptr<IifeNameClash::wrapper> &w1,
                          const std::shared_ptr<IifeNameClash::wrapper> &w2) {
  unsigned int x = std::visit(
      Overloaded{[](const typename IifeNameClash::wrapper::Wrap _args)
                     -> unsigned int { return _args.d_n; },
                 [](const typename IifeNameClash::wrapper::Empty _args)
                     -> unsigned int { return 0u; }},
      w1->v());
  unsigned int y = std::visit(
      Overloaded{[](const typename IifeNameClash::wrapper::Wrap _args0)
                     -> unsigned int { return _args0.d_n; },
                 [](const typename IifeNameClash::wrapper::Empty _args0)
                     -> unsigned int { return 0u; }},
      w2->v());
  return (std::move(x) + std::move(y));
}
