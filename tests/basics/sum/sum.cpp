#include <sum.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int Sum::either_to_nat(
    const std::shared_ptr<Sum::either<unsigned int, unsigned int>> &e) {
  return std::visit(
      Overloaded{
          [](const typename Sum::either<unsigned int, unsigned int>::Left _args)
              -> unsigned int { return _args.d_a0; },
          [](const typename Sum::either<unsigned int, unsigned int>::Right
                 _args) -> unsigned int { return _args.d_a0; }},
      e->v());
}
