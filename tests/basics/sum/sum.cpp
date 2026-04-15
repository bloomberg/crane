#include <sum.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int Sum::either_to_nat(
    const std::shared_ptr<Sum::either<unsigned int, unsigned int>> &e) {
  if (std::holds_alternative<
          typename Sum::either<unsigned int, unsigned int>::Left>(e->v())) {
    const auto &_m =
        *std::get_if<typename Sum::either<unsigned int, unsigned int>::Left>(
            &e->v());
    return _m.d_a0;
  } else {
    const auto &_m =
        *std::get_if<typename Sum::either<unsigned int, unsigned int>::Right>(
            &e->v());
    return _m.d_a0;
  }
}
