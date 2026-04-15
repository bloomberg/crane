#include <mutual_mod.h>

#include <memory>
#include <type_traits>
#include <utility>
#include <variant>

__attribute__((pure)) unsigned int
EvenOdd::even_length(const std::shared_ptr<EvenOdd::even_list> &e) {
  if (std::holds_alternative<typename EvenOdd::even_list::ENil>(e->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename EvenOdd::even_list::ECons>(e->v());
    return (odd_length(d_a1) + 1);
  }
}

__attribute__((pure)) unsigned int
EvenOdd::odd_length(const std::shared_ptr<EvenOdd::odd_list> &o) {
  const auto &[d_a0, d_a1] =
      std::get<typename EvenOdd::odd_list::OCons>(o->v());
  return (even_length(d_a1) + 1);
}
