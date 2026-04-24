#include <rocq_bug_20894.h>

#include <concepts>
#include <functional>
#include <memory>
#include <stdexcept>
#include <type_traits>
#include <utility>
#include <variant>

void RocqBug20894::M::fold(const List<Unit> &l) {
  if (std::holds_alternative<typename List<Unit>::Nil>(l.v())) {
    return;
  } else {
    const auto &[d_a0, d_a1] = std::get<typename List<Unit>::Cons>(l.v());
    fold(*(d_a1));
    return;
  }
}

RocqBug20894::M::t RocqBug20894::bug() {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.rocq_bug_20894.RocqBug20894.RocqBug20894.bug");
}
