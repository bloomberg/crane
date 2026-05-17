#include "rocq_bug_20894.h"

void RocqBug20894::M::fold(const List<Unit> &l) {
  if (std::holds_alternative<typename List<Unit>::Nil>(l.v())) {
    return;
  } else {
    const auto &[a0, a1] = std::get<typename List<Unit>::Cons>(l.v());
    fold(*a1);
    return;
  }
}

RocqBug20894::M::t RocqBug20894::bug() {
  throw std::logic_error(
      "unrealized axiom: "
      "CraneTestsRegression.rocq_bug_20894.RocqBug20894.RocqBug20894.bug");
}
