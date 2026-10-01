#include <cassert>
#include <lifted_spec_before_class_concept.h>

int main() {
  const auto &r = LiftedSpecBeforeClassConcept::run;
  assert(std::holds_alternative<typename Nat::S>(r.a0.v()));
  return 0;
}
