#include <optional_self_deep_copy.h>

#include <cassert>
#include <iostream>

namespace {

OptionalSelfDeepCopy::chain make_chain(uint64_t n) {
  OptionalSelfDeepCopy::chain x = OptionalSelfDeepCopy::chain::stop();
  while (n > 0) {
    x = OptionalSelfDeepCopy::chain::more(std::make_optional(std::move(x)));
    --n;
  }
  return x;
}

} // namespace

int main() {
  auto small = make_chain(10);
  auto copied_small = OptionalSelfDeepCopy::dup_chain(small);
  (void)copied_small;

  // Deeper chains would require iterative destructors for
  // optional<shared_ptr<chain>> fields (loopify doesn't yet handle
  // argument-level-wrapped pointer fields iteratively).
  auto deep = make_chain(1000);
  std::cout << "built deep optional self value" << std::endl;
  auto copied = OptionalSelfDeepCopy::dup_chain(deep);
  std::cout << "copied deep optional self value" << std::endl;
  (void)copied;
  return 0;
}
