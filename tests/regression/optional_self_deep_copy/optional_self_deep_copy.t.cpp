#include <optional_self_deep_copy.h>

#include <cassert>
#include <iostream>

namespace {

OptionalSelfDeepCopy::chain make_chain(uint64_t n) {
  OptionalSelfDeepCopy::chain x = OptionalSelfDeepCopy::chain::stop();
  while (n > 0) {
    x = OptionalSelfDeepCopy::chain::more(
        std::make_optional(std::make_unique<OptionalSelfDeepCopy::chain>(
            std::move(x))));
    --n;
  }
  return x;
}

} // namespace

int main() {
  auto small = make_chain(10);
  auto copied_small = OptionalSelfDeepCopy::dup_chain(small);
  (void)copied_small;

  auto deep = make_chain(200000);
  std::cout << "built deep optional self value" << std::endl;
  auto copied = OptionalSelfDeepCopy::dup_chain(deep);
  std::cout << "copied deep optional self value" << std::endl;
  (void)copied;
  return 0;
}
