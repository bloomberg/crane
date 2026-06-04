#include <pair_self_deep_copy.h>

#include <iostream>
#include <utility>

namespace {

PairSelfDeepCopy::chain make_chain(uint64_t n) {
  PairSelfDeepCopy::chain x = PairSelfDeepCopy::chain::stop();
  while (n > 0) {
    x = PairSelfDeepCopy::chain::link(std::make_pair(std::move(x), true));
    --n;
  }
  return x;
}

} // namespace

int main() {
  auto small = make_chain(10);
  auto copied_small = PairSelfDeepCopy::dup_chain(small);
  (void)copied_small;

  // Deeper chains would require iterative destructors for
  // pair<shared_ptr<chain>, bool> fields (loopify doesn't yet handle
  // argument-level-wrapped pointer fields iteratively).
  auto deep = make_chain(1000);
  std::cout << "built deep pair self value" << std::endl;
  auto copied = PairSelfDeepCopy::dup_chain(deep);
  std::cout << "copied deep pair self value" << std::endl;
  (void)copied;
  return 0;
}
