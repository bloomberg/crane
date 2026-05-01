#include <pair_self_deep_copy.h>

#include <iostream>
#include <utility>

namespace {

PairSelfDeepCopy::chain make_chain(unsigned int n) {
  PairSelfDeepCopy::chain x = PairSelfDeepCopy::chain::stop();
  while (n > 0) {
    x = PairSelfDeepCopy::chain::link(
        std::make_pair(std::make_unique<PairSelfDeepCopy::chain>(std::move(x)),
                       true));
    --n;
  }
  return x;
}

} // namespace

int main() {
  auto small = make_chain(10);
  auto copied_small = PairSelfDeepCopy::dup_chain(small);
  (void)copied_small;

  auto deep = make_chain(200000);
  std::cout << "built deep pair self value" << std::endl;
  auto copied = PairSelfDeepCopy::dup_chain(deep);
  std::cout << "copied deep pair self value" << std::endl;
  (void)copied;
  return 0;
}
