#include <list_self_deep_copy.h>

#include <iostream>

namespace {

ListSelfDeepCopy::chain make_chain(uint64_t n) {
  ListSelfDeepCopy::chain x = ListSelfDeepCopy::chain::stop();
  while (n > 0) {
    x = ListSelfDeepCopy::chain::link(
        List<ListSelfDeepCopy::chain>::cons(
            std::move(x), List<ListSelfDeepCopy::chain>::nil()));
    --n;
  }
  return x;
}

} // namespace

int main() {
  auto small = make_chain(10);
  auto copied_small = ListSelfDeepCopy::dup_chain(small);
  (void)copied_small;

  auto deep = make_chain(200000);
  std::cout << "built deep list self value" << std::endl;
  auto copied = ListSelfDeepCopy::dup_chain(deep);
  std::cout << "copied deep list self value" << std::endl;
  (void)copied;
  return 0;
}
