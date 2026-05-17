#include <mutual_value_deep_copy.h>

#include <cassert>
#include <iostream>

namespace {

MutualValueDeepCopy::a make_chain(uint64_t n) {
  MutualValueDeepCopy::a x = MutualValueDeepCopy::a::aend();
  while (n > 0) {
    x = MutualValueDeepCopy::a::anode(
        true, MutualValueDeepCopy::b::bnode(std::move(x)));
    --n;
  }
  return x;
}

} // namespace

int main() {
  auto small = make_chain(10);
  assert(MutualValueDeepCopy::reaches_end_a(small));
  assert(MutualValueDeepCopy::copied_reaches_end(small));

  auto deep = make_chain(200000);
  std::cout << "built deep mutual value" << std::endl;
  auto copied = MutualValueDeepCopy::dup_a(deep);
  std::cout << "copied deep mutual value" << std::endl;
  assert(MutualValueDeepCopy::reaches_end_a(copied.first));
  assert(MutualValueDeepCopy::reaches_end_a(copied.second));
  return 0;
}
