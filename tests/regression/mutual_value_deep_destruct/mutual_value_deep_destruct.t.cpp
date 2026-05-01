#include <mutual_value_deep_destruct.h>

#include <iostream>

namespace {

MutualValueDeepDestruct::a make_chain(unsigned int n) {
  MutualValueDeepDestruct::a x = MutualValueDeepDestruct::a::aend();
  while (n > 0) {
    x = MutualValueDeepDestruct::a::anode(
        true, MutualValueDeepDestruct::b::bnode(std::move(x)));
    --n;
  }
  return x;
}

} // namespace

int main() {
  {
    auto deep = make_chain(200000);
    std::cout << "built deep mutual value" << std::endl;
  }
  std::cout << "destroyed deep mutual value" << std::endl;
  return 0;
}
