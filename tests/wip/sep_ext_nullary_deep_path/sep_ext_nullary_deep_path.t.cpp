#include "SepExtNullaryDeepPath.h"

#include <cassert>

struct MyLeaf {
  static constexpr unsigned int val() { return 7; }
  static constexpr unsigned int extra() { return 3; }
};

struct MyMid {
  using L = MyLeaf;
};

struct MyRoot {
  using M = MyMid;
};

int main() {
  using W = SepExtNullaryDeepPath::Worker<MyRoot>;
  assert(W::deep_val() == 7);
  assert(W::deep_extra() == 3);
  assert(W::deep_sum() == 10);
  return 0;
}
