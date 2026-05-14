#include "SepExtNullaryNestedAccess.h"

#include <cassert>

struct MyInner {
  static constexpr unsigned int val() { return 10; }
};

struct MyOuter {
  using I = MyInner;
  static constexpr unsigned int name() { return 32; }
};

int main() {
  using W = SepExtNullaryNestedAccess::Worker<MyOuter>;
  assert(W::get_inner_val() == 10);
  assert(W::get_name() == 32);
  assert(W::sum() == 42);
  return 0;
}
