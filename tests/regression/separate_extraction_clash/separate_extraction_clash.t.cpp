#include <SepClashA.h>
#include <SepClashB.h>

#include <cassert>

int main() {
  // Both modules define clash_add, but namespaces prevent collision
  assert(SepClashA::clash_add(3u, 4u) == 7u);
  assert(SepClashB::clash_add(3u, 4u) == 8u);

  assert(SepClashA::only_a(5u) == 6u);
  assert(SepClashB::only_b(5u) == 7u);

  return 0;
}
