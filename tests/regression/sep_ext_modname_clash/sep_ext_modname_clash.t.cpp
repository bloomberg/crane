#include <BarFoo.h>
#include <BazFoo.h>

#include <cassert>

int main() {
  // Both modules are named Foo.v but live under different parent paths
  // (Bar/Foo.v and Baz/Foo.v). The collision is resolved by qualifying
  // with the parent: BarFoo and BazFoo.
  assert(BarFoo::bar_add(3u, 4u) == 7u);
  assert(BazFoo::baz_add(3u, 4u) == 8u);

  assert(BarFoo::bar_only(5u) == 6u);
  assert(BazFoo::baz_only(5u) == 7u);

  return 0;
}
