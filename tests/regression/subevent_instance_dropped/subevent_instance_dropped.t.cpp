#include <subevent_instance_dropped.h>

#include <cassert>

int main() {
  // [boom] triggers and never returns a value; building the tree is enough.
  auto t = SubeventInstanceDropped::use(Nat::s(Nat::o()));
  assert(t != nullptr);
  return 0;
}
