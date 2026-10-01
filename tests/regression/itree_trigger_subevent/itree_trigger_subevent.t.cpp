#include <itree_trigger_subevent.h>

#include <cassert>
#include <iostream>

int main() {
  // trigger (Foo 2) is a Vis whose event is inl1 (Foo 2).
  assert(ItreeTriggerSubevent::is_foo_two);
  std::cout << "itree_trigger_subevent: ok" << std::endl;
  return 0;
}
