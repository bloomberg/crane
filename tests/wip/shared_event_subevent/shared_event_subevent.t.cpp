#include <shared_event_subevent.h>

#include <cassert>
#include <iostream>

int main() {
  assert(SharedEventSubevent::ok);
  std::cout << "shared_event_subevent: ok" << std::endl;
  return 0;
}
