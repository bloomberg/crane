#include <unapplied_subevent_handler.h>

#include <cassert>
#include <iostream>

int main() {
  assert(UnappliedSubeventHandler::is_five);
  std::cout << "unapplied_subevent_handler: ok" << std::endl;
  return 0;
}
