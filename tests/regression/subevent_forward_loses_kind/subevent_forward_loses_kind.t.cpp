#include "subevent_forward_loses_kind.h"
#include <cassert>

int main() {
  assert(std::holds_alternative<Nat::O>(SubeventForwardLosesKind::run.v()));
  return 0;
}
