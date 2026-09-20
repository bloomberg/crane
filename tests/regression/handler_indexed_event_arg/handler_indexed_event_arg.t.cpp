#include "handler_indexed_event_arg.h"
#include <cassert>

struct P {
  static Nat width() { return Nat::o(); }
};

int main() {
  auto t = HandlerIndexedEventArg::go<P>(Nat::s(Nat::o()));
  assert(t);
  return 0;
}
