#include "stateT_dict_arg_dropped.h"
#include <cassert>

int main() {
  auto t = StateTDictArgDropped::use(Nat::s(Nat::o()));
  assert(t != nullptr);
  return 0;
}
