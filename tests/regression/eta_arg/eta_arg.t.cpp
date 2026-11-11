#include <eta_arg.h>

#include <cassert>

int main() {
  List<uint64_t> l = List<uint64_t>::nil();
  for (uint64_t i = 4; i >= 1; --i)
    l = List<uint64_t>::cons(i, l);
  uint64_t r = EtaArg::total(l);
  assert(r == 1 + 2 + 3 + 4 + 4 * 4);
  assert(eta_ticks == 1);
  return 0;
}
