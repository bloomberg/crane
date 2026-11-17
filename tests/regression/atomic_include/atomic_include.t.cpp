#include <atomic_include.h>

#include <cassert>

int main() {
  assert(AtomicInclude::sample == 3);
  return 0;
}
