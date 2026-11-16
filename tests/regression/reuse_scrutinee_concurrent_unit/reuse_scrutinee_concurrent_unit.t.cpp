#include <reuse_scrutinee_concurrent_unit.h>

#include <cassert>

int main() {
  ReuseScrutineeConcurrentUnit::run();
  assert(ReuseScrutineeConcurrentUnit::total() == 50);
  return 0;
}
