#include <reuse_scrutinee_concurrent_unit.h>

#include <cassert>

int main() {
  ReuseScrutineeConcurrentUnit::run(std::monostate{});
  assert(ReuseScrutineeConcurrentUnit::total(std::monostate{}) == 50);
  return 0;
}
