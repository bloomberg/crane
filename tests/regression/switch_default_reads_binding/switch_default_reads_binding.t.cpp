#include <cassert>
#include <switch_default_reads_binding.h>

using C = SwitchDefaultReadsBinding::Color;

int main() {
  auto red = SwitchDefaultReadsBinding::pick(C::RED);
  assert(red.a == C::RED && red.b == C::RED);
  auto blue = SwitchDefaultReadsBinding::pick(C::BLUE);
  assert(blue.a == C::GREEN && blue.b == C::GREEN);
  return 0;
}
