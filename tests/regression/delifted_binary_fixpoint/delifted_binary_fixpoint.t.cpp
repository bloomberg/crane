#include <cassert>
#include <delifted_binary_fixpoint.h>

int main() {
  Positive four = Positive::xo(Positive::xo(Positive::xh()));
  Positive five = Positive::xi(Positive::xo(Positive::xh()));
  assert(DeliftedBinaryFixpoint::same(four, four));
  assert(!DeliftedBinaryFixpoint::same(four, five));
  return 0;
}
