#include <cassert>
#include <record_param_out_of_line.h>

int main() {
  using M = RecordParamOutOfLine;
  assert(M::large == M::Bag::Kind::LARGE);
  assert(M::Bag::classify(M::Bag{Nat::o(), false}) == M::Bag::Kind::SMALL);
  return 0;
}
