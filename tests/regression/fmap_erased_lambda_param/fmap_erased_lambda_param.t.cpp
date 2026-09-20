#include "fmap_erased_lambda_param.h"
#include <cassert>

int main() {
  auto r = FmapErasedLambdaParam::go(Nat::s(Nat::o()));
  assert(r.has_value());
  return 0;
}
