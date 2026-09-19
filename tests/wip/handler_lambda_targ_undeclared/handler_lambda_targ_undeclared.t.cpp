#include "handler_lambda_targ_undeclared.h"
#include <cassert>

struct P {
  static Nat width() { return Nat::o(); }
};

int main() {
  auto t = HandlerLambdaTargUndeclared::go<P>(Nat::s(Nat::o()));
  assert(t);
  return 0;
}
