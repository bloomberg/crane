#include <cassert>
#include <alias_phantom_param_before_promoted.h>

int main() {
  assert(std::holds_alternative<Nat::O>(AliasPhantomParamBeforePromoted::run.v()));
  return 0;
}
