#include "method_returns_function_alias.h"

MethodReturnsFunctionAlias::pred<Nat>
MethodReturnsFunctionAlias::always(bool b) {
  return [=](Nat) { return b; };
}
