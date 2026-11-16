#include "local_fixpoint.h"

Monadic::State<bool, std::monostate> Monadic::foo_state() {
  return state_return<bool, std::monostate>(std::monostate{});
}
