#include "func_inline.h"

Monadic::State<bool, std::monostate> Monadic::foo_state(std::monostate) {
  return state_return<bool, std::monostate>(std::monostate{});
}
