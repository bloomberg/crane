// WIP: this test does not build yet.
//
// A state-monad type synonym (`st A := nat -> (A * nat)`) used through `bind`
// produces a call with the wrong arity on the `std::function` synonym.
#include "state_monad_type_synonym.h"

#include <cassert>
#include <iostream>

int main() {
  assert(StateMonadTypeSynonym::go == 3);
  std::cout << "state_monad_type_synonym: go = " << StateMonadTypeSynonym::go << " PASSED" << std::endl;
  return 0;
}
