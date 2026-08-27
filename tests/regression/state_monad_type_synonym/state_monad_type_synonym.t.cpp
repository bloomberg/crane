// A state-monad type synonym makes a definition a value of function type; a
// bare reference to it is a data member, not a nullary call.
#include "state_monad_type_synonym.h"

#include <cassert>
#include <iostream>

int main() {
  assert(StateMonadTypeSynonym::go == 3);
  std::cout << "state_monad_type_synonym: go = " << StateMonadTypeSynonym::go << " PASSED" << std::endl;
  return 0;
}
