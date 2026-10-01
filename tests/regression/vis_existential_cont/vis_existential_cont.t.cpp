#include <vis_existential_cont.h>

#include <cassert>
#include <iostream>

int main() {
  // Ask 2 answered with 2, continuation returns S 2.
  assert(VisExistentialCont::is_three);
  std::cout << "vis_existential_cont: ok" << std::endl;
  return 0;
}
