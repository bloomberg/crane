#include "sequential_monad_alias.h"

#include <cstdlib>
#include <iostream>
#include <sstream>
#include <string>

int main() {
  using M = SequentialMonadAlias;
  std::ostringstream out;
  std::streambuf *saved = std::cout.rdbuf(out.rdbuf());
  M::both();
  M::both();
  std::cout.rdbuf(saved);
  // Each performance runs both prints; none ran while the program started.
  if (out.str() != "aliased\ndirect\naliased\ndirect\n") {
    std::cerr << "unexpected output: " << out.str();
    return EXIT_FAILURE;
  }
  return EXIT_SUCCESS;
}
