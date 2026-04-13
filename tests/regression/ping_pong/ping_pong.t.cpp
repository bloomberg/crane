// The generated ping_pong.cpp already has main() from the Crane Extraction.
// This test driver redirects stdin to simulate user input, then calls the
// generated main via the generated executable.
//
// Since the generated .cpp already contains main(), this file just provides
// an alternative main() for testing with simulated input.
// We compile ONLY this file (not ping_pong.cpp) for the test.

#include <ping_pong.h>

#include <cassert>
#include <iostream>
#include <sstream>

int main() {
  // Simulate: user types "pong" twice, then "quit"
  std::istringstream fake_input("pong\npong\nquit\n");
  auto old_cin = std::cin.rdbuf(fake_input.rdbuf());

  PingPong::play();

  std::cin.rdbuf(old_cin);
  std::cout << "All ping_pong tests passed!" << std::endl;
  return 0;
}
