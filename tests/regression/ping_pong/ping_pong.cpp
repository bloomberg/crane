#include "ping_pong.h"

/// Check if two strings are equal using PrimString.compare.
bool PingPong::string_eq(std::string_view s1, std::string_view s2) {
  switch (static_cast<Comparison>((s1 < s2) + 2 * (s1 > s2))) {
  case Comparison::EQ: {
    return true;
  }
  default: {
    return false;
  }
  }
}

void PingPong::run_game(uint64_t round) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    std::cout << std::string("ping") << '\n';
    std::string response;
    std::getline(std::cin, response);
    if (string_eq(std::string_view{response}, std::string_view("pong"))) {
      std::cout <<
      ((std::string("  (round ") +
        (std::to_string(round) + std::string(" complete)")).substr(0,
                                                                   16777211))
           .substr(0, 16777211)) <<
      '\n';
      round = (round + 1);
    } else {
      std::cout <<
      ((std::string("You said '") + (response +
                                     std::string("' \342\200\224 game over!"))
                                        .substr(0, 16777211))
           .substr(0, 16777211)) <<
      '\n';
      return;
    }
  }
}

/// Entry point.
void PingPong::play() { run_game(UINT64_C(1)); }
