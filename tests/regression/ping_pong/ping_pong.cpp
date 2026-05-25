#include "ping_pong.h"

/// Check if two strings are equal using PrimString.compare.
bool PingPong::string_eq(std::string s1, std::string s2) {
  switch ((s1 == s2 ? Comparison::EQ
                    : (s1 < s2 ? Comparison::LT : Comparison::GT))) {
  case Comparison::EQ: {
    return true;
  }
  default: {
    return false;
  }
  }
}

void PingPong::run_game(uint64_t round) {
  uint64_t _loop_round = std::move(round);
  while (true) {
    std::cout << "ping"s << '\n';
    std::string response;
    std::getline(std::cin, response);
    if (string_eq(response, "pong")) {
      std::cout << "  (round "s + std::to_string(_loop_round) + " complete)"s
                << '\n';
      _loop_round = (_loop_round + 1);
    } else {
      std::cout << "You said '"s + response + "' — game over!"s << '\n';
      return;
    }
  }
  return;
}

/// Entry point.
void PingPong::play() {
  run_game(UINT64_C(1));
  return;
}
