#include <ping_pong.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// Check if two strings are equal using PrimString.compare.
__attribute__((pure)) bool PingPong::string_eq(const std::string s1,
                                               const std::string s2) {
  switch ((s1 == s2 ? Comparison::e_EQ
                    : (s1 < s2 ? Comparison::e_LT : Comparison::e_GT))) {
  case Comparison::e_EQ: {
    return true;
  }
  default: {
    return false;
  }
  }
}

void PingPong::run_game(unsigned int round) {
  unsigned int _loop_round = std::move(round);
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
  run_game(1u);
  return;
}
