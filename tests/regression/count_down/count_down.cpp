#include <count_down.h>

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// Single effect then recurse: effect ;; recursive_call
void CountDown::count_down(const unsigned int &n) {
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return;
    } else {
      unsigned int n_ = _loop_n - 1;
      std::cout << "tick"s << '\n';
      _loop_n = n_;
    }
  }
  return;
}

/// Two effects then recurse: effect ;; effect ;; recursive_call
void CountDown::two_prints(const unsigned int &n) {
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return;
    } else {
      unsigned int n_ = _loop_n - 1;
      std::cout << "step "s + std::to_string(_loop_n) << '\n';
      std::cout << "---"s << '\n';
      _loop_n = n_;
    }
  }
  return;
}

/// Read from user, echo back, then recurse
void CountDown::echo_loop(const unsigned int &n) {
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return;
    } else {
      unsigned int n_ = _loop_n - 1;
      std::string line;
      std::getline(std::cin, line);
      std::cout << "echo: "s + line << '\n';
      _loop_n = n_;
    }
  }
  return;
}

/// Effect in base case too: both branches do IO
void CountDown::announce(const unsigned int &n) {
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      std::cout << "done"s << '\n';
      return;
    } else {
      unsigned int n_ = _loop_n - 1;
      std::cout << "counting "s + std::to_string(_loop_n) << '\n';
      _loop_n = n_;
    }
  }
  return;
}

/// Multiple arguments: two nat params, recurse on first
void CountDown::repeat_msg(const unsigned int &n, const std::string msg) {
  unsigned int _loop_n = n;
  while (true) {
    if (_loop_n <= 0) {
      return;
    } else {
      unsigned int n_ = _loop_n - 1;
      std::cout << msg << '\n';
      _loop_n = n_;
    }
  }
  return;
}

void CountDown::run_fixpoint() {
  count_down(3u);
  two_prints(3u);
  echo_loop(0u);
  announce(2u);
  repeat_msg(2u, "hello");
  return;
}

/// Helper: compare two strings
__attribute__((pure)) bool CountDown::string_eq(const std::string s1,
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

void CountDown::co_count_down() {
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(line, "stop")) {
      return;
    } else {
      std::cout << "tick"s << '\n';
    }
  }
  return;
}

void CountDown::co_two_prints() {
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(line, "stop")) {
      return;
    } else {
      std::cout << "got: "s + line << '\n';
      std::cout << "---"s << '\n';
    }
  }
  return;
}

void CountDown::co_echo_loop() {
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(line, "quit")) {
      return;
    } else {
      std::cout << "echo: "s + line << '\n';
    }
  }
  return;
}

void CountDown::co_announce(unsigned int round) {
  unsigned int _loop_round = std::move(round);
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(line, "stop")) {
      std::cout << "done"s << '\n';
      return;
    } else {
      std::cout << "round "s + std::to_string(_loop_round) << '\n';
      _loop_round = (_loop_round + 1);
    }
  }
  return;
}

void CountDown::co_repeat(const std::string msg) {
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(line, "stop")) {
      return;
    } else {
      std::cout << msg << '\n';
    }
  }
  return;
}
