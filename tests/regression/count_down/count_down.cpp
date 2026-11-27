#include "count_down.h"

/// Single effect then recurse: effect ;; recursive_call
void CountDown::count_down(uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return;
    } else {
      uint64_t n_ = n - 1;
      std::cout << std::string("tick") << '\n';
      n = n_;
    }
  }
}

/// Two effects then recurse: effect ;; effect ;; recursive_call
void CountDown::two_prints(uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return;
    } else {
      uint64_t n_ = n - 1;
      std::cout <<
      (std::string("step ") + std::to_string(n)).substr(0, 16777211) << '\n';
      std::cout << std::string("---") << '\n';
      n = n_;
    }
  }
}

/// Read from user, echo back, then recurse
void CountDown::echo_loop(uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return;
    } else {
      uint64_t n_ = n - 1;
      std::string line;
      std::getline(std::cin, line);
      std::cout << (std::string("echo: ") + line).substr(0, 16777211) << '\n';
      n = n_;
    }
  }
}

/// Effect in base case too: both branches do IO
void CountDown::announce(uint64_t n) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      std::cout << std::string("done") << '\n';
      return;
    } else {
      uint64_t n_ = n - 1;
      std::cout <<
      (std::string("counting ") + std::to_string(n)).substr(0, 16777211) <<
      '\n';
      n = n_;
    }
  }
}

/// Multiple arguments: two nat params, recurse on first
void CountDown::repeat_msg(uint64_t n, const std::string &msg) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    if (n <= 0) {
      return;
    } else {
      uint64_t n_ = n - 1;
      std::cout << msg << '\n';
      n = n_;
    }
  }
}

void CountDown::run_fixpoint() {
  count_down(UINT64_C(3));
  two_prints(UINT64_C(3));
  echo_loop(UINT64_C(0));
  announce(UINT64_C(2));
  repeat_msg(UINT64_C(2), "hello");
}

/// Helper: compare two strings
bool CountDown::string_eq(std::string_view s1, std::string_view s2) {
  switch (static_cast<Comparison>((s1 < s2) + 2 * (s1 > s2))) {
  case Comparison::EQ: {
    return true;
  }
  default: {
    return false;
  }
  }
}

void CountDown::co_count_down() {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(std::string_view{line}, std::string_view("stop"))) {
      return;
    } else {
      std::cout << std::string("tick") << '\n';
    }
  }
}

void CountDown::co_two_prints() {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(std::string_view{line}, std::string_view("stop"))) {
      return;
    } else {
      std::cout << (std::string("got: ") + line).substr(0, 16777211) << '\n';
      std::cout << std::string("---") << '\n';
    }
  }
}

void CountDown::co_echo_loop() {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(std::string_view{line}, std::string_view("quit"))) {
      return;
    } else {
      std::cout << (std::string("echo: ") + line).substr(0, 16777211) << '\n';
    }
  }
}

void CountDown::co_announce(uint64_t round) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(std::string_view{line}, std::string_view("stop"))) {
      std::cout << std::string("done") << '\n';
      return;
    } else {
      std::cout <<
      (std::string("round ") + std::to_string(round)).substr(0, 16777211) <<
      '\n';
      round = (round + 1);
    }
  }
}

void CountDown::co_repeat(const std::string &msg) {
  // Loop replaces the tail recursion: each recursive call updates the loop
  // variables.
  while (true) {
    std::string line;
    std::getline(std::cin, line);
    if (string_eq(std::string_view{line}, std::string_view("stop"))) {
      return;
    } else {
      std::cout << msg << '\n';
    }
  }
}
