#include "recursive_monadic.h"

uint64_t RecursiveMonadic::countdown(uint64_t n) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    std::cout << "tick"s << '\n';
    return countdown(n_);
  }
}

uint64_t RecursiveMonadic::sum_list(const List<uint64_t> &xs) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v());
    std::cout << "adding"s << '\n';
    uint64_t s = sum_list(*a1);
    return (a0 + s);
  }
}

List<int64_t> RecursiveMonadic::collect_lengths(const List<std::string> &xs) {
  if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
    return List<int64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(xs.v());
    std::cout << a0 << '\n';
    List<int64_t> rest_ = collect_lengths(*a1);
    return List<int64_t>::cons(static_cast<int64_t>(a0.length()), rest_);
  }
}

uint64_t RecursiveMonadic::repeat_action(uint64_t n, std::string msg) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t n_ = n - 1;
    std::cout << msg << '\n';
    uint64_t r = repeat_action(n_, msg);
    return (r + 1);
  }
}

List<std::string> RecursiveMonadic::read_n_lines(uint64_t n) {
  if (n <= 0) {
    return List<std::string>::nil();
  } else {
    uint64_t n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    List<std::string> rest = read_n_lines(n_);
    return List<std::string>::cons(line, rest);
  }
}

std::string RecursiveMonadic::even_action(uint64_t n) {
  if (n <= 0) {
    return "even";
  } else {
    uint64_t n_ = n - 1;
    std::cout << "e"s << '\n';
    return odd_action(n_);
  }
}

std::string RecursiveMonadic::odd_action(uint64_t n) {
  if (n <= 0) {
    return "odd";
  } else {
    uint64_t n_ = n - 1;
    std::cout << "o"s << '\n';
    return even_action(n_);
  }
}
