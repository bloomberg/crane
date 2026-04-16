#include <recursive_monadic.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. Simple recursive countdown with effect
unsigned int RecursiveMonadic::countdown(const unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    std::cout << "tick"s << '\n';
    return countdown(n_);
  }
}

/// 2. Recursive sum over list with logging
unsigned int
RecursiveMonadic::sum_list(const std::shared_ptr<List<unsigned int>> &xs) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(xs->v())) {
    return 0u;
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<unsigned int>::Cons>(xs->v());
    std::cout << "adding"s << '\n';
    unsigned int s = sum_list(d_a1);
    return (d_a0 + s);
  }
}

/// 3. Recursive collect: transforms each element with effect
std::shared_ptr<List<int64_t>> RecursiveMonadic::collect_lengths(
    const std::shared_ptr<List<std::string>> &xs) {
  if (std::holds_alternative<typename List<std::string>::Nil>(xs->v())) {
    return List<int64_t>::nil();
  } else {
    const auto &[d_a0, d_a1] =
        std::get<typename List<std::string>::Cons>(xs->v());
    std::cout << d_a0 << '\n';
    std::shared_ptr<List<int64_t>> rest_ = collect_lengths(d_a1);
    return List<int64_t>::cons(d_a0.length(), rest_);
  }
}

/// 4. Recursive with two recursive calls (tree-like)
unsigned int RecursiveMonadic::repeat_action(const unsigned int n,
                                             const std::string msg) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    std::cout << msg << '\n';
    unsigned int r = repeat_action(n_, msg);
    return (r + 1);
  }
}

/// 6. Recursive with block template in each step
std::shared_ptr<List<std::string>>
RecursiveMonadic::read_n_lines(const unsigned int n) {
  if (n <= 0) {
    return List<std::string>::nil();
  } else {
    unsigned int n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    std::shared_ptr<List<std::string>> rest = read_n_lines(n_);
    return List<std::string>::cons(line, rest);
  }
}

/// 7. Mutual-like: two functions calling each other via wrapper
std::string RecursiveMonadic::even_action(const unsigned int n) {
  if (n <= 0) {
    return "even";
  } else {
    unsigned int n_ = n - 1;
    std::cout << "e"s << '\n';
    return odd_action(n_);
  }
}

std::string RecursiveMonadic::odd_action(const unsigned int n) {
  if (n <= 0) {
    return "odd";
  } else {
    unsigned int n_ = n - 1;
    std::cout << "o"s << '\n';
    return even_action(n_);
  }
}
