#include "recursive_monadic.h"

/// 1. Simple recursive countdown with effect
unsigned int RecursiveMonadic::countdown(unsigned int n) {
  if (n <= 0) {
    return 0u;
  } else {
    unsigned int n_ = n - 1;
    std::cout << "tick"s << '\n';
    return countdown(n_);
  }
}

/// 2. Recursive sum over list with logging
unsigned int RecursiveMonadic::sum_list(const List<unsigned int> &xs) {
  if (std::holds_alternative<typename List<unsigned int>::Nil>(xs.v())) {
    return 0u;
  } else {
    const auto &[a0, a1] = std::get<typename List<unsigned int>::Cons>(xs.v());
    std::cout << "adding"s << '\n';
    unsigned int s = sum_list(*a1);
    return (a0 + s);
  }
}

/// 3. Recursive collect: transforms each element with effect
List<int64_t> RecursiveMonadic::collect_lengths(const List<std::string> &xs) {
  if (std::holds_alternative<typename List<std::string>::Nil>(xs.v())) {
    return List<int64_t>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<std::string>::Cons>(xs.v());
    std::cout << a0 << '\n';
    List<int64_t> rest_ = collect_lengths(*a1);
    return List<int64_t>::cons(a0.length(), rest_);
  }
}

/// 4. Recursive with two recursive calls (tree-like)
unsigned int RecursiveMonadic::repeat_action(unsigned int n, std::string msg) {
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
List<std::string> RecursiveMonadic::read_n_lines(unsigned int n) {
  if (n <= 0) {
    return List<std::string>::nil();
  } else {
    unsigned int n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    List<std::string> rest = read_n_lines(n_);
    return List<std::string>::cons(line, rest);
  }
}

/// 7. Mutual-like: two functions calling each other via wrapper
std::string RecursiveMonadic::even_action(unsigned int n) {
  if (n <= 0) {
    return "even";
  } else {
    unsigned int n_ = n - 1;
    std::cout << "e"s << '\n';
    return odd_action(n_);
  }
}

std::string RecursiveMonadic::odd_action(unsigned int n) {
  if (n <= 0) {
    return "odd";
  } else {
    unsigned int n_ = n - 1;
    std::cout << "o"s << '\n';
    return even_action(n_);
  }
}
