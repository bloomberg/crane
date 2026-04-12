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
  return std::visit(
      Overloaded{
          [](const typename List<unsigned int>::Nil &) -> unsigned int {
            return 0u;
          },
          [](const typename List<unsigned int>::Cons &_args) -> unsigned int {
            std::cout << "adding"s << '\n';
            unsigned int s = sum_list(_args.d_a1);
            return (_args.d_a0 + s);
          }},
      xs->v());
}

/// 3. Recursive collect: transforms each element with effect
std::shared_ptr<List<int64_t>> RecursiveMonadic::collect_lengths(
    const std::shared_ptr<List<std::string>> &xs) {
  return std::visit(Overloaded{[](const typename List<std::string>::Nil &)
                                   -> std::shared_ptr<List<int64_t>> {
                                 return List<int64_t>::nil();
                               },
                               [](const typename List<std::string>::Cons &_args)
                                   -> std::shared_ptr<List<int64_t>> {
                                 std::cout << _args.d_a0 << '\n';
                                 std::shared_ptr<List<int64_t>> rest_ =
                                     collect_lengths(_args.d_a1);
                                 return List<int64_t>::cons(_args.d_a0.length(),
                                                            rest_);
                               }},
                    xs->v());
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
