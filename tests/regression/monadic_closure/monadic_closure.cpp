#include <monadic_closure.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. Lambda capturing a bind result
int64_t MonadicClosure::capture_bind() {
  std::string line;
  std::getline(std::cin, line);
  return ((_capture_bind_f(0u, line) + _capture_bind_f(1u, line)) &
          0x7FFFFFFFFFFFFFFFLL);
}

int64_t MonadicClosure::test_apply_after() {
  return apply_after_effect<std::string, int64_t>(
      [](std::string _x0) -> int64_t { return _x0.length(); },
      []() -> std::string {
        std::string _r;
        std::getline(std::cin, _r);
        return _r;
      }());
}

/// 3. Function returning a closure from monadic context
std::function<std::string(std::string)> MonadicClosure::make_greeter() {
  std::string prefix;
  std::getline(std::cin, prefix);
  return [=](std::string name) mutable { return prefix + name; };
}

int64_t MonadicClosure::test_with_length() {
  return with_length(
      [](int64_t n) { return ((n + int64_t(1)) & 0x7FFFFFFFFFFFFFFFLL); });
}

/// 5. Nested closures over bindings
int64_t MonadicClosure::nested_capture() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  int64_t la = a.length();
  int64_t lb = b.length();
  return ((la + lb) & 0x7FFFFFFFFFFFFFFFLL);
}

unsigned int MonadicClosure::test_count() {
  return count_matching([](std::string s) { return s.length() == int64_t(0); },
                        List<std::string>::cons(
                            "a", List<std::string>::cons(
                                     "", List<std::string>::cons(
                                             "bc", List<std::string>::nil()))));
}

/// 7. Effect inside a let, result used later
int64_t MonadicClosure::let_effect_capture() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = line.length();
  std::cout << line << '\n';
  return len;
}

/// 8. Two closures with different captured variables
std::pair<int64_t, int64_t> MonadicClosure::two_closures() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  int64_t la = a.length();
  int64_t lb = b.length();
  return std::make_pair(la, lb);
}
