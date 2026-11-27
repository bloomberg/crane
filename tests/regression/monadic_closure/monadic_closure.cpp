#include "monadic_closure.h"

/// 1. Lambda capturing a bind result
int64_t MonadicClosure::capture_bind() {
  std::string line;
  std::getline(std::cin, line);
  crane::fn<int64_t(uint64_t)> f = [=, line = std::move(line)](uint64_t) {
    return static_cast<int64_t>(std::string_view{line}.size());
  };
  return static_cast<int64_t>((static_cast<uint64_t>(f(UINT64_C(0))) +
                               static_cast<uint64_t>(f(UINT64_C(1)))) &
                              UINT64_C(9223372036854775807));
}

int64_t MonadicClosure::test_apply_after() {
  return apply_after_effect<std::string, int64_t>(
      [](std::string _x0) -> int64_t {
        return static_cast<int64_t>(std::string_view{_x0}.size());
      },
      []() -> std::string {
        std::string _r;
        std::getline(std::cin, _r);
        return _r;
      }());
}

/// 3. Function returning a closure from monadic context
crane::fn<std::string(std::string)> MonadicClosure::make_greeter() {
  std::string prefix;
  std::getline(std::cin, prefix);
  return [=, prefix = std::move(prefix)](const std::string &name) {
    return (prefix + name).substr(0, 16777211);
  };
}

int64_t MonadicClosure::test_with_length() {
  return with_length([](int64_t n) {
    return static_cast<int64_t>((static_cast<uint64_t>(n) + UINT64_C(1)) &
                                UINT64_C(9223372036854775807));
  });
}

/// 5. Nested closures over bindings
int64_t MonadicClosure::nested_capture() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  int64_t la = static_cast<int64_t>(std::string_view{a}.size());
  int64_t lb = static_cast<int64_t>(std::string_view{b}.size());
  return static_cast<int64_t>(
      (static_cast<uint64_t>(la) + static_cast<uint64_t>(lb)) &
      UINT64_C(9223372036854775807));
}

uint64_t MonadicClosure::test_count() {
  return count_matching(
      [](const std::string &s) {
        return static_cast<int64_t>(std::string_view{s}.size()) == INT64_C(0);
      },
      List<std::string>::cons(
          "a", List<std::string>::cons(
                   "",
                   List<std::string>::cons("bc", List<std::string>::nil()))));
}

/// 7. Effect inside a let, result used later
int64_t MonadicClosure::let_effect_capture() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = static_cast<int64_t>(std::string_view{line}.size());
  std::cout << std::move(line) << '\n';
  return len;
}

/// 8. Two closures with different captured variables
std::pair<int64_t, int64_t> MonadicClosure::two_closures() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  int64_t la = static_cast<int64_t>(std::string_view{a}.size());
  int64_t lb = static_cast<int64_t>(std::string_view{b}.size());
  return std::make_pair(la, lb);
}
