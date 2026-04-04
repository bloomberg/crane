#include <effect_getline_stress.h>

#include <cstdint>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <string>
#include <type_traits>
#include <utility>
#include <variant>

/// 1. get_line in both branches of if-then-else
std::string EffectGetlineStress::get_or_default(const bool ask) {
  if (ask) {
    return [&]() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
  } else {
    return "default";
  }
}

/// 2. get_line in a match arm
std::string EffectGetlineStress::get_nth_line(const unsigned int n) {
  if (n <= 0) {
    return "none";
  } else {
    unsigned int n0 = n - 1;
    if (n0 <= 0) {
      return [&]() -> std::string {
        std::string _r;
        std::getline(std::cin, _r);
        return _r;
      }();
    } else {
      unsigned int _x = n0 - 1;
      std::string _x0;
      std::getline(std::cin, _x0);
      return [&]() -> std::string {
        std::string _r;
        std::getline(std::cin, _r);
        return _r;
      }();
    }
  }
}

/// 3. Recursive function that uses get_line in a loop
std::shared_ptr<List<std::string>>
EffectGetlineStress::read_lines(const unsigned int n,
                                std::shared_ptr<List<std::string>> acc) {
  if (n <= 0) {
    return std::move(acc);
  } else {
    unsigned int n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    return read_lines(n_, List<std::string>::cons(std::move(line), acc));
  }
}

/// 4. get_line result immediately used in another effect
void EffectGetlineStress::read_and_echo() {
  std::string line;
  std::getline(std::cin, line);
  std::cout << line << '\n';
  return;
}

/// 5. get_line result used in a let chain
int64_t EffectGetlineStress::get_line_length() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = line.length();
  return len;
}

/// 6. Two get_lines with results combined
std::string EffectGetlineStress::concat_two_lines() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return a + b;
}

/// 7. get_line inside a monadic map
std::pair<std::string, int64_t> EffectGetlineStress::get_and_measure() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = line.length();
  return std::make_pair(line, len);
}

/// 8. Conditional get_line with print
std::string EffectGetlineStress::interactive_prompt(const bool ask) {
  if (ask) {
    std::cout << "Enter input:"s << '\n';
    std::string line;
    std::getline(std::cin, line);
    std::cout << "Got it"s << '\n';
    return line;
  } else {
    return "skipped";
  }
}
