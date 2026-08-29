#include "effect_getline_stress.h"

std::string EffectGetlineStress::get_or_default(bool ask) {
  if (ask) {
    return []() -> std::string {
      std::string _r;
      std::getline(std::cin, _r);
      return _r;
    }();
  } else {
    return "default";
  }
}

std::string EffectGetlineStress::get_nth_line(uint64_t n) {
  if (n <= 0) {
    return "none";
  } else {
    uint64_t n0 = n - 1;
    if (n0 <= 0) {
      return []() -> std::string {
        std::string _r;
        std::getline(std::cin, _r);
        return _r;
      }();
    } else {
      uint64_t _x = n0 - 1;
      std::string _x0;
      std::getline(std::cin, _x0);
      return []() -> std::string {
        std::string _r;
        std::getline(std::cin, _r);
        return _r;
      }();
    }
  }
}

List<std::string> EffectGetlineStress::read_lines(uint64_t n,
                                                  List<std::string> acc) {
  if (n <= 0) {
    return acc;
  } else {
    uint64_t n_ = n - 1;
    std::string line;
    std::getline(std::cin, line);
    return read_lines(n_,
                      List<std::string>::cons(std::move(line), std::move(acc)));
  }
}

void EffectGetlineStress::read_and_echo() {
  std::string line;
  std::getline(std::cin, line);
  std::cout << std::move(line) << '\n';
  return;
}

int64_t EffectGetlineStress::get_line_length() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = static_cast<int64_t>(std::move(line).length());
  return len;
}

std::string EffectGetlineStress::concat_two_lines() {
  std::string a;
  std::getline(std::cin, a);
  std::string b;
  std::getline(std::cin, b);
  return a + b;
}

std::pair<std::string, int64_t> EffectGetlineStress::get_and_measure() {
  std::string line;
  std::getline(std::cin, line);
  int64_t len = static_cast<int64_t>(line.length());
  return std::make_pair(line, len);
}

std::string EffectGetlineStress::interactive_prompt(bool ask) {
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
