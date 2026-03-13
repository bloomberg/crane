#include <io.h>

#include <algorithm>
#include <any>
#include <cassert>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <variant>

void iotest::test1(const std::string _x) { return; }

__attribute__((pure)) Unit iotest::test2(const std::string s) {
  std::cout << s;
  return Unit::e_TT;
}

__attribute__((pure)) void iotest::test3(const std::string s) {
  std::cout << s << '\n';
  return;
}

__attribute__((pure)) std::string iotest::test4() {
  std::cout << "what is your name?"s << '\n';
  std::string s2 = []() -> std::string {
    std::string s;
    std::getline(std::cin, s);
    return s;
  }();
  std::cout << "hello "s + s2 << '\n';
  return "I read the name "s + s2 + " from the command line!"s;
}

__attribute__((pure)) void iotest::test5() {
  std::string s = []() -> std::string {
    std::ifstream file("file.txt"s);
    if (!file) {
      std::cerr << "Failed to open file " << "file.txt"s << '\n';
      return std::string{};
    }
    return std::string(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
  }();
  std::cout << s << '\n';
  return;
}
