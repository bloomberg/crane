#include "io.h"

void iotest::test1(std::string_view) {}

void iotest::test2(const std::string &s) { std::cout << s; }

void iotest::test3(const std::string &s) { std::cout << s << '\n'; }

std::string iotest::test4() {
  std::cout << std::string("what is your name?") << '\n';
  std::string s2;
  std::getline(std::cin, s2);
  std::cout << crane::string_capped(std::string("hello ") + s2) << '\n';
  return crane::string_capped(
      std::string("I read the name ") +
      crane::string_capped(s2 + std::string(" from the command line!")));
}

void iotest::test5() {
  std::cout << [&]() -> std::string {
    std::ifstream file(std::string("file.txt"));
    if (!file) {
      std::cerr << "Failed to open file " << std::string("file.txt") << '\n';
      return std::string{};
    }
    return std::string(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
  }() << '\n';
}
