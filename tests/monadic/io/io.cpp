#include "io.h"

void iotest::test1(std::string_view) {}

void iotest::test2(const std::string &s) { std::cout << s; }

void iotest::test3(const std::string &s) { std::cout << s << '\n'; }

std::string iotest::test4() {
  std::cout << std::string("what is your name?") << '\n';
  std::string s2;
  std::getline(std::cin, s2);
  std::cout << ((std::string("hello ") + s2).substr(0, 16777211)) << '\n';
  return (std::string("I read the name ") +
          (s2 + std::string(" from the command line!")).substr(0,
                                                               16777211))
             .substr(0, 16777211);
}

void iotest::test5() {
  std::string s = [&]() -> std::string {
    std::ifstream file(std::string("file.txt"));
    if (!file) {
      std::cerr << "Failed to open file " << std::string("file.txt") << '\n';
      return std::string{};
    }
    return std::string(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
  }();
  std::cout << s << '\n';
}
