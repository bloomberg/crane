#include "io.h"

void iotest::test1(std::string) { return; }

void iotest::test2(std::string s) {
  std::cout << s;
  return;
}

void iotest::test3(std::string s) {
  std::cout << s << '\n';
  return;
}

std::string iotest::test4() {
  std::cout << std::string("what is your name?") << '\n';
  std::string s2;
  std::getline(std::cin, s2);
  std::cout << std::string("hello ") + s2 << '\n';
  return std::string("I read the name ") + s2 +
         std::string(" from the command line!");
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
  return;
}
