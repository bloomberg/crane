#include <io.h>

#include <fstream>
#include <string>
#include <type_traits>

void iotest::test1(const std::string _x) { return; }

Unit iotest::test2(const std::string s) {
  std::cout << s;
  return Unit::e_TT;
}

void iotest::test3(const std::string s) {
  std::cout << s << '\n';
  return;
}

std::string iotest::test4() {
  std::cout << "what is your name?"s << '\n';
  std::string s2 = []() -> std::string {
    std::string s;
    std::getline(std::cin, s);
    return s;
  }();
  std::cout << "hello "s + s2 << '\n';
  return "I read the name "s + s2 + " from the command line!"s;
}

void iotest::test5() {
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
