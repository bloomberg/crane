#include <fstream>
#include <functional>
#include <io.h>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

void iotest::test1(const std::string _x) { return; }

std::shared_ptr<Unit::unit> iotest::test2(const std::string s) {
  std::cout << s;
  return Unit::unit::ctor::tt_();
}

void iotest::test3(const std::string s) {
  std::cout << s << '\n';
  return;
}

std::string iotest::test4() {
  std::cout << "what is your name?" << '\n';
  std::string s2 = []() -> std::string {
    std::string s;
    std::getline(std::cin, s);
    return s;
  }();
  std::cout << "hello " + s2 << '\n';
  return "I read the name " + s2 + " frome the command line!";
}

void iotest::test5() {
  std::string s = []() -> std::string {
    std::ifstream file("file.txt");
    if (!file) {
      std::cerr << "Failed to open file " << "file.txt" << '\n';
      return std::string{};
    }
    return std::string(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
  }();
  std::cout << s << '\n';
  return;
}
