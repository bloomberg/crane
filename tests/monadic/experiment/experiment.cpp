#include <algorithm>
#include <experiment.h>
#include <fstream>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <utility>
#include <variant>

void TestITree::test1() {
  std::string s = []() -> std::string {
    std::string s;
    std::getline(std::cin, s);
    return s;
  }();
  meta22 _x = std::cout << s << '\n';
  return;
}

void TestITree::test3(const std::string s) {
  meta11 _x = std::cout << s << '\n';
  return;
}

std::string TestITree::test4() {
  meta11 _x = std::cout << "what is your name?" << '\n';
  std::string s2 = []() -> std::string {
    std::string s;
    std::getline(std::cin, s);
    return s;
  }();
  meta33 _x0 = std::cout << "hello " + s2 << '\n';
  return "I read the name " + s2 + " frome the command line!";
}

void TestITree::test5() {
  std::string s = []() -> std::string {
    std::ifstream file("file.txt");
    if (!file) {
      std::cerr << "Failed to open file " << "file.txt" << '\n';
      return std::string{};
    }
    return std::string(std::istreambuf_iterator<char>(file),
                       std::istreambuf_iterator<char>());
  }();
  meta22 _x = std::cout << s << '\n';
  return;
}
