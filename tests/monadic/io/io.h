#ifndef INCLUDED_IO
#define INCLUDED_IO

#include <filesystem>
#include <fstream>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;

struct iotest {
  static void test1(const std::string _x);
  static void test2(const std::string s);
  static void test3(const std::string s);
  static std::string test4();
  static void test5();
};

#endif // INCLUDED_IO
