#pragma once

#include <crane_string.h>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <string_view>
#include <utility>
#include <variant>

struct iotest {
  static void test1(const std::string &_x);
  static void test2(const std::string &s);
  static void test3(const std::string &s);
  static std::string test4();
  static void test5();
};
