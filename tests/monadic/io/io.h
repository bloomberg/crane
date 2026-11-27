#pragma once

#include <crane_string.h>
#include <fstream>
#include <iostream>
#include <iterator>
#include <string>
#include <string_view>
#include <variant>

struct iotest {
  static void test1(std::string_view _x);
  static void test2(const std::string &s);
  static void test3(const std::string &s);
  static std::string test4();
  static void test5();
};
