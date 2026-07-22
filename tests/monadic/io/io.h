#ifndef INCLUDED_IO
#define INCLUDED_IO

#include <filesystem>
#include <fstream>
#include <iostream>
#include <string>
#include <system_error>
#include <variant>

using namespace std::string_literals;

struct iotest {
  static void test1(std::string _x);
  static void test2(std::string s);
  static void test3(std::string s);
  static std::string test4();
  static void test5();
};

#endif // INCLUDED_IO
