#ifndef INCLUDED_IO
#define INCLUDED_IO

#include <fstream>
#include <iostream>
#include <string>
#include <utility>
#include <variant>

struct iotest {
  static void test1(std::string _x);
  static void test2(std::string s);
  static void test3(std::string s);
  static std::string test4();
  static void test5();
};

#endif // INCLUDED_IO
