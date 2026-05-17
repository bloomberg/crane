#ifndef INCLUDED_THREAD
#define INCLUDED_THREAD

#include <chrono>
#include <cstdint>
#include <iostream>
#include <string>
#include <thread>
#include <variant>

using namespace std::string_literals;

struct threadtest {
  static void fun1(unsigned int n);
  static void fun2(unsigned int n);
  static void test(unsigned int m, unsigned int n);
  static void test_pure(unsigned int m, unsigned int n);
};

#endif // INCLUDED_THREAD
