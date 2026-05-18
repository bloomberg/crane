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
  static void fun1(uint64_t n);
  static void fun2(uint64_t n);
  static void test(uint64_t m, uint64_t n);
  static void test_pure(uint64_t m, uint64_t n);
};

#endif // INCLUDED_THREAD
