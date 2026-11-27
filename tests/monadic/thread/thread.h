#pragma once

#include "shared_block.h"
#include <chrono>
#include <cstdint>
#include <future>
#include <iostream>
#include <string>
#include <thread>
#include <utility>
#include <variant>
static_assert(crane::rc_is_atomic,
              "this unit runs on several threads, but a header included before "
              "it chose CRANE_NON_ATOMIC_RC");

struct threadtest {
  static void fun1(uint64_t n);
  static void fun2(uint64_t n);
  static void test(uint64_t m, uint64_t n);
  static void test_pure(uint64_t m, uint64_t n);
};
