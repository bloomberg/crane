#pragma once

#include <chrono>
#include <cstdint>

struct Clock {
  static int64_t get_steady();
  static int64_t get_system();
  static int64_t get_time();
  static int64_t elapsed();
};
