#pragma once

#include <cstdint>

struct RecordMatch {
  struct MyRec {
    uint64_t f1;
    uint64_t f2;
    uint64_t f3;
  };

  static uint64_t sum(const MyRec &r);
};
