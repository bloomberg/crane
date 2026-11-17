#pragma once

#include "fn.h"

enum class Unit;
enum class Unit { TT };

struct RocqBug14843 {
  struct r {
    crane::fn<void(Unit)> f1;
    crane::fn<void(Unit)> f2;
  };

  struct r_ {
    crane::fn<void(Unit)> f1_;
    crane::fn<void(Unit)> f2_;
  };

  struct M {
    static void f1();
    static void f2();
    static inline const r cf =
        r{[](const auto &) { f1(); }, [](const auto &) { f2(); }};
    static void f1_();
    static void f2_();
    static inline const r_ cf_ =
        r_{[](const auto &) { f1_(); }, [](const auto &) { f2_(); }};
  };
};
