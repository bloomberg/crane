#pragma once

#include "crane_fn.h"
#include "fn.h"
#include "obj.h"
#include "shared_block.h"
#include <cstdint>
#include <functional>
#include <utility>

struct Datatypes {
  static crane::obj id(crane::obj x);
};

struct IdOverAppliedLambdaArg {
  static uint64_t one_arg(uint64_t k);
  static uint64_t two_args(uint64_t k);
  static uint64_t control(uint64_t k);
};
