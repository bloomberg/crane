#include "rank2_method_arg.h"

uint64_t Rank2MethodArg::run(uint64_t k) {
  return AI::app2([](const auto &x) { return x; }, (k + UINT64_C(4)));
}
