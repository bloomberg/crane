#include "stm_tvar_of_function.h"

uint64_t StmTvarOfFunction::fntv() {
  stm::TVar<crane::fn<uint64_t(uint64_t)>> a =
      stm::newTVar([](uint64_t x) { return x; });
  crane::fn<uint64_t(uint64_t)> f = stm::readTVar(std::move(a));
  return f(UINT64_C(1));
}

uint64_t StmTvarOfFunction::created() {
  return stm::atomically([&] { return fntv(); });
}

uint64_t StmTvarOfFunction::fnw() {
  stm::TVar<crane::fn<uint64_t(uint64_t)>> a =
      stm::newTVar([](uint64_t x) { return (x + 1); });
  stm::writeTVar(a, [](uint64_t x) { return (x + UINT64_C(2)); });
  crane::fn<uint64_t(uint64_t)> f = stm::readTVar(std::move(a));
  return f(UINT64_C(1));
}

uint64_t StmTvarOfFunction::written() {
  return stm::atomically([&] { return fnw(); });
}
