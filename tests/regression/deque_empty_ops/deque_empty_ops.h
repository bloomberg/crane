#ifndef INCLUDED_DEQUE_EMPTY_OPS
#define INCLUDED_DEQUE_EMPTY_OPS

#include <deque>
#include <type_traits>
#include <utility>

struct DequeEmptyOps {
  static uint64_t double_(uint64_t n);
  static std::deque<uint64_t> dup(uint64_t n);
  static std::deque<uint64_t> run_map(const std::deque<uint64_t> &l);
  static std::deque<uint64_t> run_flatmap(const std::deque<uint64_t> &l);
  static std::deque<uint64_t>
  run_concat(const std::deque<std::deque<uint64_t>> &_x0);
};

#endif // INCLUDED_DEQUE_EMPTY_OPS
