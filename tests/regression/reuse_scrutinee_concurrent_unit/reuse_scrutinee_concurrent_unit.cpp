#include "reuse_scrutinee_concurrent_unit.h"

ReuseScrutineeConcurrentUnit::lst
ReuseScrutineeConcurrentUnit::build(uint64_t n) {
  if (n <= 0) {
    return lst::nil();
  } else {
    uint64_t k = n - 1;
    return lst::cons(k, build(k));
  }
}

uint64_t
ReuseScrutineeConcurrentUnit::len(const ReuseScrutineeConcurrentUnit::lst &l) {
  if (std::holds_alternative<typename ReuseScrutineeConcurrentUnit::lst::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseScrutineeConcurrentUnit::lst::Cons>(l.v());
    return (len(*a1) + 1);
  }
}

/// Matches on n and rebuilds O in the O branch: a reuse candidate.
uint64_t ReuseScrutineeConcurrentUnit::churn(
    uint64_t n, const ReuseScrutineeConcurrentUnit::lst &l) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t k = n - 1;
    return (len(lst::cons(UINT64_C(0), l)) + churn(k, l));
  }
}

void ReuseScrutineeConcurrentUnit::worker(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t k = n - 1;
    []() -> void {
      if (churn(UINT64_C(100), shared) == UINT64_C(500)) {
        return;
      } else {
        std::cout << std::string("wrong total") << '\n';
        return;
      }
    }();
    worker(k);
    return;
  }
}

void ReuseScrutineeConcurrentUnit::test() {
  crane::thread t1 = crane::thread(worker, UINT64_C(20));
  crane::thread t2 = crane::thread(worker, UINT64_C(20));
  std::move(t1).join();
  std::move(t2).join();
  return;
}

void ReuseScrutineeConcurrentUnit::run(std::monostate) {
  {
    test();
    return;
  }
}

uint64_t ReuseScrutineeConcurrentUnit::total(std::monostate) {
  return churn(UINT64_C(10), shared);
}
