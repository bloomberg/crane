#include "reuse_summary_concurrent_unit.h"

ReuseSummaryConcurrentUnit::lst ReuseSummaryConcurrentUnit::build(uint64_t n) {
  if (n <= 0) {
    return lst::nil();
  } else {
    uint64_t k = n - 1;
    return lst::cons(k, build(k));
  }
}

uint64_t
ReuseSummaryConcurrentUnit::len(const ReuseSummaryConcurrentUnit::lst &l) {
  if (std::holds_alternative<typename ReuseSummaryConcurrentUnit::lst::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename ReuseSummaryConcurrentUnit::lst::Cons>(l.v());
    return (len(*a1) + 1);
  }
}

uint64_t
ReuseSummaryConcurrentUnit::step(const ReuseSummaryConcurrentUnit::lst &l) {
  return len(lst::cons(UINT64_C(0), l));
}

uint64_t
ReuseSummaryConcurrentUnit::churn(uint64_t n,
                                  const ReuseSummaryConcurrentUnit::lst &l) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t k = n - 1;
    return (step(l) + churn(k, l));
  }
}

void ReuseSummaryConcurrentUnit::worker(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t k = n - 1;
    []() -> void {
      if (churn(UINT64_C(200), shared) == UINT64_C(0)) {
        std::cout << std::string("unreachable") << '\n';
        return;
      } else {
        return;
      }
    }();
    worker(k);
    return;
  }
}

void ReuseSummaryConcurrentUnit::test() {
  crane::thread t1 = crane::thread(worker, UINT64_C(20));
  crane::thread t2 = crane::thread(worker, UINT64_C(20));
  std::move(t1).join();
  std::move(t2).join();
  return;
}

void ReuseSummaryConcurrentUnit::run(std::monostate) {
  {
    test();
    return;
  }
}
