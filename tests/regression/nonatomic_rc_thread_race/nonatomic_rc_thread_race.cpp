#include "nonatomic_rc_thread_race.h"

NonatomicRcThreadRace::lst NonatomicRcThreadRace::build(uint64_t n) {
  if (n <= 0) {
    return lst::nil();
  } else {
    uint64_t k = n - 1;
    return lst::cons(k, build(k));
  }
}

uint64_t NonatomicRcThreadRace::len(const NonatomicRcThreadRace::lst &l) {
  if (std::holds_alternative<typename NonatomicRcThreadRace::lst::Nil>(l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename NonatomicRcThreadRace::lst::Cons>(l.v());
    return (len(*a1) + 1);
  }
}

uint64_t NonatomicRcThreadRace::step(const NonatomicRcThreadRace::lst &l) {
  return len(lst::cons(UINT64_C(0), l));
}

uint64_t NonatomicRcThreadRace::churn(uint64_t n,
                                      const NonatomicRcThreadRace::lst &l) {
  if (n <= 0) {
    return UINT64_C(0);
  } else {
    uint64_t k = n - 1;
    return (step(l) + churn(k, l));
  }
}

void NonatomicRcThreadRace::worker(uint64_t n) {
  if (n <= 0) {
    return;
  } else {
    uint64_t k = n - 1;
    []() -> void {
      if (churn(UINT64_C(2000), shared) == UINT64_C(0)) {
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

void NonatomicRcThreadRace::test() {
  std::thread t1 = std::thread(worker, UINT64_C(200));
  std::thread t2 = std::thread(worker, UINT64_C(200));
  t1.join();
  t2.join();
  return;
}

void NonatomicRcThreadRace::run(std::monostate) {
  {
    test();
    return;
  }
}
