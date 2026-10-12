#include "par_future_read_twice.h"

uint64_t ParFutureReadTwice::sq(uint64_t n) { return (n * n); }

uint64_t ParFutureReadTwice::twice(uint64_t n) {
  std::future<uint64_t> t = std::async(std::launch::async, sq, n);
  uint64_t a = t.get();
  uint64_t b = std::move(t).get();
  return (a + b);
}

List<std::future<uint64_t>>
ParFutureReadTwice::spawn_all(const List<uint64_t> &l) {
  if (std::holds_alternative<typename List<uint64_t>::Nil>(l.v())) {
    return List<std::future<uint64_t>>::nil();
  } else {
    const auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(l.v());
    std::future<uint64_t> f = std::async(std::launch::async, sq, a0);
    List<std::future<uint64_t>> fs = spawn_all(*a1);
    return List<std::future<uint64_t>>::cons(std::move(f), std::move(fs));
  }
}

uint64_t ParFutureReadTwice::join_all(const List<std::future<uint64_t>> &l) {
  if (std::holds_alternative<typename List<std::future<uint64_t>>::Nil>(
          l.v())) {
    return UINT64_C(0);
  } else {
    const auto &[a0, a1] =
        std::get<typename List<std::future<uint64_t>>::Cons>(l.v());
    uint64_t a = a0.get();
    uint64_t b = join_all(*a1);
    return (a + b);
  }
}
