#include "effect_compose.h"

/// Spawn a future that doubles a number, retrieve the result.
uint64_t EffectCompose::par_double(uint64_t n) {
  std::function<uint64_t(uint64_t)> double0 = [](uint64_t x) {
    return (x + x);
  };
  std::future<uint64_t> t = std::async(std::launch::async, double0, n);
  return t.get();
}

/// Use parE to compute two values in parallel and add them.
uint64_t EffectCompose::par_add(uint64_t a, uint64_t b) {
  std::function<uint64_t(uint64_t)> double0 = [](uint64_t x) {
    return (x + x);
  };
  std::future<uint64_t> t1 = std::async(std::launch::async, double0, a);
  std::future<uint64_t> t2 = std::async(std::launch::async, double0, b);
  uint64_t r1 = t1.get();
  uint64_t r2 = t2.get();
  return (r1 + r2);
}

/// Parallel computation with IO: compute then print.
uint64_t EffectCompose::par_compute_and_greet(uint64_t n) {
  std::function<uint64_t(uint64_t)> succ = [](uint64_t x) {
    return (x + UINT64_C(1));
  };
  std::cout << "computing..."s << '\n';
  std::future<uint64_t> t = std::async(std::launch::async, succ, n);
  uint64_t result = t.get();
  std::cout << "done"s << '\n';
  return result;
}
