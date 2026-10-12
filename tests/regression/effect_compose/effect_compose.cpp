#include "effect_compose.h"

/// Spawn a future that doubles a number, retrieve the result.
uint64_t EffectCompose::par_double(uint64_t n) {
  crane::fn<uint64_t(uint64_t)> double0 = [](uint64_t x) { return (x + x); };
  std::shared_future<uint64_t> t =
      std::async(std::launch::async, std::move(double0), n).share();
  return std::move(t).get();
}

/// Use parE to compute two values in parallel and add them.
uint64_t EffectCompose::par_add(uint64_t a, uint64_t b) {
  crane::fn<uint64_t(uint64_t)> double0 = [](uint64_t x) { return (x + x); };
  std::shared_future<uint64_t> t1 =
      std::async(std::launch::async, double0, a).share();
  std::shared_future<uint64_t> t2 =
      std::async(std::launch::async, std::move(double0), b).share();
  uint64_t r1 = std::move(t1).get();
  uint64_t r2 = std::move(t2).get();
  return (r1 + r2);
}

/// Parallel computation with IO: compute then print.
uint64_t EffectCompose::par_compute_and_greet(uint64_t n) {
  crane::fn<uint64_t(uint64_t)> succ = [](uint64_t x) {
    return (x + UINT64_C(1));
  };
  std::cout << std::string("computing...") << '\n';
  std::shared_future<uint64_t> t =
      std::async(std::launch::async, std::move(succ), n).share();
  uint64_t result = std::move(t).get();
  std::cout << std::string("done") << '\n';
  return result;
}
