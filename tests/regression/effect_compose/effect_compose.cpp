#include <effect_compose.h>

#include <functional>
#include <future>
#include <iostream>
#include <string>
#include <type_traits>
#include <variant>

/// Spawn a future that doubles a number, retrieve the result.
unsigned int EffectCompose::par_double(const unsigned int &n) {
  std::function<unsigned int(unsigned int)> double0 =
      [](const unsigned int &x) { return (x + x); };
  std::future<unsigned int> t = std::async(std::launch::async, double0, n);
  return t.get();
}

/// Use parE to compute two values in parallel and add them.
unsigned int EffectCompose::par_add(const unsigned int &a, unsigned int b) {
  std::function<unsigned int(unsigned int)> double0 =
      [](const unsigned int &x) { return (x + x); };
  std::future<unsigned int> t1 = std::async(std::launch::async, double0, a);
  std::future<unsigned int> t2 = std::async(std::launch::async, double0, b);
  unsigned int r1 = t1.get();
  unsigned int r2 = t2.get();
  return (r1 + r2);
}

/// Parallel computation with IO: compute then print.
unsigned int EffectCompose::par_compute_and_greet(unsigned int n) {
  std::function<unsigned int(unsigned int)> succ = [](const unsigned int &x) {
    return (x + 1u);
  };
  std::cout << "computing..."s << '\n';
  std::future<unsigned int> t = std::async(std::launch::async, succ, n);
  unsigned int result = t.get();
  std::cout << "done"s << '\n';
  return result;
}
