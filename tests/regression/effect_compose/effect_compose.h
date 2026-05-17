#ifndef INCLUDED_EFFECT_COMPOSE
#define INCLUDED_EFFECT_COMPOSE

#include <functional>
#include <future>
#include <iostream>
#include <string>
#include <variant>

using namespace std::string_literals;

struct EffectCompose {
  /// Spawn a future that doubles a number, retrieve the result.
  static uint64_t par_double(uint64_t n);
  /// Use parE to compute two values in parallel and add them.
  static uint64_t par_add(uint64_t a, uint64_t b);
  /// Parallel computation with IO: compute then print.
  static uint64_t par_compute_and_greet(uint64_t n);
};

#endif // INCLUDED_EFFECT_COMPOSE
