#ifndef INCLUDED_EFFECT_COMPOSE
#define INCLUDED_EFFECT_COMPOSE

#include <functional>
#include <future>
#include <iostream>
#include <memory>
#include <optional>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;

struct EffectCompose {
  /// Spawn a future that doubles a number, retrieve the result.
  static unsigned int par_double(const unsigned int n);
  /// Use parE to compute two values in parallel and add them.
  static unsigned int par_add(const unsigned int a, const unsigned int b);
  /// Parallel computation with IO: compute then print.
  static unsigned int par_compute_and_greet(const unsigned int n);
};

#endif // INCLUDED_EFFECT_COMPOSE
