#ifndef INCLUDED_EFFECT_COMPOSE
#define INCLUDED_EFFECT_COMPOSE

#include <functional>
#include <future>
#include <iostream>
#include <string>
#include <utility>
#include <variant>

using namespace std::string_literals;

struct EffectCompose {
  static uint64_t par_double(uint64_t n);
  static uint64_t par_add(uint64_t a, uint64_t b);
  static uint64_t par_compute_and_greet(uint64_t n);
};

#endif // INCLUDED_EFFECT_COMPOSE
