#ifndef INCLUDED_EFFECT_COMPOSE
#define INCLUDED_EFFECT_COMPOSE

#include <functional>
#include <future>
#include <iostream>
#include <string>
#include <type_traits>
#include <variant>

using namespace std::string_literals;
template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct EffectCompose {
  /// Spawn a future that doubles a number, retrieve the result.
  static unsigned int par_double(const unsigned int n);
  /// Use parE to compute two values in parallel and add them.
  static unsigned int par_add(const unsigned int a, const unsigned int b);
  /// Parallel computation with IO: compute then print.
  static unsigned int par_compute_and_greet(const unsigned int n);
};

#endif // INCLUDED_EFFECT_COMPOSE
