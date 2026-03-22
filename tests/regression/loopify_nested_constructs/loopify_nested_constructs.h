#ifndef INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
#define INCLUDED_LOOPIFY_NESTED_CONSTRUCTS

#include <algorithm>
#include <any>
#include <cassert>
#include <functional>
#include <iostream>
#include <memory>
#include <optional>
#include <stdexcept>
#include <string>
#include <utility>
#include <variant>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_r_v<R, F &, Args &...>;

template <class... Ts> struct Overloaded : Ts... {
  using Ts::operator()...;
};
template <class... Ts> Overloaded(Ts...) -> Overloaded<Ts...>;

struct Nat {
  __attribute__((pure)) static std::pair<unsigned int, unsigned int>
  divmod(const unsigned int x, const unsigned int y, const unsigned int q,
         const unsigned int u);
  __attribute__((pure)) static unsigned int div(const unsigned int x,
                                                const unsigned int y);
};

struct LoopifyNestedConstructs {
  __attribute__((pure)) static unsigned int multi_let(const unsigned int n);
  __attribute__((pure)) static unsigned int
  nested_if_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int nested_if(const unsigned int n);
  __attribute__((pure)) static unsigned int deep_nest(const unsigned int n);
  __attribute__((pure)) static unsigned int let_nested(const unsigned int n);
  __attribute__((pure)) static unsigned int
  mod_pattern_fuel(const unsigned int fuel, const unsigned int n);
  __attribute__((pure)) static unsigned int mod_pattern(const unsigned int n);
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  tuple_constr(const unsigned int n);
  __attribute__((pure)) static unsigned int
  alternating_ops(const unsigned int n);
  __attribute__((pure)) static bool chained_comp_fuel(const unsigned int fuel,
                                                      const unsigned int n);
  __attribute__((pure)) static unsigned int chained_comp(const unsigned int n);
  __attribute__((pure)) static unsigned int
  compute_with_lets(const unsigned int n);
  __attribute__((pure)) static unsigned int nested_match(const unsigned int n);
};

#endif // INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
