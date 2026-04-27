#ifndef INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
#define INCLUDED_LOOPIFY_NESTED_CONSTRUCTS

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename F, typename R, typename... Args>
concept MapsTo = std::is_invocable_v<F &, Args &...>;

struct LoopifyNestedConstructs {
  __attribute__((pure)) static unsigned int multi_let(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  nested_if_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int nested_if(const unsigned int &n);
  __attribute__((pure)) static unsigned int deep_nest(const unsigned int &n);
  __attribute__((pure)) static unsigned int let_nested(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  mod_pattern_fuel(const unsigned int &fuel, const unsigned int &n);
  __attribute__((pure)) static unsigned int mod_pattern(const unsigned int &n);
  __attribute__((pure)) static std::pair<std::pair<unsigned int, unsigned int>,
                                         unsigned int>
  tuple_constr(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  alternating_ops(const unsigned int &n);
  __attribute__((pure)) static bool chained_comp_fuel(const unsigned int &fuel,
                                                      const unsigned int &n);
  __attribute__((pure)) static unsigned int chained_comp(const unsigned int &n);
  __attribute__((pure)) static unsigned int
  compute_with_lets(const unsigned int &n);
  __attribute__((pure)) static unsigned int nested_match(const unsigned int &n);
};

#endif // INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
