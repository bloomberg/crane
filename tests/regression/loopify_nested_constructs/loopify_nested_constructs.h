#ifndef INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
#define INCLUDED_LOOPIFY_NESTED_CONSTRUCTS

#include <utility>
#include <variant>
#include <vector>

struct LoopifyNestedConstructs {
  static uint64_t multi_let(uint64_t n);
  static uint64_t nested_if_fuel(uint64_t fuel, uint64_t n);
  static uint64_t nested_if(uint64_t n);
  static uint64_t deep_nest(uint64_t n);
  static uint64_t let_nested(uint64_t n);
  static uint64_t mod_pattern_fuel(uint64_t fuel, uint64_t n);
  static uint64_t mod_pattern(uint64_t n);
  static std::pair<std::pair<uint64_t, uint64_t>, uint64_t>
  tuple_constr(uint64_t n);
  static uint64_t alternating_ops(uint64_t n);
  static bool chained_comp_fuel(uint64_t fuel, uint64_t n);
  static uint64_t chained_comp(uint64_t n);
  static uint64_t compute_with_lets(uint64_t n);
  static uint64_t nested_match(uint64_t n);
};

#endif // INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
