#ifndef INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
#define INCLUDED_LOOPIFY_NESTED_CONSTRUCTS

#include <utility>
#include <variant>
#include <vector>

struct LoopifyNestedConstructs {
  static unsigned int multi_let(unsigned int n);
  static unsigned int nested_if_fuel(unsigned int fuel, unsigned int n);
  static unsigned int nested_if(unsigned int n);
  static unsigned int deep_nest(unsigned int n);
  static unsigned int let_nested(unsigned int n);
  static unsigned int mod_pattern_fuel(unsigned int fuel, unsigned int n);
  static unsigned int mod_pattern(unsigned int n);
  static std::pair<std::pair<unsigned int, unsigned int>, unsigned int>
  tuple_constr(unsigned int n);
  static unsigned int alternating_ops(unsigned int n);
  static bool chained_comp_fuel(unsigned int fuel, unsigned int n);
  static unsigned int chained_comp(unsigned int n);
  static unsigned int compute_with_lets(unsigned int n);
  static unsigned int nested_match(unsigned int n);
};

#endif // INCLUDED_LOOPIFY_NESTED_CONSTRUCTS
