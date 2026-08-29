#ifndef INCLUDED_ANY_CAST_NESTED_PAIR
#define INCLUDED_ANY_CAST_NESTED_PAIR

#include <any>
#include <utility>
#include <variant>

struct AnyCastNestedPair {
  using SemVal = std::any /* AXIOM TO BE REALIZED */;
  using symbols_semty = std::any;
  static uint64_t apply_pred(symbols_semty input);
  static uint64_t test_pred(uint64_t a, uint64_t b);
};

#endif // INCLUDED_ANY_CAST_NESTED_PAIR
