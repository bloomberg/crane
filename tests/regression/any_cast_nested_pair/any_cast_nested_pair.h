#ifndef INCLUDED_ANY_CAST_NESTED_PAIR
#define INCLUDED_ANY_CAST_NESTED_PAIR

#include "obj.h"
#include <any>
#include <utility>
#include <variant>

struct AnyCastNestedPair {
  using SemVal = crane::obj /* AXIOM TO BE REALIZED */;
  using symbols_semty = crane::obj;
  static uint64_t apply_pred(symbols_semty input);
  static uint64_t test_pred(uint64_t a, uint64_t b);
};

#endif // INCLUDED_ANY_CAST_NESTED_PAIR
