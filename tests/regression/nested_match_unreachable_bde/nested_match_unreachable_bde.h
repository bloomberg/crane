#pragma once

#include "obj.h"
#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_vector.h>
#include <utility>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

enum class Comparison;
enum class Comparison { e_EQ, e_LT, e_GT };

struct NestedMatchUnreachableBde {
  static bool same(Comparison c, Comparison d);
  static inline const bool t1 = same(Comparison::e_LT, Comparison::e_LT);
  static inline const bool t2 = same(Comparison::e_LT, Comparison::e_GT);
  static inline const bool t3 = same(Comparison::e_GT, Comparison::e_GT);
};
