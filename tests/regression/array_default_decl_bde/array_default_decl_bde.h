#pragma once

#include <bsl_concepts.h>
#include <bsl_cstdint.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_vector.h>
#include <persistent_array.h>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

struct ArrayDefaultDeclBde {
  static inline const unsigned int result = []() {
    persistent_array<unsigned int> w;
    unsigned int n = 5u;
    w = persistent_array<unsigned int>(INT64_C(2), n);
    return w.get(INT64_C(0));
  }();
};
