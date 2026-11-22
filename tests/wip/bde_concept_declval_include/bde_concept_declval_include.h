#pragma once

#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_vector.h>

using namespace BloombergLP;
template <class From, class To>
concept convertible_to = bsl::is_convertible<From, To>::value;

template <class T, class U>
concept same_as = bsl::is_same<T, U>::value && bsl::is_same<U, T>::value;

template <typename M>
concept SIG = requires {
  typename M::t;
  {
    M::op(bsl::declval<typename M::t>(), bsl::declval<typename M::t>())
  } -> same_as<typename M::t>;
};

struct BdeConceptDeclvalInclude {
  struct N {
    using t = unsigned int;
    static unsigned int op(unsigned int x0_, unsigned int x1_);
  };

  template <SIG E> struct F {
    static typename E::t twice(typename E::t x) { return E::op(x, x); }
  };

  using FN = F<N>;
  static inline const unsigned int result = FN::twice(4u);
};
