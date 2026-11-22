#include "coinductive_bde.h"

#include <bsl_concepts.h>
#include <bsl_functional.h>
#include <bsl_iostream.h>
#include <bsl_memory.h>
#include <bsl_stdexcept.h>
#include <bsl_string.h>
#include <bsl_type_traits.h>
#include <bsl_variant.h>
#include <bsl_vector.h>

namespace BloombergLP {}

CoinductiveBde::stream CoinductiveBde::from(unsigned int n) {
  return stream::lazy_([=]() mutable -> typename CoinductiveBde::stream::SCons {
    return {n, from((n + 1))};
  });
}

List<unsigned int> CoinductiveBde::take(unsigned int k,
                                        const CoinductiveBde::stream &s) {
  if (k <= 0) {
    return List<unsigned int>::nil();
  } else {
    unsigned int k_ = k - 1;
    const auto &[d_a0, d_a1] =
        bsl::get<typename CoinductiveBde::stream::SCons>(s.v());
    return List<unsigned int>::cons(d_a0, take(k_, d_a1));
  }
}
