#include "erased_type_field_lambda.h"

/// A record with a Type field erases its dependent fields to std::any, so
/// pairs is declared List<pair<std::any, std::function<uint64_t(std::any)>>>.
/// The producers are not erased to match: each element is built as a
/// pair<uint64_t, <concrete lambda>>, which does not convert, and the lambda
/// body adds to a std::any besides.
uint64_t ErasedTypeFieldLambda::weigh(const ErasedTypeFieldLambda::slot &s) {
  return s.pairs.template fold_left<uint64_t>(
      [](uint64_t a, const auto &p) { return (a + p.second(p.first)); },
      UINT64_C(0));
}
