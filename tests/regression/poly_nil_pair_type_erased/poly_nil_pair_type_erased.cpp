#include "poly_nil_pair_type_erased.h"

/// Found by Ephyra (https://github.com/datadog-labs/ephyra) differential
/// testing of Crane: a generated program, shrunk by ephyra and reduced by hand.
///
/// @nil (nat * A) in a polymorphic definition still loses the type
/// parameter (the @nil A case in poly_nil_type_erased is fixed): the
/// fold_left receiver is a list of crane::obj pairs and its requires
/// clause rejects the step function.
String PolyNilPairTypeErased::f4(uint64_t n) {
  return f1<PolyNilPairTypeErased::sz_nat, uint64_t>(n);
}
