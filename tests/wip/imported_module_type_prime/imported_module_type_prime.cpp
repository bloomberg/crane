#include "imported_module_type_prime.h"

/// A module type declared in another library is re-emitted as a concept, but
/// its name is copied verbatim instead of being sanitised, so the apostrophe in
/// TotalLeBool' reaches the C++ output.  The reference in the functor's
/// template head is sanitised, to TotalLeBool_, so the two never agree.
bool ImportedModuleTypePrime::NatOrd::leb(uint64_t x0_, uint64_t x1_) {
  return x0_ <= x1_;
}
