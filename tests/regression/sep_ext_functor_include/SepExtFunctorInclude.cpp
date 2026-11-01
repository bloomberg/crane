#include "SepExtFunctorInclude.h"

#include "Datatypes.h"
#include "Nat.h"
#include "Ord.h"

namespace SepExtFunctorInclude {

bool NatOrd::leb(const Datatypes::Nat &x0_, const Datatypes::Nat &x1_) {
  return Nat::leb(x0_, x1_);
}

} // namespace SepExtFunctorInclude
