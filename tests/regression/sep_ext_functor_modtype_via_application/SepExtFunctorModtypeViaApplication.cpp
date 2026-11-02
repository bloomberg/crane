#include "SepExtFunctorModtypeViaApplication.h"

#include "Datatypes.h"
#include "Inner.h"
#include "Nat.h"

namespace SepExtFunctorModtypeViaApplication {

Datatypes::Nat YY::f(bool b) {
  if (b) {
    return Datatypes::Nat::s(Datatypes::Nat::o());
  } else {
    return Datatypes::Nat::o();
  }
}

} // namespace SepExtFunctorModtypeViaApplication
