#include "vector_cases_deduction.h"

Nat VectorCasesDeduction::hd3(const T<Nat> &v) {
  return Vector::template hd<Nat>(Nat::s(Nat::s(Nat::o())), v);
}
