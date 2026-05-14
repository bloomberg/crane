#include "LambdaCapturePerf.h"

#include "Datatypes.h"
#include "ListDef.h"

namespace LambdaCapturePerf {

Datatypes::List<unsigned int> LambdaCapturePerf::iota(const unsigned int n) {
  if (n <= 0) {
    return Datatypes::template List<unsigned int>::nil();
  } else {
    unsigned int n_ = n - 1;
    return Datatypes::template List<unsigned int>::cons(n_, iota(n_));
  }
}

Datatypes::List<unsigned int> LambdaCapturePerf::map_with_captured_list(
    Datatypes::List<unsigned int> captured,
    const Datatypes::List<unsigned int> &xs) {
  return xs.template map<unsigned int>(
      [=](const unsigned int x) mutable { return (x + captured.length()); });
}

} // namespace LambdaCapturePerf
