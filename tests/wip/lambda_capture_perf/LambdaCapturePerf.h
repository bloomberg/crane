#ifndef INCLUDED_LAMBDACAPTUREPERF
#define INCLUDED_LAMBDACAPTUREPERF

#include <memory>
#include <optional>
#include <type_traits>
#include <utility>

#include "Datatypes.h"
#include "ListDef.h"

namespace LambdaCapturePerf {

struct LambdaCapturePerf {
  template <typename T1>
  static Datatypes::List<T1> replicate(const unsigned int n, const T1 x) {
    if (n <= 0) {
      return Datatypes::template List<T1>::nil();
    } else {
      unsigned int n_ = n - 1;
      return Datatypes::template List<T1>::cons(x, replicate<T1>(n_, x));
    }
  }

  static Datatypes::List<unsigned int> iota(const unsigned int n);
  static Datatypes::List<unsigned int>
  map_with_captured_list(Datatypes::List<unsigned int> captured,
                         const Datatypes::List<unsigned int> &xs);
  static inline const Datatypes::List<unsigned int> test_input = iota(500u);
  static inline const unsigned int test = []() {
    Datatypes::List<unsigned int> captured = replicate<unsigned int>(500u, 42u);
    return map_with_captured_list(std::move(captured), test_input).length();
  }();
};

} // namespace LambdaCapturePerf

#endif // INCLUDED_LAMBDACAPTUREPERF
