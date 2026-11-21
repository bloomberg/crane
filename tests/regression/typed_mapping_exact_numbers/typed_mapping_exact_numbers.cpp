#include "typed_mapping_exact_numbers.h"

boost::multiprecision::cpp_int
TypedMappingExactNumbers::factorial(const boost::multiprecision::cpp_int &n) {
  if (n == 0) {
    return boost::multiprecision::cpp_int("1");
  } else {
    boost::multiprecision::cpp_int k = boost::multiprecision::cpp_int(n - 1);
    return boost::multiprecision::cpp_int(n * factorial(std::move(k)));
  }
}

bool
TypedMappingExactNumbers::exceeds_big(const boost::multiprecision::cpp_int &n) {
  return (big < n);
}

boost::multiprecision::cpp_int
TypedMappingExactNumbers::predecessor(const boost::multiprecision::cpp_int &n) {
  if (n == 0) {
    return boost::multiprecision::cpp_int("0");
  } else {
    boost::multiprecision::cpp_int k = boost::multiprecision::cpp_int(n - 1);
    return k;
  }
}

boost::multiprecision::cpp_int
TypedMappingExactNumbers::sum3(const boost::multiprecision::cpp_int &a,
                               const boost::multiprecision::cpp_int &b,
                               const boost::multiprecision::cpp_int &c) {
  return boost::multiprecision::cpp_int(boost::multiprecision::cpp_int(a + b) +
                                        c);
}
